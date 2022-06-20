import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Std
import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Set
import LeanCodePrompts.Basic
open Lean Meta Std Elab Parser Mathlib Set
 
def s : Set Nat := fun _ => true
#check s ∩ s

def depsPrompt : IO (Array String) := do
  let file := System.mkFilePath ["data/types.txt"]
  IO.FS.lines file

syntax "(" term ")" : term
syntax "λ" ident "," term : term
syntax "λ"  ident ":" term  "," term : term
syntax "λ" "(" ident ":" term ")" "," term : term
syntax "Π"  ident ":" term  "," term : term
syntax "Π" "(" ident ":" term ")" "," term : term
syntax "⇑" term : term
macro_rules
| `(λ $x:ident : $type:term , $y:term) => 
  `(fun ($x : $type)  => $y)
| `(λ ( $x:ident : $type:term ) , $y:term) => 
  `(fun ($x : $type)  => $y)
| `(Π $x:ident : $type:term , $y:term) => 
  `(($x : $type) →  $y)
| `(Π ( $x:ident : $type:term ) , $y:term) => 
  `(($x : $type) →  $y)
| `(⇑ $x:term) => `($x)

/-- check whether a string parses as a term -/
def checkTerm (s : String) : MetaM Bool := do
  let env ← getEnv
  let chk := runParserCategory env `term  s
  match chk with
  | Except.ok _  => pure true
  | Except.error _  => pure false

/-- split prompts into those that parse -/
def promptsSplit : MetaM ((Array String) × (Array String)) := do 
  let deps ← depsPrompt
  let mut succ: Array String := Array.empty
  let mut fail: Array String := Array.empty
  for type in deps do
    let chk ←  checkTerm type
    if chk then
      succ := succ.push type
    else
      fail := fail.push type
  return (succ, fail)

def promptsSplitCore : CoreM ((Array String) × (Array String)) :=
  promptsSplit.run'



def Lean.Expr.view (expr: Expr) : MetaM String := do
  let stx ← PrettyPrinter.delab  expr
  let fmt ← PrettyPrinter.ppTerm stx
  return fmt.pretty

declare_syntax_cat argument
syntax "(" ident " : " term ")" : argument
syntax "{" ident " : " term "}" : argument
syntax "[" ident " : " term "]" : argument
syntax "[" term "]" : argument

declare_syntax_cat thmStat
syntax "theorem" (ident)? argument*  ":" term : thmStat
syntax argument*  ":" term : thmStat

partial def showSyntax : Syntax → String
| Syntax.node _ _ args => 
  (args.map <| fun s => showSyntax s).foldl (fun acc s => acc ++ " " ++ s) ""
| Lean.Syntax.atom _ val => val
| Lean.Syntax.ident _ _ val _ => val.toString
| _ => ""

def elabThm (s : String)(opens: List String := []) 
  (levelNames : List Name := [`u, `v])
  : TermElabM <| Except String Expr := do
  let env ← getEnv
  let chk := runParserCategory env `thmStat  s
  match chk with
  | Except.ok stx  =>
      match stx with
      | `(thmStat|theorem $_ $args:argument* : $type:term) =>
        elabAux type args
      | `(thmStat|$args:argument* : $type:term) =>
        elabAux type args
      | _ => return Except.error s!"parsed incorrectly to {stx}"
  | Except.error e  => return Except.error e
  where elabAux (type: Syntax)(args: Array Syntax) : 
        TermElabM <| Except String Expr := do
        let header := if opens.isEmpty then "" else 
          (opens.foldl (fun acc s => acc ++ " " ++ s) "open ") ++ " in "
        let mut argS := ""
        for arg in args do
          argS := argS ++ (showSyntax arg) ++ " -> "
        let funStx := s!"{header}{argS}{showSyntax type}"
        match runParserCategory (← getEnv) `term funStx with
        | Except.ok termStx => Term.withLevelNames levelNames <|
          try 
            let expr ← Term.withoutErrToSorry <| 
                Term.elabTerm termStx none
            return Except.ok expr
          catch e => 
            return Except.error s!"{← e.toMessageData.toString} (during elaboration)"
        | Except.error e => 
            return Except.error s!"parsed to {funStx}; error while parsing as theorem: {e}" 

def elabThmCore (s : String)(opens: List String := []) 
  (levelNames : List Name := [`u, `v])
  : CoreM <| Except String Expr := 
    (elabThm s opens levelNames).run'.run'

#eval ["a", "b"].foldl (fun acc s => acc ++ " " ++ s) "the letters"

-- Tests

#eval checkTerm "(fun x : Nat => x + 1)"

#eval checkTerm "a • s"

#eval checkTerm "λ x : Nat, x + 1"

#eval checkTerm "a - t = 0"


def checkStatements : MetaM (List (String × Bool)) := do
  let prompts ← depsPrompt
  (prompts.toList.take 50).mapM fun s => 
    do return (s, ← checkTerm s)

def checkThm (s : String) : MetaM String := do
  let env ← getEnv
  let chk := runParserCategory env `thmStat  s
  match chk with
  | Except.ok stx  =>
      match stx with
      | `(thmStat|theorem $_ $args:argument* : $type:term) =>
        let mut argS := ""
        for arg in args do
          argS := argS ++ (showSyntax arg) ++ " -> "
        let funStx := s!"{argS}{showSyntax type}"
        pure s!"match: {funStx}"
      | _ => pure s!"parsed to mysterious {stx}"
  | Except.error e  => pure s!"error: {e}"

#eval checkThm "theorem blah (n : Nat) {m: Type} : n  = n"

#eval checkThm "theorem subfield.list_sum_mem {K : Type u} [field K] (s : subfield K) {l : list K} : (∀ (x : K), x ∈ l → x ∈ s) → l.sum ∈ s"

def checkElabThm (s : String) : TermElabM String := do
  let env ← getEnv
  let chk := runParserCategory env `thmStat  s
  match chk with
  | Except.ok stx  =>
      match stx with
      | `(thmStat|theorem $_ $args:argument* : $type:term) =>
        let mut argS := ""
        for arg in args do
          argS := argS ++ (showSyntax arg) ++ " -> "
        let funStx := s!"{argS}{showSyntax type}"
        match runParserCategory env `term funStx with
        | Except.ok termStx => Term.withLevelNames [`u, `v] <|
          try 
            let expr ← Term.withoutErrToSorry <| 
                Term.elabTerm termStx none
            pure s!"elaborated: {← expr.view} from {funStx}"
          catch e => 
            pure s!"{← e.toMessageData.toString} during elaboaration"
        | Except.error e => 
            pure s!"parsed to {funStx}; error while parsing: {e}"
      | _ => pure s!"parsed to mysterious {stx}"
  | Except.error e  => pure s!"error: {e}"

#eval checkElabThm "theorem blah (n : Nat) {m : Nat} : n  = m"

#eval checkElabThm "theorem subfield.list_sum_mem {K : Type u} [field K] (s : subfield K) {l : list K} : (∀ (x : K), x ∈ l → x ∈ s) → l.sum ∈ s"

#eval elabThm "theorem blah (n : Nat) {m : Nat} : n  = m" 

#eval elabThm "theorem blah (n : Nat) {m : Nat} : n  = succ n" ["Nat"]

#eval elabThm "theorem blah (n : Nat) {m : Nat} : n  = succ n" ["Nat"]

#eval elabThm "(n : Nat) {m : Nat} : n  = succ n" ["Nat"]

#eval elabThmCore "(n : Nat) {m : Nat} : n  = succ n" ["Nat"]

#eval elabThm "theorem subfield.list_sum_mem {K : Type u} [field K] (s : subfield K) {l : list K} : (∀ (x : K), x ∈ l → x ∈ s) → l.sum ∈ s"