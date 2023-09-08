import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Lean.Parser.Extension
import LeanAide.Aides
open Lean Meta Elab Parser  Tactic
 
/-!
## Parsing and Elaboration of statements

These can be headed with `theorem`, `def`, `example` or nothing and may or may not have a name.
-/

def depsPrompt : IO (Array String) := do
  let file ← reroutePath <| System.mkFilePath ["data/types.txt"]
  IO.FS.lines file

declare_syntax_cat theorem_head
syntax "theorem" : theorem_head
syntax "def" : theorem_head
syntax "lemma" : theorem_head
syntax "instance" : theorem_head
syntax "example" : theorem_head

declare_syntax_cat theorem_statement
syntax bracketedBinder* docComment (theorem_head)?  bracketedBinder*  ":" term : theorem_statement
syntax (theorem_head)? (ident)? bracketedBinder*  ":" term : theorem_statement
syntax term : theorem_statement

def thmsPrompt : IO (Array String) := do
  let file ← reroutePath <| System.mkFilePath ["data/thms.txt"]
  IO.FS.lines file

/-- check whether a string parses as a theorem -/
def checkThm (s : String) : MetaM Bool := do
  let env ← getEnv
  let chk := Lean.Parser.runParserCategory env `theorem_statement  s
  match chk with
  | Except.ok stx  =>
      IO.println stx 
      pure true
  | Except.error _  => pure false

partial def tokens (s : Syntax) : Array String := 
match s with
| .missing => Array.empty
| .node _ _ args => args.foldl (fun acc x => acc ++ tokens x) Array.empty
| .atom _  val => #[val]
| .ident _ val .. => #[val.toString]

def getTokens (s: String) : MetaM <| Array String := do
  let env ← getEnv
  let chk := Lean.Parser.runParserCategory env `theorem_statement  s
  match chk with
  | Except.ok stx  =>
      pure <| tokens stx
  | Except.error _  => pure Array.empty


/-- split prompts into those that parse -/
def promptsThmSplit : MetaM ((Array String) × (Array String)) := do 
  let deps ← thmsPrompt
  let mut succ: Array String := Array.empty
  let mut fail: Array String := Array.empty
  for type in deps do
    let chk ←  checkThm type
    if chk then
      succ := succ.push type
    else
      fail := fail.push type
  return (succ, fail)

def promptsThmSplitCore : CoreM ((Array String) × (Array String)) :=
  promptsThmSplit.run'

def levelNames := 
  [`u, `v, `u_1, `u_2, `u_3, `u_4, `u_5, `u_6, `u_7, `u_8, `u_9, `u_10, `u_11, `u₁, `u₂, `uι, `W₁, `W₂, `w₁, `w₂, `u', `v', `uu, `w, `w', `wE, `uE, `x]

partial def idents : Syntax → List String
| Syntax.ident _ s .. => [s.toString]
| Syntax.node _ _ ss => ss.toList.bind idents
| _ => []


/--
Elaborate the statement of a theorem, returning the elaborated expression. The syntax of the statement is liberal: it can be headed with `theorem`, `def`, `example` or nothing and may or may not have a name.
-/
def elabThmFromStx (stx : Syntax)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String Expr := do
    match stx with
    | `(theorem_statement| $_:docComment $[$_:theorem_head]? $args:bracketedBinder* : $type:term) =>
      elabAux type args
    | `(theorem_statement|$[$_:theorem_head]? $[$_:ident]? $args:bracketedBinder* : $type:term) =>
      elabAux type args
    | `(theorem_statement|$vars:bracketedBinder* $_:docComment  $[$_:theorem_head]? $args:bracketedBinder* : $type:term ) =>
      elabAux type (vars ++ args)
    | `(theorem_statement|$type:term ) =>
      elabAux type #[]
    | _ => return Except.error s!"parsed to unmatched syntax {stx}"
  where elabAux (type: Syntax)(args: Array Syntax) : 
        TermElabM <| Except String Expr := do
        let header := if opens.isEmpty then "" else 
          (opens.foldl (fun acc s => acc ++ " " ++ s) "open ") ++ " in "
        let mut argS := ""
        for arg in args do
          argS := argS ++ (arg.reprint.get!) ++ " -> "
        let funStx := s!"{header}{argS}{type.reprint.get!}"
        match Lean.Parser.runParserCategory (← getEnv) `term funStx with
        | Except.ok termStx => Term.withLevelNames levelNames <|
          try 
            let expr ← Term.withoutErrToSorry <| 
                Term.elabType termStx
            Term.synthesizeSyntheticMVarsNoPostponing
            -- IO.println s!"{(←PrettyPrinter.delab expr).raw.reprint}"
            return Except.ok expr
          catch e => 
            return Except.error s!"{← e.toMessageData.toString} ; identifiers {idents termStx} (during elaboration) for {termStx.reprint.get!}"
        | Except.error e => 
            return Except.error s!"parsed to {funStx}; error while parsing as theorem: {e}" 


/--
Elaborate the statement of a theorem, returning the elaborated expression. The syntax of the statement is liberal: it can be headed with `theorem`, `def`, `example` or nothing and may or may not have a name.
-/
def elabThm (s : String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String Expr := do
  let env ← getEnv
  let stx? := Lean.Parser.runParserCategory env `theorem_statement  s
  match stx? with
  | Except.ok stx  =>
      elabThmFromStx stx opens levelNames
  | Except.error e  => return Except.error e



def elabThmCore (s : String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : CoreM <| Except String Expr := 
    (elabThm s opens levelNames).run'.run'

def elabView (s : String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String String := do
  (← elabThm s opens levelNames).mapM (fun e => 
      do return (← PrettyPrinter.delab e).raw.reprint.get!
  )

/-!
### Examples for parsing and elaboration
-/

-- #eval elabView "theorem (n : Nat) {m: Type} : n  = n"
-- #eval elabView "theorem my_name (n : Nat) {m: Type} : n  = n"
-- #eval elabView "(n : Nat)  : n  + 1 < n"
-- #eval elabView "def eg (n : Nat)  : n  + 1 < n"
-- #eval elabView "def  (n : Nat)  : n  + 1 < n"




