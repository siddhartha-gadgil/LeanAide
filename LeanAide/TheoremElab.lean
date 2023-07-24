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

declare_syntax_cat typed_ident
syntax "(" ident ":" term ")" : typed_ident
syntax "{" ident ":" term "}" : typed_ident


declare_syntax_cat argument
syntax "(" ident+ " : " term ")" : argument
syntax "{" ident+ " : " term "}" : argument
syntax "[" ident " : " term "]" : argument
syntax "[" term "]" : argument

declare_syntax_cat thmStat
syntax argument* docComment "theorem"  argument*  ":" term : thmStat
syntax "theorem" (ident)? argument*  ":" term : thmStat
syntax "def" ident argument*  ":" term : thmStat
syntax argument*  ":" term : thmStat

def thmsPrompt : IO (Array String) := do
  let file ← reroutePath <| System.mkFilePath ["data/thms.txt"]
  IO.FS.lines file

/-- check whether a string parses as a theorem -/
def checkThm (s : String) : MetaM Bool := do
  let env ← getEnv
  let chk := Lean.Parser.runParserCategory env `thmStat  s
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
  let chk := Lean.Parser.runParserCategory env `thmStat  s
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
  [`u, `v, `u_1, `u_2, `u_3, `u_4, `u_5, `u_6, `u_7, `u_8, `u_9, `u_10, `u_11, `u₁, `u₂, `W₁, `W₂, `w₁, `w₂, `u', `v', `uu, `w, `wE]

partial def idents : Syntax → List String
| Syntax.ident _ s .. => [s.toString]
| Syntax.node _ _ ss => ss.toList.bind idents
| _ => []

def elabThm (s : String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String Expr := do
  let env ← getEnv
  let chk := Lean.Parser.runParserCategory env `thmStat  s
  match chk with
  | Except.ok stx  =>
      match stx with
      | `(thmStat| $_:docComment theorem  $args:argument* : $type:term) =>
        elabAux type args
      | `(thmStat|theorem $_ $args:argument* : $type:term) =>
        elabAux type args
      | `(thmStat|theorem $args:argument* : $type:term) =>
        elabAux type args
      | `(thmStat|$vars:argument* $_:docComment  theorem $args:argument* : $type:term ) =>
        elabAux type (vars ++ args)
      | `(thmStat|def $_ $args:argument* : $type:term) =>
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
        match Lean.Parser.runParserCategory (← getEnv) `term funStx with
        | Except.ok termStx => Term.withLevelNames levelNames <|
          try 
            let expr ← Term.withoutErrToSorry <| 
                Term.elabType termStx
            Term.synthesizeSyntheticMVarsNoPostponing
            IO.println s!"{(←PrettyPrinter.delab expr).raw.reprint}"
            return Except.ok expr
          catch e => 
            return Except.error s!"{← e.toMessageData.toString} ; identifiers {idents termStx} (during elaboration)"
        | Except.error e => 
            return Except.error s!"parsed to {funStx}; error while parsing as theorem: {e}" 

def elabThmCore (s : String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : CoreM <| Except String Expr := 
    (elabThm s opens levelNames).run'.run'

/-!
### Examples for parsing and elaboration
-/

/-!
## Equality of statements
-/

theorem true_true_iff_True : true = true ↔ True := by
    apply Iff.intro
    intros
    exact True.intro
    intros
    rfl


theorem true_false_iff_false : false = true ↔ False := by
    apply Iff.intro 
    intro hyp
    simp at hyp
    intro hyp
    contradiction

syntax "lynx" ("at" ident)? : tactic
syntax "lynx" "at" "*" : tactic
macro_rules 
| `(tactic| lynx) => 
  `(tactic|try(repeat rw [true_true_iff_True]);try (repeat (rw [true_false_iff_false])))
| `(tactic| lynx at $t:ident) => 
  `(tactic| try(repeat rw [true_true_iff_True] at $t:ident);try (repeat (rw [true_false_iff_false] at $t:ident)))
| `(tactic| lynx at *) => 
  `(tactic|try(repeat rw [true_true_iff_True] at *);try (repeat (rw [true_false_iff_false] at *)))


def provedEqual (e₁ e₂ : Expr) : TermElabM Bool := do
  let type ← mkEq e₁ e₂
  let mvar ← mkFreshExprMVar <| some type
  let mvarId := mvar.mvarId!
  let stx ← `(tactic| lynx;  try (rfl))
  let res ←  runTactic mvarId stx
  let (remaining, _) := res
  return remaining.isEmpty

def provedEquiv (e₁ e₂ : Expr) : TermElabM Bool := do
  try
  let type ← mkAppM ``Iff #[e₁, e₂]
  let mvar ← mkFreshExprMVar <| some type
  let mvarId := mvar.mvarId!
  let stx ← `(tactic| intros; lynx at *<;> apply Iff.intro <;> intro hyp  <;> (lynx at *) <;> (try assumption) <;> try (intros; apply Eq.symm; apply hyp))
  let res ←  runTactic mvarId stx
  let (remaining, _) := res
  return remaining.isEmpty
  catch _ => pure false


def compareThms(s₁ s₂ : String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String Bool := do
  let e₁ ← elabThm s₁ opens levelNames
  let e₂ ← elabThm s₂ opens levelNames
  match e₁ with
  | Except.ok e₁ => match e₂ with
    | Except.ok e₂ => 
        let p := (← provedEqual e₁ e₂) || 
          (← provedEquiv e₁ e₂)
        return Except.ok p
    | Except.error e₂ => return Except.error e₂
  | Except.error e₁ => return Except.error e₁

def compareThmsCore(s₁ s₂ : String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : CoreM <| Except String Bool := 
    (compareThms s₁ s₂ opens levelNames).run'.run'

def compareThmExps(e₁ e₂: Expr)
  : TermElabM <| Except String Bool := do
      let p := (← provedEqual e₁ e₂) || 
        (← provedEquiv e₁ e₂)
      return Except.ok p

def compareThmExpsCore(e₁ e₂: Expr)
  : CoreM <| Except String Bool := do
      (compareThmExps e₁ e₂).run'.run'

def equalThms(s₁ s₂ : String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : TermElabM Bool := do
  match ← compareThms s₁ s₂ opens levelNames with
  | Except.ok p => return p
  | Except.error _ => return false

def groupThms(ss: Array String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : TermElabM (Array (Array String)) := do
    let mut groups: Array (Array String) := Array.empty
    for s in ss do
      match ← groups.findIdxM? (fun g => 
          equalThms s g[0]! opens levelNames) with
      |none  => 
        groups := groups.push #[s]
      | some j => 
        groups := groups.set! j (groups[j]!.push s)
    return groups

def groupTheoremsCore(ss: Array String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : CoreM (Array (Array String)) := 
    (groupThms ss opens levelNames).run'.run'

def groupThmsSort(ss: Array String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : TermElabM (Array (Array String)) := do
  let gps ← groupThms ss opens levelNames
  return gps.qsort (fun xs ys => xs.size > ys.size)

def groupThmsSortCore(ss: Array String)(opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : CoreM (Array (Array String)) := 
    (groupThmsSort ss opens levelNames).run'.run'

-- Tests


def eg :=
"section 
variable (α : Type) {n : Nat}
/-- A doc that should be ignored -/
theorem blah (m: Nat) : n  = m "

#eval checkThm eg

#eval checkThm "(n : Nat) {m: Type} : n  = n"


example : (∀ {A: Sort}, False → A) ↔ (∀ {A: Sort}, false = true → A) := by
  intros; lynx at *<;> apply Iff.intro <;> intro hyp  <;> (lynx at *) <;> (try assumption) <;> try (intros; apply Eq.symm; apply hyp)


example : (∀ (a b c: Nat), 
  a + (b + c) = (a + b) + c) ↔ (∀ (a b c: Nat), (a + b) + c = a + (b + c)) := by 
  intros; apply Iff.intro <;> intro hyp  <;> (try assumption) <;> try (intros; apply Eq.symm; apply hyp)
  
-- #eval compareThms "(a b c: Nat): a + (b + c) = (a + b) + c" "(a b c: Nat): (a + b) + c = a + (b + c)"
