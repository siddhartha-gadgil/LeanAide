import Lean
import LeanAide.Aides
import LeanAide.TranslateHelpers
open Lean Meta Elab Parser  Tactic

/-!
## Parsing and Elaboration of statements

These can be headed with `theorem`, `def`, `example` or nothing and may or may not have a name.
-/


declare_syntax_cat theorem_head
syntax "theorem" : theorem_head
syntax "def" : theorem_head
syntax "lemma" : theorem_head
syntax "instance" : theorem_head
syntax "example" : theorem_head

declare_syntax_cat theorem_statement
syntax bracketedBinder* docComment (theorem_head)?  bracketedBinder*  ":" term : theorem_statement
syntax (theorem_head)? (ident)? bracketedBinder*  ":" term : theorem_statement
syntax (theorem_head)? (ident)? bracketedBinder*  ":" term  ":=" term: theorem_statement
syntax term : theorem_statement

def thmsPrompt : IO (Array String) := do
  let file ← reroutePath <| System.mkFilePath ["extra_resources/thms.txt"]
  IO.FS.lines file
open Lean.Parser.Category

/-- check whether a string parses as a theorem -/
def checkThm (s : String) : MetaM Bool := do
  let env ← getEnv
  let chk := Lean.Parser.runParserCategory env ``theorem_statement  s
  match chk with
  | Except.ok stx  =>
      IO.println stx
      pure true
  | Except.error _  => pure false


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
  [`u, `v, `u_1, `u_2, `u_3, `u_4, `u_5, `u_6, `u_7, `u_8, `u_9, `u_10, `u_11, `u₁, `u₂, `v₁, `v₂, `uι, `W₁, `W₂, `w₁, `w₂, `u', `v', `uu, `w, `w', `wE, `uE, `x]


def typeFromThmSyntax (stx : Syntax)
  : TermElabM  Syntax.Term := do
    match stx with
    | `(theorem_statement| $_:docComment $[$_:theorem_head]? $args:bracketedBinder* : $type:term) =>
      typeStx type args
    | `(theorem_statement|$[$_:theorem_head]? $[$_:ident]? $args:bracketedBinder* : $type:term) =>
      typeStx type args
    | `(theorem_statement|$[$_:theorem_head]? $[$_:ident]?   $args:bracketedBinder* : $type:term := $_:term) =>
      typeStx type args
    | `(theorem_statement|$vars:bracketedBinder* $_:docComment  $[$_:theorem_head]? $args:bracketedBinder* : $type:term ) =>
      typeStx type (vars ++ args)
    | `(theorem_statement|$type:term ) =>
      return type
    | _ => throwError s!"parsed to unmatched syntax {stx}"
  where typeStx (type: Term)
  (args : TSyntaxArray `Lean.Parser.Term.bracketedBinder) : MetaM <| TSyntax `term := do
    let mut typeStx : TSyntax `term := type
    for arg in args.reverse do
      let stx ← `(Lean.Parser.Term.depArrow|$arg → $typeStx)
      typeStx := ⟨stx.raw⟩
    typeStx ← fixSyntax typeStx
    return typeStx

def typeFromThm (s : String)
  : TermElabM  Syntax.Term := do
  let env ← getEnv
  let stx? := Lean.Parser.runParserCategory env `theorem_statement  s
  match stx? with
  | Except.ok stx  =>
      typeFromThmSyntax stx
  | Except.error e  => throwError e

-- #eval typeFromThm "Nat"

/--
Elaborate the statement of a theorem, returning the elaborated expression. The syntax of the statement is liberal: it can be headed with `theorem`, `def`, `example` or nothing and may or may not have a name.
-/
def elabThmFromStx (stx : Syntax)
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String Expr := do
    try
      let typeStx ← typeFromThmSyntax stx
      elabAux typeStx
    catch _ =>
      return Except.error s!"parsed to unmatched syntax {stx}"
  where elabAux (typeStx: TSyntax `term) :
        TermElabM <| Except String Expr := do
        Term.withLevelNames levelNames <|
        try
          let expr ← Term.withoutErrToSorry <|
              Term.elabType typeStx
          Term.synthesizeSyntheticMVarsNoPostponing
          let expr ← instantiateMVars expr
          return Except.ok expr
        catch e =>
          return Except.error s!"{← e.toMessageData.toString} ; identifiers {idents typeStx} (during elaboration) for {typeStx.raw.reprint.get!}"

/--
Elaborate the statement of a theorem, returning the elaborated expression. The syntax of the statement is liberal: it can be headed with `theorem`, `def`, `example` or nothing and may or may not have a name.
-/
def elabThm (s : String)
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String Expr := do
  let env ← getEnv
  let stx? := Lean.Parser.runParserCategory env ``theorem_statement  s
  match stx? with
  | Except.ok stx  =>
      elabThmFromStx stx levelNames
  | Except.error e  => return Except.error e



def elabThmCore (s : String)
  (levelNames : List Lean.Name := levelNames)
  : CoreM <| Except String Expr :=
    (elabThm s levelNames).run'.run'

def elabView (s : String)
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String String := do
  (← elabThm s levelNames).mapM (fun e =>
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
