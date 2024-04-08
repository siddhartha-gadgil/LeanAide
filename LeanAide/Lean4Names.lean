import Lean
import Mathlib
import LeanAide.TheoremElab
open Lean Meta Elab Term
open Mathlib.Prelude.Rename


def lean4Name? (name: Name) : MetaM (Option Name) := do
  let m := renameExtension.getState (← getEnv) |>.get
  let name? :=
    (m.find? name).map (·.2)
  match name? with
  | none => pure none
  | some name =>
    pure name

#eval lean4Name? `nat.prime -- some (`Nat.Prime, true)
#eval lean4Name? `nat -- some (`Nat, true)

partial def lean4NamesSyntax : Syntax → MetaM Syntax := fun stx => do
match stx with
| Syntax.ident _ _ name .. =>
    match ← lean4Name? name with
    | some name' => do
        return mkIdent name'
    | none => return stx
| Syntax.node _ k args  => do
  let args ← args.mapM lean4NamesSyntax
  return mkNode k args
| stx => pure stx

def parseThm4 (s : String) : TermElabM <| Except String Syntax := do
  let env ← getEnv
  let stx? := Lean.Parser.runParserCategory env `theorem_statement  s
  match stx? with
  | Except.error err => return Except.error err
  | Except.ok stx => return Except.ok <| ← lean4NamesSyntax stx

partial def elabThm4 (s : String)
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String Expr := do
  let env ← getEnv
  let stx? :=
    Lean.Parser.runParserCategory env `theorem_statement  s
  match stx? with
  | Except.error err =>
    let stx? ←  polyParser
      (Parser.categoryParser `theorem_statement 0) s
    match stx? with
    | none =>
      let jsError :=
        Json.mkObj [
        ("input", s),
        ("parsed", false),
        ("parse-error", err)
        ]
      appendLog "elab_errors" jsError
      return Except.error s!"{err} for:\n {s}"
    | some stx =>
      elaborate stx
  | Except.ok stx =>
    elaborate stx
  where elaborate (stx) := do
    match ← elabThmFromStx stx levelNames with
    | Except.error err₁ =>
      match ← elabThmFromStx (← lean4NamesSyntax stx) levelNames with
      | Except.error err₂ =>
        logInfo m!"failed to elaborate {stx} with error {err₁} (with lean4NamesSyntax)"
        let tail := s.dropWhile (fun c => c != '\n') |>.drop 1 |>.trim
        if !tail.isEmpty then
          elabThm4 tail
        else
          let jsError := Json.mkObj [
            ("input", s),
            ("parsed", true),
            ("elab-error", err₁),
            ("elab-error-lean4names", err₂)
            ]
          appendLog "elab_errors" jsError
          return Except.error s!"{err₁}\n{err₂} (with lean4NamesSyntax)"
      | Except.ok e => return Except.ok e
    | Except.ok e => return  Except.ok e

-- for testing

elab "lean3named" t:term : term => do
  let t' ← lean4NamesSyntax t
  elabTerm t' none

#check lean3named nat.prime
#check lean3named (fun (n: Nat) ↦ nat.prime n) -- handles a mix fine

def egLines := "Yes, a vector space with dimension `2` is indeed finite dimensional. In the language of Lean theorem prover, you don't need to write an explicit proof for this, because the fact that the space has dimension `2` already implies that it is finite dimensional. However, if you want to insist on having an explicit statement, it could be something like:

     ∀ {K : Type u} {V : Type v} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V],
       (Module.rank K V = 2) → FiniteDimensional K V

     Please note that `Module.rank K V = 2` is the way to express that the vector space `V` over the field `K` has dimension `2` in Lean. The `→` is logical implication."

#eval elabThm4 egLines
