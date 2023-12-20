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

def elabThm4 (s : String)(opens: List String := [])
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String Expr := do
  let env ← getEnv
  let stx? := Lean.Parser.runParserCategory env `theorem_statement  s
  match stx? with
  | Except.error err => return Except.error s!"{err} for:\n {s}"
  | Except.ok stx =>
    match ← elabThmFromStx stx opens levelNames with
    | Except.error err₁ =>
      match ← elabThmFromStx (← lean4NamesSyntax stx) opens levelNames with
      | Except.error err₂ => return Except.error s!"{err₁}\n{err₂} (with lean4NamesSyntax)"
      | Except.ok e => return Except.ok e
    | Except.ok e => return  Except.ok e

-- for testing

elab "lean3named" t:term : term => do
  let t' ← lean4NamesSyntax t
  elabTerm t' none

#check lean3named nat.prime
#check lean3named (fun (n: Nat) ↦ nat.prime n) -- handles a mix fine
