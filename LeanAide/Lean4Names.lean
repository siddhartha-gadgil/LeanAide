import Lean
import Mathlib
open Lean Meta Elab Term
open Mathlib.Prelude.Rename


def lean4Name? (name: Name) : MetaM (Option Name) := do
  let name? := 
    ((getRenameMap  (←getEnv)).find? name).map (·.2)
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

-- for testing

elab "lean3named" t:term : term => do 
  let t' ← lean4NamesSyntax t
  elabTerm t' none 

#check lean3named nat.prime
#check lean3named (fun (n: Nat) ↦ nat.prime n) -- handles a mix fine
