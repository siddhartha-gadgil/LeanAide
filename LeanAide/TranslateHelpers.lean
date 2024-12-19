import Lean
import Mathlib

open Lean Meta Elab Term

def existsUniqueSeqTerm (xs : List (TSyntax `Lean.binderIdent)) (type prop : Syntax.Term) : MetaM Syntax.Term := do
  match xs with
  | [] => return prop
  | h :: t =>
    let tailTerm ← existsUniqueSeqTerm t type prop
    `(∃! ($h : $type), $tailTerm)


mutual

partial def expandExistsUniqueStep? (stx: Syntax.Term) :
  MetaM <| Option Syntax.Term := do
  match stx with
  | `(∃! ($xs* : $type), $value) =>
    let value ← expandExistsUnique value
    existsUniqueSeqTerm xs.toList type ⟨value⟩
  | _  => return none

partial def expandExistsUnique (stx: Syntax.Term) : MetaM Syntax.Term := do
  match ← expandExistsUniqueStep? stx with
  | some newStx => return newStx
  | none =>
    match stx.raw with
    | .node info kind args =>
      let newArgs ← args.mapM fun arg => do
         pure (← expandExistsUnique ⟨arg⟩).raw
      return {raw := Syntax.node info kind newArgs}
    | s => return ⟨s⟩
end

elab "ex_uniq" t:term : term => do
  let newTerm ← expandExistsUnique t
  let type ← elabType newTerm
  return type

#check ex_uniq (∃! (x y : Nat), x + y = 0)

set_option pp.funBinderTypes true
#check ex_uniq (∃! (x y : Nat), x + y = 0)

#check ex_uniq (∀ n: Nat, (∃! (x y : Nat), x + y = n))


#check ex_uniq (∀ n: Nat, (∃! (x y : Nat), x + y = n
  ∧ (∃! (z w : Nat), z + w = x + y)))
