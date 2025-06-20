import Lean
import Mathlib

open Lean Meta Elab Term Nat




def existsUniqueSeqTerm (xs : List (TSyntax `Lean.binderIdent)) (type prop : Syntax.Term) : MetaM Syntax.Term := do
  match xs with
  | [] => return prop
  | h :: t =>
    let tailTerm ← existsUniqueSeqTerm t type prop
    `(∃! ($h : $type), $tailTerm)


mutual

partial def fixSyntaxStep? (stx: Syntax.Term) :
  MetaM <| Option Syntax.Term := do
  match stx with
  | `(∃! ($xs* : $type), $value) =>
    let value ← fixSyntax value
    existsUniqueSeqTerm xs.toList type ⟨value⟩
  | `($n:ident) =>
    let n := n.getId.toString
    if n.endsWith "!" then
      let n := n.dropRight 1
      let n := n.toName
      let n := mkIdent n
      return some <| ← `(($n)!)
    else
      return none
  | _  => return none

partial def fixSyntax (stx: Syntax.Term) : MetaM Syntax.Term := do
  match ← fixSyntaxStep? stx with
  | some newStx => return newStx
  | none =>
    match stx.raw with
    | .node info kind args =>
      let newArgs ← args.mapM fun arg => do
         pure (← fixSyntax ⟨arg⟩).raw
      return {raw := Syntax.node info kind newArgs}
    | s => return ⟨s⟩
end

elab "ex_uniq" t:term : term => do
  let newTerm ← fixSyntax t
  let type ← elabTerm newTerm none
  return type

#check ex_uniq (∃! (x y : Nat), x + y = 0)

set_option pp.funBinderTypes true
#check ex_uniq (∃! (x y : Nat), x + y = 0)

#check ex_uniq (∀ n: Nat, (∃! (x y : Nat), x + y = n))


#check ex_uniq (∀ n: Nat, (∃! (x y : Nat), x + y = n
  ∧ (∃! (z w : Nat), z + w = x + y)))

#check ex_uniq (fun (n: Nat) ↦ ((n! + 1)! + 1!))
