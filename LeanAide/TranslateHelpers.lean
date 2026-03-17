import Lean
import Mathlib
import LeanAideCore.ConfigExts

open Lean Meta Elab Term Nat

namespace LeanAide


def existsUniqueSeqTerm (xs : List (TSyntax `Lean.binderIdent)) (type prop : Syntax.Term) : MetaM Syntax.Term := do
  match xs with
  | [] => return prop
  | h :: t =>
    let tailTerm ← existsUniqueSeqTerm t type prop
    `(∃! ($h : $type), $tailTerm)

@[syntax_fix]
partial def fixExistsUniqueSyntaxStep? (stx: Syntax) :
  MetaM <| Option Syntax := do
  match stx with
  | `(∃! ($xs* : $type), $value) =>
    let value ← fixSyntax value -- recursive call for combining from extension
    existsUniqueSeqTerm xs.toList type ⟨value⟩
  | _  => return none

@[syntax_fix]
partial def fixFactorySyntaxStep? (stx: Syntax) :
  MetaM <| Option Syntax := do
  match stx with
  | `($n:ident) =>
    let n := n.getId.toString
    if n.endsWith "!" then
      let n := n.dropEnd 1
      let n := n.toName
      let n := mkIdent n
      return some <| ← `(($n)!)
    else
      return none
  | _ => return none

elab "ex_uniq" t:term : term => do
  let newTerm ← fixSyntax t
  let type ← elabTerm newTerm none
  return type

/-- info: ∃! x, ∃! y, x + y = 0 : Prop -/
#guard_msgs in
#check ex_uniq (∃! (x y : Nat), x + y = 0)

set_option pp.funBinderTypes true
/-- info: ∃! x : ℕ, ∃! y : ℕ, x + y = 0 : Prop -/
#guard_msgs in
#check ex_uniq (∃! (x y : Nat), x + y = 0)

/-- info: ∀ (n : ℕ), ∃! x : ℕ, ∃! y : ℕ, x + y = n : Prop -/
#guard_msgs in
#check ex_uniq (∀ n: Nat, (∃! (x y : Nat), x + y = n))


#check ex_uniq (∀ n: Nat, (∃! (x y : Nat), x + y = n
  ∧ (∃! (z w : Nat), z + w = x + y)))

set_option linter.unusedVariables false in
/-- info: 7 -/
#guard_msgs in
#eval ex_uniq (fun (n: Nat) ↦ ((n! + 1)! + 1!)) <| 2
