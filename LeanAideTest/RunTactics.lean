import Lean
import Mathlib
import LeanAide
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Lean Meta LeanAide Elab Term Parser Tactic PrettyPrinter

elab "#findTryThis?" goal:term "using" tactics:tacticSeq,* : command =>
  Command.liftTermElabM do
    let goal ← Term.elabTerm goal none
    let tactics? ←
      runTacticsAndFindTryThis? goal tactics.getElems.toList
    match tactics? with
    | some tacticSeq =>
      logInfo m!"#findTryThis? found tactics: {← ppCategory ``tacticSeq tacticSeq}"
    | none =>
      logInfo "#findTryThis? found no applicable tactics"

-- Test that if `simp?` makes partial progress, it is still not considered successful.
/-- info: #findTryThis? found tactics: grind only -/
#guard_msgs in
#findTryThis? ∀ (n m : Nat), n + m = m + n using simp? [Nat.add_assoc], grind?

example : ∀ (n m : ℕ),
  n + (m + 1) = m + n + 1 := by
    simp? [Nat.add_assoc]
    grind

-- Test that if `simp?` solves the goal, it is considered successful.
/-- info: #findTryThis? found tactics: simp only [add_zero, implies_true] -/
#guard_msgs in
#findTryThis? ∀ (n : Nat), n + 0 = n using simp?, grind?

/-- info: #findTryThis? found tactics: exact fun n m => Nat.add_comm n m -/
#guard_msgs in
#findTryThis? ∀ (n m : Nat), n + m = m + n using exact?

/-- info: #findTryThis? found no applicable tactics -/
#guard_msgs in
#findTryThis? ∀ (n m : Nat), n + m = m + n + 1 using simp?, grind?, exact?

universe u_11 u_12
#findTryThis? ∀ {G : Type u_11} {H : Type u_12} [Group G] [Group H] (ϕ : G ≃* H),
        Function.Bijective (⇑ϕ.toMonoidHom : G → H) using simp?; exact?
