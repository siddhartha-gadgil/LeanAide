import Lean
import Mathlib
import LeanAide
import LeanAideCore.RunTactics
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Lean Meta LeanAide Elab Term Parser Tactic PrettyPrinter

syntax (name := testTryTacticOnGoalAndAddSuggestion)
  "test_try_tactic_on_goal " tactic : tactic

@[tactic testTryTacticOnGoalAndAddSuggestion]
def evalTestTryTacticOnGoalAndAddSuggestion : Tactic := fun stx => do
  match stx with
  | `(tactic| test_try_tactic_on_goal $tac:tactic) =>
        tryTacticOnGoalAndAddSuggestion stx (← getMainGoal) tac
  | _ => throwUnsupportedSyntax


/--
info: Try this:
  [apply] rfl
-/
#guard_msgs in
example : 5 = 4 + 1 := by
  test_try_tactic_on_goal rfl
  rfl

elab "#findTryThis?" goal:term "using" tactics:tacticSeq,* : command =>
  Command.liftTermElabM do
    let goal ← Term.elabTerm goal none
    let mvar ← mkFreshExprMVar goal
    let tactics? ←
      runTacticsAndFindTryThis? mvar.mvarId! tactics.getElems.toList none
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
/--
info: #findTryThis? found tactics: ⏎
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact fun {G} {H} [Group G] [Group H] ϕ => MulEquiv.bijective ϕ
-/
#guard_msgs in
#findTryThis? ∀ {G : Type u_11} {H : Type u_12} [Group G] [Group H] (ϕ : G ≃* H),
        Function.Bijective (⇑ϕ.toMonoidHom : G → H) using try simp?; exact?

example : ∀ {G : Type u_11} {H : Type u_12} [Group G] [Group H] (ϕ : G ≃* H),
        Function.Bijective (⇑ϕ.toMonoidHom : G → H) := by
          simp?; exact?

opaque P : Prop

axiom ax : P

/-- info: #findTryThis? found tactics: simp only [ax] -/
#guard_msgs in
#findTryThis? P using (try simp?); simp? [ax]

example : P := by
  (try simp?); simp? [ax]

example : 1 ≤ 3 := by
  try_this (apply Nat.succ_le_succ)
  simp?

/--
info: #findTryThis? found tactics: ⏎
  apply Nat.succ_le_succ
  simp only [zero_le]
-/
#guard_msgs in
#findTryThis? (1 : Nat) ≤ 3 using try_this (apply Nat.succ_le_succ); simp?

/-- info: #findTryThis? found tactics: simp only [Nat.one_le_ofNat] -/
#guard_msgs in
#findTryThis? (1 : Nat) ≤ 3 using try_this (apply Nat.succ); simp?

/-- info: #findTryThis? found no applicable tactics -/
#guard_msgs in
#findTryThis? (1 : Nat) ≤ 3 using try_this (apply Nat.succ; simp)

/--
info: #findTryThis? found tactics: ⏎
  apply Nat.succ_le_succ
  simp only [zero_le]
-/
#guard_msgs in
#findTryThis? (1 : Nat) ≤ 3 using try_this_strict (apply Nat.succ_le_succ); simp?

/-- info: #findTryThis? found no applicable tactics -/
#guard_msgs in
#findTryThis? (1 : Nat) ≤ 3 using try_this_strict (apply Nat.succ); simp?

/--
info: #findTryThis? found tactics: ⏎
  apply Nat.succ_le_succ
  simp
-/
#guard_msgs in
#findTryThis? (1 : Nat) ≤ 3 using try_this (apply Nat.succ_le_succ; simp)

example : (1 : ℕ) ≤ (3 : ℕ) := by
  try_this (apply Nat.succ_le_succ; simp)

/--
info: #findTryThis? found tactics: ⏎
  apply Nat.succ_le_succ
  simp only [zero_le]
-/
#guard_msgs in
#findTryThis? (1 : Nat) ≤ 3 using try_this (apply Nat.succ_le_succ) then (simp?)

/-- info: #findTryThis? found no applicable tactics -/
#guard_msgs in
#findTryThis? (1 : Nat) ≤ 3 using try_this (apply Nat.succ_le) then (simp?)

/--
info: #findTryThis? found tactics: ⏎
  intro n
  apply Nat.le_of_succ_le_succ
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Order.add_one_le_iff, Lake.FamilyOut.fam_eq]
-/
#guard_msgs in
#findTryThis? ∀(n : Nat), n + 1 ≤ 3 using try_this (intro n; apply Nat.le_of_succ_le_succ) then (simp?; sorry)

example : ∀(n : ℕ), n + 1 ≤ 3 := by
  intro n
  apply Nat.le_of_succ_le_succ
  simp?
  try (simp?)
  sorry

/-- info: #findTryThis? found no applicable tactics -/
#guard_msgs in
#findTryThis? ∀(n : Nat), n + 1 ≤ 3 using try_this (intro n; apply Nat.le_of_succ_le_succ) then (simp?; simp; sorry)

set_option trace.leanaide.frontend.debug true in
/--
info: #findTryThis? found no applicable tactics
---
trace: [leanaide.frontend.debug] Try this:
      [apply] intro n; apply Nat.le_of_succ_le_succ
    ⏎
[leanaide.frontend.debug] Try this:
      [apply] simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Order.add_one_le_iff, Lake.FamilyOut.fam_eq]
    ⏎
[leanaide.frontend.debug] <input>:8:46: error: unsolved goals
    case a
    n : ℕ
    ⊢ n + 1 < 4
-/
#guard_msgs in
#findTryThis? ∀(n : Nat), n + 1 ≤ 3 using try_this (intro n; apply Nat.le_of_succ_le_succ) then (simp?; try(simp?); sorry)

example : ∀ (n : ℕ), n + (1 : ℕ) ≤ (3 : ℕ) := by
  try_this(intro n; apply Nat.le_of_succ_le_succ)then(simp?; sorry)


/--
info: Try this:
  [apply] apply hq
---
warning: unused variable `hp`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example (P Q : Prop) (hp : P) (hq : Q) : Q := by
  apply_any?
  exact hq

/--
info: Try this:
  [apply] apply ‹P›
-/
#guard_msgs in
theorem hidden_hypotheses_example (P Q : Prop) (h : P ∧ Q) : P := by
  -- We use `cases` to split the conjunction (AND) into its two parts.
  -- However, we didn't tell Lean what to name the two new hypotheses!
  cases h
  apply_any?
  -- At this exact line, if you look at the Lean infoview,
  -- your proof state looks like this:
  -- P Q : Prop
  -- ✝¹ : P
  -- ✝ : Q
  -- ⊢ P
  -- Because they have daggers, we cannot type `exact ✝¹`.
  -- Instead, we can use the French quote syntax we discussed earlier
  -- to extract the inaccessible hypothesis by its type:
  exact ‹P›
