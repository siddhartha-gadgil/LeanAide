import Lean
import Mathlib
open Lean Meta Elab Tactic

opaque sillyN  : Nat
opaque sillyM : Nat

axiom n_is_m : sillyN = sillyM

inductive MyEmpty : Type

theorem MyEmpty.eql (a b : MyEmpty) : a = b := by
  cases a



elab "test_aesop" : tactic =>
  withMainContext do
    let tac ←   `(tactic|aesop (add unsafe 50% apply MyEmpty.eql) (add simp Nat.add_comm) (add unsafe [(by rw [n_is_m]), (by rw [← n_is_m] )] ))
    evalTactic tac


set_option trace.aesop.proof true
-- set_option trace.aesop.tree true
-- set_option trace.aesop.steps.ruleSelection true

example (a b : MyEmpty): a = b := by
  test_aesop -- uses `apply MyEmpty.eql`


example (h : sillyN = 1) : 2 = sillyM + 1 := by
  test_aesop -- uses `rw [n_is_m] at h`

example : (sillyN = 1) →  2 = sillyM + 1 := by
  test_aesop -- uses `rw [← n_is_m]`, does not use `rw .. at ..`


elab "power_aesop" : tactic => do
  withMainContext do
    let tac ←   `(tactic|aesop (add unsafe 50% apply MyEmpty.eql) (add simp Nat.add_comm) (add unsafe (by rw [n_is_m])) (add unsafe [(by ring),(by linarith), (by norm_num), (by positivity), (by polyrith)]))
    evalTactic tac


example : (∀ (a b c: Nat),
  a + (b + c) = (a + b) + c) ↔ (∀ (a b c: Nat), (a + b) + c = a + (b + c)) := by
  power_aesop

example : α → α := by
  aesop

set_option pp.rawOnError true

example : α → α := by
  test_aesop

example (x: List Nat) : (3 :: x).length = x.length + 1 := by
  test_aesop


example (x y: Nat) : x + y = y + x := by
  test_aesop -- uses `Nat.add_comm`

-- example : 1 ≤1 := by
--   messages library_search

-- example : 1 ≤1 := by
--   messages aesop?
