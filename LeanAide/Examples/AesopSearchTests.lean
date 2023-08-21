import LeanAide.AesopSearch
import Lean
import Mathlib
open Lean Meta Elab

opaque sillyN  : Nat
opaque sillyM : Nat

axiom n_is_m : sillyN = sillyM

inductive MyEmpty : Type

theorem MyEmpty.eql (a b : MyEmpty) : a = b := by
  cases a
  


elab "test_aesop" : tactic => do
  Tactic.liftMetaTactic (
    runAesop {apps := #[(``MyEmpty.eql, 0.5)], simps := #[``Nat.add_comm], rws := #[``n_is_m], dynTactics := #[]}
    )

set_option trace.leanaide.proof.info true 

set_option trace.aesop.proof true 
-- set_option trace.aesop.tree true 
-- set_option trace.aesop.steps.ruleSelection true 

example (a b : MyEmpty): a = b := by
  test_aesop -- uses `apply MyEmpty.eql`


example (h : sillyN = 1) : 2 = sillyM + 1 := by
  test_aesop -- uses `rw [n_is_m] at h`

example : (sillyN = 1) →  2 = sillyM + 1 := by
  test_aesop -- uses `rw [← n_is_m]`, does not use `rw .. at ..`

example: ∀ {α : Type u_1} {β : Type u_2} {r : α → β → Prop}, Relator.LeftUnique r → Relator.RightUnique (flip r) := by
  test_aesop -- uses introduction with default transparency

elab "power_aesop" : tactic => do
  Tactic.liftMetaTactic (
    runAesop  {apps := #[(``MyEmpty.eql, 0.5)], simps := #[``Nat.add_comm], rws :=  #[``n_is_m], dynTactics :=
    #["gcongr", "ring", "linarith", "norm_num", "positivity", "polyrith"]}
    )

example : (∀ (a b c: Nat), 
  a + (b + c) = (a + b) + c) ↔ (∀ (a b c: Nat), (a + b) + c = a + (b + c)) := by 
  power_aesop

elab "test_aesop'" : tactic => do
  Tactic.liftMetaTactic (fun mvar => do
    let chk  ← polyAesopRun [{apps := #[(``MyEmpty.eql, 0.5)], simps := #[``Nat.add_comm], rws :=  #[``n_is_m], dynTactics :=
    #[]},
      {apps := #[], simps := #[], rws :=  #[], dynTactics := #["sorry"]}] 
      mvar
    if chk then return [] else return [mvar]
    )


example : False := by
  test_aesop' -- uses sorry

example : α → α := by
  aesop

set_option pp.rawOnError true
set_option trace.Translate.info true

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