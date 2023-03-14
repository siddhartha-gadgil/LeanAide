import LeanCodePrompts.AesopSearch
import Lean
open Lean Meta Elab

opaque sillyN  : Nat
opaque sillyM : Nat

axiom n_is_m : sillyN = sillyM


elab "test_aesop" : tactic => do
  Tactic.liftMetaTactic (
    runAesop 0.5 #[``Nat.le_succ] #[``Nat.add_comm] #[``n_is_m]
    )

-- set_option trace.aesop.steps true in
example : sillyN = sillyM := by
  test_aesop -- uses rw [n_is_m]

example : α → α := by
  aesop

set_option pp.rawOnError true
set_option trace.Translate.info true

example : α → α := by
  test_aesop

example (x: List Nat) : (3 :: x).length = x.length + 1 := by
  test_aesop

example (x y: Nat) : x + y = y + x := by
  test_aesop -- uses Nat.add_comm


