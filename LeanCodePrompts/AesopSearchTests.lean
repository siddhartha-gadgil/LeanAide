import LeanCodePrompts.AesopSearch
import Lean
open Lean Meta Elab

elab "test_aesop" : tactic => do
  Tactic.liftMetaTactic (runAesop 0.5 #[``Nat.le_succ] #[``Nat.add_comm] #[])


example : α → α := by
  aesop

example : α → α := by
  test_aesop

example (x: List Nat) : (3 :: x).length = x.length + 1 := by
  test_aesop

example (x y: Nat) : x + y = y + x := by
  test_aesop -- uses Nat.add_comm

example (n : Nat) : n + 1 ≤ n + 2 := by 
  test_aesop -- uses Nat.le_succ