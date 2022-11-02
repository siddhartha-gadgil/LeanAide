import LeanCodePrompts.FirstTacticFinder
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Use
-- import Mathbin.All

example : ∀ n : ℕ, ∃ m : ℕ, n < Nat.succ (2 * m) := by
  show_tactic_prompt
  aide
  aide
  aide  
  repeat (sorry)

-- example : ∀ n : ℕ, ∃ m : ℕ, n < 2 * m + 1 := by
--   repeat (aide!)
--   repeat (sorry)