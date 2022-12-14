import LeanCodePrompts.FirstTacticFinder
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Use
-- import Mathlib

-- example : ∀ n : ℕ, ∃ m : ℕ, n < 2 * m + 1 := by
--   repeat (aide_lookahead)
--   repeat (sorry)


example : ∀ n : ℕ, ∃ m : ℕ, n < 2 * m + 1 := by
  show_tactic_prompt
  aide
  aide
  aide  
  repeat (sorry)


