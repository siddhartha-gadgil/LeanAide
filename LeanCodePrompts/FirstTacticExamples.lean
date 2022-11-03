import LeanCodePrompts.FirstTacticFinder
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Use
-- import Mathbin.All

example : ∀ n : ℕ, ∃ m : ℕ, n < 2 * m + 1 := by
  aide_lookahead
  -- aide_lookahead
  repeat (sorry)


example : ∀ n : ℕ, ∃ m : ℕ, n < 2 * m + 1 := by
  show_tactic_prompt
  aide
  aide
  aide  
  repeat (sorry)


