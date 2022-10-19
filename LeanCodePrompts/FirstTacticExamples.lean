import LeanCodePrompts.FirstTacticFinder
-- import Mathbin.All


example : ∀ n : ℕ, ∃ m : ℕ, n < 2 * m + 1 := by 
  show_tactic_prompt
  aide
  aide
  aide
  repeat (sorry)

-- example : ∀ n : ℕ, ∃ m : ℕ, n < 2 * m + 1 := by
--   repeat (aide!)
--   repeat (sorry)