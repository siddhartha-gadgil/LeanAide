import LeanCodePrompts.FirstTacticFinder
import Mathlib.Tactic.Basic
-- import Mathbin.All

macro "existsi " e:term : tactic => 
  `(apply Exists.intro $e)

macro "use " e:term : tactic =>
  `(apply Exists.intro $e)


example : ∀ n : ℕ, ∃ m : ℕ, n < 2 * m + 1 := by 
  -- show_tactic_prompt
  -- aide
  -- aide
  intro n
  
  repeat (sorry)

-- example : ∀ n : ℕ, ∃ m : ℕ, n < 2 * m + 1 := by
--   repeat (aide!)
--   repeat (sorry)