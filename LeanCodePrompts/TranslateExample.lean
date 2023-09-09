import Mathlib
import LeanCodePrompts.Translate

/-!
# Translation demo

-/

-- set_option trace.Translate.info true 
#eval translateViewM "If a vector space has dimension `2` then it is finite dimensional."

#eval translateViewM "Every prime number is either `2` or odd"

-- set_option lean_aide.translate.model "gpt-4" -- comment out for gpt-3.5-turbo

theorem infinitude_odds : l!"There are infinitely many odd numbers" :=
  by
    sorry 

-- example : l!"If a vector space has dimension `2` then it is finite dimensional." :=
--   by
--     sorry