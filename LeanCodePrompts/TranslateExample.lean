import Mathlib
import LeanCodePrompts.Translate

/-!
# Translation demo

-/

#eval pingEmbedding

-- set_option trace.Translate.info true 
-- #eval translateViewM "There are infinitely many odd numbers"
#eval translateViewM "If a vector space has dimension `2` then it is finite dimensional."

#eval translateViewM "Every prime number is either `2` or odd"

theorem infinitude_odds : l!"There are infinitely many odd numbers" :=
  by
    sorry 

example : l!"If a vector space has dimension `2` then it is finite dimensional." :=
  by
    sorry