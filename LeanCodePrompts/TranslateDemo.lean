import Mathlib
import LeanCodePrompts.Translate

set_option lean_aide.translate.model "gpt-4o" -- remove to use "gpt-3.5-turbo"

-- set_option lean_aide.translate.azure true
-- set_option lean_aide.translate.greedy true

theorem infinitude_odds : l!"There are infinitely many odd numbers" :=
  by
    sorry

set_option trace.Translate.info true in

example : l!"If a vector space has dimension `2` then it is finite dimensional." :=
  by
    sorry

-- set_option trace.Translate.info true in
-- #eval findTheorem? "There are infinitely many prime numbers." (numConcise := 3) (numSim := 2)
