import Mathlib
import LeanCodePrompts.Translate

/-!
# Translation demo

-/

set_option lean_aide.translate.model "gpt-4-1106-preview" -- remove to use "gpt-3.5-turbo"
set_option trace.Translate.info true

#eval translateViewM "There are infinitely many odd numbers"
#eval translateViewM "If a vector space has dimension `2` then it is finite dimensional."

#eval translateViewM "Suppose $E\\subset\\mathbb{R}^k$ is uncountable, and let $P$ be the set of condensation points of $E$. Then $P$ is perfect."

#eval translateViewM "Suppose $E\\subset\\mathbb{R}^k$ is uncountable, and let $P$ be the set of accumulation points of $E$. Then $P$ is perfect."

#eval translateViewM "Suppose $E\\subset\\mathbb{R}^k$ is uncountable, and let $P$ be the set of limit points of $E$. Then $P$ is perfect."

#eval translateViewM "Every prime number is either `2` or odd"

-- set_option lean_aide.translate.model "bert"
theorem infinitude_odds : l!"There are infinitely many odd numbers" :=
  by
    sorry

-- example : l!"If a vector space has dimension `2` then it is finite dimensional." :=
--   by
--     sorry
