import Mathlib
import LeanCodePrompts.Translate

set_option lean_aide.translate.model "gpt-4-1106-preview" -- remove to use "gpt-3.5-turbo"

-- set_option lean_aide.translate.azure true

theorem infinitude_odds : l!"There are infinitely many odd numbers" :=
  by
    sorry

example : l!"If a vector space has dimension `2` then it is finite dimensional." :=
  by
    sorry


set_option lean_aide.translate.prompt_size 20 in
example : l!"Suppose $E\\subset\\mathbb{R}^k$ is uncountable, and let $P$ be the set of accumulation points of $E$. Then $P$ is perfect." :=
  by
    sorry
