import Mathlib
import LeanAideCore.Translate
import LeanAide.Syntax

set_option lean_aide.translate.greedy true

#theorem silly : "If a vector space has dimension `2` then it is finite dimensional." >>
  translate_theorem

#theorem : "There are infinitely many odd numbers." >> translate_theorem

#llm_query "Prove that there are infinitely many even numbers."

#def "A group is said to be sane if every proper normal subgroup is cyclic." >> translate_definition

#doc
theorem InfiniteOddNumbers : ∀ n:ℕ, ∃ m:ℕ, m > n ∧ Odd m := by sorry