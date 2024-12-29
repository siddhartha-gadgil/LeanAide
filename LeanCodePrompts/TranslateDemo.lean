import Mathlib
import LeanCodePrompts.Translate
import LeanAide.Syntax

set_option lean_aide.translate.greedy true

#theorem silly "If a vector space has dimension `2` then it is finite dimensional"

/-- The set of all odd natural numbers is infinite. -/
theorem exists_infinitely_many_odd : {n | n % 2 = 1}.Infinite := by sorry

#ask "Prove that there are infinitely many even numbers"
