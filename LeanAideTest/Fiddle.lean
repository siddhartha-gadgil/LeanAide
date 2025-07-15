import Mathlib
import LeanAide
open Nat LeanAide
set_option autoImplicit false


abbrev hard.prop : Prop := False


def deferred.hard [inst_hard: Fact hard.prop] : hard.prop := inst_hard.elim

section
open deferred (hard)
variable [Fact hard.prop]

theorem hard_copy : hard.prop := hard

end


#check hard_copy -- hard_copy [inst_hard : Fact hard.prop] : hard.prop

example : 1 ≤ 2 := by first | (simp? ; done) | hammer


universe u
example : ∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m : ℕ, n = m * orderOf a := by sorry

#eval elabFrontTheoremExprM "∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m : ℕ, n = m * orderOf a"
