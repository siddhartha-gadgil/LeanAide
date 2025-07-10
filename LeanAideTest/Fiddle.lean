import Mathlib
import LeanAide


abbrev hard.prop : Prop := False


def deferred.hard [inst_hard: Fact hard.prop] : hard.prop := inst_hard.elim

section
open deferred (hard)
variable [Fact hard.prop]

theorem hard_copy : hard.prop := hard

end


#check hard_copy -- hard_copy [inst_hard : Fact hard.prop] : hard.prop

example : 1 ≤ 2 := by first | simp? | hammer
