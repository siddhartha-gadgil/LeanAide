import Mathlib
universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u₁ u₂ u₃
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false
open scoped Nat
theorem infinite_setOf_odd : {n : ℕ | Odd n}.Infinite := by sorry

