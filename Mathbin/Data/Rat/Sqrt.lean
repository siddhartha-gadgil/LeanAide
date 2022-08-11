/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Rat.Order
import Mathbin.Data.Int.Sqrt

/-!
# Square root on rational numbers

This file defines the square root function on rational numbers `rat.sqrt`
and proves several theorems about it.

-/


namespace Rat

/-- Square root function on rational numbers, defined by taking the (integer) square root of the
numerator and the square root (on natural numbers) of the denominator. -/
@[pp_nodot]
def sqrt (q : ℚ) : ℚ :=
  Rat.mk (Int.sqrt q.num) (Nat.sqrt q.denom)

theorem sqrt_eq (q : ℚ) : Rat.sqrt (q * q) = abs q := by
  rw [sqrt, mul_self_num, mul_self_denom, Int.sqrt_eq, Nat.sqrt_eq, abs_def]

theorem exists_mul_self (x : ℚ) : (∃ q, q * q = x) ↔ Rat.sqrt x * Rat.sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by
    rw [← hn, sqrt_eq, abs_mul_abs_self], fun h => ⟨Rat.sqrt x, h⟩⟩

theorem sqrt_nonneg (q : ℚ) : 0 ≤ Rat.sqrt q :=
  nonneg_iff_zero_le.1 <|
    (mk_nonneg _ <|
          Int.coe_nat_pos.2 <| Nat.pos_of_ne_zeroₓ fun H => pos_iff_ne_zero.1 q.Pos <| Nat.sqrt_eq_zero.1 H).2 <|
      Int.coe_nat_nonneg _

end Rat

