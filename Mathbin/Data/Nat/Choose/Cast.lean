/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Nat.Choose.Basic
import Mathbin.Data.Nat.Factorial.Cast

/-!
# Cast of binomial coefficients

This file allows calculating the binomial coefficient `a.choose b` as an element of a division ring
of characteristic `0`.
-/


open Nat

variable (K : Type _) [DivisionRing K] [CharZero K]

namespace Nat

theorem cast_choose {a b : ℕ} (h : a ≤ b) : (b.choose a : K) = b ! / (a ! * (b - a)!) := by
  have : ∀ {n : ℕ}, (n ! : K) ≠ 0 := fun n => Nat.cast_ne_zero.2 (factorial_ne_zero _)
  rw [eq_div_iff_mul_eq (mul_ne_zero this this)]
  rw_mod_cast[← mul_assoc, choose_mul_factorial_mul_factorial h]

theorem cast_add_choose {a b : ℕ} : ((a + b).choose a : K) = (a + b)! / (a ! * b !) := by
  rw [cast_choose K (le_add_right le_rfl), add_tsub_cancel_left]

theorem cast_choose_eq_pochhammer_div (a b : ℕ) : (a.choose b : K) = (pochhammer K b).eval (a - (b - 1) : ℕ) / b ! := by
  rw [eq_div_iff_mul_eq (Nat.cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) ≠ 0), ← Nat.cast_mulₓ, mul_comm, ←
    Nat.desc_factorial_eq_factorial_mul_choose, ← cast_desc_factorial]

theorem cast_choose_two (a : ℕ) : (a.choose 2 : K) = a * (a - 1) / 2 := by
  rw [← cast_desc_factorial_two, desc_factorial_eq_factorial_mul_choose, factorial_two, mul_comm, cast_mul, cast_two,
    eq_div_iff_mul_eq (two_ne_zero' : (2 : K) ≠ 0)]

end Nat

