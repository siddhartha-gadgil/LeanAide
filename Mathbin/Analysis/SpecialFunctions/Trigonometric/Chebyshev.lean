/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.RingTheory.Polynomial.Chebyshev
import Mathbin.Data.Complex.Exponential

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

* `polynomial.chebyshev.T_complex_cos`: the `n`-th Chebyshev polynomial evaluates on `complex.cos θ`
  to the value `complex.cos (n * θ)`.
-/


namespace Polynomial.Chebyshev

open Polynomial Complex

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
theorem T_complex_cos (θ : ℂ) : ∀ n, (t ℂ n).eval (cos θ) = cos (n * θ)
  | 0 => by
    simp only [← T_zero, ← eval_one, ← Nat.cast_zeroₓ, ← zero_mul, ← cos_zero]
  | 1 => by
    simp only [← eval_X, ← one_mulₓ, ← T_one, ← Nat.cast_oneₓ]
  | n + 2 => by
    simp only [← eval_X, ← eval_one, ← T_add_two, ← eval_sub, ← eval_bit0, ← Nat.cast_succₓ, ← eval_mul]
    rw [T_complex_cos (n + 1), T_complex_cos n]
    have aux : sin θ * sin θ = 1 - cos θ * cos θ := by
      rw [← sin_sq_add_cos_sq θ]
      ring
    simp only [← Nat.cast_addₓ, ← Nat.cast_oneₓ, ← add_mulₓ, ← cos_add, ← one_mulₓ, ← sin_add, ← mul_assoc, ← aux]
    ring

/-- `cos (n * θ)` is equal to the `n`-th Chebyshev polynomial of the first kind evaluated
on `cos θ`. -/
theorem cos_nat_mul (n : ℕ) (θ : ℂ) : cos (n * θ) = (t ℂ n).eval (cos θ) :=
  (T_complex_cos θ n).symm

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n+1) * θ) / sin θ`. -/
theorem U_complex_cos (θ : ℂ) (n : ℕ) : (u ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  induction' n with d hd
  · simp only [← U_zero, ← Nat.cast_zeroₓ, ← eval_one, ← mul_oneₓ, ← zero_addₓ, ← one_mulₓ]
    
  · rw [U_eq_X_mul_U_add_T]
    simp only [← eval_add, ← eval_mul, ← eval_X, ← T_complex_cos, ← add_mulₓ, ← mul_assoc, ← hd, ← one_mulₓ]
    conv_rhs => rw [sin_add, mul_comm]
    push_cast
    simp only [← add_mulₓ, ← one_mulₓ]
    

/-- `sin ((n + 1) * θ)` is equal to `sin θ` multiplied with the `n`-th Chebyshev polynomial of the
second kind evaluated on `cos θ`. -/
theorem sin_nat_succ_mul (n : ℕ) (θ : ℂ) : sin ((n + 1) * θ) = (u ℂ n).eval (cos θ) * sin θ :=
  (U_complex_cos θ n).symm

end Polynomial.Chebyshev

