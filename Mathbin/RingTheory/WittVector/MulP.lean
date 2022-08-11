/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.RingTheory.WittVector.IsPoly

/-!
## Multiplication by `n` in the ring of Witt vectors

In this file we show that multiplication by `n` in the ring of Witt vectors
is a polynomial function. We then use this fact to show that the composition of Frobenius
and Verschiebung is equal to multiplication by `p`.

### Main declarations

* `mul_n_is_poly`: multiplication by `n` is a polynomial function

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable {p : ℕ} {R : Type _} [hp : Fact p.Prime] [CommRingₓ R]

-- mathport name: «expr𝕎»
local notation "𝕎" => WittVector p

-- type as `\bbW`
open MvPolynomial

noncomputable section

include hp

variable (p)

/-- `witt_mul_n p n` is the family of polynomials that computes
the coefficients of `x * n` in terms of the coefficients of the Witt vector `x`. -/
noncomputable def wittMulN : ℕ → ℕ → MvPolynomial ℕ ℤ
  | 0 => 0
  | n + 1 => fun k => bind₁ (Function.uncurry <| ![witt_mul_n n, x]) (wittAdd p k)

variable {p}

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
theorem mul_n_coeff (n : ℕ) (x : 𝕎 R) (k : ℕ) : (x * n).coeff k = aeval x.coeff (wittMulN p n k) := by
  induction' n with n ih generalizing k
  · simp only [← Nat.nat_zero_eq_zero, ← Nat.cast_zeroₓ, ← mul_zero, ← zero_coeff, ← witt_mul_n, ← AlgHom.map_zero, ←
      Pi.zero_apply]
    
  · rw [witt_mul_n, Nat.succ_eq_add_one, Nat.cast_addₓ, Nat.cast_oneₓ, mul_addₓ, mul_oneₓ, aeval_bind₁, add_coeff]
    apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl
    ext1 ⟨b, i⟩
    fin_cases b
    · simp only [← Function.uncurry, ← Matrix.cons_val_zero, ← ih]
      
    · simp only [← Function.uncurry, ← Matrix.cons_val_one, ← Matrix.head_cons, ← aeval_X]
      
    

variable (p)

/-- Multiplication by `n` is a polynomial function. -/
@[is_poly]
theorem mul_n_is_poly (n : ℕ) : IsPoly p fun R _Rcr x => x * n :=
  ⟨⟨wittMulN p n, fun R _Rcr x => by
      funext k
      exact mul_n_coeff n x k⟩⟩

@[simp]
theorem bind₁_witt_mul_n_witt_polynomial (n k : ℕ) :
    bind₁ (wittMulN p n) (wittPolynomial p ℤ k) = n * wittPolynomial p ℤ k := by
  induction' n with n ih
  · simp only [← witt_mul_n, ← Nat.cast_zeroₓ, ← zero_mul, ← bind₁_zero_witt_polynomial]
    
  · rw [witt_mul_n, ← bind₁_bind₁, witt_add, witt_structure_int_prop]
    simp only [← AlgHom.map_add, ← Nat.cast_succₓ, ← bind₁_X_right]
    rw [add_mulₓ, one_mulₓ, bind₁_rename, bind₁_rename]
    simp only [← ih, ← Function.uncurry, ← Function.comp, ← bind₁_X_left, ← AlgHom.id_apply, ← Matrix.cons_val_zero, ←
      Matrix.head_cons, ← Matrix.cons_val_one]
    

end WittVector

