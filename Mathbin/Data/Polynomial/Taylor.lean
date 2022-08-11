/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Polynomial.HasseDeriv

/-!
# Taylor expansions of polynomials

## Main declarations

* `polynomial.taylor`: the Taylor expansion of the polynomial `f` at `r`
* `polynomial.taylor_coeff`: the `k`th coefficient of `taylor r f` is
  `(polynomial.hasse_deriv k f).eval r`
* `polynomial.eq_zero_of_hasse_deriv_eq_zero`:
  the identity principle: a polynomial is 0 iff all its Hasse derivatives are zero

-/


noncomputable section

namespace Polynomial

open Polynomial

variable {R : Type _} [Semiringₓ R] (r : R) (f : R[X])

/-- The Taylor expansion of a polynomial `f` at `r`. -/
def taylor (r : R) : R[X] →ₗ[R] R[X] where
  toFun := fun f => f.comp (X + c r)
  map_add' := fun f g => add_comp
  map_smul' := fun c f => by
    simp only [← smul_eq_C_mul, ← C_mul_comp, ← RingHom.id_apply]

theorem taylor_apply : taylor r f = f.comp (X + c r) :=
  rfl

@[simp]
theorem taylor_X : taylor r x = X + c r := by
  simp only [← taylor_apply, ← X_comp]

@[simp]
theorem taylor_C (x : R) : taylor r (c x) = c x := by
  simp only [← taylor_apply, ← C_comp]

@[simp]
theorem taylor_zero' : taylor (0 : R) = LinearMap.id := by
  ext
  simp only [← taylor_apply, ← add_zeroₓ, ← comp_X, ← _root_.map_zero, ← LinearMap.id_comp, ← Function.comp_app, ←
    LinearMap.coe_comp]

theorem taylor_zero (f : R[X]) : taylor 0 f = f := by
  rw [taylor_zero', LinearMap.id_apply]

@[simp]
theorem taylor_one : taylor r (1 : R[X]) = c 1 := by
  rw [← C_1, taylor_C]

@[simp]
theorem taylor_monomial (i : ℕ) (k : R) : taylor r (monomial i k) = c k * (X + c r) ^ i := by
  simp [← taylor_apply]

/-- The `k`th coefficient of `polynomial.taylor r f` is `(polynomial.hasse_deriv k f).eval r`. -/
theorem taylor_coeff (n : ℕ) : (taylor r f).coeff n = (hasseDeriv n f).eval r :=
  show (lcoeff R n).comp (taylor r) f = (leval r).comp (hasseDeriv n) f by
    congr 1
    clear f
    ext i
    simp only [← leval_apply, ← mul_oneₓ, ← one_mulₓ, ← eval_monomial, ← LinearMap.comp_apply, ← coeff_C_mul, ←
      hasse_deriv_monomial, ← taylor_apply, ← monomial_comp, ← C_1, ← (commute_X (C r)).add_pow i, ← LinearMap.map_sum]
    simp only [← lcoeff_apply, C_eq_nat_cast, ← mul_assoc, C_pow, C_mul, ← coeff_mul_C, ← (Nat.cast_commute _ _).Eq, ←
      coeff_X_pow, ← boole_mul, ← Finset.sum_ite_eq, ← Finset.mem_range]
    split_ifs with h
    · rfl
      
    push_neg  at h
    rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zeroₓ, mul_zero]

@[simp]
theorem taylor_coeff_zero : (taylor r f).coeff 0 = f.eval r := by
  rw [taylor_coeff, hasse_deriv_zero, LinearMap.id_apply]

@[simp]
theorem taylor_coeff_one : (taylor r f).coeff 1 = f.derivative.eval r := by
  rw [taylor_coeff, hasse_deriv_one]

@[simp]
theorem nat_degree_taylor (p : R[X]) (r : R) : natDegree (taylor r p) = natDegree p := by
  refine' map_nat_degree_eq_nat_degree _ _
  nontriviality R
  intro n c c0
  simp [← taylor_monomial, ← nat_degree_C_mul_eq_of_mul_ne_zero, ← nat_degree_pow_X_add_C, ← c0]

@[simp]
theorem taylor_mul {R} [CommSemiringₓ R] (r : R) (p q : R[X]) : taylor r (p * q) = taylor r p * taylor r q := by
  simp only [← taylor_apply, ← mul_comp]

/-- `polynomial.taylor` as a `alg_hom` for commutative semirings -/
@[simps apply]
def taylorAlgHom {R} [CommSemiringₓ R] (r : R) : R[X] →ₐ[R] R[X] :=
  AlgHom.ofLinearMap (taylor r) (taylor_one r) (taylor_mul r)

theorem taylor_taylor {R} [CommSemiringₓ R] (f : R[X]) (r s : R) : taylor r (taylor s f) = taylor (r + s) f := by
  simp only [← taylor_apply, ← comp_assoc, ← map_add, ← add_comp, ← X_comp, ← C_comp, ← C_add, ← add_assocₓ]

theorem taylor_eval {R} [CommSemiringₓ R] (r : R) (f : R[X]) (s : R) : (taylor r f).eval s = f.eval (s + r) := by
  simp only [← taylor_apply, ← eval_comp, ← eval_C, ← eval_X, ← eval_add]

theorem taylor_eval_sub {R} [CommRingₓ R] (r : R) (f : R[X]) (s : R) : (taylor r f).eval (s - r) = f.eval s := by
  rw [taylor_eval, sub_add_cancel]

theorem taylor_injective {R} [CommRingₓ R] (r : R) : Function.Injective (taylor r) := by
  intro f g h
  apply_fun taylor (-r)  at h
  simpa only [← taylor_apply, ← comp_assoc, ← add_comp, ← X_comp, ← C_comp, ← C_neg, ← neg_add_cancel_right, ←
    comp_X] using h

theorem eq_zero_of_hasse_deriv_eq_zero {R} [CommRingₓ R] (f : R[X]) (r : R) (h : ∀ k, (hasseDeriv k f).eval r = 0) :
    f = 0 := by
  apply taylor_injective r
  rw [LinearMap.map_zero]
  ext k
  simp only [← taylor_coeff, ← h, ← coeff_zero]

/-- Taylor's formula. -/
theorem sum_taylor_eq {R} [CommRingₓ R] (f : R[X]) (r : R) : ((taylor r f).Sum fun i a => c a * (X - c r) ^ i) = f := by
  rw [← comp_eq_sum_left, sub_eq_add_neg, ← C_neg, ← taylor_apply, taylor_taylor, neg_add_selfₓ, taylor_zero]

end Polynomial

