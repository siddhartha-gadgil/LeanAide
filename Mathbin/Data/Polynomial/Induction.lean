/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathbin.Data.Polynomial.Coeff

/-!
# Theory of univariate polynomials

The main results are `induction_on` and `as_sum`.
-/


noncomputable section

open Finsupp Finset

namespace Polynomial

open Polynomial

universe u v w x y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z} {a b : R} {m n : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q r : R[X]}

theorem sum_C_mul_X_eq (p : R[X]) : (p.Sum fun n a => c a * X ^ n) = p := by
  ext n
  simp only [← Polynomial.sum, ← X_pow_eq_monomial, ← coeff_monomial, ← mul_oneₓ, ← finset_sum_coeff, ← C_mul_monomial,
    ← not_not, ← mem_support_iff, ← Finset.sum_ite_eq', ← ite_eq_left_iff]
  exact fun h => h.symm

theorem sum_monomial_eq (p : R[X]) : (p.Sum fun n a => monomial n a) = p := by
  simp only [← monomial_eq_C_mul_X, ← sum_C_mul_X_eq]

@[elab_as_eliminator]
protected theorem induction_on {M : R[X] → Prop} (p : R[X]) (h_C : ∀ a, M (c a)) (h_add : ∀ p q, M p → M q → M (p + q))
    (h_monomial : ∀ (n : ℕ) (a : R), M (c a * X ^ n) → M (c a * X ^ (n + 1))) : M p := by
  have A : ∀ {n : ℕ} {a}, M (C a * X ^ n) := by
    intro n a
    induction' n with n ih
    · simp only [← pow_zeroₓ, ← mul_oneₓ, ← h_C]
      
    · exact h_monomial _ _ ih
      
  have B : ∀ s : Finset ℕ, M (s.Sum fun n : ℕ => C (p.coeff n) * X ^ n) := by
    apply Finset.induction
    · convert h_C 0
      exact C_0.symm
      
    · intro n s ns ih
      rw [sum_insert ns]
      exact h_add _ _ A ih
      
  rw [← sum_C_mul_X_eq p, Polynomial.sum]
  exact B _

/-- To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_eliminator]
protected theorem induction_on' {M : R[X] → Prop} (p : R[X]) (h_add : ∀ p q, M p → M q → M (p + q))
    (h_monomial : ∀ (n : ℕ) (a : R), M (monomial n a)) : M p :=
  Polynomial.induction_on p (h_monomial 0) h_add fun n a h => by
    rw [← monomial_eq_C_mul_X]
    exact h_monomial _ _

section Coeff

theorem coeff_mul_monomial (p : R[X]) (n d : ℕ) (r : R) : coeff (p * monomial n r) (d + n) = coeff p d * r := by
  rw [monomial_eq_C_mul_X, ← X_pow_mul, ← mul_assoc, coeff_mul_C, coeff_mul_X_pow]

theorem coeff_monomial_mul (p : R[X]) (n d : ℕ) (r : R) : coeff (monomial n r * p) (d + n) = r * coeff p d := by
  rw [monomial_eq_C_mul_X, mul_assoc, coeff_C_mul, X_pow_mul, coeff_mul_X_pow]

-- This can already be proved by `simp`.
theorem coeff_mul_monomial_zero (p : R[X]) (d : ℕ) (r : R) : coeff (p * monomial 0 r) d = coeff p d * r :=
  coeff_mul_monomial p 0 d r

-- This can already be proved by `simp`.
theorem coeff_monomial_zero_mul (p : R[X]) (d : ℕ) (r : R) : coeff (monomial 0 r * p) d = r * coeff p d :=
  coeff_monomial_mul p 0 d r

end Coeff

open Submodule Polynomial Set

variable {f : R[X]} {I : Submodule R[X] R[X]}

/-- If the coefficients of a polynomial belong to n ideal contains the submodule span of the
coefficients of a polynomial. -/
theorem span_le_of_coeff_mem_C_inverse (cf : ∀ i : ℕ, f.coeff i ∈ C ⁻¹' I.Carrier) :
    span R[X] { g | ∃ i, g = c (f.coeff i) } ≤ I := by
  refine' bInter_subset_of_mem _
  rintro _ ⟨i, rfl⟩
  exact set_like.mem_coe.mpr (cf i)

theorem mem_span_C_coeff : f ∈ span R[X] { g : R[X] | ∃ i : ℕ, g = c (coeff f i) } := by
  let p := span R[X] { g : R[X] | ∃ i : ℕ, g = C (coeff f i) }
  nth_rw 0[(sum_C_mul_X_eq f).symm]
  refine' Submodule.sum_mem _ fun n hn => _
  dsimp'
  have : C (coeff f n) ∈ p := by
    apply subset_span
    simp
  have : monomial n (1 : R) • C (coeff f n) ∈ p := p.smul_mem _ this
  convert this using 1
  simp only [← monomial_mul_C, ← one_mulₓ, ← smul_eq_mul]
  rw [monomial_eq_C_mul_X]

theorem exists_coeff_not_mem_C_inverse : f ∉ I → ∃ i : ℕ, coeff f i ∉ C ⁻¹' I.Carrier :=
  imp_of_not_imp_not _ _ fun cf =>
    not_not.mpr ((span_le_of_coeff_mem_C_inverse (not_exists_not.mp cf)) mem_span_C_coeff)

end Semiringₓ

end Polynomial

