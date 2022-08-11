/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Data.MvPolynomial.Supported
import Mathbin.RingTheory.Derivation

/-!
# Derivations of multivariate polynomials

In this file we prove that a derivation of `mv_polynomial σ R` is determined by its values on all
monomials `mv_polynomial.X i`. We also provide a constructor `mv_polynomial.mk_derivation` that
builds a derivation from its values on `X i`s and a linear equivalence
`mv_polynomial.equiv_derivation` between `σ → A` and `derivation (mv_polynomial σ R) A`.
-/


namespace MvPolynomial

open BigOperators

noncomputable section

variable {σ R A : Type _} [CommSemiringₓ R] [AddCommMonoidₓ A] [Module R A] [Module (MvPolynomial σ R) A]

section

variable (R)

/-- The derivation on `mv_polynomial σ R` that takes value `f i` on `X i`, as a linear map.
Use `mv_polynomial.mk_derivation` instead. -/
def mkDerivationₗ (f : σ → A) : MvPolynomial σ R →ₗ[R] A :=
  (Finsupp.lsum R) fun xs : σ →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf R R A).symm <| xs.Sum fun i k => monomial (xs - Finsupp.single i 1) (k : R) • f i

end

theorem mk_derivationₗ_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    mkDerivationₗ R f (monomial s r) = r • s.Sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i :=
  sum_monomial_eq <| LinearMap.map_zero _

theorem mk_derivationₗ_C (f : σ → A) (r : R) : mkDerivationₗ R f (c r) = 0 :=
  (mk_derivationₗ_monomial f _ _).trans (smul_zero _)

theorem mk_derivationₗ_X (f : σ → A) (i : σ) : mkDerivationₗ R f (x i) = f i :=
  (mk_derivationₗ_monomial f _ _).trans <| by
    simp

@[simp]
theorem derivation_C (D : Derivation R (MvPolynomial σ R) A) (a : R) : D (c a) = 0 :=
  D.map_algebra_map a

@[simp]
theorem derivation_C_mul (D : Derivation R (MvPolynomial σ R) A) (a : R) (f : MvPolynomial σ R) :
    D (c a * f) = a • D f := by
  rw [C_mul', D.map_smul]

/-- If two derivations agree on `X i`, `i ∈ s`, then they agree on all polynomials from
`mv_polynomial.supported R s`. -/
theorem derivation_eq_on_supported {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {s : Set σ}
    (h : Set.EqOn (D₁ ∘ X) (D₂ ∘ X) s) {f : MvPolynomial σ R} (hf : f ∈ supported R s) : D₁ f = D₂ f :=
  Derivation.eq_on_adjoin (Set.ball_image_iff.2 h) hf

theorem derivation_eq_of_forall_mem_vars {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {f : MvPolynomial σ R}
    (h : ∀, ∀ i ∈ f.vars, ∀, D₁ (x i) = D₂ (x i)) : D₁ f = D₂ f :=
  derivation_eq_on_supported h f.mem_supported_vars

theorem derivation_eq_zero_of_forall_mem_vars {D : Derivation R (MvPolynomial σ R) A} {f : MvPolynomial σ R}
    (h : ∀, ∀ i ∈ f.vars, ∀, D (x i) = 0) : D f = 0 :=
  show D f = (0 : Derivation R (MvPolynomial σ R) A) f from derivation_eq_of_forall_mem_vars h

@[ext]
theorem derivation_ext {D₁ D₂ : Derivation R (MvPolynomial σ R) A} (h : ∀ i, D₁ (x i) = D₂ (x i)) : D₁ = D₂ :=
  Derivation.ext fun f => derivation_eq_of_forall_mem_vars fun i _ => h i

variable [IsScalarTower R (MvPolynomial σ R) A]

theorem leibniz_iff_X (D : MvPolynomial σ R →ₗ[R] A) (h₁ : D 1 = 0) :
    (∀ p q, D (p * q) = p • D q + q • D p) ↔
      ∀ s i,
        D (monomial s 1 * x i) =
          (monomial s 1 : MvPolynomial σ R) • D (x i) + (x i : MvPolynomial σ R) • D (monomial s 1) :=
  by
  refine' ⟨fun H p i => H _ _, fun H => _⟩
  have hC : ∀ r, D (C r) = 0 := by
    intro r
    rw [C_eq_smul_one, D.map_smul, h₁, smul_zero]
  have : ∀ p i, D (p * X i) = p • D (X i) + (X i : MvPolynomial σ R) • D p := by
    intro p i
    induction' p using MvPolynomial.induction_on' with s r p q hp hq
    · rw [← mul_oneₓ r, ← C_mul_monomial, mul_assoc, C_mul', D.map_smul, H, C_mul', smul_assoc, smul_add, D.map_smul,
        smul_comm r (X i)]
      infer_instance
      
    · rw [add_mulₓ, map_add, map_add, hp, hq, add_smul, smul_add, add_add_add_commₓ]
      
  intro p q
  induction q using MvPolynomial.induction_on
  case h_C c =>
    rw [mul_comm, C_mul', hC, smul_zero, zero_addₓ, D.map_smul, C_eq_smul_one, smul_one_smul]
  case h_add q₁ q₂ h₁ h₂ =>
    simp only [← mul_addₓ, ← map_add, ← h₁, ← h₂, ← smul_add, ← add_smul]
    abel
  case h_X q i hq =>
    simp only [← this, mul_assoc, ← hq, ← mul_smul, ← smul_add, ← smul_comm (X i), ← add_assocₓ]

variable (R)

/-- The derivation on `mv_polynomial σ R` that takes value `f i` on `X i`. -/
def mkDerivation (f : σ → A) : Derivation R (MvPolynomial σ R) A where
  toLinearMap := mkDerivationₗ R f
  map_one_eq_zero' := mk_derivationₗ_C _ 1
  leibniz' :=
    (leibniz_iff_X (mkDerivationₗ R f) (mk_derivationₗ_C _ 1)).2 fun s i => by
      simp only [← mk_derivationₗ_monomial, ← X, ← monomial_mul, ← one_smul, ← one_mulₓ]
      rw [Finsupp.sum_add_index] <;> [skip,
        · simp
          ,
        · intros
          simp only [← Nat.cast_addₓ, ← (monomial _).map_add, ← add_smul]
          ]
      rw [Finsupp.sum_single_index, Finsupp.sum_single_index] <;> [skip,
        · simp
          ,
        · simp
          ]
      rw [tsub_self, add_tsub_cancel_right, Nat.cast_oneₓ, ← C_apply, C_1, one_smul, add_commₓ, Finsupp.smul_sum]
      refine' congr_arg2ₓ (· + ·) rfl (Finset.sum_congr rfl fun j hj => _)
      dsimp' only
      rw [smul_smul, monomial_mul, one_mulₓ, add_commₓ s, add_tsub_assoc_of_le]
      rwa [Finsupp.single_le_iff, Nat.succ_le_iff, pos_iff_ne_zero, ← Finsupp.mem_support_iff]

@[simp]
theorem mk_derivation_X (f : σ → A) (i : σ) : mkDerivation R f (x i) = f i :=
  mk_derivationₗ_X f i

theorem mk_derivation_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    mkDerivation R f (monomial s r) = r • s.Sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i :=
  mk_derivationₗ_monomial f s r

/-- `mv_polynomial.mk_derivation` as a linear equivalence. -/
def mkDerivationEquiv : (σ → A) ≃ₗ[R] Derivation R (MvPolynomial σ R) A :=
  LinearEquiv.symm <|
    { invFun := mkDerivation R, toFun := fun D i => D (x i), map_add' := fun D₁ D₂ => rfl, map_smul' := fun c D => rfl,
      left_inv := fun D => derivation_ext <| mk_derivation_X _ _, right_inv := fun f => funext <| mk_derivation_X _ _ }

end MvPolynomial

