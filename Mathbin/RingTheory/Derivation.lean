/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.RingTheory.Adjoin.Basic
import Mathbin.Algebra.Lie.OfAssociative

/-!
# Derivations

This file defines derivation. A derivation `D` from the `R`-algebra `A` to the `A`-module `M` is an
`R`-linear map that satisfy the Leibniz rule `D (a * b) = a * D b + D a * b`.

## Notation

The notation `⁅D1, D2⁆` is used for the commutator of two derivations.

TODO: this file is just a stub to go on with some PRs in the geometry section. It only
implements the definition of derivations in commutative algebra. This will soon change: as soon
as bimodules will be there in mathlib I will change this file to take into account the
non-commutative case. Any development on the theory of derivations is discouraged until the
definitive definition of derivation will be implemented.
-/


open Algebra

open BigOperators

/-- `D : derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`
equality. We also require that `D 1 = 0`. See `derivation.mk'` for a constructor that deduces this
assumption from the Leibniz rule when `M` is cancellative.

TODO: update this when bimodules are defined. -/
@[protect_proj]
structure Derivation (R : Type _) (A : Type _) [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] (M : Type _)
  [AddCommMonoidₓ M] [Module A M] [Module R M] extends A →ₗ[R] M where
  map_one_eq_zero' : to_linear_map 1 = 0
  leibniz' (a b : A) : to_linear_map (a * b) = a • to_linear_map b + b • to_linear_map a

/-- The `linear_map` underlying a `derivation`. -/
add_decl_doc Derivation.toLinearMap

namespace Derivation

section

variable {R : Type _} [CommSemiringₓ R]

variable {A : Type _} [CommSemiringₓ A] [Algebra R A]

variable {M : Type _} [AddCommMonoidₓ M] [Module A M] [Module R M]

variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

instance : AddMonoidHomClass (Derivation R A M) A M where
  coe := fun D => D.toFun
  coe_injective' := fun D1 D2 h => by
    cases D1
    cases D2
    congr
    exact FunLike.coe_injective h
  map_add := fun D => D.toLinearMap.map_add'
  map_zero := fun D => D.toLinearMap.map_zero

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (Derivation R A M) fun _ => A → M :=
  ⟨fun D => D.toLinearMap.toFun⟩

-- Not a simp lemma because it can be proved via `coe_fn_coe` + `to_linear_map_eq_coe`
theorem to_fun_eq_coe : D.toFun = ⇑D :=
  rfl

instance hasCoeToLinearMap : Coe (Derivation R A M) (A →ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩

@[simp]
theorem to_linear_map_eq_coe : D.toLinearMap = D :=
  rfl

@[simp]
theorem mk_coe (f : A →ₗ[R] M) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : Derivation R A M) : A → M) = f :=
  rfl

@[simp, norm_cast]
theorem coe_fn_coe (f : Derivation R A M) : ⇑(f : A →ₗ[R] M) = f :=
  rfl

theorem coe_injective : @Function.Injective (Derivation R A M) (A → M) coeFn :=
  FunLike.coe_injective

@[ext]
theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
  FunLike.ext _ _ H

theorem congr_fun (h : D1 = D2) (a : A) : D1 a = D2 a :=
  FunLike.congr_fun h a

protected theorem map_add : D (a + b) = D a + D b :=
  map_add D a b

protected theorem map_zero : D 0 = 0 :=
  map_zero D

@[simp]
theorem map_smul : D (r • a) = r • D a :=
  D.toLinearMap.map_smul r a

@[simp]
theorem leibniz : D (a * b) = a • D b + b • D a :=
  D.leibniz' _ _

theorem map_sum {ι : Type _} (s : Finset ι) (f : ι → A) : D (∑ i in s, f i) = ∑ i in s, D (f i) :=
  D.toLinearMap.map_sum

@[simp]
theorem map_smul_of_tower {S : Type _} [HasSmul S A] [HasSmul S M] [LinearMap.CompatibleSmul A M S R]
    (D : Derivation R A M) (r : S) (a : A) : D (r • a) = r • D a :=
  D.toLinearMap.map_smul_of_tower r a

@[simp]
theorem map_one_eq_zero : D 1 = 0 :=
  D.map_one_eq_zero'

@[simp]
theorem map_algebra_map : D (algebraMap R A r) = 0 := by
  rw [← mul_oneₓ r, RingHom.map_mul, RingHom.map_one, ← smul_def, map_smul, map_one_eq_zero, smul_zero]

@[simp]
theorem map_coe_nat (n : ℕ) : D (n : A) = 0 := by
  rw [← nsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]

@[simp]
theorem leibniz_pow (n : ℕ) : D (a ^ n) = n • a ^ (n - 1) • D a := by
  induction' n with n ihn
  · rw [pow_zeroₓ, map_one_eq_zero, zero_smul]
    
  · rcases(zero_le n).eq_or_lt with (rfl | hpos)
    · rw [pow_oneₓ, one_smul, pow_zeroₓ, one_smul]
      
    · have : a * a ^ (n - 1) = a ^ n := by
        rw [← pow_succₓ, Nat.sub_add_cancelₓ hpos]
      simp only [← pow_succₓ, ← leibniz, ← ihn, ← smul_comm a n, ← smul_smul a, ← add_smul, ← this, ←
        Nat.succ_eq_add_one, ← Nat.add_succ_sub_one, ← add_zeroₓ, ← one_nsmul]
      
    

theorem eq_on_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) : Set.EqOn D1 D2 (adjoin R s) := fun x hx =>
  Algebra.adjoin_induction hx h (fun r => (D1.map_algebra_map r).trans (D2.map_algebra_map r).symm)
    (fun x y hx hy => by
      simp only [← map_add, *])
    fun x y hx hy => by
    simp only [← leibniz, *]

/-- If adjoin of a set is the whole algebra, then any two derivations equal on this set are equal
on the whole algebra. -/
theorem ext_of_adjoin_eq_top (s : Set A) (hs : adjoin R s = ⊤) (h : Set.EqOn D1 D2 s) : D1 = D2 :=
  ext fun a => eq_on_adjoin h <| hs.symm ▸ trivialₓ

-- Data typeclasses
instance : Zero (Derivation R A M) :=
  ⟨{ toLinearMap := 0, map_one_eq_zero' := rfl,
      leibniz' := fun a b => by
        simp only [← add_zeroₓ, ← LinearMap.zero_apply, ← smul_zero] }⟩

@[simp]
theorem coe_zero : ⇑(0 : Derivation R A M) = 0 :=
  rfl

@[simp]
theorem coe_zero_linear_map : ↑(0 : Derivation R A M) = (0 : A →ₗ[R] M) :=
  rfl

theorem zero_apply (a : A) : (0 : Derivation R A M) a = 0 :=
  rfl

instance : Add (Derivation R A M) :=
  ⟨fun D1 D2 =>
    { toLinearMap := D1 + D2,
      map_one_eq_zero' := by
        simp ,
      leibniz' := fun a b => by
        simp only [← leibniz, ← LinearMap.add_apply, ← coe_fn_coe, ← smul_add, ← add_add_add_commₓ] }⟩

@[simp]
theorem coe_add (D1 D2 : Derivation R A M) : ⇑(D1 + D2) = D1 + D2 :=
  rfl

@[simp]
theorem coe_add_linear_map (D1 D2 : Derivation R A M) : ↑(D1 + D2) = (D1 + D2 : A →ₗ[R] M) :=
  rfl

theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
  rfl

instance : Inhabited (Derivation R A M) :=
  ⟨0⟩

section Scalar

variable {S : Type _} [Monoidₓ S] [DistribMulAction S M] [SmulCommClass R S M] [SmulCommClass S A M]

instance (priority := 100) : HasSmul S (Derivation R A M) :=
  ⟨fun r D =>
    { toLinearMap := r • D,
      map_one_eq_zero' := by
        rw [LinearMap.smul_apply, coe_fn_coe, D.map_one_eq_zero, smul_zero],
      leibniz' := fun a b => by
        simp only [← LinearMap.smul_apply, ← coe_fn_coe, ← leibniz, ← smul_add, ← smul_comm r] }⟩

@[simp]
theorem coe_smul (r : S) (D : Derivation R A M) : ⇑(r • D) = r • D :=
  rfl

@[simp]
theorem coe_smul_linear_map (r : S) (D : Derivation R A M) : ↑(r • D) = (r • D : A →ₗ[R] M) :=
  rfl

theorem smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a :=
  rfl

instance : AddCommMonoidₓ (Derivation R A M) :=
  coe_injective.AddCommMonoid _ coe_zero coe_add fun _ _ => rfl

/-- `coe_fn` as an `add_monoid_hom`. -/
def coeFnAddMonoidHom : Derivation R A M →+ A → M where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add

instance (priority := 100) : DistribMulAction S (Derivation R A M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

instance [DistribMulAction Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar S (Derivation R A M) where op_smul_eq_smul := fun _ _ => ext fun _ => op_smul_eq_smul _ _

end Scalar

instance (priority := 100) {S : Type _} [Semiringₓ S] [Module S M] [SmulCommClass R S M] [SmulCommClass S A M] :
    Module S (Derivation R A M) :=
  Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

instance [IsScalarTower R A M] : IsScalarTower R A (Derivation R A M) :=
  ⟨fun x y z => ext fun a => smul_assoc _ _ _⟩

section PushForward

variable {N : Type _} [AddCommMonoidₓ N] [Module A N] [Module R N] [IsScalarTower R A M] [IsScalarTower R A N]

variable (f : M →ₗ[A] N)

/-- We can push forward derivations using linear maps, i.e., the composition of a derivation with a
linear map is a derivation. Furthermore, this operation is linear on the spaces of derivations. -/
def _root_.linear_map.comp_der : Derivation R A M →ₗ[R] Derivation R A N where
  toFun := fun D =>
    { toLinearMap := (f : M →ₗ[R] N).comp (D : A →ₗ[R] M),
      map_one_eq_zero' := by
        simp only [← LinearMap.comp_apply, ← coe_fn_coe, ← map_one_eq_zero, ← map_zero],
      leibniz' := fun a b => by
        simp only [← coe_fn_coe, ← LinearMap.comp_apply, ← LinearMap.map_add, ← leibniz, ←
          LinearMap.coe_coe_is_scalar_tower, ← LinearMap.map_smul] }
  map_add' := fun D₁ D₂ => by
    ext
    exact LinearMap.map_add _ _ _
  map_smul' := fun r D => by
    ext
    exact LinearMap.map_smul _ _ _

@[simp]
theorem coe_to_linear_map_comp : (f.compDer D : A →ₗ[R] N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl

@[simp]
theorem coe_comp : (f.compDer D : A → N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl

end PushForward

end

section Cancel

variable {R : Type _} [CommSemiringₓ R] {A : Type _} [CommSemiringₓ A] [Algebra R A] {M : Type _}
  [AddCancelCommMonoid M] [Module R M] [Module A M]

/-- Define `derivation R A M` from a linear map when `M` is cancellative by verifying the Leibniz
rule. -/
def mk' (D : A →ₗ[R] M) (h : ∀ a b, D (a * b) = a • D b + b • D a) : Derivation R A M where
  toLinearMap := D
  map_one_eq_zero' :=
    add_right_eq_selfₓ.1 <| by
      simpa only [← one_smul, ← one_mulₓ] using (h 1 1).symm
  leibniz' := h

@[simp]
theorem coe_mk' (D : A →ₗ[R] M) (h) : ⇑(mk' D h) = D :=
  rfl

@[simp]
theorem coe_mk'_linear_map (D : A →ₗ[R] M) (h) : (mk' D h : A →ₗ[R] M) = D :=
  rfl

end Cancel

section

variable {R : Type _} [CommRingₓ R]

variable {A : Type _} [CommRingₓ A] [Algebra R A]

section

variable {M : Type _} [AddCommGroupₓ M] [Module A M] [Module R M]

variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

protected theorem map_neg : D (-a) = -D a :=
  map_neg D a

protected theorem map_sub : D (a - b) = D a - D b :=
  map_sub D a b

@[simp]
theorem map_coe_int (n : ℤ) : D (n : A) = 0 := by
  rw [← zsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]

theorem leibniz_of_mul_eq_one {a b : A} (h : a * b = 1) : D a = -(a ^ 2) • D b := by
  rw [neg_smul]
  refine' eq_neg_of_add_eq_zero_left _
  calc D a + a ^ 2 • D b = a • b • D a + a • a • D b := by
      simp only [← smul_smul, ← h, ← one_smul, ← sq]_ = a • D (a * b) := by
      rw [leibniz, smul_add, add_commₓ]_ = 0 := by
      rw [h, map_one_eq_zero, smul_zero]

theorem leibniz_inv_of [Invertible a] : D (⅟ a) = -(⅟ a ^ 2) • D a :=
  D.leibniz_of_mul_eq_one <| inv_of_mul_self a

theorem leibniz_inv {K : Type _} [Field K] [Module K M] [Algebra R K] (D : Derivation R K M) (a : K) :
    D a⁻¹ = -(a⁻¹ ^ 2) • D a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
    
  · exact D.leibniz_of_mul_eq_one (inv_mul_cancel ha)
    

instance : Neg (Derivation R A M) :=
  ⟨fun D =>
    (mk' (-D)) fun a b => by
      simp only [← LinearMap.neg_apply, ← smul_neg, ← neg_add_rev, ← leibniz, ← coe_fn_coe, ← add_commₓ]⟩

@[simp]
theorem coe_neg (D : Derivation R A M) : ⇑(-D) = -D :=
  rfl

@[simp]
theorem coe_neg_linear_map (D : Derivation R A M) : ↑(-D) = (-D : A →ₗ[R] M) :=
  rfl

theorem neg_apply : (-D) a = -D a :=
  rfl

instance : Sub (Derivation R A M) :=
  ⟨fun D1 D2 =>
    (mk' (D1 - D2 : A →ₗ[R] M)) fun a b => by
      simp only [← LinearMap.sub_apply, ← leibniz, ← coe_fn_coe, ← smul_sub, ← add_sub_add_comm]⟩

@[simp]
theorem coe_sub (D1 D2 : Derivation R A M) : ⇑(D1 - D2) = D1 - D2 :=
  rfl

@[simp]
theorem coe_sub_linear_map (D1 D2 : Derivation R A M) : ↑(D1 - D2) = (D1 - D2 : A →ₗ[R] M) :=
  rfl

theorem sub_apply : (D1 - D2) a = D1 a - D2 a :=
  rfl

instance : AddCommGroupₓ (Derivation R A M) :=
  coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end

section LieStructures

/-! # Lie structures -/


variable (D : Derivation R A A) {D1 D2 : Derivation R A A} (r : R) (a b : A)

/-- The commutator of derivations is again a derivation. -/
instance : HasBracket (Derivation R A A) (Derivation R A A) :=
  ⟨fun D1 D2 =>
    (mk' ⁅(D1 : Module.End R A),(D2 : Module.End R A)⁆) fun a b => by
      simp only [← Ringₓ.lie_def, ← map_add, ← id.smul_eq_mul, ← LinearMap.mul_apply, ← leibniz, ← coe_fn_coe, ←
        LinearMap.sub_apply]
      ring⟩

@[simp]
theorem commutator_coe_linear_map : ↑⁅D1,D2⁆ = ⁅(D1 : Module.End R A),(D2 : Module.End R A)⁆ :=
  rfl

theorem commutator_apply : ⁅D1,D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl

instance : LieRing (Derivation R A A) where
  add_lie := fun d e f => by
    ext a
    simp only [← commutator_apply, ← add_apply, ← map_add]
    ring
  lie_add := fun d e f => by
    ext a
    simp only [← commutator_apply, ← add_apply, ← map_add]
    ring
  lie_self := fun d => by
    ext a
    simp only [← commutator_apply, ← add_apply, ← map_add]
    ring_nf
  leibniz_lie := fun d e f => by
    ext a
    simp only [← commutator_apply, ← add_apply, ← sub_apply, ← map_sub]
    ring

instance : LieAlgebra R (Derivation R A A) :=
  { Derivation.module with
    lie_smul := fun r d e => by
      ext a
      simp only [← commutator_apply, ← map_smul, ← smul_sub, ← smul_apply] }

end LieStructures

end

end Derivation

