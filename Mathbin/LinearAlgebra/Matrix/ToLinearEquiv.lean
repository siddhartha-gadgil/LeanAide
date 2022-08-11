/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.LinearAlgebra.Matrix.Nondegenerate
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Integer

/-!
# Matrices and linear equivalences

This file gives the map `matrix.to_linear_equiv` from matrices with invertible determinant,
to linear equivs.

## Main definitions

 * `matrix.to_linear_equiv`: a matrix with an invertible determinant forms a linear equiv

## Main results

 * `matrix.exists_mul_vec_eq_zero_iff`: `M` maps some `v ≠ 0` to zero iff `det M = 0`

## Tags

matrix, linear_equiv, determinant, inverse

-/


namespace Matrix

open LinearMap

variable {R M : Type _} [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

variable {n : Type _} [Fintype n]

section ToLinearEquiv'

variable [DecidableEq n]

/-- An invertible matrix yields a linear equivalence from the free module to itself.

See `matrix.to_linear_equiv` for the same map on arbitrary modules.
-/
def toLinearEquiv' (P : Matrix n n R) (h : Invertible P) : (n → R) ≃ₗ[R] n → R :=
  { P.toLin' with invFun := (⅟ P).toLin',
    left_inv := fun v =>
      show ((⅟ P).toLin'.comp P.toLin') v = v by
        rw [← Matrix.to_lin'_mul, P.inv_of_mul_self, Matrix.to_lin'_one, LinearMap.id_apply],
    right_inv := fun v =>
      show (P.toLin'.comp (⅟ P).toLin') v = v by
        rw [← Matrix.to_lin'_mul, P.mul_inv_of_self, Matrix.to_lin'_one, LinearMap.id_apply] }

@[simp]
theorem to_linear_equiv'_apply (P : Matrix n n R) (h : Invertible P) :
    (↑(P.toLinearEquiv' h) : Module.End R (n → R)) = P.toLin' :=
  rfl

@[simp]
theorem to_linear_equiv'_symm_apply (P : Matrix n n R) (h : Invertible P) :
    (↑(P.toLinearEquiv' h).symm : Module.End R (n → R)) = P⁻¹.toLin' :=
  show (⅟ P).toLin' = _ from congr_arg _ P.inv_of_eq_nonsing_inv

end ToLinearEquiv'

section ToLinearEquiv

variable (b : Basis n R M)

include b

/-- Given `hA : is_unit A.det` and `b : basis R b`, `A.to_linear_equiv b hA` is
the `linear_equiv` arising from `to_lin b b A`.

See `matrix.to_linear_equiv'` for this result on `n → R`.
-/
@[simps apply]
noncomputable def toLinearEquiv [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) : M ≃ₗ[R] M := by
  refine'
      { to_lin b b A with toFun := to_lin b b A, invFun := to_lin b b A⁻¹, left_inv := fun x => _,
        right_inv := fun x => _ } <;>
    rw [← LinearMap.comp_apply] <;>
      simp only [Matrix.to_lin_mul b b b, ← Matrix.nonsing_inv_mul _ hA, ← Matrix.mul_nonsing_inv _ hA, ← to_lin_one, ←
        LinearMap.id_apply]

theorem ker_to_lin_eq_bot [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) : (toLin b b A).ker = ⊥ :=
  ker_eq_bot.mpr (toLinearEquiv b A hA).Injective

theorem range_to_lin_eq_top [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) : (toLin b b A).range = ⊤ :=
  range_eq_top.mpr (toLinearEquiv b A hA).Surjective

end ToLinearEquiv

section Nondegenerate

open Matrix

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (v «expr ≠ » 0)
/-- This holds for all integral domains (see `matrix.exists_mul_vec_eq_zero_iff`),
not just fields, but it's easier to prove it for the field of fractions first. -/
theorem exists_mul_vec_eq_zero_iff_aux {K : Type _} [DecidableEq n] [Field K] {M : Matrix n n K} :
    (∃ (v : _)(_ : v ≠ 0), M.mulVec v = 0) ↔ M.det = 0 := by
  constructor
  · rintro ⟨v, hv, mul_eq⟩
    contrapose! hv
    exact eq_zero_of_mul_vec_eq_zero hv mul_eq
    
  · contrapose!
    intro h
    have : Function.Injective M.to_lin' := by
      simpa only [LinearMap.ker_eq_bot, ← ker_to_lin'_eq_bot_iff, ← not_imp_not] using h
    have : M ⬝ LinearMap.toMatrix' ((LinearEquiv.ofInjectiveEndo M.to_lin' this).symm : (n → K) →ₗ[K] n → K) = 1 := by
      refine' matrix.to_lin'.injective (LinearMap.ext fun v => _)
      rw [Matrix.to_lin'_mul, Matrix.to_lin'_one, Matrix.to_lin'_to_matrix', LinearMap.comp_apply]
      exact (LinearEquiv.ofInjectiveEndo M.to_lin' this).apply_symm_apply v
    exact Matrix.det_ne_zero_of_right_inverse this
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (v «expr ≠ » 0)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (v «expr ≠ » 0)
theorem exists_mul_vec_eq_zero_iff' {A : Type _} (K : Type _) [DecidableEq n] [CommRingₓ A] [Nontrivial A] [Field K]
    [Algebra A K] [IsFractionRing A K] {M : Matrix n n A} : (∃ (v : _)(_ : v ≠ 0), M.mulVec v = 0) ↔ M.det = 0 := by
  have : (∃ (v : _)(_ : v ≠ 0), mul_vec ((algebraMap A K).mapMatrix M) v = 0) ↔ _ := exists_mul_vec_eq_zero_iff_aux
  rw [← RingHom.map_det, IsFractionRing.to_map_eq_zero_iff] at this
  refine' Iff.trans _ this
  constructor <;> rintro ⟨v, hv, mul_eq⟩
  · refine' ⟨fun i => algebraMap _ _ (v i), mt (fun h => funext fun i => _) hv, _⟩
    · exact is_fraction_ring.to_map_eq_zero_iff.mp (congr_fun h i)
      
    · ext i
      refine' (RingHom.map_mul_vec _ _ _ i).symm.trans _
      rw [mul_eq, Pi.zero_apply, RingHom.map_zero, Pi.zero_apply]
      
    
  · let this := Classical.decEq K
    obtain ⟨⟨b, hb⟩, ba_eq⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (finset.univ.image v)
    choose f hf using ba_eq
    refine' ⟨fun i => f _ (finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), mt (fun h => funext fun i => _) hv, _⟩
    · have := congr_arg (algebraMap A K) (congr_fun h i)
      rw [hf, Subtype.coe_mk, Pi.zero_apply, RingHom.map_zero, Algebra.smul_def, mul_eq_zero,
        IsFractionRing.to_map_eq_zero_iff] at this
      exact this.resolve_left (nonZeroDivisors.ne_zero hb)
      
    · ext i
      refine' IsFractionRing.injective A K _
      calc
        algebraMap A K (M.mul_vec (fun i : n => f (v i) _) i) =
            ((algebraMap A K).mapMatrix M).mulVec (algebraMap _ K b • v) i :=
          _ _ = 0 := _ _ = algebraMap A K 0 := (RingHom.map_zero _).symm
      · simp_rw [RingHom.map_mul_vec, mul_vec, dot_product, Function.comp_app, hf, Subtype.coe_mk,
          RingHom.map_matrix_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
        
      · rw [mul_vec_smul, mul_eq, Pi.smul_apply, Pi.zero_apply, smul_zero]
        
      
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (v «expr ≠ » 0)
theorem exists_mul_vec_eq_zero_iff {A : Type _} [DecidableEq n] [CommRingₓ A] [IsDomain A] {M : Matrix n n A} :
    (∃ (v : _)(_ : v ≠ 0), M.mulVec v = 0) ↔ M.det = 0 :=
  exists_mul_vec_eq_zero_iff' (FractionRing A)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (v «expr ≠ » 0)
theorem exists_vec_mul_eq_zero_iff {A : Type _} [DecidableEq n] [CommRingₓ A] [IsDomain A] {M : Matrix n n A} :
    (∃ (v : _)(_ : v ≠ 0), M.vecMul v = 0) ↔ M.det = 0 := by
  simpa only [M.det_transpose, mul_vec_transpose] using exists_mul_vec_eq_zero_iff

theorem nondegenerate_iff_det_ne_zero {A : Type _} [DecidableEq n] [CommRingₓ A] [IsDomain A] {M : Matrix n n A} :
    Nondegenerate M ↔ M.det ≠ 0 := by
  refine' Iff.trans _ (not_iff_not.mpr exists_vec_mul_eq_zero_iff)
  simp only [← not_exists]
  constructor
  · intro hM v hv hMv
    obtain ⟨w, hwMv⟩ := hM.exists_not_ortho_of_ne_zero hv
    simpa only [← dot_product_mul_vec, ← hMv, ← zero_dot_product] using hwMv
    
  · intro h v hv
    refine' not_imp_not.mp (h v) (funext fun i => _)
    simpa only [← dot_product_mul_vec, ← dot_product_single, ← mul_oneₓ] using hv (Pi.single i 1)
    

alias nondegenerate_iff_det_ne_zero ↔ nondegenerate.det_ne_zero nondegenerate.of_det_ne_zero

end Nondegenerate

end Matrix

