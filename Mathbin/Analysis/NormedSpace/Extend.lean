/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathbin.Algebra.Algebra.RestrictScalars
import Mathbin.Data.Complex.IsROrC

/-!
# Extending a continuous `ℝ`-linear map to a continuous `𝕜`-linear map

In this file we provide a way to extend a continuous `ℝ`-linear map to a continuous `𝕜`-linear map
in a way that bounds the norm by the norm of the original map, when `𝕜` is either `ℝ` (the
extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `is_R_or_C 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`Re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `Im (fc x) = -Re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.

## Main definitions

* `linear_map.extend_to_𝕜`
* `continuous_linear_map.extend_to_𝕜`

## Implementation details

For convenience, the main definitions above operate in terms of `restrict_scalars ℝ 𝕜 F`.
Alternate forms which operate on `[is_scalar_tower ℝ 𝕜 F]` instead are provided with a primed name.

-/


open IsROrC

variable {𝕜 : Type _} [IsROrC 𝕜] {F : Type _} [SemiNormedGroup F] [NormedSpace 𝕜 F]

-- mathport name: «exprabs𝕜»
local notation "abs𝕜" => @IsROrC.abs 𝕜 _

/-- Extend `fr : F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜` in a way that will also be continuous and have its norm
bounded by `∥fr∥` if `fr` is continuous. -/
noncomputable def LinearMap.extendTo𝕜' [Module ℝ F] [IsScalarTower ℝ 𝕜 F] (fr : F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 := by
  let fc : F → 𝕜 := fun x => (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x)
  have add : ∀ x y : F, fc (x + y) = fc x + fc y := by
    intro x y
    simp only [← fc]
    simp only [← smul_add, ← LinearMap.map_add, ← of_real_add]
    rw [mul_addₓ]
    abel
  have A : ∀ (c : ℝ) (x : F), (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜) := by
    intro c x
    rw [← of_real_mul]
    congr 1
    rw [IsROrC.of_real_alg, smul_assoc, fr.map_smul, Algebra.id.smul_eq_mul, one_smul]
  have smul_ℝ : ∀ (c : ℝ) (x : F), fc ((c : 𝕜) • x) = (c : 𝕜) * fc x := by
    intro c x
    simp only [← fc, ← A]
    rw [A c x]
    rw [smul_smul, mul_comm I (c : 𝕜), ← smul_smul, A, mul_sub]
    ring
  have smul_I : ∀ x : F, fc ((I : 𝕜) • x) = (I : 𝕜) * fc x := by
    intro x
    simp only [← fc]
    cases' @I_mul_I_ax 𝕜 _ with h h
    · simp [← h]
      
    rw [mul_sub, ← mul_assoc, smul_smul, h]
    simp only [← neg_mul, ← LinearMap.map_neg, ← one_mulₓ, ← one_smul, ← mul_neg, ← of_real_neg, ← neg_smul, ←
      sub_neg_eq_add, ← add_commₓ]
  have smul_𝕜 : ∀ (c : 𝕜) (x : F), fc (c • x) = c • fc x := by
    intro c x
    rw [← re_add_im c, add_smul, add_smul, add, smul_ℝ, ← smul_smul, smul_ℝ, smul_I, ← mul_assoc]
    rfl
  exact { toFun := fc, map_add' := add, map_smul' := smul_𝕜 }

theorem LinearMap.extend_to_𝕜'_apply [Module ℝ F] [IsScalarTower ℝ 𝕜 F] (fr : F →ₗ[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜' x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x) :=
  rfl

/-- The norm of the extension is bounded by `∥fr∥`. -/
theorem norm_bound [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] (fr : F →L[ℝ] ℝ) (x : F) :
    ∥(fr.toLinearMap.extendTo𝕜' x : 𝕜)∥ ≤ ∥fr∥ * ∥x∥ := by
  let lm : F →ₗ[𝕜] 𝕜 := fr.to_linear_map.extend_to_𝕜'
  -- We aim to find a `t : 𝕜` such that
  -- * `lm (t • x) = fr (t • x)` (so `lm (t • x) = t * lm x ∈ ℝ`)
  -- * `∥lm x∥ = ∥lm (t • x)∥` (so `t.abs` must be 1)
  -- If `lm x ≠ 0`, `(lm x)⁻¹` satisfies the first requirement, and after normalizing, it
  -- satisfies the second.
  -- (If `lm x = 0`, the goal is trivial.)
  classical
  by_cases' h : lm x = 0
  · rw [h, norm_zero]
    apply mul_nonneg <;> exact norm_nonneg _
    
  let fx := (lm x)⁻¹
  let t := fx / (abs𝕜 fx : 𝕜)
  have ht : abs𝕜 t = 1 := by
    field_simp [← abs_of_real, ← of_real_inv, ← IsROrC.abs_inv, ← IsROrC.abs_div, ← IsROrC.abs_abs, ← h]
  have h1 : (fr (t • x) : 𝕜) = lm (t • x) := by
    apply ext
    · simp only [← lm, ← of_real_re, ← LinearMap.extend_to_𝕜'_apply, ← mul_re, ← I_re, ← of_real_im, ← zero_mul, ←
        AddMonoidHom.map_sub, ← sub_zero, ← mul_zero]
      rfl
      
    · symm
      calc im (lm (t • x)) = im (t * lm x) := by
          rw [lm.map_smul, smul_eq_mul]_ = im ((lm x)⁻¹ / abs𝕜 (lm x)⁻¹ * lm x) :=
          rfl _ = im (1 / (abs𝕜 (lm x)⁻¹ : 𝕜)) := by
          rw [div_mul_eq_mul_div, inv_mul_cancel h]_ = 0 := by
          rw [← of_real_one, ← of_real_div, of_real_im]_ = im (fr (t • x) : 𝕜) := by
          rw [of_real_im]
      
  calc ∥lm x∥ = abs𝕜 t * ∥lm x∥ := by
      rw [ht, one_mulₓ]_ = ∥t * lm x∥ := by
      rw [← norm_eq_abs, norm_mul]_ = ∥lm (t • x)∥ := by
      rw [← smul_eq_mul, lm.map_smul]_ = ∥(fr (t • x) : 𝕜)∥ := by
      rw [h1]_ = ∥fr (t • x)∥ := by
      rw [norm_eq_abs, abs_of_real, norm_eq_abs, abs_to_real]_ ≤ ∥fr∥ * ∥t • x∥ :=
      ContinuousLinearMap.le_op_norm _ _ _ = ∥fr∥ * (∥t∥ * ∥x∥) := by
      rw [norm_smul]_ ≤ ∥fr∥ * ∥x∥ := by
      rw [norm_eq_abs, ht, one_mulₓ]

/-- Extend `fr : F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def ContinuousLinearMap.extendTo𝕜' [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] (fr : F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous _ ∥fr∥ (norm_bound _)

theorem ContinuousLinearMap.extend_to_𝕜'_apply [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] (fr : F →L[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜' x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x) :=
  rfl

/-- Extend `fr : restrict_scalars ℝ 𝕜 F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜`. -/
noncomputable def LinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 :=
  fr.extendTo𝕜'

theorem LinearMap.extend_to_𝕜_apply (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜 x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x : _) :=
  rfl

/-- Extend `fr : restrict_scalars ℝ 𝕜 F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def ContinuousLinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  fr.extendTo𝕜'

theorem ContinuousLinearMap.extend_to_𝕜_apply (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜 x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x : _) :=
  rfl

