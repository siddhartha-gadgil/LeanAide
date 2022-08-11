/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathbin.Data.Complex.IsROrC
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Analysis.NormedSpace.Pointwise

/-!
# Normed spaces over R or C

This file is about results on normed spaces over the fields `ℝ` and `ℂ`.

## Main definitions

None.

## Main theorems

* `continuous_linear_map.op_norm_bound_of_ball_bound`: A bound on the norms of values of a linear
  map in a ball yields a bound on the operator norm.

## Notes

This file exists mainly to avoid importing `is_R_or_C` in the main normed space theory files.
-/


open Metric

@[simp, is_R_or_C_simps]
theorem IsROrC.norm_coe_norm {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [NormedGroup E] {z : E} : ∥(∥z∥ : 𝕜)∥ = ∥z∥ := by
  unfold_coes
  simp only [← norm_algebra_map', ← RingHom.to_fun_eq_coe, ← norm_norm]

variable {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

/-- Lemma to normalize a vector in a normed space `E` over either `ℂ` or `ℝ` to unit length. -/
@[simp]
theorem norm_smul_inv_norm {x : E} (hx : x ≠ 0) : ∥(∥x∥⁻¹ : 𝕜) • x∥ = 1 := by
  have : ∥x∥ ≠ 0 := by
    simp [← hx]
  field_simp [← norm_smul]

/-- Lemma to normalize a vector in a normed space `E` over either `ℂ` or `ℝ` to length `r`. -/
theorem norm_smul_inv_norm' {r : ℝ} (r_nonneg : 0 ≤ r) {x : E} (hx : x ≠ 0) : ∥(r * ∥x∥⁻¹ : 𝕜) • x∥ = r := by
  have : ∥x∥ ≠ 0 := by
    simp [← hx]
  field_simp [← norm_smul, ← IsROrC.norm_eq_abs, ← r_nonneg] with is_R_or_C_simps

theorem LinearMap.bound_of_sphere_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
    (h : ∀, ∀ z ∈ Sphere (0 : E) r, ∀, ∥f z∥ ≤ c) (z : E) : ∥f z∥ ≤ c / r * ∥z∥ := by
  by_cases' z_zero : z = 0
  · rw [z_zero]
    simp only [← LinearMap.map_zero, ← norm_zero, ← mul_zero]
    
  set z₁ := (r * ∥z∥⁻¹ : 𝕜) • z with hz₁
  have norm_f_z₁ : ∥f z₁∥ ≤ c := by
    apply h
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm' r_pos.le z_zero
  have r_ne_zero : (r : 𝕜) ≠ 0 := (algebraMap ℝ 𝕜).map_ne_zero.mpr r_pos.ne.symm
  have eq : f z = ∥z∥ / r * f z₁ := by
    rw [hz₁, LinearMap.map_smul, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, div_mul_cancel _ r_ne_zero, mul_inv_cancel, one_mulₓ]
    simp only [← z_zero, ← IsROrC.of_real_eq_zero, ← norm_eq_zero, ← Ne.def, ← not_false_iff]
  rw [Eq, norm_mul, norm_div, IsROrC.norm_coe_norm, IsROrC.norm_of_nonneg r_pos.le, div_mul_eq_mul_div,
    div_mul_eq_mul_div, mul_comm]
  apply div_le_div _ _ r_pos rfl.ge
  · exact mul_nonneg ((norm_nonneg _).trans norm_f_z₁) (norm_nonneg z)
    
  apply mul_le_mul norm_f_z₁ rfl.le (norm_nonneg z) ((norm_nonneg _).trans norm_f_z₁)

/-- `linear_map.bound_of_ball_bound` is a version of this over arbitrary nondiscrete normed fields.
It produces a less precise bound so we keep both versions. -/
theorem LinearMap.bound_of_ball_bound' {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
    (h : ∀, ∀ z ∈ ClosedBall (0 : E) r, ∀, ∥f z∥ ≤ c) (z : E) : ∥f z∥ ≤ c / r * ∥z∥ :=
  f.bound_of_sphere_bound r_pos c (fun z hz => h z hz.le) z

theorem ContinuousLinearMap.op_norm_bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →L[𝕜] 𝕜)
    (h : ∀, ∀ z ∈ ClosedBall (0 : E) r, ∀, ∥f z∥ ≤ c) : ∥f∥ ≤ c / r := by
  apply ContinuousLinearMap.op_norm_le_bound
  · apply div_nonneg _ r_pos.le
    exact
      (norm_nonneg _).trans
        (h 0
          (by
            simp only [← norm_zero, ← mem_closed_ball, ← dist_zero_left, ← r_pos.le]))
    
  apply LinearMap.bound_of_ball_bound' r_pos
  exact fun z hz => h z hz

variable (𝕜)

include 𝕜

theorem NormedSpace.sphere_nonempty_is_R_or_C [Nontrivial E] {r : ℝ} (hr : 0 ≤ r) : Nonempty (Sphere (0 : E) r) := by
  let this : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  exact set.nonempty_coe_sort.mpr (normed_space.sphere_nonempty.mpr hr)

