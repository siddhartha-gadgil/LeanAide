/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.
-/


noncomputable section

namespace Complex

open Set Filter

open Real

theorem has_strict_deriv_at_tan {x : ℂ} (h : cos x ≠ 0) : HasStrictDerivAt tan (1 / cos x ^ 2) x := by
  convert (has_strict_deriv_at_sin x).div (has_strict_deriv_at_cos x) h
  rw [← sin_sq_add_cos_sq x]
  ring

theorem has_deriv_at_tan {x : ℂ} (h : cos x ≠ 0) : HasDerivAt tan (1 / cos x ^ 2) x :=
  (has_strict_deriv_at_tan h).HasDerivAt

open TopologicalSpace

theorem tendsto_abs_tan_of_cos_eq_zero {x : ℂ} (hx : cos x = 0) : Tendsto (fun x => abs (tan x)) (𝓝[≠] x) atTop := by
  simp only [← tan_eq_sin_div_cos, norm_eq_abs, ← norm_div]
  have A : sin x ≠ 0 := fun h => by
    simpa [*, ← sq] using sin_sq_add_cos_sq x
  have B : tendsto cos (𝓝[≠] x) (𝓝[≠] 0) := hx ▸ (has_deriv_at_cos x).tendsto_punctured_nhds (neg_ne_zero.2 A)
  exact
    continuous_sin.continuous_within_at.norm.mul_at_top (norm_pos_iff.2 A)
      (tendsto_norm_nhds_within_zero.comp B).inv_tendsto_zero

theorem tendsto_abs_tan_at_top (k : ℤ) : Tendsto (fun x => abs (tan x)) (𝓝[≠] ((2 * k + 1) * π / 2)) atTop :=
  tendsto_abs_tan_of_cos_eq_zero <| cos_eq_zero_iff.2 ⟨k, rfl⟩

@[simp]
theorem continuous_at_tan {x : ℂ} : ContinuousAt tan x ↔ cos x ≠ 0 := by
  refine' ⟨fun hc h₀ => _, fun h => (has_deriv_at_tan h).ContinuousAt⟩
  exact not_tendsto_nhds_of_tendsto_at_top (tendsto_abs_tan_of_cos_eq_zero h₀) _ (hc.norm.tendsto.mono_left inf_le_left)

@[simp]
theorem differentiable_at_tan {x : ℂ} : DifferentiableAt ℂ tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuous_at_tan.1 h.ContinuousAt, fun h => (has_deriv_at_tan h).DifferentiableAt⟩

@[simp]
theorem deriv_tan (x : ℂ) : deriv tan x = 1 / cos x ^ 2 :=
  if h : cos x = 0 then by
    have : ¬DifferentiableAt ℂ tan x := mt differentiable_at_tan.1 (not_not.2 h)
    simp [← deriv_zero_of_not_differentiable_at this, ← h, ← sq]
  else (has_deriv_at_tan h).deriv

@[simp]
theorem cont_diff_at_tan {x : ℂ} {n : WithTop ℕ} : ContDiffAt ℂ n tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuous_at_tan.1 h.ContinuousAt, cont_diff_sin.ContDiffAt.div cont_diff_cos.ContDiffAt⟩

end Complex

