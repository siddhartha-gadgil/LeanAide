/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathbin.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

/-!
# Derivatives of the `tan` and `arctan` functions.

Continuity and derivatives of the tangent and arctangent functions.
-/


noncomputable section

namespace Real

open Set Filter

open TopologicalSpace Real

theorem has_strict_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) : HasStrictDerivAt tan (1 / cos x ^ 2) x := by
  exact_mod_cast
    (Complex.has_strict_deriv_at_tan
        (by
          exact_mod_cast h)).real_of_complex

theorem has_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) : HasDerivAt tan (1 / cos x ^ 2) x := by
  exact_mod_cast
    (Complex.has_deriv_at_tan
        (by
          exact_mod_cast h)).real_of_complex

theorem tendsto_abs_tan_of_cos_eq_zero {x : ℝ} (hx : cos x = 0) : Tendsto (fun x => abs (tan x)) (𝓝[≠] x) atTop := by
  have hx : Complex.cos x = 0 := by
    exact_mod_cast hx
  simp only [Complex.abs_of_real, ← Complex.of_real_tan]
  refine' (Complex.tendsto_abs_tan_of_cos_eq_zero hx).comp _
  refine' tendsto.inf complex.continuous_of_real.continuous_at _
  exact tendsto_principal_principal.2 fun y => mt Complex.of_real_inj.1

theorem tendsto_abs_tan_at_top (k : ℤ) : Tendsto (fun x => abs (tan x)) (𝓝[≠] ((2 * k + 1) * π / 2)) atTop :=
  tendsto_abs_tan_of_cos_eq_zero <| cos_eq_zero_iff.2 ⟨k, rfl⟩

theorem continuous_at_tan {x : ℝ} : ContinuousAt tan x ↔ cos x ≠ 0 := by
  refine' ⟨fun hc h₀ => _, fun h => (has_deriv_at_tan h).ContinuousAt⟩
  exact not_tendsto_nhds_of_tendsto_at_top (tendsto_abs_tan_of_cos_eq_zero h₀) _ (hc.norm.tendsto.mono_left inf_le_left)

theorem differentiable_at_tan {x : ℝ} : DifferentiableAt ℝ tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuous_at_tan.1 h.ContinuousAt, fun h => (has_deriv_at_tan h).DifferentiableAt⟩

@[simp]
theorem deriv_tan (x : ℝ) : deriv tan x = 1 / cos x ^ 2 :=
  if h : cos x = 0 then by
    have : ¬DifferentiableAt ℝ tan x := mt differentiable_at_tan.1 (not_not.2 h)
    simp [← deriv_zero_of_not_differentiable_at this, ← h, ← sq]
  else (has_deriv_at_tan h).deriv

@[simp]
theorem cont_diff_at_tan {n x} : ContDiffAt ℝ n tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuous_at_tan.1 h.ContinuousAt, fun h =>
    (Complex.cont_diff_at_tan.2 <| by
        exact_mod_cast h).real_of_complex⟩

theorem has_deriv_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π / 2) : ℝ) (π / 2)) : HasDerivAt tan (1 / cos x ^ 2) x :=
  has_deriv_at_tan (cos_pos_of_mem_Ioo h).ne'

theorem differentiable_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π / 2) : ℝ) (π / 2)) : DifferentiableAt ℝ tan x :=
  (has_deriv_at_tan_of_mem_Ioo h).DifferentiableAt

theorem has_strict_deriv_at_arctan (x : ℝ) : HasStrictDerivAt arctan (1 / (1 + x ^ 2)) x := by
  have A : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne'
  simpa [← cos_sq_arctan] using
    tan_local_homeomorph.has_strict_deriv_at_symm trivialₓ
      (by
        simpa)
      (has_strict_deriv_at_tan A)

theorem has_deriv_at_arctan (x : ℝ) : HasDerivAt arctan (1 / (1 + x ^ 2)) x :=
  (has_strict_deriv_at_arctan x).HasDerivAt

theorem differentiable_at_arctan (x : ℝ) : DifferentiableAt ℝ arctan x :=
  (has_deriv_at_arctan x).DifferentiableAt

theorem differentiable_arctan : Differentiable ℝ arctan :=
  differentiable_at_arctan

@[simp]
theorem deriv_arctan : deriv arctan = fun x => 1 / (1 + x ^ 2) :=
  funext fun x => (has_deriv_at_arctan x).deriv

theorem cont_diff_arctan {n : WithTop ℕ} : ContDiff ℝ n arctan :=
  cont_diff_iff_cont_diff_at.2 fun x =>
    have : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne'
    tanLocalHomeomorph.cont_diff_at_symm_deriv
      (by
        simpa)
      trivialₓ (has_deriv_at_tan this) (cont_diff_at_tan.2 this)

end Real

section

/-!
### Lemmas for derivatives of the composition of `real.arctan` with a differentiable function

In this section we register lemmas for the derivatives of the composition of `real.arctan` with a
differentiable function, for standalone use and use with `simp`. -/


open Real

section deriv

variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

theorem HasStrictDerivAt.arctan (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') x :=
  (Real.has_strict_deriv_at_arctan (f x)).comp x hf

theorem HasDerivAt.arctan (hf : HasDerivAt f f' x) : HasDerivAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') x :=
  (Real.has_deriv_at_arctan (f x)).comp x hf

theorem HasDerivWithinAt.arctan (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') s x :=
  (Real.has_deriv_at_arctan (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_arctan (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => arctan (f x)) s x = 1 / (1 + f x ^ 2) * derivWithin f s x :=
  hf.HasDerivWithinAt.arctan.derivWithin hxs

@[simp]
theorem deriv_arctan (hc : DifferentiableAt ℝ f x) : deriv (fun x => arctan (f x)) x = 1 / (1 + f x ^ 2) * deriv f x :=
  hc.HasDerivAt.arctan.deriv

end deriv

section fderiv

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E} {s : Set E} {n : WithTop ℕ}

theorem HasStrictFderivAt.arctan (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') x :=
  (has_strict_deriv_at_arctan (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.arctan (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') x :=
  (has_deriv_at_arctan (f x)).comp_has_fderiv_at x hf

theorem HasFderivWithinAt.arctan (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') s x :=
  (has_deriv_at_arctan (f x)).comp_has_fderiv_within_at x hf

theorem fderiv_within_arctan (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => arctan (f x)) s x = (1 / (1 + f x ^ 2)) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.arctan.fderivWithin hxs

@[simp]
theorem fderiv_arctan (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => arctan (f x)) x = (1 / (1 + f x ^ 2)) • fderiv ℝ f x :=
  hc.HasFderivAt.arctan.fderiv

theorem DifferentiableWithinAt.arctan (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.arctan (f x)) s x :=
  hf.HasFderivWithinAt.arctan.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.arctan (hc : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun x => arctan (f x)) x :=
  hc.HasFderivAt.arctan.DifferentiableAt

theorem DifferentiableOn.arctan (hc : DifferentiableOn ℝ f s) : DifferentiableOn ℝ (fun x => arctan (f x)) s :=
  fun x h => (hc x h).arctan

@[simp]
theorem Differentiable.arctan (hc : Differentiable ℝ f) : Differentiable ℝ fun x => arctan (f x) := fun x =>
  (hc x).arctan

theorem ContDiffAt.arctan (h : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => arctan (f x)) x :=
  cont_diff_arctan.ContDiffAt.comp x h

theorem ContDiff.arctan (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => arctan (f x) :=
  cont_diff_arctan.comp h

theorem ContDiffWithinAt.arctan (h : ContDiffWithinAt ℝ n f s x) : ContDiffWithinAt ℝ n (fun x => arctan (f x)) s x :=
  cont_diff_arctan.comp_cont_diff_within_at h

theorem ContDiffOn.arctan (h : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => arctan (f x)) s :=
  cont_diff_arctan.comp_cont_diff_on h

end fderiv

end

