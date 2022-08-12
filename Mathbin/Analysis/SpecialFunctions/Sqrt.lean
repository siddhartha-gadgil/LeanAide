/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.Calculus.ContDiff

/-!
# Smoothness of `real.sqrt`

In this file we prove that `real.sqrt` is infinitely smooth at all points `x ≠ 0` and provide some
dot-notation lemmas.

## Tags

sqrt, differentiable
-/


open Set

open TopologicalSpace

namespace Real

/-- Local homeomorph between `(0, +∞)` and `(0, +∞)` with `to_fun = λ x, x ^ 2` and
`inv_fun = sqrt`. -/
noncomputable def sqLocalHomeomorph : LocalHomeomorph ℝ ℝ where
  toFun := fun x => x ^ 2
  invFun := sqrt
  Source := Ioi 0
  Target := Ioi 0
  map_source' := fun x hx => mem_Ioi.2 (pow_pos hx _)
  map_target' := fun x hx => mem_Ioi.2 (sqrt_pos.2 hx)
  left_inv' := fun x hx => sqrt_sq (le_of_ltₓ hx)
  right_inv' := fun x hx => sq_sqrt (le_of_ltₓ hx)
  open_source := is_open_Ioi
  open_target := is_open_Ioi
  continuous_to_fun := (continuous_pow 2).ContinuousOn
  continuous_inv_fun := continuous_on_id.sqrt

theorem deriv_sqrt_aux {x : ℝ} (hx : x ≠ 0) : HasStrictDerivAt sqrt (1 / (2 * sqrt x)) x ∧ ∀ n, ContDiffAt ℝ n sqrt x :=
  by
  cases' hx.lt_or_lt with hx hx
  · rw [sqrt_eq_zero_of_nonpos hx.le, mul_zero, div_zero]
    have : sqrt =ᶠ[𝓝 x] fun _ => 0 := (gt_mem_nhds hx).mono fun x hx => sqrt_eq_zero_of_nonpos hx.le
    exact
      ⟨(has_strict_deriv_at_const x (0 : ℝ)).congr_of_eventually_eq this.symm, fun n =>
        cont_diff_at_const.congr_of_eventually_eq this⟩
    
  · have : ↑2 * sqrt x ^ (2 - 1) ≠ 0 := by
      simp [← (sqrt_pos.2 hx).ne', ← @two_ne_zero ℝ]
    constructor
    · simpa using sq_local_homeomorph.has_strict_deriv_at_symm hx this (has_strict_deriv_at_pow 2 _)
      
    · exact fun n =>
        sq_local_homeomorph.cont_diff_at_symm_deriv this hx (has_deriv_at_pow 2 (sqrt x)) (cont_diff_at_id.pow 2)
      
    

theorem has_strict_deriv_at_sqrt {x : ℝ} (hx : x ≠ 0) : HasStrictDerivAt sqrt (1 / (2 * sqrt x)) x :=
  (deriv_sqrt_aux hx).1

theorem cont_diff_at_sqrt {x : ℝ} {n : WithTop ℕ} (hx : x ≠ 0) : ContDiffAt ℝ n sqrt x :=
  (deriv_sqrt_aux hx).2 n

theorem has_deriv_at_sqrt {x : ℝ} (hx : x ≠ 0) : HasDerivAt sqrt (1 / (2 * sqrt x)) x :=
  (has_strict_deriv_at_sqrt hx).HasDerivAt

end Real

open Real

section deriv

variable {f : ℝ → ℝ} {s : Set ℝ} {f' x : ℝ}

theorem HasDerivWithinAt.sqrt (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun y => sqrt (f y)) (f' / (2 * sqrt (f x))) s x := by
  simpa only [← (· ∘ ·), ← div_eq_inv_mul, ← mul_oneₓ] using (has_deriv_at_sqrt hx).comp_has_deriv_within_at x hf

theorem HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
    HasDerivAt (fun y => sqrt (f y)) (f' / (2 * sqrt (f x))) x := by
  simpa only [← (· ∘ ·), ← div_eq_inv_mul, ← mul_oneₓ] using (has_deriv_at_sqrt hx).comp x hf

theorem HasStrictDerivAt.sqrt (hf : HasStrictDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictDerivAt (fun t => sqrt (f t)) (f' / (2 * sqrt (f x))) x := by
  simpa only [← (· ∘ ·), ← div_eq_inv_mul, ← mul_oneₓ] using (has_strict_deriv_at_sqrt hx).comp x hf

theorem deriv_within_sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => sqrt (f x)) s x = derivWithin f s x / (2 * sqrt (f x)) :=
  (hf.HasDerivWithinAt.sqrt hx).derivWithin hxs

@[simp]
theorem deriv_sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    deriv (fun x => sqrt (f x)) x = deriv f x / (2 * sqrt (f x)) :=
  (hf.HasDerivAt.sqrt hx).deriv

end deriv

section fderiv

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {f : E → ℝ} {n : WithTop ℕ} {s : Set E} {x : E} {f' : E →L[ℝ] ℝ}

theorem HasFderivAt.sqrt (hf : HasFderivAt f f' x) (hx : f x ≠ 0) :
    HasFderivAt (fun y => sqrt (f y)) ((1 / (2 * sqrt (f x))) • f') x :=
  (has_deriv_at_sqrt hx).comp_has_fderiv_at x hf

theorem HasStrictFderivAt.sqrt (hf : HasStrictFderivAt f f' x) (hx : f x ≠ 0) :
    HasStrictFderivAt (fun y => sqrt (f y)) ((1 / (2 * sqrt (f x))) • f') x :=
  (has_strict_deriv_at_sqrt hx).comp_has_strict_fderiv_at x hf

theorem HasFderivWithinAt.sqrt (hf : HasFderivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasFderivWithinAt (fun y => sqrt (f y)) ((1 / (2 * sqrt (f x))) • f') s x :=
  (has_deriv_at_sqrt hx).comp_has_fderiv_within_at x hf

theorem DifferentiableWithinAt.sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun y => sqrt (f y)) s x :=
  (hf.HasFderivWithinAt.sqrt hx).DifferentiableWithinAt

theorem DifferentiableAt.sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    DifferentiableAt ℝ (fun y => sqrt (f y)) x :=
  (hf.HasFderivAt.sqrt hx).DifferentiableAt

theorem DifferentiableOn.sqrt (hf : DifferentiableOn ℝ f s) (hs : ∀, ∀ x ∈ s, ∀, f x ≠ 0) :
    DifferentiableOn ℝ (fun y => sqrt (f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)

theorem Differentiable.sqrt (hf : Differentiable ℝ f) (hs : ∀ x, f x ≠ 0) : Differentiable ℝ fun y => sqrt (f y) :=
  fun x => (hf x).sqrt (hs x)

theorem fderiv_within_sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => sqrt (f x)) s x = (1 / (2 * sqrt (f x))) • fderivWithin ℝ f s x :=
  (hf.HasFderivWithinAt.sqrt hx).fderivWithin hxs

@[simp]
theorem fderiv_sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    fderiv ℝ (fun x => sqrt (f x)) x = (1 / (2 * sqrt (f x))) • fderiv ℝ f x :=
  (hf.HasFderivAt.sqrt hx).fderiv

theorem ContDiffAt.sqrt (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0) : ContDiffAt ℝ n (fun y => sqrt (f y)) x :=
  (cont_diff_at_sqrt hx).comp x hf

theorem ContDiffWithinAt.sqrt (hf : ContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y => sqrt (f y)) s x :=
  (cont_diff_at_sqrt hx).comp_cont_diff_within_at x hf

theorem ContDiffOn.sqrt (hf : ContDiffOn ℝ n f s) (hs : ∀, ∀ x ∈ s, ∀, f x ≠ 0) :
    ContDiffOn ℝ n (fun y => sqrt (f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)

theorem ContDiff.sqrt (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => sqrt (f y) :=
  cont_diff_iff_cont_diff_at.2 fun x => hf.ContDiffAt.sqrt (h x)

end fderiv

