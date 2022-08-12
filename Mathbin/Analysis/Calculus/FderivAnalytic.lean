/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Calculus.Deriv
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.Calculus.ContDiff

/-!
# Frechet derivatives of analytic functions.

A function expressible as a power series at a point has a Frechet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.
-/


open Filter Asymptotics

open Ennreal

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜]

variable {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F]

section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞}

variable {f : E → F} {x : E} {s : Set E}

theorem HasFpowerSeriesAt.has_strict_fderiv_at (h : HasFpowerSeriesAt f p x) :
    HasStrictFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x := by
  refine' h.is_O_image_sub_norm_mul_norm_sub.trans_is_o (is_o.of_norm_right _)
  refine' is_o_iff_exists_eq_mul.2 ⟨fun y => ∥y - (x, x)∥, _, eventually_eq.rfl⟩
  refine' (continuous_id.sub continuous_const).norm.tendsto' _ _ _
  rw [_root_.id, sub_self, norm_zero]

theorem HasFpowerSeriesAt.has_fderiv_at (h : HasFpowerSeriesAt f p x) :
    HasFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x :=
  h.HasStrictFderivAt.HasFderivAt

theorem HasFpowerSeriesAt.differentiable_at (h : HasFpowerSeriesAt f p x) : DifferentiableAt 𝕜 f x :=
  h.HasFderivAt.DifferentiableAt

theorem AnalyticAt.differentiable_at : AnalyticAt 𝕜 f x → DifferentiableAt 𝕜 f x
  | ⟨p, hp⟩ => hp.DifferentiableAt

theorem AnalyticAt.differentiable_within_at (h : AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x :=
  h.DifferentiableAt.DifferentiableWithinAt

theorem HasFpowerSeriesAt.fderiv_eq (h : HasFpowerSeriesAt f p x) :
    fderiv 𝕜 f x = continuousMultilinearCurryFin1 𝕜 E F (p 1) :=
  h.HasFderivAt.fderiv

theorem HasFpowerSeriesOnBall.differentiable_on [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) :
    DifferentiableOn 𝕜 f (Emetric.Ball x r) := fun y hy => (h.analytic_at_of_mem hy).DifferentiableWithinAt

theorem AnalyticOn.differentiable_on (h : AnalyticOn 𝕜 f s) : DifferentiableOn 𝕜 f s := fun y hy =>
  (h y hy).DifferentiableWithinAt

theorem HasFpowerSeriesOnBall.has_fderiv_at [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) {y : E}
    (hy : (∥y∥₊ : ℝ≥0∞) < r) : HasFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).HasFpowerSeriesAt.HasFderivAt

theorem HasFpowerSeriesOnBall.fderiv_eq [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) {y : E}
    (hy : (∥y∥₊ : ℝ≥0∞) < r) : fderiv 𝕜 f (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.HasFderivAt hy).fderiv

/-- If a function has a power series on a ball, then so does its derivative. -/
theorem HasFpowerSeriesOnBall.fderiv [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) :
    HasFpowerSeriesOnBall (fderiv 𝕜 f)
      ((continuousMultilinearCurryFin1 𝕜 E F : (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F).compFormalMultilinearSeries
        (p.changeOriginSeries 1))
      x r :=
  by
  suffices A :
    HasFpowerSeriesOnBall (fun z => continuousMultilinearCurryFin1 𝕜 E F (p.change_origin (z - x) 1))
      ((continuousMultilinearCurryFin1 𝕜 E F : (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F).compFormalMultilinearSeries
        (p.change_origin_series 1))
      x r
  · apply A.congr
    intro z hz
    dsimp'
    rw [← h.fderiv_eq, add_sub_cancel'_right]
    simpa only [← edist_eq_coe_nnnorm_sub, ← Emetric.mem_ball] using hz
    
  suffices B : HasFpowerSeriesOnBall (fun z => p.change_origin (z - x) 1) (p.change_origin_series 1) x r
  exact
    (continuousMultilinearCurryFin1 𝕜 E F).toContinuousLinearEquiv.toContinuousLinearMap.comp_has_fpower_series_on_ball
      B
  simpa using ((p.has_fpower_series_on_ball_change_origin 1 (h.r_pos.trans_le h.r_le)).mono h.r_pos h.r_le).comp_sub x

/-- If a function is analytic on a set `s`, so is its Fréchet derivative. -/
theorem AnalyticOn.fderiv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (fderiv 𝕜 f) s := by
  intro y hy
  rcases h y hy with ⟨p, r, hp⟩
  exact hp.fderiv.analytic_at

/-- If a function is analytic on a set `s`, so are its successive Fréchet derivative. -/
theorem AnalyticOn.iterated_fderiv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 (iteratedFderiv 𝕜 n f) s := by
  induction' n with n IH
  · rw [iterated_fderiv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E[×0]→L[𝕜] F).comp_analytic_on h
    
  · rw [iterated_fderiv_succ_eq_comp_left]
    apply
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun i : Finₓ (n + 1) => E)
              F).toContinuousLinearEquiv.toContinuousLinearMap.comp_analytic_on
    exact IH.fderiv
    

/-- An analytic function is infinitely differentiable. -/
theorem AnalyticOn.cont_diff_on [CompleteSpace F] (h : AnalyticOn 𝕜 f s) {n : WithTop ℕ} : ContDiffOn 𝕜 n f s := by
  let t := { x | AnalyticAt 𝕜 f x }
  suffices : ContDiffOn 𝕜 n f t
  exact this.mono h
  have H : AnalyticOn 𝕜 f t := fun x hx => hx
  have t_open : IsOpen t := is_open_analytic_at 𝕜 f
  apply cont_diff_on_of_continuous_on_differentiable_on
  · intro m hm
    apply (H.iterated_fderiv m).ContinuousOn.congr
    intro x hx
    exact iterated_fderiv_within_of_is_open _ t_open hx
    
  · intro m hm
    apply (H.iterated_fderiv m).DifferentiableOn.congr
    intro x hx
    exact iterated_fderiv_within_of_is_open _ t_open hx
    

end fderiv

section deriv

variable {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ℝ≥0∞}

variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

protected theorem HasFpowerSeriesAt.has_strict_deriv_at (h : HasFpowerSeriesAt f p x) :
    HasStrictDerivAt f (p 1 fun _ => 1) x :=
  h.HasStrictFderivAt.HasStrictDerivAt

protected theorem HasFpowerSeriesAt.has_deriv_at (h : HasFpowerSeriesAt f p x) : HasDerivAt f (p 1 fun _ => 1) x :=
  h.HasStrictDerivAt.HasDerivAt

protected theorem HasFpowerSeriesAt.deriv (h : HasFpowerSeriesAt f p x) : deriv f x = p 1 fun _ => 1 :=
  h.HasDerivAt.deriv

/-- If a function is analytic on a set `s`, so is its derivative. -/
theorem AnalyticOn.deriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_analytic_on h.fderiv

/-- If a function is analytic on a set `s`, so are its successive derivatives. -/
theorem AnalyticOn.iterated_deriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) (n : ℕ) : AnalyticOn 𝕜 ((deriv^[n]) f) s :=
  by
  induction' n with n IH
  · exact h
    
  · simpa only [← Function.iterate_succ', ← Function.comp_app] using IH.deriv
    

end deriv

