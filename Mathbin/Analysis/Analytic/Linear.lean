/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.Analytic.Basic

/-!
# Linear functions are analytic

In this file we prove that a `continuous_linear_map` defines an analytic function with
the formal power series `f x = f a + f (x - a)`.
-/


variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G]

open TopologicalSpace Classical BigOperators Nnreal Ennreal

open Set Filter Asymptotics

noncomputable section

namespace ContinuousLinearMap

/-- Formal power series of a continuous linear map `f : E →L[𝕜] F` at `x : E`:
`f y = f x + f (y - x)`. -/
@[simp]
def fpowerSeries (f : E →L[𝕜] F) (x : E) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.curry0 𝕜 _ (f x)
  | 1 => (continuousMultilinearCurryFin1 𝕜 E F).symm f
  | _ => 0

@[simp]
theorem fpower_series_apply_add_two (f : E →L[𝕜] F) (x : E) (n : ℕ) : f.fpowerSeries x (n + 2) = 0 :=
  rfl

@[simp]
theorem fpower_series_radius (f : E →L[𝕜] F) (x : E) : (f.fpowerSeries x).radius = ∞ :=
  ((f.fpowerSeries x).radius_eq_top_of_forall_image_add_eq_zero 2) fun n => rfl

protected theorem has_fpower_series_on_ball (f : E →L[𝕜] F) (x : E) : HasFpowerSeriesOnBall f (f.fpowerSeries x) x ∞ :=
  { r_le := by
      simp ,
    r_pos := Ennreal.coe_lt_top,
    HasSum := fun y _ =>
      (has_sum_nat_add_iff' 2).1 <| by
        simp [← Finset.sum_range_succ, sub_sub, ← has_sum_zero] }

protected theorem has_fpower_series_at (f : E →L[𝕜] F) (x : E) : HasFpowerSeriesAt f (f.fpowerSeries x) x :=
  ⟨∞, f.HasFpowerSeriesOnBall x⟩

protected theorem analytic_at (f : E →L[𝕜] F) (x : E) : AnalyticAt 𝕜 f x :=
  (f.HasFpowerSeriesAt x).AnalyticAt

/-- Reinterpret a bilinear map `f : E →L[𝕜] F →L[𝕜] G` as a multilinear map
`(E × F) [×2]→L[𝕜] G`. This multilinear map is the second term in the formal
multilinear series expansion of `uncurry f`. It is given by
`f.uncurry_bilinear ![(x, y), (x', y')] = f x y'`. -/
def uncurryBilinear (f : E →L[𝕜] F →L[𝕜] G) : E × F[×2]→L[𝕜] G :=
  @ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _ <|
    (↑(continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F →L[𝕜] G) →L[𝕜] _).comp <|
      f.bilinearComp (fst _ _ _) (snd _ _ _)

@[simp]
theorem uncurry_bilinear_apply (f : E →L[𝕜] F →L[𝕜] G) (m : Finₓ 2 → E × F) : f.uncurryBilinear m = f (m 0).1 (m 1).2 :=
  rfl

/-- Formal multilinear series expansion of a bilinear function `f : E →L[𝕜] F →L[𝕜] G`. -/
@[simp]
def fpowerSeriesBilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) : FormalMultilinearSeries 𝕜 (E × F) G
  | 0 => ContinuousMultilinearMap.curry0 𝕜 _ (f x.1 x.2)
  | 1 => (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x)
  | 2 => f.uncurryBilinear
  | _ => 0

@[simp]
theorem fpower_series_bilinear_radius (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) : (f.fpowerSeriesBilinear x).radius = ∞ :=
  ((f.fpowerSeriesBilinear x).radius_eq_top_of_forall_image_add_eq_zero 3) fun n => rfl

protected theorem has_fpower_series_on_ball_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFpowerSeriesOnBall (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x ∞ :=
  { r_le := by
      simp ,
    r_pos := Ennreal.coe_lt_top,
    HasSum := fun y _ =>
      (has_sum_nat_add_iff' 3).1 <| by
        simp only [← Finset.sum_range_succ, ← Finset.sum_range_one, ← Prod.fst_add, ← Prod.snd_add, ← f.map_add_add]
        dsimp'
        simp only [← add_commₓ, ← sub_self, ← has_sum_zero] }

protected theorem has_fpower_series_at_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFpowerSeriesAt (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x :=
  ⟨∞, f.has_fpower_series_on_ball_bilinear x⟩

protected theorem analytic_at_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    AnalyticAt 𝕜 (fun x : E × F => f x.1 x.2) x :=
  (f.has_fpower_series_at_bilinear x).AnalyticAt

end ContinuousLinearMap

