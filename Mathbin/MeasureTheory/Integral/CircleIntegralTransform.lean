/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathbin.Analysis.Complex.CauchyIntegral
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.Calculus.ParametricIntervalIntegral
import Mathbin.Data.Complex.Basic
import Mathbin.MeasureTheory.Integral.CircleIntegral

/-!
# Circle integral transform

In this file we define the circle integral transform of a function `f` with complex domain. This is
defined as $(2πi)^{-1}\frac{f(x)}{x-w}$ where `x` moves along a circle. We then prove some basic
facts about these functions.

These results are useful for proving that the uniform limit of a sequence of holomorphic functions
is holomorphic.

-/


open Set MeasureTheory Metric Filter Function

open Interval Real

noncomputable section

variable {E : Type} [NormedGroup E] [NormedSpace ℂ E] (R : ℝ) (z w : ℂ)

namespace Complex

/-- Given a function `f : ℂ → E`, `circle_transform R z w f` is the functions mapping `θ` to
`(2 * ↑π * I)⁻¹ • deriv (circle_map z R) θ • ((circle_map z R θ) - w)⁻¹ • f (circle_map z R θ)`.

If `f` is differentiable and `w` is in the interior of the ball, then the integral from `0` to
`2 * π` of this gives the value `f(w)`. -/
def circleTransform (f : ℂ → E) (θ : ℝ) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • (circleMap z R θ - w)⁻¹ • f (circleMap z R θ)

/-- The derivative of `circle_transform` w.r.t `w`.-/
def circleTransformDeriv (f : ℂ → E) (θ : ℝ) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • ((circleMap z R θ - w) ^ 2)⁻¹ • f (circleMap z R θ)

theorem circle_transform_deriv_periodic (f : ℂ → E) : Periodic (circleTransformDeriv R z w f) (2 * π) := by
  have := periodic_circle_map
  simp_rw [periodic] at *
  intro x
  simp_rw [circle_transform_deriv, this]
  congr 2
  simp [← this]

theorem circle_transform_deriv_eq (f : ℂ → E) :
    circleTransformDeriv R z w f = fun θ => (circleMap z R θ - w)⁻¹ • circleTransform R z w f θ := by
  ext
  simp_rw [circle_transform_deriv, circle_transform, ← mul_smul, ← mul_assoc]
  ring_nf
  rw [inv_pow]
  congr
  ring

theorem integral_circle_transform [CompleteSpace E] (f : ℂ → E) :
    (∫ θ : ℝ in 0 ..2 * π, circleTransform R z w f θ) = (2 * ↑π * I)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z := by
  simp_rw [circle_transform, circleIntegral, deriv_circle_map, circleMap]
  simp

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
theorem continuous_circle_transform {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ} (hf : ContinuousOn f <| Sphere z R)
    (hw : w ∈ Ball z R) : Continuous (circleTransform R z w f) := by
  apply_rules [Continuous.smul, continuous_const]
  simp_rw [deriv_circle_map]
  apply_rules [Continuous.mul, continuous_circle_map 0 R, continuous_const]
  · apply continuous_circle_map_inv hw
    
  · apply ContinuousOn.comp_continuous hf (continuous_circle_map z R)
    exact fun _ => (circle_map_mem_sphere _ hR.le) _
    

theorem continuous_circle_transform_deriv {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ} (hf : ContinuousOn f (Sphere z R))
    (hw : w ∈ Ball z R) : Continuous (circleTransformDeriv R z w f) := by
  rw [circle_transform_deriv_eq]
  exact (continuous_circle_map_inv hw).smul (continuous_circle_transform hR hf hw)

/-- A useful bound for circle integrals (with complex codomain)-/
def circleTransformBoundingFunction (R : ℝ) (z : ℂ) (w : ℂ × ℝ) : ℂ :=
  circleTransformDeriv R z w.1 (fun x => 1) w.2

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
theorem continuous_on_prod_circle_transform_function {R r : ℝ} (hr : r < R) {z : ℂ} :
    ContinuousOn (fun w : ℂ × ℝ => (circleMap z R w.snd - w.fst)⁻¹ ^ 2) (ClosedBall z r ×ˢ (⊤ : Set ℝ)) := by
  simp_rw [← one_div]
  apply_rules [ContinuousOn.pow, ContinuousOn.div, continuous_on_const]
  refine'
    ((continuous_circle_map z R).ContinuousOn.comp continuous_on_snd fun _ => And.right).sub
      (continuous_on_id.comp continuous_on_fst fun _ => And.left)
  simp only [← mem_prod, ← Ne.def, ← and_imp, ← Prod.forall]
  intro a b ha hb
  have ha2 : a ∈ ball z R := by
    simp at *
    linarith
  exact sub_ne_zero.2 (circle_map_ne_mem_ball ha2 b)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
theorem continuous_on_abs_circle_transform_bounding_function {R r : ℝ} (hr : r < R) (z : ℂ) :
    ContinuousOn (abs ∘ fun t => circleTransformBoundingFunction R z t)
      (ClosedBall z r ×ˢ (⊤ : Set ℝ) : Set <| ℂ × ℝ) :=
  by
  have : ContinuousOn (circle_transform_bounding_function R z) (closed_ball z r ×ˢ (⊤ : Set ℝ)) := by
    apply_rules [ContinuousOn.smul, continuous_on_const]
    simp only [← deriv_circle_map]
    have c := (continuous_circle_map 0 R).ContinuousOn
    apply_rules [ContinuousOn.mul, c.comp continuous_on_snd fun _ => And.right, continuous_on_const]
    simp_rw [← inv_pow]
    apply continuous_on_prod_circle_transform_function hr
  refine' continuous_abs.continuous_on.comp this _
  show maps_to _ _ (⊤ : Set ℂ)
  simp [← maps_to]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem abs_circle_transform_bounding_function_le {R r : ℝ} (hr : r < R) (hr' : 0 ≤ r) (z : ℂ) :
    ∃ x :
      (ClosedBall z r ×ˢ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" : Set <| ℂ × ℝ),
      ∀ y :
        (ClosedBall z r ×ˢ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :
          Set <| ℂ × ℝ),
        abs (circleTransformBoundingFunction R z y) ≤ abs (circleTransformBoundingFunction R z x) :=
  by
  have cts := continuous_on_abs_circle_transform_bounding_function hr z
  have comp :
    IsCompact
      (closed_ball z r ×ˢ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :
        Set (ℂ × ℝ)) :=
    by
    apply_rules [IsCompact.prod, ProperSpace.is_compact_closed_ball z r, is_compact_interval]
  have none := (nonempty_closed_ball.2 hr').Prod nonempty_interval
  simpa using
    IsCompact.exists_forall_ge comp none
      (cts.mono
        (by
          intro z
          simp
          tauto))

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- The derivative of a `circle_transform` is locally bounded. -/
theorem circle_transform_deriv_bound {R : ℝ} (hR : 0 < R) {z x : ℂ} {f : ℂ → ℂ} (hx : x ∈ Ball z R)
    (hf : ContinuousOn f (Sphere z R)) :
    ∃ B ε : ℝ, 0 < ε ∧ Ball x ε ⊆ Ball z R ∧ ∀ (t : ℝ), ∀ y ∈ Ball x ε, ∀, ∥circleTransformDeriv R z y f t∥ ≤ B := by
  obtain ⟨r, hr, hrx⟩ := exists_lt_mem_ball_of_mem_ball hx
  obtain ⟨ε', hε', H⟩ := exists_ball_subset_ball hrx
  obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩⟩, hab⟩ := abs_circle_transform_bounding_function_le hr (pos_of_mem_ball hrx).le z
  let V : ℝ → ℂ → ℂ := fun θ w => circle_transform_deriv R z w (fun x => 1) θ
  have funccomp : ContinuousOn (fun r => abs (f r)) (sphere z R) := by
    have cabs : ContinuousOn abs ⊤ := by
      apply continuous_abs.continuous_on
    apply cabs.comp hf
    rw [maps_to]
    tauto
  have sbou := IsCompact.exists_forall_ge (is_compact_sphere z R) (NormedSpace.sphere_nonempty.2 hR.le) funccomp
  obtain ⟨X, HX, HX2⟩ := sbou
  refine' ⟨abs (V b a) * abs (f X), ε', hε', subset.trans H (ball_subset_ball hr.le), _⟩
  intro y v hv
  obtain ⟨y1, hy1, hfun⟩ := periodic.exists_mem_Ico₀ (circle_transform_deriv_periodic R z v f) Real.two_pi_pos y
  have hy2 : y1 ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" := by
    convert Ico_subset_Icc_self hy1
    simp [← interval_of_le real.two_pi_pos.le]
  have :=
    mul_le_mul (hab ⟨⟨v, y1⟩, ⟨ball_subset_closed_ball (H hv), hy2⟩⟩)
      (HX2 (circleMap z R y1) (circle_map_mem_sphere z hR.le y1)) (abs_nonneg _) (abs_nonneg _)
  simp_rw [hfun]
  simp only [← circle_transform_bounding_function, ← circle_transform_deriv, ← V, ← norm_eq_abs, ←
    Algebra.id.smul_eq_mul, ← deriv_circle_map, ← abs_mul, ← abs_circle_map_zero, ← abs_I, ← mul_oneₓ, mul_assoc, ←
    mul_inv_rev, ← inv_I, ← abs_neg, ← abs_inv, ← abs_of_real, ← one_mulₓ, ← abs_two, ← abs_pow, ← mem_ball, ←
    gt_iff_lt, ← Subtype.coe_mk, ← SetCoe.forall, ← mem_prod, ← mem_closed_ball, ← and_imp, ← Prod.forall, ←
    NormedSpace.sphere_nonempty, ← mem_sphere_iff_norm] at *
  exact this

end Complex

