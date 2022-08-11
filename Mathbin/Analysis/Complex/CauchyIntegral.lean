/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.MeasureTheory.Measure.ComplexLebesgue
import Mathbin.MeasureTheory.Integral.DivergenceTheorem
import Mathbin.MeasureTheory.Integral.CircleIntegral
import Mathbin.Analysis.Calculus.Dslope
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.Complex.ReImTopology
import Mathbin.Analysis.Calculus.DiffOnIntCont
import Mathbin.Data.Real.Cardinality

/-!
# Cauchy integral formula

In this file we prove the Cauchy-Goursat theorem and the Cauchy integral formula for integrals over
circles. Most results are formulated for a function `f : ℂ → E` that takes values in a complex
Banach space with second countable topology.

## Main statements

In the following theorems, if the name ends with `off_countable`, then the actual theorem assumes
differentiability at all but countably many points of the set mentioned below.

* `complex.integral_boundary_rect_of_has_fderiv_within_at_real_off_countable`: If a function
  `f : ℂ → E` is continuous on a closed rectangle and *real* differentiable on its interior, then
  its integral over the boundary of this rectangle is equal to the integral of
  `I • f' (x + y * I) 1 - f' (x + y * I) I` over the rectangle, where `f' z w : E` is the derivative
  of `f` at `z` in the direction `w` and `I = complex.I` is the imaginary unit.

* `complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`: If a function
  `f : ℂ → E` is continuous on a closed rectangle and is *complex* differentiable on its interior,
  then its integral over the boundary of this rectangle is equal to zero.

* `complex.circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`: If a
  function `f : ℂ → E` is continuous on a closed annulus `{z | r ≤ |z - c| ≤ R}` and is complex
  differentiable on its interior `{z | r < |z - c| < R}`, then the integrals of `(z - c)⁻¹ • f z`
  over the outer boundary and over the inner boundary are equal.

* `complex.circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto`,
  `complex.circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable`:
  If a function `f : ℂ → E` is continuous on a punctured closed disc `{z | |z - c| ≤ R ∧ z ≠ c}`, is
  complex differentiable on the corresponding punctured open disc, and tends to `y` as `z → c`,
  `z ≠ c`, then the integral of `(z - c)⁻¹ • f z` over the circle `|z - c| = R` is equal to
  `2πiy`. In particular, if `f` is continuous on the whole closed disc and is complex differentiable
  on the corresponding open disc, then this integral is equal to `2πif(c)`.

* `complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable`,
  `complex.two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable`
  **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
  complex differentiable on the corresponding open disc, then for any `w` in the corresponding open
  disc the integral of `(z - w)⁻¹ • f z` over the boundary of the disc is equal to `2πif(w)`.
  Two versions of the lemma put the multiplier `2πi` at the different sides of the equality.

* `complex.has_fpower_series_on_ball_of_differentiable_off_countable`: If `f : ℂ → E` is continuous
  on a closed disc of positive radius and is complex differentiable on the corresponding open disc,
  then it is analytic on the corresponding open disc, and the coefficients of the power series are
  given by Cauchy integral formulas.

* `differentiable_on.has_fpower_series_on_ball`: If `f : ℂ → E` is complex differentiable on a
  closed disc of positive radius, then it is analytic on the corresponding open disc, and the
  coefficients of the power series are given by Cauchy integral formulas.

* `differentiable_on.analytic_at`, `differentiable.analytic_at`: If `f : ℂ → E` is differentiable
  on a neighborhood of a point, then it is analytic at this point. In particular, if `f : ℂ → E`
  is differentiable on the whole `ℂ`, then it is analytic at every point `z : ℂ`.

* `differentiable.has_power_series_on_ball`: If `f : ℂ → E` is differentiable everywhere then the
  `cauchy_power_series f z R` is a formal power series representing `f` at `z` with infinite
  radius of convergence (this holds for any choice of `0 < R`).

## Implementation details

The proof of the Cauchy integral formula in this file is based on a very general version of the
divergence theorem, see `measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable`
(a version for functions defined on `fin (n + 1) → ℝ`),
`measure_theory.integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le`, and
`measure_theory.integral2_divergence_prod_of_has_fderiv_within_at_off_countable` (versions for
functions defined on `ℝ × ℝ`).

Usually, the divergence theorem is formulated for a $C^1$ smooth function. The theorems formulated
above deal with a function that is

* continuous on a closed box/rectangle;
* differentiable at all but countably many points of its interior;
* have divergence integrable over the closed box/rectangle.

First, we reformulate the theorem for a *real*-differentiable map `ℂ → E`, and relate the integral
of `f` over the boundary of a rectangle in `ℂ` to the integral of the derivative
$\frac{\partial f}{\partial \bar z}$ over the interior of this box. In particular, for a *complex*
differentiable function, the latter derivative is zero, hence the integral over the boundary of a
rectangle is zero. Thus we get the Cauchy-Goursat theorem for a rectangle in `ℂ`.

Next, we apply the this theorem to the function $F(z)=f(c+e^{z})$ on the rectangle
$[\ln r, \ln R]\times [0, 2\pi]$ to prove that
$$
  \oint_{|z-c|=r}\frac{f(z)\,dz}{z-c}=\oint_{|z-c|=R}\frac{f(z)\,dz}{z-c}
$$
provided that `f` is continuous on the closed annulus `r ≤ |z - c| ≤ R` and is complex
differentiable on its interior `r < |z - c| < R` (possibly, at all but countably many points).

Here and below, we write $\frac{f(z)}{z-c}$ in the documentation while the actual lemmas use
`(z - c)⁻¹ • f z` because `f z` belongs to some Banach space over `ℂ` and `f z / (z - c)` is
undefined.

Taking the limit of this equality as `r` tends to `𝓝[>] 0`, we prove
$$
  \oint_{|z-c|=R}\frac{f(z)\,dz}{z-c}=2\pi if(c)
$$
provided that `f` is continuous on the closed disc `|z - c| ≤ R` and is differentiable at all but
countably many points of its interior. This is the Cauchy integral formula for the center of a
circle. In particular, if we apply this function to `F z = (z - c) • f z`, then we get
$$
  \oint_{|z-c|=R} f(z)\,dz=0.
$$

In order to deduce the Cauchy integral formula for any point `w`, `|w - c| < R`, we consider the
slope function `g : ℂ → E` given by `g z = (z - w)⁻¹ • (f z - f w)` if `z ≠ w` and `g w = f' w`.
This function satisfies assumptions of the previous theorem, so we have
$$
  \oint_{|z-c|=R} \frac{f(z)\,dz}{z-w}=\oint_{|z-c|=R} \frac{f(w)\,dz}{z-w}=
  \left(\oint_{|z-c|=R} \frac{dz}{z-w}\right)f(w).
$$
The latter integral was computed in `circle_integral.integral_sub_inv_of_mem_ball` and is equal to
`2 * π * complex.I`.

There is one more step in the actual proof. Since we allow `f` to be non-differentiable on a
countable set `s`, we cannot immediately claim that `g` is continuous at `w` if `w ∈ s`. So, we use
the proof outlined in the previous paragraph for `w ∉ s` (see
`complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux`), then use continuity
of both sides of the formula and density of `sᶜ` to prove the formula for all points of the open
ball, see `complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable`.

Finally, we use the properties of the Cauchy integrals established elsewhere (see
`has_fpower_series_on_cauchy_integral`) and Cauchy integral formula to prove that the original
function is analytic on the open ball.

## Tags

Cauchy-Goursat theorem, Cauchy integral formula
-/


open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function

open Interval Real Nnreal Ennreal TopologicalSpace BigOperators

noncomputable section

universe u

variable {E : Type u} [NormedGroup E] [NormedSpace ℂ E] [CompleteSpace E]

namespace Complex

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opposite corners at
`z w : ℂ`, is *real* differentiable at all but countably many points of the corresponding open
rectangle, and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the
integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
theorem integral_boundary_rect_of_has_fderiv_at_real_off_countable (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E) (z w : ℂ)
    (s : Set ℂ) (hs : s.Countable)
    (Hc :
      ContinuousOn f
        ("./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
          "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"))
    (Hd :
      ∀,
        ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s, ∀, HasFderivAt f (f' x) x)
    (Hi :
      IntegrableOn (fun z => I • f' z 1 - f' z i)
        ("./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
          "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")) :
    ((((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - ∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
          I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
        I • ∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) i :=
  by
  set e : (ℝ × ℝ) ≃L[ℝ] ℂ := equiv_real_prodₗ.symm
  have he : ∀ x y : ℝ, ↑x + ↑y * I = e (x, y) := fun x y => (mk_eq_add_mul_I x y).symm
  have he₁ : e (1, 0) = 1 := rfl
  have he₂ : e (0, 1) = I := rfl
  simp only [← he] at *
  set F : ℝ × ℝ → E := f ∘ e
  set F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E := fun p => (f' (e p)).comp (e : ℝ × ℝ →L[ℝ] ℂ)
  have hF' : ∀ p : ℝ × ℝ, (-(I • F' p)) (1, 0) + F' p (0, 1) = -(I • f' (e p) 1 - f' (e p) I) := by
    rintro ⟨x, y⟩
    simp [← F', ← he₁, ← he₂, sub_eq_neg_add]
  set R : Set (ℝ × ℝ) :=
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ˢ
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"
  set t : Set (ℝ × ℝ) := e ⁻¹' s
  rw [interval_swap z.im] at Hc Hi
  rw [min_commₓ z.im, max_commₓ z.im] at Hd
  have hR :
    e ⁻¹'
        ("./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
          "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") =
      R :=
    rfl
  have htc : ContinuousOn F R := Hc.comp e.continuous_on hR.ge
  have htd :
    ∀,
      ∀ p ∈ Ioo (min z.re w.re) (max z.re w.re) ×ˢ Ioo (min w.im z.im) (max w.im z.im) \ t, ∀, HasFderivAt F (F' p) p :=
    fun p hp => (Hd (e p) hp).comp p e.has_fderiv_at
  simp_rw [← intervalIntegral.integral_smul, intervalIntegral.integral_symm w.im z.im, ← intervalIntegral.integral_neg,
    ← hF']
  refine'
    (integral2_divergence_prod_of_has_fderiv_within_at_off_countable (fun p => -(I • F p)) F (fun p => -(I • F' p)) F'
        z.re w.im w.re z.im t (hs.preimage e.injective) (htc.const_smul _).neg htc
        (fun p hp => ((htd p hp).const_smul I).neg) htd _).symm
  rw [←
    (volume_preserving_equiv_real_prod.symm _).integrable_on_comp_preimage (MeasurableEquiv.measurable_embedding _)] at
    Hi
  simpa only [← hF'] using Hi.neg

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opposite corners at
`z w : ℂ`, is *real* differentiable on the corresponding open rectangle, and
$\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the integral of `f` over
the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
theorem integral_boundary_rect_of_continuous_on_of_has_fderiv_at_real (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E) (z w : ℂ)
    (Hc :
      ContinuousOn f
        ("./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
          "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"))
    (Hd :
      ∀, ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im), ∀, HasFderivAt f (f' x) x)
    (Hi :
      IntegrableOn (fun z => I • f' z 1 - f' z i)
        ("./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
          "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")) :
    ((((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - ∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
          I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
        I • ∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) i :=
  integral_boundary_rect_of_has_fderiv_at_real_off_countable f f' z w ∅ countable_empty Hc (fun x hx => Hd x hx.1) Hi

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- Suppose that a function `f : ℂ → E` is *real* differentiable on a closed rectangle with opposite
corners at `z w : ℂ` and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then
the integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
theorem integral_boundary_rect_of_differentiable_on_real (f : ℂ → E) (z w : ℂ)
    (Hd :
      DifferentiableOn ℝ f
        ("./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
          "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"))
    (Hi :
      IntegrableOn (fun z => I • fderiv ℝ f z 1 - fderiv ℝ f z i)
        ("./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
          "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")) :
    ((((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - ∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
          I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
        I • ∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • fderiv ℝ f (x + y * I) 1 - fderiv ℝ f (x + y * I) i :=
  integral_boundary_rect_of_has_fderiv_at_real_off_countable f (fderiv ℝ f) z w ∅ countable_empty Hd.ContinuousOn
    (fun x hx =>
      Hd.HasFderivAt <| by
        simpa only [mem_interior_iff_mem_nhds, ← interior_re_prod_im, ← interval, ← interior_Icc] using hx.1)
    Hi

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- **Cauchy-Goursat theorem** for a rectangle: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is continuous on a closed
rectangle and is complex differentiable at all but countably many points of the corresponding open
rectangle, then its integral over the boundary of the rectangle equals zero. -/
theorem integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : ℂ → E) (z w : ℂ) (s : Set ℂ)
    (hs : s.Countable)
    (Hc :
      ContinuousOn f
        ("./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
          "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"))
    (Hd :
      ∀,
        ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
          ∀, DifferentiableAt ℂ f x) :
    ((((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - ∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
          I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
        I • ∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      0 :=
  by
  refine'
      (integral_boundary_rect_of_has_fderiv_at_real_off_countable f (fun z => (fderiv ℂ f z).restrictScalars ℝ) z w s hs
            Hc (fun x hx => (Hd x hx).HasFderivAt.restrictScalars ℝ) _).trans
        _ <;>
    simp [ContinuousLinearMap.map_smul]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- **Cauchy-Goursat theorem for a rectangle**: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is continuous on a closed
rectangle and is complex differentiable on the corresponding open rectangle, then its integral over
the boundary of the rectangle equals zero. -/
theorem integral_boundary_rect_eq_zero_of_continuous_on_of_differentiable_on (f : ℂ → E) (z w : ℂ)
    (Hc :
      ContinuousOn f
        ("./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
          "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"))
    (Hd : DifferentiableOn ℂ f (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im))) :
    ((((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - ∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
          I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
        I • ∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      0 :=
  (integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ countable_empty Hc) fun x hx =>
    Hd.DifferentiableAt <| (is_open_Ioo.ReProdIm is_open_Ioo).mem_nhds hx.1

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- **Cauchy-Goursat theorem** for a rectangle: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is complex differentiable on a
closed rectangle, then its integral over the boundary of the rectangle equals zero. -/
theorem integral_boundary_rect_eq_zero_of_differentiable_on (f : ℂ → E) (z w : ℂ)
    (H :
      DifferentiableOn ℂ f
        ("./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
          "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")) :
    ((((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - ∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
          I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
        I • ∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      0 :=
  integral_boundary_rect_eq_zero_of_continuous_on_of_differentiable_on f z w H.ContinuousOn <|
    H.mono <| inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- If `f : ℂ → E` is continuous the closed annulus `r ≤ ∥z - c∥ ≤ R`, `0 < r ≤ R`, and is complex
differentiable at all but countably many points of its interior, then the integrals of
`f z / (z - c)` (formally, `(z - c)⁻¹ • f z`) over the circles `∥z - c∥ = r` and `∥z - c∥ = R` are
equal to each other. -/
theorem circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable {c : ℂ} {r R : ℝ} (h0 : 0 < r)
    (hle : r ≤ R) {f : ℂ → E} {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (ClosedBall c R \ Ball c r))
    (hd : ∀, ∀ z ∈ (Ball c R \ ClosedBall c r) \ s, ∀, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = ∮ z in C(c, r), (z - c)⁻¹ • f z := by
  /- We apply the previous lemma to `λ z, f (c + exp z)` on the rectangle
    `[log r, log R] × [0, 2 * π]`. -/
  set A := closed_ball c R \ ball c r
  obtain ⟨a, rfl⟩ : ∃ a, Real.exp a = r
  exact ⟨Real.log r, Real.exp_log h0⟩
  obtain ⟨b, rfl⟩ : ∃ b, Real.exp b = R
  exact ⟨Real.log R, Real.exp_log (h0.trans_le hle)⟩
  rw [Real.exp_le_exp] at hle
  -- Unfold definition of `circle_integral` and cancel some terms.
  suffices (∫ θ in 0 ..2 * π, I • f (circleMap c (Real.exp b) θ)) = ∫ θ in 0 ..2 * π, I • f (circleMap c (Real.exp a) θ)
    by
    simpa only [← circleIntegral, ← add_sub_cancel', ← of_real_exp, exp_add, ← smul_smul, div_eq_mul_inv, ←
      mul_div_cancel_left _ (circle_map_ne_center (Real.exp_pos _).ne'), ← circle_map_sub_center, ← deriv_circle_map]
  set R :=
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ×ℂ
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"
  set g : ℂ → ℂ := (· + ·) c ∘ exp
  have hdg : Differentiable ℂ g := differentiable_exp.const_add _
  replace hs : (g ⁻¹' s).Countable := (hs.preimage (add_right_injective c)).preimage_cexp
  have h_maps : maps_to g R A := by
    rintro z ⟨h, -⟩
    simpa [← dist_eq, ← g, ← abs_exp, ← hle] using h.symm
  replace hc : ContinuousOn (f ∘ g) R
  exact hc.comp hdg.continuous.continuous_on h_maps
  replace hd :
    ∀, ∀ z ∈ Ioo (min a b) (max a b) ×ℂ Ioo (min 0 (2 * π)) (max 0 (2 * π)) \ g ⁻¹' s, ∀, DifferentiableAt ℂ (f ∘ g) z
  · refine' fun z hz => (hd (g z) ⟨_, hz.2⟩).comp z (hdg _)
    simpa [← g, ← dist_eq, ← abs_exp, ← hle, ← And.comm] using hz.1.1
    
  simpa [← g, ← circleMap, ← exp_periodic _, ← sub_eq_zero, exp_add] using
    integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ ⟨a, 0⟩ ⟨b, 2 * π⟩ _ hs hc hd

/-- **Cauchy-Goursat theorem** for an annulus. If `f : ℂ → E` is continuous on the closed annulus
`r ≤ ∥z - c∥ ≤ R`, `0 < r ≤ R`, and is complex differentiable at all but countably many points of
its interior, then the integrals of `f` over the circles `∥z - c∥ = r` and `∥z - c∥ = R` are equal
to each other. -/
theorem circle_integral_eq_of_differentiable_on_annulus_off_countable {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R)
    {f : ℂ → E} {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (ClosedBall c R \ Ball c r))
    (hd : ∀, ∀ z ∈ (Ball c R \ ClosedBall c r) \ s, ∀, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, r), f z :=
  calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _).symm
    _ = ∮ z in C(c, r), (z - c)⁻¹ • (z - c) • f z :=
      circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable h0 hle hs
        ((continuous_on_id.sub continuous_on_const).smul hc) fun z hz =>
        (differentiable_at_id.sub_const _).smul (hd z hz)
    _ = ∮ z in C(c, r), f z := circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _
    

/-- **Cauchy integral formula** for the value at the center of a disc. If `f` is continuous on a
punctured closed disc of radius `R`, is differentiable at all but countably many points of the
interior of this disc, and has a limit `y` at the center of the disc, then the integral
$\oint_{∥z-c∥=R} \frac{f(z)}{z-c}\,dz$ is equal to $2πiy`. -/
theorem circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto {c : ℂ} {R : ℝ} (h0 : 0 < R)
    {f : ℂ → E} {y : E} {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (ClosedBall c R \ {c}))
    (hd : ∀, ∀ z ∈ (Ball c R \ {c}) \ s, ∀, DifferentiableAt ℂ f z) (hy : Tendsto f (𝓝[{c}ᶜ] c) (𝓝 y)) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I : ℂ) • y := by
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine' le_of_forall_le_of_dense fun ε ε0 => _
  obtain ⟨δ, δ0, hδ⟩ : ∃ δ > (0 : ℝ), ∀, ∀ z ∈ closed_ball c δ \ {c}, ∀, dist (f z) y < ε / (2 * π)
  exact
    ((nhds_within_has_basis nhds_basis_closed_ball _).tendsto_iff nhds_basis_ball).1 hy _ (div_pos ε0 Real.two_pi_pos)
  obtain ⟨r, hr0, hrδ, hrR⟩ : ∃ r, 0 < r ∧ r ≤ δ ∧ r ≤ R :=
    ⟨min δ R, lt_minₓ δ0 h0, min_le_leftₓ _ _, min_le_rightₓ _ _⟩
  have hsub : closed_ball c R \ ball c r ⊆ closed_ball c R \ {c} :=
    diff_subset_diff_right (singleton_subset_iff.2 <| mem_ball_self hr0)
  have hsub' : ball c R \ closed_ball c r ⊆ ball c R \ {c} :=
    diff_subset_diff_right (singleton_subset_iff.2 <| mem_closed_ball_self hr0.le)
  have hzne : ∀, ∀ z ∈ sphere c r, ∀, z ≠ c := fun z hz =>
    ne_of_mem_of_not_mem hz fun h => hr0.ne' <| dist_self c ▸ Eq.symm h
  /- The integral `∮ z in C(c, r), f z / (z - c)` does not depend on `0 < r ≤ R` and tends to
    `2πIy` as `r → 0`. -/
  calc
    ∥(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * ↑π * I) • y∥ =
        ∥(∮ z in C(c, r), (z - c)⁻¹ • f z) - ∮ z in C(c, r), (z - c)⁻¹ • y∥ :=
      by
      congr 2
      · exact
          circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable hr0 hrR hs (hc.mono hsub)
            fun z hz => hd z ⟨hsub' hz.1, hz.2⟩
        
      · simp [← hr0.ne']
        _ = ∥∮ z in C(c, r), (z - c)⁻¹ • (f z - y)∥ :=
      by
      simp only [← smul_sub]
      have hc' : ContinuousOn (fun z => (z - c)⁻¹) (sphere c r) :=
        (continuous_on_id.sub continuous_on_const).inv₀ fun z hz => sub_ne_zero.2 <| hzne _ hz
      rw [circleIntegral.integral_sub] <;> refine' (hc'.smul _).CircleIntegrable hr0.le
      · exact hc.mono (subset_inter (sphere_subset_closed_ball.trans <| closed_ball_subset_closed_ball hrR) hzne)
        
      · exact continuous_on_const
        _ ≤ 2 * π * r * (r⁻¹ * (ε / (2 * π))) :=
      by
      refine' circleIntegral.norm_integral_le_of_norm_le_const hr0.le fun z hz => _
      specialize hzne z hz
      rw [mem_sphere, dist_eq_norm] at hz
      rw [norm_smul, norm_inv, hz, ← dist_eq_norm]
      refine' mul_le_mul_of_nonneg_left (hδ _ ⟨_, hzne⟩).le (inv_nonneg.2 hr0.le)
      rwa [mem_closed_ball_iff_norm, hz]_ = ε := by
      field_simp [← hr0.ne', ← real.two_pi_pos.ne']
      ac_rfl

/-- **Cauchy integral formula** for the value at the center of a disc. If `f : ℂ → E` is continuous
on a closed disc of radius `R` and is complex differentiable at all but countably many points of its
interior, then the integral $\oint_{|z-c|=R} \frac{f(z)}{z-c}\,dz$ is equal to $2πiy`. -/
theorem circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 < R) {f : ℂ → E} {c : ℂ}
    {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (ClosedBall c R))
    (hd : ∀, ∀ z ∈ Ball c R \ s, ∀, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I : ℂ) • f c :=
  circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto h0 hs (hc.mono <| diff_subset _ _)
    (fun z hz => hd z ⟨hz.1.1, hz.2⟩) (hc.ContinuousAt <| closed_ball_mem_nhds _ h0).ContinuousWithinAt

/-- **Cauchy-Goursat theorem** for a disk: if `f : ℂ → E` is continuous on a closed disk
`{z | ∥z - c∥ ≤ R}` and is complex differentiable at all but countably many points of its interior,
then the integral $\oint_{|z-c|=R}f(z)\,dz$ equals zero. -/
theorem circle_integral_eq_zero_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E} {c : ℂ} {s : Set ℂ}
    (hs : s.Countable) (hc : ContinuousOn f (ClosedBall c R)) (hd : ∀, ∀ z ∈ Ball c R \ s, ∀, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z) = 0 := by
  rcases h0.eq_or_lt with (rfl | h0)
  · apply circleIntegral.integral_radius_zero
    
  calc (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _).symm _ = (2 * ↑π * I : ℂ) • (c - c) • f c :=
      circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable h0 hs
        ((continuous_on_id.sub continuous_on_const).smul hc) fun z hz =>
        (differentiable_at_id.sub_const _).smul (hd z hz)_ = 0 :=
      by
      rw [sub_self, zero_smul, smul_zero]

/-- An auxiliary lemma for
`complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable`. This lemma assumes
`w ∉ s` while the main lemma drops this assumption. -/
theorem circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux {R : ℝ} {c w : ℂ} {f : ℂ → E} {s : Set ℂ}
    (hs : s.Countable) (hw : w ∈ Ball c R \ s) (hc : ContinuousOn f (ClosedBall c R))
    (hd : ∀, ∀ x ∈ Ball c R \ s, ∀, DifferentiableAt ℂ f x) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w := by
  have hR : 0 < R := dist_nonneg.trans_lt hw.1
  set F : ℂ → E := dslope f w
  have hws : (insert w s).Countable := hs.insert w
  have hnhds : closed_ball c R ∈ 𝓝 w := closed_ball_mem_nhds_of_mem hw.1
  have hcF : ContinuousOn F (closed_ball c R) :=
    (continuous_on_dslope <| closed_ball_mem_nhds_of_mem hw.1).2 ⟨hc, hd _ hw⟩
  have hdF : ∀, ∀ z ∈ ball (c : ℂ) R \ insert w s, ∀, DifferentiableAt ℂ F z := fun z hz =>
    (differentiable_at_dslope_of_ne (ne_of_mem_of_not_mem (mem_insert _ _) hz.2).symm).2
      (hd _ (diff_subset_diff_right (subset_insert _ _) hz))
  have HI := circle_integral_eq_zero_of_differentiable_on_off_countable hR.le hws hcF hdF
  have hne : ∀, ∀ z ∈ sphere c R, ∀, z ≠ w := fun z hz => ne_of_mem_of_not_mem hz (ne_of_ltₓ hw.1)
  have hFeq : eq_on F (fun z => (z - w)⁻¹ • f z - (z - w)⁻¹ • f w) (sphere c R) := by
    intro z hz
    calc F z = (z - w)⁻¹ • (f z - f w) := update_noteq (hne z hz) _ _ _ = (z - w)⁻¹ • f z - (z - w)⁻¹ • f w :=
        smul_sub _ _ _
  have hc' : ContinuousOn (fun z => (z - w)⁻¹) (sphere c R) :=
    (continuous_on_id.sub continuous_on_const).inv₀ fun z hz => sub_ne_zero.2 <| hne z hz
  rw [← circleIntegral.integral_sub_inv_of_mem_ball hw.1, ← circleIntegral.integral_smul_const, ← sub_eq_zero, ←
    circleIntegral.integral_sub, ← circleIntegral.integral_congr hR.le hFeq, HI]
  exacts[(hc'.smul (hc.mono sphere_subset_closed_ball)).CircleIntegrable hR.le,
    (hc'.smul continuous_on_const).CircleIntegrable hR.le]

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\frac{1}{2πi}\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=f(w)$.
-/
theorem two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {f : ℂ → E}
    {s : Set ℂ} (hs : s.Countable) (hw : w ∈ Ball c R) (hc : ContinuousOn f (ClosedBall c R))
    (hd : ∀, ∀ x ∈ Ball c R \ s, ∀, DifferentiableAt ℂ f x) :
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) = f w := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices w ∈ Closure (ball c R \ s) by
    lift R to ℝ≥0 using hR.le
    have A : ContinuousAt (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w := by
      have :=
        has_fpower_series_on_cauchy_integral ((hc.mono sphere_subset_closed_ball).CircleIntegrable R.coe_nonneg) hR
      refine' this.continuous_on.continuous_at (emetric.is_open_ball.mem_nhds _)
      rwa [Metric.emetric_ball_nnreal]
    have B : ContinuousAt f w := hc.continuous_at (closed_ball_mem_nhds_of_mem hw)
    refine' tendsto_nhds_unique_of_frequently_eq A B ((mem_closure_iff_frequently.1 this).mono _)
    intro z hz
    rw [circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux hs hz hc hd, inv_smul_smul₀]
    simp [← Real.pi_ne_zero, ← I_ne_zero]
  refine' mem_closure_iff_nhds.2 fun t ht => _
  -- TODO: generalize to any vector space over `ℝ`
  set g : ℝ → ℂ := fun x => w + x
  have : tendsto g (𝓝 0) (𝓝 w) := (continuous_const.add continuous_of_real).tendsto' 0 w (add_zeroₓ _)
  rcases mem_nhds_iff_exists_Ioo_subset.1 (this <| inter_mem ht <| is_open_ball.mem_nhds hw) with ⟨l, u, hlu₀, hlu_sub⟩
  obtain ⟨x, hx⟩ : (Ioo l u \ g ⁻¹' s).Nonempty := by
    refine' nonempty_diff.2 fun hsub => _
    have : (Ioo l u).Countable := (hs.preimage ((add_right_injective w).comp of_real_injective)).mono hsub
    rw [← Cardinal.mk_set_le_aleph_0, Cardinal.mk_Ioo_real (hlu₀.1.trans hlu₀.2)] at this
    exact this.not_lt Cardinal.aleph_0_lt_continuum
  exact ⟨g x, (hlu_sub hx.1).1, (hlu_sub hx.1).2, hx.2⟩

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$.
-/
theorem circle_integral_sub_inv_smul_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {f : ℂ → E} {s : Set ℂ}
    (hs : s.Countable) (hw : w ∈ Ball c R) (hc : ContinuousOn f (ClosedBall c R))
    (hd : ∀, ∀ x ∈ Ball c R \ s, ∀, DifferentiableAt ℂ f x) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w := by
  rw [← two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd, smul_inv_smul₀]
  simp [← Real.pi_ne_zero, ← I_ne_zero]

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on an open disc and is
continuous on its closure, then for any `w` in this open ball we have
$\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$. -/
theorem _root_.diff_cont_on_cl.circle_integral_sub_inv_smul {R : ℝ} {c w : ℂ} {f : ℂ → E}
    (h : DiffContOnCl ℂ f (Ball c R)) (hw : w ∈ Ball c R) : (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
  (circle_integral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw h.continuous_on_ball) fun x hx =>
    h.DifferentiableAt is_open_ball hx.1

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on a closed disc of radius
`R`, then for any `w` in its interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$. -/
theorem _root_.differentiable_on.circle_integral_sub_inv_smul {R : ℝ} {c w : ℂ} {f : ℂ → E}
    (hd : DifferentiableOn ℂ f (ClosedBall c R)) (hw : w ∈ Ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
  (hd.mono closure_ball_subset_closed_ball).DiffContOnCl.circle_integral_sub_inv_smul hw

/-- **Cauchy integral formula**: if `f : ℂ → ℂ` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\oint_{|z-c|=R}\frac{f(z)}{z-w}dz=2\pi i\,f(w)$.
-/
theorem circle_integral_div_sub_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {s : Set ℂ} (hs : s.Countable)
    (hw : w ∈ Ball c R) {f : ℂ → ℂ} (hc : ContinuousOn f (ClosedBall c R))
    (hd : ∀, ∀ z ∈ Ball c R \ s, ∀, DifferentiableAt ℂ f z) : (∮ z in C(c, R), f z / (z - w)) = 2 * π * I * f w := by
  simpa only [← smul_eq_mul, ← div_eq_inv_mul] using
    circle_integral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd

/-- If `f : ℂ → E` is continuous on a closed ball of positive radius and is differentiable at all
but countably many points of the corresponding open ball, then it is analytic on the open ball with
coefficients of the power series given by Cauchy integral formulas. -/
theorem has_fpower_series_on_ball_of_differentiable_off_countable {R : ℝ≥0 } {c : ℂ} {f : ℂ → E} {s : Set ℂ}
    (hs : s.Countable) (hc : ContinuousOn f (ClosedBall c R)) (hd : ∀, ∀ z ∈ Ball c R \ s, ∀, DifferentiableAt ℂ f z)
    (hR : 0 < R) : HasFpowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  { r_le := le_radius_cauchy_power_series _ _ _, r_pos := Ennreal.coe_pos.2 hR,
    HasSum := fun w hw => by
      have hw' : c + w ∈ ball c R := by
        simpa only [← add_mem_ball_iff_norm, coe_nnnorm, ← mem_emetric_ball_zero_iff, ← Nnreal.coe_lt_coe, ←
          Ennreal.coe_lt_coe] using hw
      rw [← two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable hs hw' hc hd]
      exact
        (has_fpower_series_on_cauchy_integral ((hc.mono sphere_subset_closed_ball).CircleIntegrable R.2) hR).HasSum hw }

/-- If `f : ℂ → E` is complex differentiable on an open disc of positive radius and is continuous
on its closure, then it is analytic on the open disc with coefficients of the power series given by
Cauchy integral formulas. -/
theorem _root_.diff_cont_on_cl.has_fpower_series_on_ball {R : ℝ≥0 } {c : ℂ} {f : ℂ → E}
    (hf : DiffContOnCl ℂ f (Ball c R)) (hR : 0 < R) : HasFpowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  has_fpower_series_on_ball_of_differentiable_off_countable countable_empty hf.continuous_on_ball
    (fun z hz => hf.DifferentiableAt is_open_ball hz.1) hR

/-- If `f : ℂ → E` is complex differentiable on a closed disc of positive radius, then it is
analytic on the corresponding open disc, and the coefficients of the power series are given by
Cauchy integral formulas. See also
`complex.has_fpower_series_on_ball_of_differentiable_off_countable` for a version of this lemma with
weaker assumptions. -/
protected theorem _root_.differentiable_on.has_fpower_series_on_ball {R : ℝ≥0 } {c : ℂ} {f : ℂ → E}
    (hd : DifferentiableOn ℂ f (ClosedBall c R)) (hR : 0 < R) : HasFpowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  (hd.mono closure_ball_subset_closed_ball).DiffContOnCl.HasFpowerSeriesOnBall hR

/-- If `f : ℂ → E` is complex differentiable on some set `s`, then it is analytic at any point `z`
such that `s ∈ 𝓝 z` (equivalently, `z ∈ interior s`). -/
protected theorem _root_.differentiable_on.analytic_at {s : Set ℂ} {f : ℂ → E} {z : ℂ} (hd : DifferentiableOn ℂ f s)
    (hz : s ∈ 𝓝 z) : AnalyticAt ℂ f z := by
  rcases nhds_basis_closed_ball.mem_iff.1 hz with ⟨R, hR0, hRs⟩
  lift R to ℝ≥0 using hR0.le
  exact ((hd.mono hRs).HasFpowerSeriesOnBall hR0).AnalyticAt

/-- A complex differentiable function `f : ℂ → E` is analytic at every point. -/
protected theorem _root_.differentiable.analytic_at {f : ℂ → E} (hf : Differentiable ℂ f) (z : ℂ) : AnalyticAt ℂ f z :=
  hf.DifferentiableOn.AnalyticAt univ_mem

/-- When `f : ℂ → E` is differentiable, the `cauchy_power_series f z R` represents `f` as a power
series centered at `z` in the entirety of `ℂ`, regardless of `R : ℝ≥0`, with  `0 < R`. -/
protected theorem _root_.differentiable.has_fpower_series_on_ball {f : ℂ → E} (h : Differentiable ℂ f) (z : ℂ)
    {R : ℝ≥0 } (hR : 0 < R) : HasFpowerSeriesOnBall f (cauchyPowerSeries f z R) z ∞ :=
  (h.DifferentiableOn.HasFpowerSeriesOnBall hR).r_eq_top_of_exists fun r hr =>
    ⟨_, h.DifferentiableOn.HasFpowerSeriesOnBall hr⟩

end Complex

