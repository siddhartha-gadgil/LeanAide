/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.MeasureTheory.Integral.IntervalIntegral
import Mathbin.Analysis.NormedSpace.Pointwise
import Mathbin.Analysis.SpecialFunctions.NonIntegrable
import Mathbin.Analysis.Analytic.Basic

/-!
# Integral over a circle in `ℂ`

In this file we define `∮ z in C(c, R), f z` to be the integral $\oint_{|z-c|=|R|} f(z)\,dz$ and
prove some properties of this integral. We give definition and prove most lemmas for a function
`f : ℂ → E`, where `E` is a complex Banach space. For this reason,
some lemmas use, e.g., `(z - c)⁻¹ • f z` instead of `f z / (z - c)`.

## Main definitions

* `circle_map c R`: the exponential map $θ ↦ c + R e^{θi}$;

* `circle_integrable f c R`: a function `f : ℂ → E` is integrable on the circle with center `c` and
  radius `R` if `f ∘ circle_map c R` is integrable on `[0, 2π]`;

* `circle_integral f c R`: the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$;

* `cauchy_power_series f c R`: the power series that is equal to
  $\sum_{n=0}^{\infty} \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
  `w - c`. The coefficients of this power series depend only on `f ∘ circle_map c R`, and the power
  series converges to `f w` if `f` is differentiable on the closed ball `metric.closed_ball c R`
  and `w` belongs to the corresponding open ball.

## Main statements

* `has_fpower_series_on_cauchy_integral`: for any circle integrable function `f`, the power series
  `cauchy_power_series f c R`, `R > 0`, converges to the Cauchy integral
  `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc `metric.ball c R`;

* `circle_integral.integral_sub_zpow_of_undef`, `circle_integral.integral_sub_zpow_of_ne`, and
  `circle_integral.integral_sub_inv_of_mem_ball`: formulas for `∮ z in C(c, R), (z - w) ^ n`,
  `n : ℤ`. These lemmas cover the following cases:

  - `circle_integral.integral_sub_zpow_of_undef`, `n < 0` and `|w - c| = |R|`: in this case the
    function is not integrable, so the integral is equal to its default value (zero);

  - `circle_integral.integral_sub_zpow_of_ne`, `n ≠ -1`: in the cases not covered by the previous
    lemma, we have `(z - w) ^ n = ((z - w) ^ (n + 1) / (n + 1))'`, thus the integral equals zero;

  - `circle_integral.integral_sub_inv_of_mem_ball`, `n = -1`, `|w - c| < R`: in this case the
    integral is equal to `2πi`.

  The case `n = -1`, `|w -c| > R` is not covered by these lemmas. While it is possible to construct
  an explicit primitive, it is easier to apply Cauchy theorem, so we postpone the proof till we have
  this theorem (see #10000).

## Notation

- `∮ z in C(c, R), f z`: notation for the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$.

## Tags

integral, circle, Cauchy integral
-/


variable {E : Type _} [NormedGroup E]

noncomputable section

open Real Nnreal Interval Pointwise TopologicalSpace

open Complex MeasureTheory TopologicalSpace Metric Function Set Filter Asymptotics

/-!
### `circle_map`, a parametrization of a circle
-/


/-- The exponential map $θ ↦ c + R e^{θi}$. The range of this map is the circle in `ℂ` with center
`c` and radius `|R|`. -/
def circleMap (c : ℂ) (R : ℝ) : ℝ → ℂ := fun θ => c + R * exp (θ * I)

/-- `circle_map` is `2π`-periodic. -/
theorem periodic_circle_map (c : ℂ) (R : ℝ) : Periodic (circleMap c R) (2 * π) := fun θ => by
  simp [← circleMap, ← add_mulₓ, ← exp_periodic _]

theorem Set.Countable.preimage_circle_map {s : Set ℂ} (hs : s.Countable) (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (circleMap c R ⁻¹' s).Countable :=
  show (coe ⁻¹' ((· * i) ⁻¹' (exp ⁻¹' ((· * ·) R ⁻¹' ((· + ·) c ⁻¹' s))))).Countable from
    (((hs.Preimage (add_right_injective _)).Preimage <|
                mul_right_injective₀ <| of_real_ne_zero.2 hR).preimage_cexp.Preimage <|
          mul_left_injective₀ I_ne_zero).Preimage
      of_real_injective

@[simp]
theorem circle_map_sub_center (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ - c = circleMap 0 R θ := by
  simp [← circleMap]

theorem circle_map_zero (R θ : ℝ) : circleMap 0 R θ = R * exp (θ * I) :=
  zero_addₓ _

@[simp]
theorem abs_circle_map_zero (R : ℝ) (θ : ℝ) : abs (circleMap 0 R θ) = abs R := by
  simp [← circleMap]

theorem circle_map_mem_sphere' (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ ∈ Sphere c (abs R) := by
  simp

theorem circle_map_mem_sphere (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) : circleMap c R θ ∈ Sphere c R := by
  simpa only [← _root_.abs_of_nonneg hR] using circle_map_mem_sphere' c R θ

theorem circle_map_mem_closed_ball (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) : circleMap c R θ ∈ ClosedBall c R :=
  sphere_subset_closed_ball (circle_map_mem_sphere c hR θ)

theorem circle_map_not_mem_ball (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ ∉ Ball c R := by
  simp [← dist_eq, ← le_abs_self]

theorem circle_map_ne_mem_ball {c : ℂ} {R : ℝ} {w : ℂ} (hw : w ∈ Ball c R) (θ : ℝ) : circleMap c R θ ≠ w :=
  (ne_of_mem_of_not_mem hw (circle_map_not_mem_ball _ _ _)).symm

/-- The range of `circle_map c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
theorem range_circle_map (c : ℂ) (R : ℝ) : Range (circleMap c R) = Sphere c (abs R) :=
  calc
    Range (circleMap c R) = c +ᵥ R • Range fun θ : ℝ => exp (θ * I) := by
      simp only [image_vadd, image_smul, range_comp, ← vadd_eq_add, ← circleMap, ← (· ∘ ·), ← real_smul]
    _ = Sphere c (abs R) := by
      simp [← smul_sphere R (0 : ℂ) zero_le_one]
    

/-- The image of `(0, 2π]` under `circle_map c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
theorem image_circle_map_Ioc (c : ℂ) (R : ℝ) : circleMap c R '' Ioc 0 (2 * π) = Sphere c (abs R) := by
  rw [← range_circle_map, ← (periodic_circle_map c R).image_Ioc Real.two_pi_pos 0, zero_addₓ]

@[simp]
theorem circle_map_eq_center_iff {c : ℂ} {R : ℝ} {θ : ℝ} : circleMap c R θ = c ↔ R = 0 := by
  simp [← circleMap, ← exp_ne_zero]

@[simp]
theorem circle_map_zero_radius (c : ℂ) : circleMap c 0 = const ℝ c :=
  funext fun θ => circle_map_eq_center_iff.2 rfl

theorem circle_map_ne_center {c : ℂ} {R : ℝ} (hR : R ≠ 0) {θ : ℝ} : circleMap c R θ ≠ c :=
  mt circle_map_eq_center_iff.1 hR

theorem has_deriv_at_circle_map (c : ℂ) (R : ℝ) (θ : ℝ) : HasDerivAt (circleMap c R) (circleMap 0 R θ * I) θ := by
  simpa only [← mul_assoc, ← one_mulₓ, ← of_real_clm_apply, ← circleMap, ← of_real_one, ← zero_addₓ] using
    ((of_real_clm.has_deriv_at.mul_const I).cexp.const_mul (R : ℂ)).const_add c

/- TODO: prove `cont_diff ℝ (circle_map c R)`. This needs a version of `cont_diff.mul`
for multiplication in a normed algebra over the base field. -/
theorem differentiable_circle_map (c : ℂ) (R : ℝ) : Differentiable ℝ (circleMap c R) := fun θ =>
  (has_deriv_at_circle_map c R θ).DifferentiableAt

@[continuity]
theorem continuous_circle_map (c : ℂ) (R : ℝ) : Continuous (circleMap c R) :=
  (differentiable_circle_map c R).Continuous

@[measurability]
theorem measurable_circle_map (c : ℂ) (R : ℝ) : Measurable (circleMap c R) :=
  (continuous_circle_map c R).Measurable

@[simp]
theorem deriv_circle_map (c : ℂ) (R : ℝ) (θ : ℝ) : deriv (circleMap c R) θ = circleMap 0 R θ * I :=
  (has_deriv_at_circle_map _ _ _).deriv

theorem deriv_circle_map_eq_zero_iff {c : ℂ} {R : ℝ} {θ : ℝ} : deriv (circleMap c R) θ = 0 ↔ R = 0 := by
  simp [← I_ne_zero]

theorem deriv_circle_map_ne_zero {c : ℂ} {R : ℝ} {θ : ℝ} (hR : R ≠ 0) : deriv (circleMap c R) θ ≠ 0 :=
  mt deriv_circle_map_eq_zero_iff.1 hR

theorem lipschitz_with_circle_map (c : ℂ) (R : ℝ) : LipschitzWith R.nnabs (circleMap c R) :=
  (lipschitz_with_of_nnnorm_deriv_le (differentiable_circle_map _ _)) fun θ =>
    Nnreal.coe_le_coe.1 <| by
      simp

theorem continuous_circle_map_inv {R : ℝ} {z w : ℂ} (hw : w ∈ Ball z R) : Continuous fun θ => (circleMap z R θ - w)⁻¹ :=
  by
  have : ∀ θ, circleMap z R θ - w ≠ 0 := by
    simp_rw [sub_ne_zero]
    exact fun θ => circle_map_ne_mem_ball hw θ
  continuity

/-!
### Integrability of a function on a circle
-/


/-- We say that a function `f : ℂ → E` is integrable on the circle with center `c` and radius `R` if
the function `f ∘ circle_map c R` is integrable on `[0, 2π]`.

Note that the actual function used in the definition of `circle_integral` is
`(deriv (circle_map c R) θ) • f (circle_map c R θ)`. Integrability of this function is equivalent
to integrability of `f ∘ circle_map c R` whenever `R ≠ 0`. -/
def CircleIntegrable (f : ℂ → E) (c : ℂ) (R : ℝ) : Prop :=
  IntervalIntegrable (fun θ : ℝ => f (circleMap c R θ)) volume 0 (2 * π)

@[simp]
theorem circle_integrable_const (a : E) (c : ℂ) (R : ℝ) : CircleIntegrable (fun _ => a) c R :=
  interval_integrable_const

namespace CircleIntegrable

variable {f g : ℂ → E} {c : ℂ} {R : ℝ}

theorem add (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) : CircleIntegrable (f + g) c R :=
  hf.add hg

theorem neg (hf : CircleIntegrable f c R) : CircleIntegrable (-f) c R :=
  hf.neg

/-- The function we actually integrate over `[0, 2π]` in the definition of `circle_integral` is
integrable. -/
theorem out [NormedSpace ℂ E] (hf : CircleIntegrable f c R) :
    IntervalIntegrable (fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0 (2 * π) := by
  simp only [← CircleIntegrable, ← deriv_circle_map, ← interval_integrable_iff] at *
  refine' (hf.norm.const_mul (abs R)).mono' _ _
  · exact ((continuous_circle_map _ _).AeStronglyMeasurable.mul_const I).smul hf.ae_strongly_measurable
    
  · simp [← norm_smul]
    

end CircleIntegrable

@[simp]
theorem circle_integrable_zero_radius {f : ℂ → E} {c : ℂ} : CircleIntegrable f c 0 := by
  simp [← CircleIntegrable]

theorem circle_integrable_iff [NormedSpace ℂ E] {f : ℂ → E} {c : ℂ} (R : ℝ) :
    CircleIntegrable f c R ↔
      IntervalIntegrable (fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0 (2 * π) :=
  by
  by_cases' h₀ : R = 0
  · simp [← h₀]
    
  refine' ⟨fun h => h.out, fun h => _⟩
  simp only [← CircleIntegrable, ← interval_integrable_iff, ← deriv_circle_map] at h⊢
  refine' (h.norm.const_mul (abs R)⁻¹).mono' _ _
  · have H : ∀ {θ}, circleMap 0 R θ * I ≠ 0 := fun θ => by
      simp [← h₀, ← I_ne_zero]
    simpa only [← inv_smul_smul₀ H] using
      ((continuous_circle_map 0 R).AeStronglyMeasurable.mul_const I).AeMeasurable.inv.AeStronglyMeasurable.smul
        h.ae_strongly_measurable
    
  · simp [← norm_smul, ← h₀]
    

theorem ContinuousOn.circle_integrable' {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : ContinuousOn f (Sphere c (abs R))) :
    CircleIntegrable f c R :=
  (hf.comp_continuous (continuous_circle_map _ _) (circle_map_mem_sphere' _ _)).IntervalIntegrable _ _

theorem ContinuousOn.circle_integrable {f : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hf : ContinuousOn f (Sphere c R)) :
    CircleIntegrable f c R :=
  ContinuousOn.circle_integrable' <| (abs_of_nonneg hR).symm ▸ hf

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- The function `λ z, (z - w) ^ n`, `n : ℤ`, is circle integrable on the circle with center `c` and
radius `|R|` if and only if `R = 0` or `0 ≤ n`, or `w` does not belong to this circle. -/
@[simp]
theorem circle_integrable_sub_zpow_iff {c w : ℂ} {R : ℝ} {n : ℤ} :
    CircleIntegrable (fun z => (z - w) ^ n) c R ↔ R = 0 ∨ 0 ≤ n ∨ w ∉ Sphere c (abs R) := by
  constructor
  · intro h
    contrapose! h
    rcases h with ⟨hR, hn, hw⟩
    simp only [← circle_integrable_iff R, ← deriv_circle_map]
    rw [← image_circle_map_Ioc] at hw
    rcases hw with ⟨θ, hθ, rfl⟩
    replace hθ : θ ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"
    exact Icc_subset_interval (Ioc_subset_Icc_self hθ)
    refine' not_interval_integrable_of_sub_inv_is_O_punctured _ real.two_pi_pos.ne hθ
    set f : ℝ → ℂ := fun θ' => circleMap c R θ' - circleMap c R θ
    have : ∀ᶠ θ' in 𝓝[≠] θ, f θ' ∈ ball (0 : ℂ) 1 \ {0} := by
      suffices : ∀ᶠ z in 𝓝[≠] circleMap c R θ, z - circleMap c R θ ∈ ball (0 : ℂ) 1 \ {0}
      exact
        ((differentiable_circle_map c R θ).HasDerivAt.tendsto_punctured_nhds (deriv_circle_map_ne_zero hR)).Eventually
          this
      filter_upwards [self_mem_nhds_within, mem_nhds_within_of_mem_nhds (ball_mem_nhds _ zero_lt_one)]
      simp (config := { contextual := true })[← dist_eq, ← sub_eq_zero]
    refine'
      (((has_deriv_at_circle_map c R θ).is_O_sub.mono inf_le_left).inv_rev
            (this.mono fun θ' h₁ h₂ => absurd h₂ h₁.2)).trans
        _
    refine' is_O.of_bound (abs R)⁻¹ (this.mono fun θ' hθ' => _)
    set x := abs (f θ')
    suffices x⁻¹ ≤ x ^ n by
      simpa [← inv_mul_cancel_left₀, ← mt _root_.abs_eq_zero.1 hR]
    have : x ∈ Ioo (0 : ℝ) 1 := by
      simpa [← And.comm, ← x] using hθ'
    rw [← zpow_neg_one]
    refine' (zpow_strict_anti this.1 this.2).le_iff_le.2 (Int.lt_add_one_iff.1 _)
    exact hn
    
  · rintro (rfl | H)
    exacts[circle_integrable_zero_radius,
      (((continuous_on_id.sub continuous_on_const).zpow₀ _) fun z hz =>
          H.symm.imp_left fun hw => sub_ne_zero.2 <| ne_of_mem_of_not_mem hz hw).circle_integrable']
    

@[simp]
theorem circle_integrable_sub_inv_iff {c w : ℂ} {R : ℝ} :
    CircleIntegrable (fun z => (z - w)⁻¹) c R ↔ R = 0 ∨ w ∉ Sphere c (abs R) := by
  simp only [zpow_neg_one, ← circle_integrable_sub_zpow_iff]
  norm_num

variable [NormedSpace ℂ E] [CompleteSpace E]

/-- Definition for $\oint_{|z-c|=R} f(z)\,dz$. -/
def circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  ∫ θ : ℝ in 0 ..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)

-- mathport name: «expr∮ inC( , ), »
notation3"∮ "(...)" in ""C("c", "R")"", "r:(scoped f => circleIntegral f c R) => r

theorem circle_integral_def_Icc (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z) = ∫ θ in Icc 0 (2 * π), deriv (circleMap c R) θ • f (circleMap c R θ) := by
  simp only [← circleIntegral, ← intervalIntegral.integral_of_le real.two_pi_pos.le, ←
    measure.restrict_congr_set Ioc_ae_eq_Icc]

namespace circleIntegral

@[simp]
theorem integral_radius_zero (f : ℂ → E) (c : ℂ) : (∮ z in C(c, 0), f z) = 0 := by
  simp [← circleIntegral]

theorem integral_congr {f g : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h : EqOn f g (Sphere c R)) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), g z :=
  intervalIntegral.integral_congr fun θ hθ => by
    simp only [← h (circle_map_mem_sphere _ hR _)]

theorem integral_sub_inv_smul_sub_smul (f : ℂ → E) (c w : ℂ) (R : ℝ) :
    (∮ z in C(c, R), (z - w)⁻¹ • (z - w) • f z) = ∮ z in C(c, R), f z := by
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [← integral_radius_zero]
    
  have : (circleMap c R ⁻¹' {w}).Countable := (countable_singleton _).preimage_circle_map c hR
  refine' intervalIntegral.integral_congr_ae ((this.ae_not_mem _).mono fun θ hθ hθ' => _)
  change circleMap c R θ ≠ w at hθ
  simp only [← inv_smul_smul₀ (sub_ne_zero.2 <| hθ)]

theorem integral_undef {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : ¬CircleIntegrable f c R) : (∮ z in C(c, R), f z) = 0 :=
  intervalIntegral.integral_undef (mt (circle_integrable_iff R).mpr hf)

theorem integral_sub {f g : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    (∮ z in C(c, R), f z - g z) = (∮ z in C(c, R), f z) - ∮ z in C(c, R), g z := by
  simp only [← circleIntegral, ← smul_sub, ← intervalIntegral.integral_sub hf.out hg.out]

theorem norm_integral_le_of_norm_le_const' {f : ℂ → E} {c : ℂ} {R C : ℝ}
    (hf : ∀, ∀ z ∈ Sphere c (abs R), ∀, ∥f z∥ ≤ C) : ∥∮ z in C(c, R), f z∥ ≤ 2 * π * abs R * C :=
  calc
    ∥∮ z in C(c, R), f z∥ ≤ abs R * C * abs (2 * π - 0) :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ =>
        calc
          ∥deriv (circleMap c R) θ • f (circleMap c R θ)∥ = abs R * ∥f (circleMap c R θ)∥ := by
            simp [← norm_smul]
          _ ≤ abs R * C := mul_le_mul_of_nonneg_left (hf _ <| circle_map_mem_sphere' _ _ _) (abs_nonneg _)
          
    _ = 2 * π * abs R * C := by
      rw [sub_zero, _root_.abs_of_pos Real.two_pi_pos]
      ac_rfl
    

theorem norm_integral_le_of_norm_le_const {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hf : ∀, ∀ z ∈ Sphere c R, ∀, ∥f z∥ ≤ C) : ∥∮ z in C(c, R), f z∥ ≤ 2 * π * R * C :=
  have : abs R = R := abs_of_nonneg hR
  calc
    ∥∮ z in C(c, R), f z∥ ≤ 2 * π * abs R * C :=
      norm_integral_le_of_norm_le_const' <| by
        rwa [this]
    _ = 2 * π * R * C := by
      rw [this]
    

theorem norm_two_pi_I_inv_smul_integral_le_of_norm_le_const {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hf : ∀, ∀ z ∈ Sphere c R, ∀, ∥f z∥ ≤ C) : ∥(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), f z∥ ≤ R * C := by
  have : ∥(2 * π * I : ℂ)⁻¹∥ = (2 * π)⁻¹ := by
    simp [← real.pi_pos.le]
  rw [norm_smul, this, ← div_eq_inv_mul, div_le_iff Real.two_pi_pos, mul_comm (R * C), ← mul_assoc]
  exact norm_integral_le_of_norm_le_const hR hf

/-- If `f` is continuous on the circle `|z - c| = R`, `R > 0`, the `∥f z∥` is less than or equal to
`C : ℝ` on this circle, and this norm is strictly less than `C` at some point `z` of the circle,
then `∥∮ z in C(c, R), f z∥ < 2 * π * R * C`. -/
theorem norm_integral_lt_of_norm_le_const_of_lt {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hc : ContinuousOn f (Sphere c R)) (hf : ∀, ∀ z ∈ Sphere c R, ∀, ∥f z∥ ≤ C) (hlt : ∃ z ∈ Sphere c R, ∥f z∥ < C) :
    ∥∮ z in C(c, R), f z∥ < 2 * π * R * C := by
  rw [← _root_.abs_of_pos hR, ← image_circle_map_Ioc] at hlt
  rcases hlt with ⟨_, ⟨θ₀, hmem, rfl⟩, hlt⟩
  calc ∥∮ z in C(c, R), f z∥ ≤ ∫ θ in 0 ..2 * π, ∥deriv (circleMap c R) θ • f (circleMap c R θ)∥ :=
      intervalIntegral.norm_integral_le_integral_norm real.two_pi_pos.le _ < ∫ θ in 0 ..2 * π, R * C := by
      simp only [← norm_smul, ← deriv_circle_map, ← norm_eq_abs, ← Complex.abs_mul, ← abs_I, ← mul_oneₓ, ←
        abs_circle_map_zero, ← abs_of_pos hR]
      refine'
        intervalIntegral.integral_lt_integral_of_continuous_on_of_le_of_exists_lt Real.two_pi_pos _ continuous_on_const
          (fun θ hθ => _) ⟨θ₀, Ioc_subset_Icc_self hmem, _⟩
      · exact
          continuous_on_const.mul
            (hc.comp (continuous_circle_map _ _).ContinuousOn fun θ hθ => circle_map_mem_sphere _ hR.le _).norm
        
      · exact mul_le_mul_of_nonneg_left (hf _ <| circle_map_mem_sphere _ hR.le _) hR.le
        
      · exact (mul_lt_mul_left hR).2 hlt
        _ = 2 * π * R * C :=
      by
      simp [← mul_assoc]

@[simp]
theorem integral_smul {𝕜 : Type _} [IsROrC 𝕜] [NormedSpace 𝕜 E] [SmulCommClass 𝕜 ℂ E] (a : 𝕜) (f : ℂ → E) (c : ℂ)
    (R : ℝ) : (∮ z in C(c, R), a • f z) = a • ∮ z in C(c, R), f z := by
  simp only [← circleIntegral, smul_comm a, ← intervalIntegral.integral_smul]

@[simp]
theorem integral_smul_const (f : ℂ → ℂ) (a : E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z • a) = (∮ z in C(c, R), f z) • a := by
  simp only [← circleIntegral, ← intervalIntegral.integral_smul_const, smul_assoc]

@[simp]
theorem integral_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : (∮ z in C(c, R), a * f z) = a * ∮ z in C(c, R), f z :=
  integral_smul a f c R

@[simp]
theorem integral_sub_center_inv (c : ℂ) {R : ℝ} (hR : R ≠ 0) : (∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I := by
  simp [← circleIntegral, div_eq_mul_inv, ← mul_div_cancel_left _ (circle_map_ne_center hR)]

/-- If `f' : ℂ → E` is a derivative of a complex differentiable function on the circle
`metric.sphere c |R|`, then `∮ z in C(c, R), f' z = 0`. -/
theorem integral_eq_zero_of_has_deriv_within_at' {f f' : ℂ → E} {c : ℂ} {R : ℝ}
    (h : ∀, ∀ z ∈ Sphere c (abs R), ∀, HasDerivWithinAt f (f' z) (Sphere c (abs R)) z) : (∮ z in C(c, R), f' z) = 0 :=
  by
  by_cases' hi : CircleIntegrable f' c R
  · rw [← sub_eq_zero.2 ((periodic_circle_map c R).comp f).Eq]
    refine' intervalIntegral.integral_eq_sub_of_has_deriv_at (fun θ hθ => _) hi.out
    exact
      (h _ (circle_map_mem_sphere' _ _ _)).scomp_has_deriv_at θ (differentiable_circle_map _ _ _).HasDerivAt
        (circle_map_mem_sphere' _ _)
    
  · exact integral_undef hi
    

/-- If `f' : ℂ → E` is a derivative of a complex differentiable function on the circle
`metric.sphere c R`, then `∮ z in C(c, R), f' z = 0`. -/
theorem integral_eq_zero_of_has_deriv_within_at {f f' : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀, ∀ z ∈ Sphere c R, ∀, HasDerivWithinAt f (f' z) (Sphere c R) z) : (∮ z in C(c, R), f' z) = 0 :=
  integral_eq_zero_of_has_deriv_within_at' <| (abs_of_nonneg hR).symm.subst h

/-- If `n < 0` and `|w - c| = |R|`, then `(z - w) ^ n` is not circle integrable on the circle with
center `c` and radius `(|R|)`, so the integral `∮ z in C(c, R), (z - w) ^ n` is equal to zero. -/
theorem integral_sub_zpow_of_undef {n : ℤ} {c w : ℂ} {R : ℝ} (hn : n < 0) (hw : w ∈ Sphere c (abs R)) :
    (∮ z in C(c, R), (z - w) ^ n) = 0 := by
  rcases eq_or_ne R 0 with (rfl | h0)
  · apply integral_radius_zero
    
  apply integral_undef
  simp [← circle_integrable_sub_zpow_iff, *]

/-- If `n ≠ -1` is an integer number, then the integral of `(z - w) ^ n` over the circle equals
zero. -/
theorem integral_sub_zpow_of_ne {n : ℤ} (hn : n ≠ -1) (c w : ℂ) (R : ℝ) : (∮ z in C(c, R), (z - w) ^ n) = 0 := by
  rcases em (w ∈ sphere c (abs R) ∧ n < -1) with (⟨hw, hn⟩ | H)
  · exact
      integral_sub_zpow_of_undef
        (hn.trans
          (by
            decide))
        hw
    
  push_neg  at H
  have hd : ∀ z, z ≠ w ∨ -1 ≤ n → HasDerivAt (fun z => (z - w) ^ (n + 1) / (n + 1)) ((z - w) ^ n) z := by
    intro z hne
    convert ((has_deriv_at_zpow (n + 1) _ (hne.imp _ _)).comp z ((has_deriv_at_id z).sub_const w)).div_const _ using 1
    · have hn' : (n + 1 : ℂ) ≠ 0 := by
        rwa [Ne, ← eq_neg_iff_add_eq_zero, ← Int.cast_oneₓ, ← Int.cast_neg, Int.cast_inj]
      simp [← mul_assoc, ← mul_div_cancel_left _ hn']
      
    exacts[sub_ne_zero.2, neg_le_iff_add_nonneg.1]
  refine' integral_eq_zero_of_has_deriv_within_at' fun z hz => (hd z _).HasDerivWithinAt
  exact (ne_or_eq z w).imp_right fun h => H <| h ▸ hz

end circleIntegral

/-- The power series that is equal to
$\sum_{n=0}^{\infty} \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
`w - c`. The coefficients of this power series depend only on `f ∘ circle_map c R`, and the power
series converges to `f w` if `f` is differentiable on the closed ball `metric.closed_ball c R` and
`w` belongs to the corresponding open ball. For any circle integrable function `f`, this power
series converges to the Cauchy integral for `f`. -/
def cauchyPowerSeries (f : ℂ → E) (c : ℂ) (R : ℝ) : FormalMultilinearSeries ℂ ℂ E := fun n =>
  ContinuousMultilinearMap.mkPiField ℂ _ <| (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z

theorem cauchy_power_series_apply (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) (w : ℂ) :
    (cauchyPowerSeries f c R n fun _ => w) = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z :=
  by
  simp only [← cauchyPowerSeries, ← ContinuousMultilinearMap.mk_pi_field_apply, ← Finₓ.prod_const, ← div_eq_mul_inv, ←
    mul_powₓ, ← mul_smul, ← circleIntegral.integral_smul, smul_comm (w ^ n)]

theorem norm_cauchy_power_series_le (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) :
    ∥cauchyPowerSeries f c R n∥ ≤ ((2 * π)⁻¹ * ∫ θ : ℝ in 0 ..2 * π, ∥f (circleMap c R θ)∥) * (abs R)⁻¹ ^ n :=
  calc
    ∥cauchyPowerSeries f c R n∥ = (2 * π)⁻¹ * ∥∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z∥ := by
      simp [← cauchyPowerSeries, ← norm_smul, ← real.pi_pos.le]
    _ ≤
        (2 * π)⁻¹ *
          ∫ θ in 0 ..2 * π,
            ∥deriv (circleMap c R) θ • (circleMap c R θ - c)⁻¹ ^ n • (circleMap c R θ - c)⁻¹ • f (circleMap c R θ)∥ :=
      mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le)
        (by
          simp [← real.pi_pos.le])
    _ = (2 * π)⁻¹ * ((abs R)⁻¹ ^ n * (abs R * ((abs R)⁻¹ * ∫ x : ℝ in 0 ..2 * π, ∥f (circleMap c R x)∥))) := by
      simp [← norm_smul, ← mul_left_commₓ (abs R)]
    _ ≤ ((2 * π)⁻¹ * ∫ θ : ℝ in 0 ..2 * π, ∥f (circleMap c R θ)∥) * (abs R)⁻¹ ^ n := by
      rcases eq_or_ne R 0 with (rfl | hR)
      · cases n <;> simp [-mul_inv_rev, ← Real.two_pi_pos]
        
      · rw [mul_inv_cancel_left₀, mul_assoc, mul_comm ((abs R)⁻¹ ^ n)]
        rwa [Ne.def, _root_.abs_eq_zero]
        
    

theorem le_radius_cauchy_power_series (f : ℂ → E) (c : ℂ) (R : ℝ≥0 ) : ↑R ≤ (cauchyPowerSeries f c R).radius := by
  refine'
    (cauchyPowerSeries f c R).le_radius_of_bound ((2 * π)⁻¹ * ∫ θ : ℝ in 0 ..2 * π, ∥f (circleMap c R θ)∥) fun n => _
  refine' (mul_le_mul_of_nonneg_right (norm_cauchy_power_series_le _ _ _ _) (pow_nonneg R.coe_nonneg _)).trans _
  rw [_root_.abs_of_nonneg R.coe_nonneg]
  cases' eq_or_ne (R ^ n : ℝ) 0 with hR hR
  · rw [hR, mul_zero]
    exact
      mul_nonneg (inv_nonneg.2 real.two_pi_pos.le)
        (intervalIntegral.integral_nonneg real.two_pi_pos.le fun _ _ => norm_nonneg _)
    
  · rw [inv_pow, inv_mul_cancel_right₀ hR]
    

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- For any circle integrable function `f`, the power series `cauchy_power_series f c R` multiplied
by `2πI` converges to the integral `∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc
`metric.ball c R`. -/
theorem has_sum_two_pi_I_cauchy_power_series_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ} (hf : CircleIntegrable f c R)
    (hw : abs w < R) :
    HasSum (fun n : ℕ => ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z) (∮ z in C(c, R), (z - (c + w))⁻¹ • f z) :=
  by
  have hR : 0 < R := (abs_nonneg w).trans_lt hw
  have hwR : abs w / R ∈ Ico (0 : ℝ) 1 := ⟨div_nonneg (abs_nonneg w) hR.le, (div_lt_one hR).2 hw⟩
  refine'
    intervalIntegral.has_sum_integral_of_dominated_convergence (fun n θ => ∥f (circleMap c R θ)∥ * (abs w / R) ^ n)
      (fun n => _) (fun n => _) _ _ _
  · simp only [← deriv_circle_map]
    apply_rules [ae_strongly_measurable.smul, hf.def.1] <;>
      · apply Measurable.ae_strongly_measurable
        measurability
        
    
  · simp [← norm_smul, ← abs_of_pos hR, ← mul_left_commₓ R, ← mul_inv_cancel_left₀ hR.ne', ← mul_comm ∥_∥]
    
  · exact eventually_of_forall fun _ _ => (summable_geometric_of_lt_1 hwR.1 hwR.2).mul_left _
    
  · simpa only [← tsum_mul_left, ← tsum_geometric_of_lt_1 hwR.1 hwR.2] using
      hf.norm.mul_continuous_on continuous_on_const
    
  · refine' eventually_of_forall fun θ hθ => HasSum.const_smul _
    simp only [← smul_smul]
    refine' HasSum.smul_const _
    have : ∥w / (circleMap c R θ - c)∥ < 1 := by
      simpa [← abs_of_pos hR] using hwR.2
    convert (has_sum_geometric_of_norm_lt_1 this).mul_right _
    simp [sub_sub, mul_inv, ← sub_mul, ← div_mul_cancel _ (circle_map_ne_center hR.ne')]
    

/-- For any circle integrable function `f`, the power series `cauchy_power_series f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `metric.ball c R`. -/
theorem has_sum_cauchy_power_series_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ} (hf : CircleIntegrable f c R)
    (hw : abs w < R) :
    HasSum (fun n => cauchyPowerSeries f c R n fun _ => w)
      ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f z) :=
  by
  simp only [← cauchy_power_series_apply]
  exact (has_sum_two_pi_I_cauchy_power_series_integral hf hw).const_smul

/-- For any circle integrable function `f`, the power series `cauchy_power_series f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `metric.ball c R`. -/
theorem sum_cauchy_power_series_eq_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ} (hf : CircleIntegrable f c R)
    (hw : abs w < R) : (cauchyPowerSeries f c R).Sum w = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f z :=
  (has_sum_cauchy_power_series_integral hf hw).tsum_eq

/-- For any circle integrable function `f`, the power series `cauchy_power_series f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `metric.ball c R`. -/
theorem has_fpower_series_on_cauchy_integral {f : ℂ → E} {c : ℂ} {R : ℝ≥0 } (hf : CircleIntegrable f c R) (hR : 0 < R) :
    HasFpowerSeriesOnBall (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) (cauchyPowerSeries f c R) c
      R :=
  { r_le := le_radius_cauchy_power_series _ _ _, r_pos := Ennreal.coe_pos.2 hR,
    HasSum := fun y hy => by
      refine' has_sum_cauchy_power_series_integral hf _
      rw [← norm_eq_abs, ← coe_nnnorm, Nnreal.coe_lt_coe, ← Ennreal.coe_lt_coe]
      exact mem_emetric_ball_zero_iff.1 hy }

namespace circleIntegral

/-- Integral $\oint_{|z-c|=R} \frac{dz}{z-w}=2πi$ whenever $|w-c|<R$. -/
theorem integral_sub_inv_of_mem_ball {c w : ℂ} {R : ℝ} (hw : w ∈ Ball c R) : (∮ z in C(c, R), (z - w)⁻¹) = 2 * π * I :=
  by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices H : HasSum (fun n : ℕ => ∮ z in C(c, R), ((w - c) / (z - c)) ^ n * (z - c)⁻¹) (2 * π * I)
  · have A : CircleIntegrable (fun _ => (1 : ℂ)) c R := continuous_on_const.circle_integrable'
    refine' (H.unique _).symm
    simpa only [← smul_eq_mul, ← mul_oneₓ, ← add_sub_cancel'_right] using
      has_sum_two_pi_I_cauchy_power_series_integral A hw
    
  have H : ∀ n : ℕ, n ≠ 0 → (∮ z in C(c, R), (z - c) ^ (-n - 1 : ℤ)) = 0 := by
    refine' fun n hn => integral_sub_zpow_of_ne _ _ _ _
    simpa
  have : (∮ z in C(c, R), ((w - c) / (z - c)) ^ 0 * (z - c)⁻¹) = 2 * π * I := by
    simp [← hR.ne']
  refine' this ▸ has_sum_single _ fun n hn => _
  simp only [← div_eq_mul_inv, ← mul_powₓ, ← integral_const_mul, ← mul_assoc]
  rw [(integral_congr hR.le fun z hz => _).trans (H n hn), mul_zero]
  rw [← pow_succ'ₓ, ← zpow_coe_nat, inv_zpow, ← zpow_neg, Int.coe_nat_succ, neg_add, sub_eq_add_neg _ (1 : ℤ)]

end circleIntegral

