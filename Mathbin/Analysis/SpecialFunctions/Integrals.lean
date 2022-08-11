/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import Mathbin.MeasureTheory.Integral.IntervalIntegral
import Mathbin.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various specific functions. This includes:
* Integrals of simple functions, such as `id`, `pow`, `inv`, `exp`, `log`
* Integrals of some trigonometric functions, such as `sin`, `cos`, `1 / (1 + x^2)`
* The integral of `cos x ^ 2 - sin x ^ 2`
* Reduction formulae for the integrals of `sin x ^ n` and `cos x ^ n` for `n ≥ 2`
* The computation of `∫ x in 0..π, sin x ^ n` as a product for even and odd `n` (used in proving the
  Wallis product for pi)
* Integrals of the form `sin x ^ m * cos x ^ n`

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`.
See `test/integration.lean` for specific examples.

This file also contains some facts about the interval integrability of specific functions.

This file is still being developed.

## Tags

integrate, integration, integrable, integrability
-/


open Real Nat Set Finset

open Real BigOperators Interval

variable {a b : ℝ} (n : ℕ)

namespace intervalIntegral

open MeasureTheory

variable {f : ℝ → ℝ} {μ ν : Measureₓ ℝ} [IsLocallyFiniteMeasure μ] (c d : ℝ)

/-! ### Interval integrability -/


@[simp]
theorem interval_integrable_pow : IntervalIntegrable (fun x => x ^ n) μ a b :=
  (continuous_pow n).IntervalIntegrable a b

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_integrable_zpow {n : ℤ}
    (h : 0 ≤ n ∨ (0 : ℝ) ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    IntervalIntegrable (fun x => x ^ n) μ a b :=
  ((continuous_on_id.zpow₀ n) fun x hx => h.symm.imp (ne_of_mem_of_not_mem hx) id).IntervalIntegrable

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_integrable_rpow {r : ℝ}
    (h : 0 ≤ r ∨ (0 : ℝ) ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    IntervalIntegrable (fun x => x ^ r) μ a b :=
  (continuous_on_id.rpow_const fun x hx => h.symm.imp (ne_of_mem_of_not_mem hx) id).IntervalIntegrable

/-- Alternative version with a weaker hypothesis on `r`, but assuming the measure is volume. -/
theorem interval_integrable_rpow' {r : ℝ} (h : -1 < r) : IntervalIntegrable (fun x => x ^ r) volume a b := by
  suffices ∀ c : ℝ, IntervalIntegrable (fun x => x ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x => x ^ r) volume 0 c := by
    intro c hc
    rw [interval_integrable_iff, interval_oc_of_le hc]
    have hderiv : ∀, ∀ x ∈ Ioo 0 c, ∀, HasDerivAt (fun x : ℝ => x ^ (r + 1) / (r + 1)) (x ^ r) x := by
      intro x hx
      convert (Real.has_deriv_at_rpow_const (Or.inl hx.1.ne')).div_const (r + 1)
      field_simp [←
        (by
          linarith : r + 1 ≠ 0)]
      ring
    apply integrable_on_deriv_of_nonneg hc _ hderiv
    · intro x hx
      apply rpow_nonneg_of_nonneg hx.1.le
      
    · refine' (continuous_on_id.rpow_const _).div_const
      intro x hx
      right
      linarith
      
  intro c
  rcases le_totalₓ 0 c with (hc | hc)
  · exact this c hc
    
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    have m :=
      (this (-c)
            (by
              linarith)).smul
        (cos (r * π))
    rw [interval_integrable_iff] at m⊢
    refine' m.congr_fun _ measurable_set_Ioc
    intro x hx
    rw
      [interval_oc_of_le
        (by
          linarith : 0 ≤ -c)] at
      hx
    simp only [← Pi.smul_apply, ← Algebra.id.smul_eq_mul, ← log_neg_eq_log, ← mul_comm, ← rpow_def_of_pos hx.1, ←
      rpow_def_of_neg
        (by
          linarith [hx.1] : -x < 0)]
    

theorem interval_integrable_cpow {r : ℂ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) volume a b := by
  refine' (complex.continuous_of_real.continuous_on.cpow_const _).IntervalIntegrable
  intro c hc
  left
  exact_mod_cast lt_of_lt_of_leₓ (lt_minₓ ha hb) hc.left

@[simp]
theorem interval_integrable_id : IntervalIntegrable (fun x => x) μ a b :=
  continuous_id.IntervalIntegrable a b

@[simp]
theorem interval_integrable_const : IntervalIntegrable (fun x => c) μ a b :=
  continuous_const.IntervalIntegrable a b

@[simp]
theorem IntervalIntegrable.const_mul (h : IntervalIntegrable f ν a b) : IntervalIntegrable (fun x => c * f x) ν a b :=
  by
  convert h.smul c

@[simp]
theorem IntervalIntegrable.mul_const (h : IntervalIntegrable f ν a b) : IntervalIntegrable (fun x => f x * c) ν a b :=
  by
  simp only [← mul_comm, ← interval_integrable.const_mul c h]

@[simp]
theorem IntervalIntegrable.div (h : IntervalIntegrable f ν a b) : IntervalIntegrable (fun x => f x / c) ν a b :=
  IntervalIntegrable.mul_const c⁻¹ h

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_integrable_one_div
    (h : ∀ x : ℝ, x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" → f x ≠ 0)
    (hf : ContinuousOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    IntervalIntegrable (fun x => 1 / f x) μ a b :=
  (continuous_on_const.div hf h).IntervalIntegrable

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem interval_integrable_inv
    (h : ∀ x : ℝ, x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" → f x ≠ 0)
    (hf : ContinuousOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    IntervalIntegrable (fun x => (f x)⁻¹) μ a b := by
  simpa only [← one_div] using interval_integrable_one_div h hf

@[simp]
theorem interval_integrable_exp : IntervalIntegrable exp μ a b :=
  continuous_exp.IntervalIntegrable a b

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem IntervalIntegrable.log
    (hf : ContinuousOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (h : ∀ x : ℝ, x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" → f x ≠ 0) :
    IntervalIntegrable (fun x => log (f x)) μ a b :=
  (ContinuousOn.log hf h).IntervalIntegrable

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem interval_integrable_log
    (h : (0 : ℝ) ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    IntervalIntegrable log μ a b :=
  (IntervalIntegrable.log continuous_on_id) fun x hx => ne_of_mem_of_not_mem hx h

@[simp]
theorem interval_integrable_sin : IntervalIntegrable sin μ a b :=
  continuous_sin.IntervalIntegrable a b

@[simp]
theorem interval_integrable_cos : IntervalIntegrable cos μ a b :=
  continuous_cos.IntervalIntegrable a b

theorem interval_integrable_one_div_one_add_sq : IntervalIntegrable (fun x : ℝ => 1 / (1 + x ^ 2)) μ a b := by
  refine' (continuous_const.div _ fun x => _).IntervalIntegrable a b
  · continuity
    
  · nlinarith
    

@[simp]
theorem interval_integrable_inv_one_add_sq : IntervalIntegrable (fun x : ℝ => (1 + x ^ 2)⁻¹) μ a b := by
  simpa only [← one_div] using interval_integrable_one_div_one_add_sq

/-! ### Integrals of the form `c * ∫ x in a..b, f (c * x + d)` -/


@[simp]
theorem mul_integral_comp_mul_right : (c * ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x :=
  smul_integral_comp_mul_right f c

@[simp]
theorem mul_integral_comp_mul_left : (c * ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x :=
  smul_integral_comp_mul_left f c

@[simp]
theorem inv_mul_integral_comp_div : (c⁻¹ * ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x :=
  inv_smul_integral_comp_div f c

@[simp]
theorem mul_integral_comp_mul_add : (c * ∫ x in a..b, f (c * x + d)) = ∫ x in c * a + d..c * b + d, f x :=
  smul_integral_comp_mul_add f c d

@[simp]
theorem mul_integral_comp_add_mul : (c * ∫ x in a..b, f (d + c * x)) = ∫ x in d + c * a..d + c * b, f x :=
  smul_integral_comp_add_mul f c d

@[simp]
theorem inv_mul_integral_comp_div_add : (c⁻¹ * ∫ x in a..b, f (x / c + d)) = ∫ x in a / c + d..b / c + d, f x :=
  inv_smul_integral_comp_div_add f c d

@[simp]
theorem inv_mul_integral_comp_add_div : (c⁻¹ * ∫ x in a..b, f (d + x / c)) = ∫ x in d + a / c..d + b / c, f x :=
  inv_smul_integral_comp_add_div f c d

@[simp]
theorem mul_integral_comp_mul_sub : (c * ∫ x in a..b, f (c * x - d)) = ∫ x in c * a - d..c * b - d, f x :=
  smul_integral_comp_mul_sub f c d

@[simp]
theorem mul_integral_comp_sub_mul : (c * ∫ x in a..b, f (d - c * x)) = ∫ x in d - c * b..d - c * a, f x :=
  smul_integral_comp_sub_mul f c d

@[simp]
theorem inv_mul_integral_comp_div_sub : (c⁻¹ * ∫ x in a..b, f (x / c - d)) = ∫ x in a / c - d..b / c - d, f x :=
  inv_smul_integral_comp_div_sub f c d

@[simp]
theorem inv_mul_integral_comp_sub_div : (c⁻¹ * ∫ x in a..b, f (d - x / c)) = ∫ x in d - b / c..d - a / c, f x :=
  inv_smul_integral_comp_sub_div f c d

end intervalIntegral

open intervalIntegral

/-! ### Integrals of simple functions -/


-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem integral_rpow {r : ℝ}
    (h : -1 < r ∨ r ≠ -1 ∧ (0 : ℝ) ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    (∫ x in a..b, x ^ r) = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  rw [sub_div]
  have hderiv : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x : ℝ => x ^ (r + 1) / (r + 1)) (x ^ r) x := by
    intro x hx
    convert (Real.has_deriv_at_rpow_const (Or.inl hx)).div_const (r + 1)
    rw [add_sub_cancel, mul_div_cancel_left]
    contrapose! h
    rw [← eq_neg_iff_add_eq_zero] at h
    rw [h]
    tauto
  cases h
  · suffices ∀ c : ℝ, (∫ x in 0 ..c, x ^ r) = c ^ (r + 1) / (r + 1) by
      rw [← integral_add_adjacent_intervals (interval_integrable_rpow' h) (interval_integrable_rpow' h), this b]
      have t := this a
      rw [integral_symm] at t
      apply_fun fun x => -x  at t
      rw [neg_negₓ] at t
      rw [t]
      ring
    intro c
    rcases le_totalₓ 0 c with (hc | hc)
    · convert integral_eq_sub_of_has_deriv_at_of_le hc _ (fun x hx => hderiv x hx.1.ne') _
      · rw [zero_rpow]
        ring
        linarith
        
      · apply ContinuousAt.continuous_on
        intro x hx
        refine' (continuous_at_id.rpow_const _).div_const
        right
        linarith
        
      apply interval_integrable_rpow' h
      
    · rw [integral_symm]
      symm
      rw [eq_neg_iff_eq_neg]
      convert integral_eq_sub_of_has_deriv_at_of_le hc _ (fun x hx => hderiv x hx.2.Ne) _
      · rw [zero_rpow]
        ring
        linarith
        
      · apply ContinuousAt.continuous_on
        intro x hx
        refine' (continuous_at_id.rpow_const _).div_const
        right
        linarith
        
      apply interval_integrable_rpow' h
      
    
  · have hderiv' :
      ∀ x : ℝ,
        x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" →
          HasDerivAt (fun x : ℝ => x ^ (r + 1) / (r + 1)) (x ^ r) x :=
      by
      intro x hx
      apply hderiv x
      exact ne_of_mem_of_not_mem hx h.2
    exact integral_eq_sub_of_has_deriv_at hderiv' (interval_integrable_rpow (Or.inr h.2))
    

theorem integral_cpow {r : ℂ} (ha : 0 < a) (hb : 0 < b) (hr : r ≠ -1) :
    (∫ x : ℝ in a..b, (x : ℂ) ^ r) = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  suffices ∀, ∀ x ∈ Set.Interval a b, ∀, HasDerivAt (fun x : ℝ => (x : ℂ) ^ (r + 1) / (r + 1)) (x ^ r) x by
    rw [sub_div]
    exact integral_eq_sub_of_has_deriv_at this (interval_integrable_cpow ha hb)
  intro x hx
  suffices HasDerivAt (fun z : ℂ => z ^ (r + 1) / (r + 1)) (x ^ r) x by
    simpa using HasDerivAt.comp x this complex.of_real_clm.has_deriv_at
  have hx' : 0 < (x : ℂ).re ∨ (x : ℂ).im ≠ 0 := by
    left
    norm_cast
    calc 0 < min a b := lt_minₓ ha hb _ ≤ x := hx.left
  convert ((has_deriv_at_id (x : ℂ)).cpow_const hx').div_const (r + 1)
  simp only [← id.def, ← add_sub_cancel, ← mul_oneₓ]
  rw [mul_comm, mul_div_cancel]
  contrapose! hr
  rwa [add_eq_zero_iff_eq_neg] at hr

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem integral_zpow {n : ℤ}
    (h : 0 ≤ n ∨ n ≠ -1 ∧ (0 : ℝ) ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    (∫ x in a..b, x ^ n) = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  replace h :
    -1 < (n : ℝ) ∨
      (n : ℝ) ≠ -1 ∧ (0 : ℝ) ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"
  · exact_mod_cast h
    
  exact_mod_cast integral_rpow h

@[simp]
theorem integral_pow : (∫ x in a..b, x ^ n) = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  simpa using integral_zpow (Or.inl (Int.coe_nat_nonneg n))

/-- Integral of `|x - a| ^ n` over `Ι a b`. This integral appears in the proof of the
Picard-Lindelöf/Cauchy-Lipschitz theorem. -/
theorem integral_pow_abs_sub_interval_oc : (∫ x in Ι a b, abs (x - a) ^ n) = abs (b - a) ^ (n + 1) / (n + 1) := by
  cases' le_or_ltₓ a b with hab hab
  · calc (∫ x in Ι a b, abs (x - a) ^ n) = ∫ x in a..b, abs (x - a) ^ n := by
        rw [interval_oc_of_le hab, ← integral_of_le hab]_ = ∫ x in 0 ..b - a, x ^ n := by
        simp only [← integral_comp_sub_right fun x => abs x ^ n, ← sub_self]
        refine' integral_congr fun x hx => congr_arg2ₓ Pow.pow (abs_of_nonneg <| _) rfl
        rw [interval_of_le (sub_nonneg.2 hab)] at hx
        exact hx.1_ = abs (b - a) ^ (n + 1) / (n + 1) := by
        simp [← abs_of_nonneg (sub_nonneg.2 hab)]
    
  · calc (∫ x in Ι a b, abs (x - a) ^ n) = ∫ x in b..a, abs (x - a) ^ n := by
        rw [interval_oc_of_lt hab, ← integral_of_le hab.le]_ = ∫ x in b - a..0, -x ^ n := by
        simp only [← integral_comp_sub_right fun x => abs x ^ n, ← sub_self]
        refine' integral_congr fun x hx => congr_arg2ₓ Pow.pow (abs_of_nonpos <| _) rfl
        rw [interval_of_le (sub_nonpos.2 hab.le)] at hx
        exact hx.2_ = abs (b - a) ^ (n + 1) / (n + 1) := by
        simp [← integral_comp_neg fun x => x ^ n, ← abs_of_neg (sub_neg.2 hab)]
    

@[simp]
theorem integral_id : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 := by
  simpa using integral_pow 1

@[simp]
theorem integral_one : (∫ x in a..b, (1 : ℝ)) = b - a := by
  simp only [← mul_oneₓ, ← smul_eq_mul, ← integral_const]

theorem integral_const_on_unit_interval : (∫ x in a..a + 1, b) = b := by
  simp

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem integral_inv (h : (0 : ℝ) ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    (∫ x in a..b, x⁻¹) = log (b / a) := by
  have h' := fun x hx => ne_of_mem_of_not_mem hx h
  rw
    [integral_deriv_eq_sub' _ deriv_log' (fun x hx => differentiable_at_log (h' x hx))
      (continuous_on_inv₀.mono <| subset_compl_singleton_iff.mpr h),
    log_div (h' b right_mem_interval) (h' a left_mem_interval)]

@[simp]
theorem integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : (∫ x in a..b, x⁻¹) = log (b / a) :=
  integral_inv <| not_mem_interval_of_lt ha hb

@[simp]
theorem integral_inv_of_neg (ha : a < 0) (hb : b < 0) : (∫ x in a..b, x⁻¹) = log (b / a) :=
  integral_inv <| not_mem_interval_of_gt ha hb

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem integral_one_div (h : (0 : ℝ) ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    (∫ x : ℝ in a..b, 1 / x) = log (b / a) := by
  simp only [← one_div, ← integral_inv h]

theorem integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) : (∫ x : ℝ in a..b, 1 / x) = log (b / a) := by
  simp only [← one_div, ← integral_inv_of_pos ha hb]

theorem integral_one_div_of_neg (ha : a < 0) (hb : b < 0) : (∫ x : ℝ in a..b, 1 / x) = log (b / a) := by
  simp only [← one_div, ← integral_inv_of_neg ha hb]

@[simp]
theorem integral_exp : (∫ x in a..b, exp x) = exp b - exp a := by
  rw [integral_deriv_eq_sub'] <;> norm_num [← continuous_on_exp]

theorem integral_exp_mul_complex {c : ℂ} (hc : c ≠ 0) :
    (∫ x in a..b, Complex.exp (c * x)) = (Complex.exp (c * b) - Complex.exp (c * a)) / c := by
  have D : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
    intro x
    conv => congr skip rw [← mul_div_cancel (Complex.exp (c * x)) hc]
    convert ((Complex.has_deriv_at_exp _).comp x _).div_const c using 1
    simpa only [← Complex.of_real_clm_apply, ← Complex.of_real_one, ← one_mulₓ, ← mul_oneₓ, ← mul_comm] using
      complex.of_real_clm.has_deriv_at.mul_const c
  rw [integral_deriv_eq_sub' _ (funext fun x => (D x).deriv) fun x hx => (D x).DifferentiableAt]
  · ring_nf
    
  · apply Continuous.continuous_on
    continuity
    

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem integral_log (h : (0 : ℝ) ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    (∫ x in a..b, log x) = b * log b - a * log a - b + a := by
  obtain ⟨h', heq⟩ := fun x hx => ne_of_mem_of_not_mem hx h, fun x hx => mul_inv_cancel (h' x hx)
  convert
      integral_mul_deriv_eq_deriv_mul (fun x hx => has_deriv_at_log (h' x hx)) (fun x hx => has_deriv_at_id x)
        (continuous_on_inv₀.mono <| subset_compl_singleton_iff.mpr h).IntervalIntegrable
        continuous_on_const.interval_integrable using
      1 <;>
    simp [← integral_congr HEq, ← mul_comm, sub_add]

@[simp]
theorem integral_log_of_pos (ha : 0 < a) (hb : 0 < b) : (∫ x in a..b, log x) = b * log b - a * log a - b + a :=
  integral_log <| not_mem_interval_of_lt ha hb

@[simp]
theorem integral_log_of_neg (ha : a < 0) (hb : b < 0) : (∫ x in a..b, log x) = b * log b - a * log a - b + a :=
  integral_log <| not_mem_interval_of_gt ha hb

@[simp]
theorem integral_sin : (∫ x in a..b, sin x) = cos a - cos b := by
  rw [integral_deriv_eq_sub' fun x => -cos x] <;> norm_num [← continuous_on_sin]

@[simp]
theorem integral_cos : (∫ x in a..b, cos x) = sin b - sin a := by
  rw [integral_deriv_eq_sub'] <;> norm_num [← continuous_on_cos]

theorem integral_cos_sq_sub_sin_sq : (∫ x in a..b, cos x ^ 2 - sin x ^ 2) = sin b * cos b - sin a * cos a := by
  simpa only [← sq, ← sub_eq_add_neg, ← neg_mul_eq_mul_neg] using
    integral_deriv_mul_eq_sub (fun x hx => has_deriv_at_sin x) (fun x hx => has_deriv_at_cos x)
      continuous_on_cos.interval_integrable continuous_on_sin.neg.interval_integrable

@[simp]
theorem integral_inv_one_add_sq : (∫ x : ℝ in a..b, (1 + x ^ 2)⁻¹) = arctan b - arctan a := by
  simp only [one_div]
  refine' integral_deriv_eq_sub' _ _ _ (continuous_const.div _ fun x => _).ContinuousOn
  · norm_num
    
  · norm_num
    
  · continuity
    
  · nlinarith
    

theorem integral_one_div_one_add_sq : (∫ x : ℝ in a..b, 1 / (1 + x ^ 2)) = arctan b - arctan a := by
  simp only [← one_div, ← integral_inv_one_add_sq]

/-! ### Integral of `sin x ^ n` -/


-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem integral_sin_pow_aux :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b + (n + 1) * ∫ x in a..b, sin x ^ n) -
        (n + 1) * ∫ x in a..b, sin x ^ (n + 2) :=
  by
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
  have h : ∀ α β γ : ℝ, α * (β * α * γ) = β * (α * α * γ) := fun α β γ => by
    ring
  have hu : ∀, ∀ x ∈ _, ∀, HasDerivAt (fun y => sin y ^ (n + 1)) ((n + 1 : ℕ) * cos x * sin x ^ n) x := fun x hx => by
    simpa only [← mul_right_commₓ] using (has_deriv_at_sin x).pow (n + 1)
  have hv :
    ∀,
      ∀ x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)",
        ∀, HasDerivAt (-cos) (sin x) x :=
    fun x hx => by
    simpa only [← neg_negₓ] using (has_deriv_at_cos x).neg
  have H := integral_mul_deriv_eq_deriv_mul hu hv _ _
  calc (∫ x in a..b, sin x ^ (n + 2)) = ∫ x in a..b, sin x ^ (n + 1) * sin x := by
      simp only [← pow_succ'ₓ]_ = C + (n + 1) * ∫ x in a..b, cos x ^ 2 * sin x ^ n := by
      simp [← H, ← h, ← sq]_ = C + (n + 1) * ∫ x in a..b, sin x ^ n - sin x ^ (n + 2) := by
      simp [← cos_sq', ← sub_mul, pow_addₓ, ←
        add_commₓ]_ = (C + (n + 1) * ∫ x in a..b, sin x ^ n) - (n + 1) * ∫ x in a..b, sin x ^ (n + 2) :=
      by
      rw [integral_sub, mul_sub, add_sub_assoc] <;> apply Continuous.interval_integrable <;> continuity
  all_goals
    apply Continuous.interval_integrable
    continuity

/-- The reduction formula for the integral of `sin x ^ n` for any natural `n ≥ 2`. -/
theorem integral_sin_pow :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b) / (n + 2) + (n + 1) / (n + 2) * ∫ x in a..b, sin x ^ n :=
  by
  have : (n : ℝ) + 2 ≠ 0 := by
    exact_mod_cast succ_ne_zero n.succ
  field_simp
  convert eq_sub_iff_add_eq.mp (integral_sin_pow_aux n)
  ring

@[simp]
theorem integral_sin_sq : (∫ x in a..b, sin x ^ 2) = (sin a * cos a - sin b * cos b + b - a) / 2 := by
  field_simp [← integral_sin_pow, ← add_sub_assoc]

theorem integral_sin_pow_odd : (∫ x in 0 ..π, sin x ^ (2 * n + 1)) = 2 * ∏ i in range n, (2 * i + 2) / (2 * i + 3) := by
  induction' n with k ih
  · norm_num
    
  rw [prod_range_succ_comm, mul_left_commₓ, ← ih, mul_succ, integral_sin_pow]
  norm_cast
  simp' [-cast_add] with field_simps

theorem integral_sin_pow_even : (∫ x in 0 ..π, sin x ^ (2 * n)) = π * ∏ i in range n, (2 * i + 1) / (2 * i + 2) := by
  induction' n with k ih
  · simp
    
  rw [prod_range_succ_comm, mul_left_commₓ, ← ih, mul_succ, integral_sin_pow]
  norm_cast
  simp' [-cast_add] with field_simps

theorem integral_sin_pow_pos : 0 < ∫ x in 0 ..π, sin x ^ n := by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩ <;>
    simp only [← integral_sin_pow_even, ← integral_sin_pow_odd] <;>
      refine'
          mul_pos
            (by
              norm_num [← pi_pos])
            (prod_pos fun n hn => div_pos _ _) <;>
        norm_cast <;> linarith

theorem integral_sin_pow_succ_le : (∫ x in 0 ..π, sin x ^ (n + 1)) ≤ ∫ x in 0 ..π, sin x ^ n := by
  let H := fun x h => pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc h) (sin_le_one x) (n.le_add_right 1)
  refine' integral_mono_on pi_pos.le _ _ H <;> exact (continuous_sin.pow _).IntervalIntegrable 0 π

theorem integral_sin_pow_antitone : Antitone fun n : ℕ => ∫ x in 0 ..π, sin x ^ n :=
  antitone_nat_of_succ_le integral_sin_pow_succ_le

/-! ### Integral of `cos x ^ n` -/


-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem integral_cos_pow_aux :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a + (n + 1) * ∫ x in a..b, cos x ^ n) -
        (n + 1) * ∫ x in a..b, cos x ^ (n + 2) :=
  by
  let C := cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a
  have h : ∀ α β γ : ℝ, α * (β * α * γ) = β * (α * α * γ) := fun α β γ => by
    ring
  have hu : ∀, ∀ x ∈ _, ∀, HasDerivAt (fun y => cos y ^ (n + 1)) (-(n + 1 : ℕ) * sin x * cos x ^ n) x := fun x hx => by
    simpa only [← mul_right_commₓ, ← neg_mul, ← mul_neg] using (has_deriv_at_cos x).pow (n + 1)
  have hv :
    ∀,
      ∀ x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)",
        ∀, HasDerivAt sin (cos x) x :=
    fun x hx => has_deriv_at_sin x
  have H := integral_mul_deriv_eq_deriv_mul hu hv _ _
  calc (∫ x in a..b, cos x ^ (n + 2)) = ∫ x in a..b, cos x ^ (n + 1) * cos x := by
      simp only [← pow_succ'ₓ]_ = C + (n + 1) * ∫ x in a..b, sin x ^ 2 * cos x ^ n := by
      simp [← H, ← h, ← sq, -neg_add_rev]_ = C + (n + 1) * ∫ x in a..b, cos x ^ n - cos x ^ (n + 2) := by
      simp [← sin_sq, ← sub_mul, pow_addₓ, ←
        add_commₓ]_ = (C + (n + 1) * ∫ x in a..b, cos x ^ n) - (n + 1) * ∫ x in a..b, cos x ^ (n + 2) :=
      by
      rw [integral_sub, mul_sub, add_sub_assoc] <;> apply Continuous.interval_integrable <;> continuity
  all_goals
    apply Continuous.interval_integrable
    continuity

/-- The reduction formula for the integral of `cos x ^ n` for any natural `n ≥ 2`. -/
theorem integral_cos_pow :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a) / (n + 2) + (n + 1) / (n + 2) * ∫ x in a..b, cos x ^ n :=
  by
  have : (n : ℝ) + 2 ≠ 0 := by
    exact_mod_cast succ_ne_zero n.succ
  field_simp
  convert eq_sub_iff_add_eq.mp (integral_cos_pow_aux n)
  ring

@[simp]
theorem integral_cos_sq : (∫ x in a..b, cos x ^ 2) = (cos b * sin b - cos a * sin a + b - a) / 2 := by
  field_simp [← integral_cos_pow, ← add_sub_assoc]

/-! ### Integral of `sin x ^ m * cos x ^ n` -/


/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `n` is odd. -/
theorem integral_sin_pow_mul_cos_pow_odd (m n : ℕ) :
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) = ∫ u in sin a..sin b, u ^ m * (1 - u ^ 2) ^ n :=
  have hc : Continuous fun u : ℝ => u ^ m * (1 - u ^ 2) ^ n := by
    continuity
  calc
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) = ∫ x in a..b, sin x ^ m * (1 - sin x ^ 2) ^ n * cos x := by
      simp only [← pow_succ'ₓ, mul_assoc, ← pow_mulₓ, ← cos_sq']
    _ = ∫ u in sin a..sin b, u ^ m * (1 - u ^ 2) ^ n :=
      integral_comp_mul_deriv (fun x hx => has_deriv_at_sin x) continuous_on_cos hc
    

/-- The integral of `sin x * cos x`, given in terms of sin².
  See `integral_sin_mul_cos₂` below for the integral given in terms of cos². -/
@[simp]
theorem integral_sin_mul_cos₁ : (∫ x in a..b, sin x * cos x) = (sin b ^ 2 - sin a ^ 2) / 2 := by
  simpa using integral_sin_pow_mul_cos_pow_odd 1 0

@[simp]
theorem integral_sin_sq_mul_cos : (∫ x in a..b, sin x ^ 2 * cos x) = (sin b ^ 3 - sin a ^ 3) / 3 := by
  simpa using integral_sin_pow_mul_cos_pow_odd 2 0

@[simp]
theorem integral_cos_pow_three : (∫ x in a..b, cos x ^ 3) = sin b - sin a - (sin b ^ 3 - sin a ^ 3) / 3 := by
  simpa using integral_sin_pow_mul_cos_pow_odd 0 1

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` is odd. -/
theorem integral_sin_pow_odd_mul_cos_pow (m n : ℕ) :
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) = ∫ u in cos b..cos a, u ^ n * (1 - u ^ 2) ^ m :=
  have hc : Continuous fun u : ℝ => u ^ n * (1 - u ^ 2) ^ m := by
    continuity
  calc
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) = -∫ x in b..a, sin x ^ (2 * m + 1) * cos x ^ n := by
      rw [integral_symm]
    _ = ∫ x in b..a, (1 - cos x ^ 2) ^ m * -sin x * cos x ^ n := by
      simp [← pow_succ'ₓ, ← pow_mulₓ, ← sin_sq]
    _ = ∫ x in b..a, cos x ^ n * (1 - cos x ^ 2) ^ m * -sin x := by
      congr
      ext
      ring
    _ = ∫ u in cos b..cos a, u ^ n * (1 - u ^ 2) ^ m :=
      integral_comp_mul_deriv (fun x hx => has_deriv_at_cos x) continuous_on_sin.neg hc
    

/-- The integral of `sin x * cos x`, given in terms of cos².
See `integral_sin_mul_cos₁` above for the integral given in terms of sin². -/
theorem integral_sin_mul_cos₂ : (∫ x in a..b, sin x * cos x) = (cos a ^ 2 - cos b ^ 2) / 2 := by
  simpa using integral_sin_pow_odd_mul_cos_pow 0 1

@[simp]
theorem integral_sin_mul_cos_sq : (∫ x in a..b, sin x * cos x ^ 2) = (cos a ^ 3 - cos b ^ 3) / 3 := by
  simpa using integral_sin_pow_odd_mul_cos_pow 0 2

@[simp]
theorem integral_sin_pow_three : (∫ x in a..b, sin x ^ 3) = cos a - cos b - (cos a ^ 3 - cos b ^ 3) / 3 := by
  simpa using integral_sin_pow_odd_mul_cos_pow 1 0

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` and `n` are both even. -/
theorem integral_sin_pow_even_mul_cos_pow_even (m n : ℕ) :
    (∫ x in a..b, sin x ^ (2 * m) * cos x ^ (2 * n)) =
      ∫ x in a..b, ((1 - cos (2 * x)) / 2) ^ m * ((1 + cos (2 * x)) / 2) ^ n :=
  by
  field_simp [← pow_mulₓ, ← sin_sq, ← cos_sq, sub_sub, ←
    (by
      ring : (2 : ℝ) - 1 = 1)]

@[simp]
theorem integral_sin_sq_mul_cos_sq :
    (∫ x in a..b, sin x ^ 2 * cos x ^ 2) = (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 := by
  convert integral_sin_pow_even_mul_cos_pow_even 1 1 using 1
  have h1 : ∀ c : ℝ, (1 - c) / 2 * ((1 + c) / 2) = (1 - c ^ 2) / 4 := fun c => by
    ring
  have h2 : Continuous fun x => cos (2 * x) ^ 2 := by
    continuity
  have h3 : ∀ x, cos x * sin x = sin (2 * x) / 2 := by
    intro
    rw [sin_two_mul]
    ring
  have h4 : ∀ d : ℝ, 2 * (2 * d) = 4 * d := fun d => by
    ring
  simp [← h1, ← h2.interval_integrable, ← integral_comp_mul_left fun x => cos x ^ 2, ← h3, ← h4]
  ring

