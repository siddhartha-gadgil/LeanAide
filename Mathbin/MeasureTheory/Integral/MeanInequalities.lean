/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.MeasureTheory.Integral.Lebesgue
import Mathbin.Analysis.MeanInequalities
import Mathbin.Analysis.MeanInequalitiesPow
import Mathbin.MeasureTheory.Function.SpecialFunctions

/-!
# Mean value inequalities for integrals

In this file we prove several inequalities on integrals, notably the Hölder inequality and
the Minkowski inequality. The versions for finite sums are in `analysis.mean_inequalities`.

## Main results

Hölder's inequality for the Lebesgue integral of `ℝ≥0∞` and `ℝ≥0` functions: we prove
`∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q` conjugate real exponents
and `α→(e)nnreal` functions in two cases,
* `ennreal.lintegral_mul_le_Lp_mul_Lq` : ℝ≥0∞ functions,
* `nnreal.lintegral_mul_le_Lp_mul_Lq`  : ℝ≥0 functions.

Minkowski's inequality for the Lebesgue integral of measurable functions with `ℝ≥0∞` values:
we prove `(∫ (f + g)^p ∂μ) ^ (1/p) ≤ (∫ f^p ∂μ) ^ (1/p) + (∫ g^p ∂μ) ^ (1/p)` for `1 ≤ p`.
-/


section Lintegral

/-!
### Hölder's inequality for the Lebesgue integral of ℝ≥0∞ and nnreal functions

We prove `∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q`
conjugate real exponents and `α→(e)nnreal` functions in several cases, the first two being useful
only to prove the more general results:
* `ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one` : ℝ≥0∞ functions for which the
    integrals on the right are equal to 1,
* `ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top` : ℝ≥0∞ functions for which the
    integrals on the right are neither ⊤ nor 0,
* `ennreal.lintegral_mul_le_Lp_mul_Lq` : ℝ≥0∞ functions,
* `nnreal.lintegral_mul_le_Lp_mul_Lq`  : nnreal functions.
-/


noncomputable section

open Classical BigOperators Nnreal Ennreal

open MeasureTheory

variable {α : Type _} [MeasurableSpace α] {μ : Measureₓ α}

namespace Ennreal

theorem lintegral_mul_le_one_of_lintegral_rpow_eq_one {p q : ℝ} (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0∞}
    (hf : AeMeasurable f μ) (hf_norm : (∫⁻ a, f a ^ p ∂μ) = 1) (hg_norm : (∫⁻ a, g a ^ q ∂μ) = 1) :
    (∫⁻ a, (f * g) a ∂μ) ≤ 1 := by
  calc (∫⁻ a : α, (f * g) a ∂μ) ≤ ∫⁻ a : α, f a ^ p / Ennreal.ofReal p + g a ^ q / Ennreal.ofReal q ∂μ :=
      lintegral_mono fun a => young_inequality (f a) (g a) hpq _ = 1 := by
      simp only [← div_eq_mul_inv]
      rw [lintegral_add_left']
      · rw [lintegral_mul_const'' _ (hf.pow_const p), lintegral_mul_const', hf_norm, hg_norm, ← div_eq_mul_inv, ←
          div_eq_mul_inv, hpq.inv_add_inv_conj_ennreal]
        simp [← hpq.symm.pos]
        
      · exact (hf.pow_const _).mul_const _
        

/-- Function multiplied by the inverse of its p-seminorm `(∫⁻ f^p ∂μ) ^ 1/p`-/
def funMulInvSnorm (f : α → ℝ≥0∞) (p : ℝ) (μ : Measureₓ α) : α → ℝ≥0∞ := fun a => f a * ((∫⁻ c, f c ^ p ∂μ) ^ (1 / p))⁻¹

theorem fun_eq_fun_mul_inv_snorm_mul_snorm {p : ℝ} (f : α → ℝ≥0∞) (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0)
    (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) {a : α} : f a = funMulInvSnorm f p μ a * (∫⁻ c, f c ^ p ∂μ) ^ (1 / p) := by
  simp [← fun_mul_inv_snorm, ← mul_assoc, ← inv_mul_cancel, ← hf_nonzero, ← hf_top]

theorem fun_mul_inv_snorm_rpow {p : ℝ} (hp0 : 0 < p) {f : α → ℝ≥0∞} {a : α} :
    funMulInvSnorm f p μ a ^ p = f a ^ p * (∫⁻ c, f c ^ p ∂μ)⁻¹ := by
  rw [fun_mul_inv_snorm, mul_rpow_of_nonneg _ _ (le_of_ltₓ hp0)]
  suffices h_inv_rpow : ((∫⁻ c : α, f c ^ p ∂μ) ^ (1 / p))⁻¹ ^ p = (∫⁻ c : α, f c ^ p ∂μ)⁻¹
  · rw [h_inv_rpow]
    
  rw [inv_rpow, ← rpow_mul, one_div_mul_cancel hp0.ne', rpow_one]

theorem lintegral_rpow_fun_mul_inv_snorm_eq_one {p : ℝ} (hp0_lt : 0 < p) {f : α → ℝ≥0∞}
    (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ c, funMulInvSnorm f p μ c ^ p ∂μ) = 1 := by
  simp_rw [fun_mul_inv_snorm_rpow hp0_lt]
  rw [lintegral_mul_const', mul_inv_cancel hf_nonzero hf_top]
  rwa [inv_ne_top]

/-- Hölder's inequality in case of finite non-zero integrals -/
theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top {p q : ℝ} (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0∞}
    (hf : AeMeasurable f μ) (hf_nontop : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) (hg_nontop : (∫⁻ a, g a ^ q ∂μ) ≠ ⊤)
    (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0) (hg_nonzero : (∫⁻ a, g a ^ q ∂μ) ≠ 0) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  let npf := (∫⁻ c : α, f c ^ p ∂μ) ^ (1 / p)
  let nqg := (∫⁻ c : α, g c ^ q ∂μ) ^ (1 / q)
  calc (∫⁻ a : α, (f * g) a ∂μ) = ∫⁻ a : α, (fun_mul_inv_snorm f p μ * fun_mul_inv_snorm g q μ) a * (npf * nqg) ∂μ := by
      refine' lintegral_congr fun a => _
      rw [Pi.mul_apply, fun_eq_fun_mul_inv_snorm_mul_snorm f hf_nonzero hf_nontop,
        fun_eq_fun_mul_inv_snorm_mul_snorm g hg_nonzero hg_nontop, Pi.mul_apply]
      ring _ ≤ npf * nqg := by
      rw
        [lintegral_mul_const' (npf * nqg) _
          (by
            simp [← hf_nontop, ← hg_nontop, ← hf_nonzero, ← hg_nonzero])]
      nth_rw 1[← one_mulₓ (npf * nqg)]
      refine' mul_le_mul _ (le_reflₓ (npf * nqg))
      have hf1 := lintegral_rpow_fun_mul_inv_snorm_eq_one hpq.pos hf_nonzero hf_nontop
      have hg1 := lintegral_rpow_fun_mul_inv_snorm_eq_one hpq.symm.pos hg_nonzero hg_nontop
      exact lintegral_mul_le_one_of_lintegral_rpow_eq_one hpq (hf.mul_const _) hf1 hg1

theorem ae_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0 : 0 ≤ p) {f : α → ℝ≥0∞} (hf : AeMeasurable f μ)
    (hf_zero : (∫⁻ a, f a ^ p ∂μ) = 0) : f =ᵐ[μ] 0 := by
  rw [lintegral_eq_zero_iff' (hf.pow_const p)] at hf_zero
  refine' Filter.Eventually.mp hf_zero (Filter.eventually_of_forall fun x => _)
  dsimp' only
  rw [Pi.zero_apply, ← not_imp_not]
  exact fun hx => (rpow_pos_of_nonneg (pos_iff_ne_zero.2 hx) hp0).ne'

theorem lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0 : 0 ≤ p) {f g : α → ℝ≥0∞} (hf : AeMeasurable f μ)
    (hf_zero : (∫⁻ a, f a ^ p ∂μ) = 0) : (∫⁻ a, (f * g) a ∂μ) = 0 := by
  rw [← @lintegral_zero_fun α _ μ]
  refine' lintegral_congr_ae _
  suffices h_mul_zero : f * g =ᵐ[μ] 0 * g
  · rwa [zero_mul] at h_mul_zero
    
  have hf_eq_zero : f =ᵐ[μ] 0 := ae_eq_zero_of_lintegral_rpow_eq_zero hp0 hf hf_zero
  exact hf_eq_zero.mul (ae_eq_refl g)

theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top {p q : ℝ} (hp0_lt : 0 < p) (hq0 : 0 ≤ q) {f g : α → ℝ≥0∞}
    (hf_top : (∫⁻ a, f a ^ p ∂μ) = ⊤) (hg_nonzero : (∫⁻ a, g a ^ q ∂μ) ≠ 0) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  refine' le_transₓ le_top (le_of_eqₓ _)
  have hp0_inv_lt : 0 < 1 / p := by
    simp [← hp0_lt]
  rw [hf_top, Ennreal.top_rpow_of_pos hp0_inv_lt]
  simp [← hq0, ← hg_nonzero]

/-- Hölder's inequality for functions `α → ℝ≥0∞`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem lintegral_mul_le_Lp_mul_Lq (μ : Measureₓ α) {p q : ℝ} (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0∞}
    (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  by_cases' hf_zero : (∫⁻ a, f a ^ p ∂μ) = 0
  · refine' Eq.trans_le _ (zero_le _)
    exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.nonneg hf hf_zero
    
  by_cases' hg_zero : (∫⁻ a, g a ^ q ∂μ) = 0
  · refine' Eq.trans_le _ (zero_le _)
    rw [mul_comm]
    exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.symm.nonneg hg hg_zero
    
  by_cases' hf_top : (∫⁻ a, f a ^ p ∂μ) = ⊤
  · exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.pos hpq.symm.nonneg hf_top hg_zero
    
  by_cases' hg_top : (∫⁻ a, g a ^ q ∂μ) = ⊤
  · rw [mul_comm, mul_comm ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p))]
    exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.symm.pos hpq.nonneg hg_top hf_zero
    
  -- non-⊤ non-zero case
  exact Ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top hpq hf hf_top hg_top hf_zero hg_zero

theorem lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top {p : ℝ} {f g : α → ℝ≥0∞} (hf : AeMeasurable f μ)
    (hf_top : (∫⁻ a, f a ^ p ∂μ) < ⊤) (hg_top : (∫⁻ a, g a ^ p ∂μ) < ⊤) (hp1 : 1 ≤ p) : (∫⁻ a, (f + g) a ^ p ∂μ) < ⊤ :=
  by
  have hp0_lt : 0 < p := lt_of_lt_of_leₓ zero_lt_one hp1
  have hp0 : 0 ≤ p := le_of_ltₓ hp0_lt
  calc (∫⁻ a : α, (f a + g a) ^ p ∂μ) ≤ ∫⁻ a, (2 : ℝ≥0∞) ^ (p - 1) * f a ^ p + (2 : ℝ≥0∞) ^ (p - 1) * g a ^ p ∂μ := by
      refine' lintegral_mono fun a => _
      dsimp' only
      have h_zero_lt_half_rpow : (0 : ℝ≥0∞) < (1 / 2) ^ p := by
        rw [← Ennreal.zero_rpow_of_pos hp0_lt]
        exact
          Ennreal.rpow_lt_rpow
            (by
              simp [← zero_lt_one])
            hp0_lt
      have h_rw : (1 / 2) ^ p * (2 : ℝ≥0∞) ^ (p - 1) = 1 / 2 := by
        rw [sub_eq_add_neg, Ennreal.rpow_add _ _ Ennreal.two_ne_zero Ennreal.coe_ne_top, ← mul_assoc, ←
          Ennreal.mul_rpow_of_nonneg _ _ hp0, one_div, Ennreal.inv_mul_cancel Ennreal.two_ne_zero Ennreal.coe_ne_top,
          Ennreal.one_rpow, one_mulₓ, Ennreal.rpow_neg_one]
      rw [← Ennreal.mul_le_mul_left (ne_of_ltₓ h_zero_lt_half_rpow).symm _]
      · rw [mul_addₓ, ← mul_assoc, ← mul_assoc, h_rw, ← Ennreal.mul_rpow_of_nonneg _ _ hp0, mul_addₓ]
        refine' Ennreal.rpow_arith_mean_le_arith_mean2_rpow (1 / 2 : ℝ≥0∞) (1 / 2 : ℝ≥0∞) (f a) (g a) _ hp1
        rw [Ennreal.div_add_div_same, one_add_one_eq_two, Ennreal.div_self Ennreal.two_ne_zero Ennreal.coe_ne_top]
        
      · rw [← lt_top_iff_ne_top]
        refine' Ennreal.rpow_lt_top_of_nonneg hp0 _
        rw [one_div, Ennreal.inv_ne_top]
        exact Ennreal.two_ne_zero
        _ < ⊤ :=
      by
      have h_two : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ :=
        Ennreal.rpow_ne_top_of_nonneg
          (by
            simp [← hp1])
          Ennreal.coe_ne_top
      rw [lintegral_add_left', lintegral_const_mul'' _ (hf.pow_const p), lintegral_const_mul' _ _ h_two,
        Ennreal.add_lt_top]
      · exact ⟨Ennreal.mul_lt_top h_two hf_top.ne, Ennreal.mul_lt_top h_two hg_top.ne⟩
        
      · exact (hf.pow_const p).const_mul _
        

theorem lintegral_Lp_mul_le_Lq_mul_Lr {α} [MeasurableSpace α] {p q r : ℝ} (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) (μ : Measureₓ α) {f g : α → ℝ≥0∞} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    (∫⁻ a, (f * g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ a, f a ^ q ∂μ) ^ (1 / q) * (∫⁻ a, g a ^ r ∂μ) ^ (1 / r) := by
  have hp0_ne : p ≠ 0 := (ne_of_ltₓ hp0_lt).symm
  have hp0 : 0 ≤ p := le_of_ltₓ hp0_lt
  have hq0_lt : 0 < q := lt_of_le_of_ltₓ hp0 hpq
  have hq0_ne : q ≠ 0 := (ne_of_ltₓ hq0_lt).symm
  have h_one_div_r : 1 / r = 1 / p - 1 / q := by
    simp [← hpqr]
  have hr0_ne : r ≠ 0 := by
    have hr_inv_pos : 0 < 1 / r := by
      rwa [h_one_div_r, sub_pos, one_div_lt_one_div hq0_lt hp0_lt]
    rw [one_div, _root_.inv_pos] at hr_inv_pos
    exact (ne_of_ltₓ hr_inv_pos).symm
  let p2 := q / p
  let q2 := p2.conjugate_exponent
  have hp2q2 : p2.is_conjugate_exponent q2 :=
    Real.is_conjugate_exponent_conjugate_exponent
      (by
        simp [← lt_div_iff, ← hpq, ← hp0_lt])
  calc (∫⁻ a : α, (f * g) a ^ p ∂μ) ^ (1 / p) = (∫⁻ a : α, f a ^ p * g a ^ p ∂μ) ^ (1 / p) := by
      simp_rw [Pi.mul_apply,
        Ennreal.mul_rpow_of_nonneg _ _
          hp0]_ ≤ ((∫⁻ a, f a ^ (p * p2) ∂μ) ^ (1 / p2) * (∫⁻ a, g a ^ (p * q2) ∂μ) ^ (1 / q2)) ^ (1 / p) :=
      by
      refine'
        Ennreal.rpow_le_rpow _
          (by
            simp [← hp0])
      simp_rw [Ennreal.rpow_mul]
      exact
        Ennreal.lintegral_mul_le_Lp_mul_Lq μ hp2q2 (hf.pow_const _)
          (hg.pow_const _)_ = (∫⁻ a : α, f a ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) :=
      by
      rw
        [@Ennreal.mul_rpow_of_nonneg _ _ (1 / p)
          (by
            simp [← hp0]),
        ← Ennreal.rpow_mul, ← Ennreal.rpow_mul]
      have hpp2 : p * p2 = q := by
        symm
        rw [mul_comm, ← div_eq_iff hp0_ne]
      have hpq2 : p * q2 = r := by
        rw [← inv_invₓ r, ← one_div, ← one_div, h_one_div_r]
        field_simp [← q2, ← Real.conjugateExponent, ← p2, ← hp0_ne, ← hq0_ne]
      simp_rw [div_mul_div_comm, mul_oneₓ, mul_comm p2, mul_comm q2, hpp2, hpq2]

theorem lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow {p q : ℝ} (hpq : p.IsConjugateExponent q)
    {f g : α → ℝ≥0∞} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, f a * g a ^ (p - 1) ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ p ∂μ) ^ (1 / q) := by
  refine' le_transₓ (Ennreal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (hg.pow_const _)) _
  by_cases' hf_zero_rpow : (∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) = 0
  · rw [hf_zero_rpow, zero_mul]
    exact zero_le _
    
  have hf_top_rpow : (∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) ≠ ⊤ := by
    by_contra h
    refine' hf_top _
    have hp_not_neg : ¬p < 0 := by
      simp [← hpq.nonneg]
    simpa [← hpq.pos, ← hp_not_neg] using h
  refine' (Ennreal.mul_le_mul_left hf_zero_rpow hf_top_rpow).mpr (le_of_eqₓ _)
  congr
  ext1 a
  rw [← Ennreal.rpow_mul, hpq.sub_one_mul_conj]

theorem lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add {p q : ℝ} (hpq : p.IsConjugateExponent q)
    {f g : α → ℝ≥0∞} (hf : AeMeasurable f μ) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) (hg : AeMeasurable g μ)
    (hg_top : (∫⁻ a, g a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ≤
      ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) * (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q) :=
  by
  calc (∫⁻ a, (f + g) a ^ p ∂μ) ≤ ∫⁻ a, (f + g) a * (f + g) a ^ (p - 1) ∂μ := by
      refine' lintegral_mono fun a => _
      dsimp' only
      by_cases' h_zero : (f + g) a = 0
      · rw [h_zero, Ennreal.zero_rpow_of_pos hpq.pos]
        exact zero_le _
        
      by_cases' h_top : (f + g) a = ⊤
      · rw [h_top, Ennreal.top_rpow_of_pos hpq.sub_one_pos, Ennreal.top_mul_top]
        exact le_top
        
      refine' le_of_eqₓ _
      nth_rw 1[← Ennreal.rpow_one ((f + g) a)]
      rw [← Ennreal.rpow_add _ _ h_zero h_top,
        add_sub_cancel'_right]_ = (∫⁻ a : α, f a * (f + g) a ^ (p - 1) ∂μ) + ∫⁻ a : α, g a * (f + g) a ^ (p - 1) ∂μ :=
      by
      have h_add_m : AeMeasurable (fun a : α => (f + g) a ^ (p - 1)) μ := (hf.add hg).pow_const _
      have h_add_apply :
        (∫⁻ a : α, (f + g) a * (f + g) a ^ (p - 1) ∂μ) = ∫⁻ a : α, (f a + g a) * (f + g) a ^ (p - 1) ∂μ := rfl
      simp_rw [h_add_apply, add_mulₓ]
      rw
        [lintegral_add_left'
          (hf.mul
            h_add_m)]_ ≤
        ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) * (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q) :=
      by
      rw [add_mulₓ]
      exact
        add_le_add (lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hf (hf.add hg) hf_top)
          (lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hg (hf.add hg) hg_top)

private theorem lintegral_Lp_add_le_aux {p q : ℝ} (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0∞}
    (hf : AeMeasurable f μ) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) (hg : AeMeasurable g μ) (hg_top : (∫⁻ a, g a ^ p ∂μ) ≠ ⊤)
    (h_add_zero : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ 0) (h_add_top : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by
  have hp_not_nonpos : ¬p ≤ 0 := by
    simp [← hpq.pos]
  have htop_rpow : (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≠ ⊤ := by
    by_contra h
    exact
      h_add_top
        (@Ennreal.rpow_eq_top_of_nonneg _ (1 / p)
          (by
            simp [← hpq.nonneg])
          h)
  have h0_rpow : (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≠ 0 := by
    simp [← h_add_zero, ← h_add_top, ← hpq.nonneg, ← hp_not_nonpos, -Pi.add_apply]
  suffices h :
    1 ≤ (∫⁻ a : α, (f + g) a ^ p ∂μ) ^ -(1 / p) * ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a : α, g a ^ p ∂μ) ^ (1 / p))
  · rwa [← mul_le_mul_left h0_rpow htop_rpow, ← mul_assoc, ← rpow_add _ _ h_add_zero h_add_top, ← sub_eq_add_neg,
      _root_.sub_self, rpow_zero, one_mulₓ, mul_oneₓ] at h
    
  have h :
    (∫⁻ a : α, (f + g) a ^ p ∂μ) ≤
      ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a : α, g a ^ p ∂μ) ^ (1 / p)) * (∫⁻ a : α, (f + g) a ^ p ∂μ) ^ (1 / q) :=
    lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add hpq hf hf_top hg hg_top
  have h_one_div_q : 1 / q = 1 - 1 / p := by
    nth_rw 1[← hpq.inv_add_inv_conj]
    ring
  simp_rw [h_one_div_q, sub_eq_add_neg 1 (1 / p), Ennreal.rpow_add _ _ h_add_zero h_add_top, rpow_one] at h
  nth_rw 1[mul_comm]  at h
  nth_rw 0[← one_mulₓ (∫⁻ a : α, (f + g) a ^ p ∂μ)]  at h
  rwa [← mul_assoc, Ennreal.mul_le_mul_right h_add_zero h_add_top, mul_comm] at h

/-- Minkowski's inequality for functions `α → ℝ≥0∞`: the `ℒp` seminorm of the sum of two
functions is bounded by the sum of their `ℒp` seminorms. -/
theorem lintegral_Lp_add_le {p : ℝ} {f g : α → ℝ≥0∞} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) (hp1 : 1 ≤ p) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one hp1
  by_cases' hf_top : (∫⁻ a, f a ^ p ∂μ) = ⊤
  · simp [← hf_top, ← hp_pos]
    
  by_cases' hg_top : (∫⁻ a, g a ^ p ∂μ) = ⊤
  · simp [← hg_top, ← hp_pos]
    
  by_cases' h1 : p = 1
  · refine' le_of_eqₓ _
    simp_rw [h1, one_div_one, Ennreal.rpow_one]
    exact lintegral_add_left' hf _
    
  have hp1_lt : 1 < p := by
    refine' lt_of_le_of_neₓ hp1 _
    symm
    exact h1
  have hpq := Real.is_conjugate_exponent_conjugate_exponent hp1_lt
  by_cases' h0 : (∫⁻ a, (f + g) a ^ p ∂μ) = 0
  · rw [h0,
      @Ennreal.zero_rpow_of_pos (1 / p)
        (by
          simp [← lt_of_lt_of_leₓ zero_lt_one hp1])]
    exact zero_le _
    
  have htop : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ ⊤ := by
    rw [← Ne.def] at hf_top hg_top
    rw [← lt_top_iff_ne_top] at hf_top hg_top⊢
    exact lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top hf hf_top hg_top hp1
  exact lintegral_Lp_add_le_aux hpq hf hf_top hg hg_top h0 htop

end Ennreal

/-- Hölder's inequality for functions `α → ℝ≥0`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem Nnreal.lintegral_mul_le_Lp_mul_Lq {p q : ℝ} (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0 }
    (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  simp_rw [Pi.mul_apply, Ennreal.coe_mul]
  exact Ennreal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.coe_nnreal_ennreal hg.coe_nnreal_ennreal

end Lintegral

