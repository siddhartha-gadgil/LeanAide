/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.MeasureTheory.Group.FundamentalDomain
import Mathbin.MeasureTheory.Integral.IntervalIntegral
import Mathbin.Topology.Algebra.Order.Floor

/-!
# Integrals of periodic functions

In this file we prove that `∫ x in t..t + T, f x = ∫ x in s..s + T, f x` for any (not necessarily
measurable) function periodic function with period `T`.
-/


open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace

open MeasureTheory

theorem is_add_fundamental_domain_Ioc {T : ℝ} (hT : 0 < T) (t : ℝ)
    (μ : Measureₓ ℝ := by
      run_tac
        volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples T) (Ioc t (t + T)) μ := by
  refine' is_add_fundamental_domain.mk' measurable_set_Ioc.null_measurable_set fun x => _
  have : bijective (cod_restrict (fun n : ℤ => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equivₓ.ofInjective (fun n : ℤ => n • T) (zsmul_strict_mono_left hT).Injective).Bijective
  refine' this.exists_unique_iff.2 _
  simpa only [← add_commₓ x] using exists_unique_add_zsmul_mem_Ioc hT x t

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace Function

namespace Periodic

open intervalIntegral

variable {f : ℝ → E} {T : ℝ}

/-- An auxiliary lemma for a more general `function.periodic.interval_integral_add_eq`. -/
theorem interval_integral_add_eq_of_pos (hf : Periodic f T) (hT : 0 < T) (t s : ℝ) :
    (∫ x in t..t + T, f x) = ∫ x in s..s + T, f x := by
  have : Encodable (AddSubgroup.zmultiples T) := (countable_range _).toEncodable
  simp only [← integral_of_le, ← hT.le, ← le_add_iff_nonneg_right]
  have : vadd_invariant_measure (AddSubgroup.zmultiples T) ℝ volume := ⟨fun c s hs => measure_preimage_add _ _ _⟩
  exact (is_add_fundamental_domain_Ioc hT t).set_integral_eq (is_add_fundamental_domain_Ioc hT s) hf.map_vadd_zmultiples

/-- If `f` is a periodic function with period `T`, then its integral over `[t, t + T]` does not
depend on `t`. -/
theorem interval_integral_add_eq (hf : Periodic f T) (t s : ℝ) : (∫ x in t..t + T, f x) = ∫ x in s..s + T, f x := by
  rcases lt_trichotomyₓ 0 T with (hT | rfl | hT)
  · exact hf.interval_integral_add_eq_of_pos hT t s
    
  · simp
    
  · rw [← neg_inj, ← integral_symm, ← integral_symm]
    simpa only [sub_eq_add_neg, ← add_sub_cancel] using
      hf.neg.interval_integral_add_eq_of_pos (neg_pos.2 hT) (t + T) (s + T)
    

/-- If `f` is an integrable periodic function with period `T`, then its integral over `[t, s + T]`
is the sum of its integrals over the intervals `[t, s]` and `[t, t + T]`. -/
theorem interval_integral_add_eq_add (hf : Periodic f T) (t s : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    (∫ x in t..s + T, f x) = (∫ x in t..s, f x) + ∫ x in t..t + T, f x := by
  rw [hf.interval_integral_add_eq t s, integral_add_adjacent_intervals (h_int t s) (h_int s _)]

/-- If `f` is an integrable periodic function with period `T`, and `n` is an integer, then its
integral over `[t, t + n • T]` is `n` times its integral over `[t, t + T]`. -/
theorem interval_integral_add_zsmul_eq (hf : Periodic f T) (n : ℤ) (t : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    (∫ x in t..t + n • T, f x) = n • ∫ x in t..t + T, f x := by
  -- Reduce to the case `b = 0`
  suffices (∫ x in 0 ..n • T, f x) = n • ∫ x in 0 ..T, f x by
    simp only [← hf.interval_integral_add_eq t 0, ← (hf.zsmul n).interval_integral_add_eq t 0, ← zero_addₓ, ← this]
  -- First prove it for natural numbers
  have : ∀ m : ℕ, (∫ x in 0 ..m • T, f x) = m • ∫ x in 0 ..T, f x := by
    intros
    induction' m with m ih
    · simp
      
    · simp only [← succ_nsmul', ← hf.interval_integral_add_eq_add 0 (m • T) h_int, ← ih, ← zero_addₓ]
      
  -- Then prove it for all integers
  cases' n with n n
  · simp [this n]
    
  · conv_rhs => rw [zsmul_neg_succ_of_nat]
    have h₀ : Int.negSucc n • T + (n + 1) • T = 0 := by
      simp
      linarith
    rw [integral_symm, ← (hf.nsmul (n + 1)).funext, neg_inj]
    simp_rw [integral_comp_add_right, h₀, zero_addₓ, this (n + 1), add_commₓ T,
      hf.interval_integral_add_eq ((n + 1) • T) 0, zero_addₓ]
    

section RealValued

open Filter

variable {g : ℝ → ℝ}

variable (hg : Periodic g T) (h_int : ∀ t₁ t₂, IntervalIntegrable g MeasureSpace.volume t₁ t₂)

include hg h_int

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded below by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
theorem Inf_add_zsmul_le_integral_of_pos (hT : 0 < T) (t : ℝ) :
    (inf ((fun t => ∫ x in 0 ..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in 0 ..T, g x) ≤ ∫ x in 0 ..t, g x := by
  let ε := Int.fract (t / T) * T
  conv_rhs =>
    rw [←
      Int.fract_div_mul_self_add_zsmul_eq T t
        (by
          linarith),
      ← integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)]
  rw [hg.interval_integral_add_zsmul_eq ⌊t / T⌋ ε h_int, hg.interval_integral_add_eq ε 0, zero_addₓ,
    add_le_add_iff_right]
  exact
    (continuous_primitive h_int 0).ContinuousOn.Inf_image_Icc_le
      (mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT))

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded above by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
theorem integral_le_Sup_add_zsmul_of_pos (hT : 0 < T) (t : ℝ) :
    (∫ x in 0 ..t, g x) ≤ sup ((fun t => ∫ x in 0 ..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in 0 ..T, g x := by
  let ε := Int.fract (t / T) * T
  conv_lhs =>
    rw [←
      Int.fract_div_mul_self_add_zsmul_eq T t
        (by
          linarith),
      ← integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)]
  rw [hg.interval_integral_add_zsmul_eq ⌊t / T⌋ ε h_int, hg.interval_integral_add_eq ε 0, zero_addₓ,
    add_le_add_iff_right]
  exact
    (continuous_primitive h_int 0).ContinuousOn.le_Sup_image_Icc
      (mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT))

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `∞` as `t` tends to `∞`. -/
theorem tendsto_at_top_interval_integral_of_pos (h₀ : 0 < ∫ x in 0 ..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0 ..t, g x) atTop atTop := by
  apply tendsto_at_top_mono (hg.Inf_add_zsmul_le_integral_of_pos h_int hT)
  apply at_top.tendsto_at_top_add_const_left (Inf <| (fun t => ∫ x in 0 ..t, g x) '' Icc 0 T)
  apply tendsto.at_top_zsmul_const h₀
  exact tendsto_floor_at_top.comp (tendsto_id.at_top_mul_const (inv_pos.mpr hT))

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `-∞` as `t` tends to `-∞`. -/
theorem tendsto_at_bot_interval_integral_of_pos (h₀ : 0 < ∫ x in 0 ..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0 ..t, g x) atBot atBot := by
  apply tendsto_at_bot_mono (hg.integral_le_Sup_add_zsmul_of_pos h_int hT)
  apply at_bot.tendsto_at_bot_add_const_left (Sup <| (fun t => ∫ x in 0 ..t, g x) '' Icc 0 T)
  apply tendsto.at_bot_zsmul_const h₀
  exact tendsto_floor_at_bot.comp (tendsto_id.at_bot_mul_const (inv_pos.mpr hT))

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `∞` as `t` tends to `∞`. -/
theorem tendsto_at_top_interval_integral_of_pos' (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0 ..t, g x) atTop atTop :=
  hg.tendsto_at_top_interval_integral_of_pos h_int (interval_integral_pos_of_pos (h_int 0 T) h₀ hT) hT

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `-∞` as `t` tends to `-∞`. -/
theorem tendsto_at_bot_interval_integral_of_pos' (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0 ..t, g x) atBot atBot :=
  hg.tendsto_at_bot_interval_integral_of_pos h_int (interval_integral_pos_of_pos (h_int 0 T) h₀ hT) hT

end RealValued

end Periodic

end Function

