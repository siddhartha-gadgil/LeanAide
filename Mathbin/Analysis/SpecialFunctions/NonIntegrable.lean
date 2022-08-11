/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.SpecialFunctions.Integrals
import Mathbin.Analysis.Calculus.FderivMeasurable

/-!
# Non integrable functions

In this file we prove that the derivative of a function that tends to infinity is not interval
integrable, see `interval_integral.not_integrable_has_deriv_at_of_tendsto_norm_at_top_filter` and
`interval_integral.not_integrable_has_deriv_at_of_tendsto_norm_at_top_punctured`.  Then we apply the
latter lemma to prove that the function `λ x, x⁻¹` is integrable on `a..b` if and only if `a = b` or
`0 ∉ [a, b]`.

## Main results

* `not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_punctured`: if `f` tends to infinity
  along `𝓝[≠] c` and `f' = O(g)` along the same filter, then `g` is not interval integrable on any
  nontrivial integral `a..b`, `c ∈ [a, b]`.

* `not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_filter`: a version of
  `not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_punctured` that works for one-sided
  neighborhoods;

* `not_interval_integrable_of_sub_inv_is_O_punctured`: if `1 / (x - c) = O(f)` as `x → c`, `x ≠ c`,
  then `f` is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`;

* `interval_integrable_sub_inv_iff`, `interval_integrable_inv_iff`: integrability conditions for
  `(x - c)⁻¹` and `x⁻¹`.

## Tags

integrable function
-/


open MeasureTheory TopologicalSpace Interval Nnreal Ennreal

open MeasureTheory TopologicalSpace Set Filter Asymptotics intervalIntegral

variable {E F : Type _} [NormedGroup E] [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] [NormedGroup F]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- If `f` is eventually differentiable along a nontrivial filter `l : filter ℝ` that is generated
by convex sets, the norm of `f` tends to infinity along `l`, and `f' = O(g)` along `l`, where `f'`
is the derivative of `f`, then `g` is not integrable on any interval `a..b` such that
`[a, b] ∈ l`. -/
theorem not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_filter {f : ℝ → E} {g : ℝ → F} {a b : ℝ}
    (l : Filter ℝ) [NeBot l] [TendstoIxxClass Icc l l]
    (hl : "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ∈ l)
    (hd : ∀ᶠ x in l, DifferentiableAt ℝ f x) (hf : Tendsto (fun x => ∥f x∥) l atTop) (hfg : deriv f =O[l] g) :
    ¬IntervalIntegrable g volume a b := by
  intro hgi
  obtain ⟨C, hC₀, s, hsl, hsub, hfd, hg⟩ :
    ∃ (C : ℝ)(hC₀ : 0 ≤ C),
      ∃ s ∈ l,
        (∀,
            ∀ x ∈ s,
              ∀,
                ∀ y ∈ s,
                  ∀,
                    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
                      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") ∧
          (∀,
              ∀ x ∈ s,
                ∀,
                  ∀ y ∈ s,
                    ∀,
                      ∀ z ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)",
                        ∀, DifferentiableAt ℝ f z) ∧
            ∀,
              ∀ x ∈ s,
                ∀,
                  ∀ y ∈ s,
                    ∀,
                      ∀ z ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)",
                        ∀, ∥deriv f z∥ ≤ C * ∥g z∥ :=
    by
    rcases hfg.exists_nonneg with ⟨C, C₀, hC⟩
    have h :
      ∀ᶠ x : ℝ × ℝ in l.prod l,
        ∀,
          ∀ y ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)",
            ∀,
              (DifferentiableAt ℝ f y ∧ ∥deriv f y∥ ≤ C * ∥g y∥) ∧
                y ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
      (tendsto_fst.interval tendsto_snd).Eventually ((hd.and hC.bound).And hl).smallSets
    rcases mem_prod_self_iff.1 h with ⟨s, hsl, hs⟩
    simp only [← prod_subset_iff, ← mem_set_of_eq] at hs
    exact
      ⟨C, C₀, s, hsl, fun x hx y hy z hz => (hs x hx y hy z hz).2, fun x hx y hy z hz => (hs x hx y hy z hz).1.1,
        fun x hx y hy z hz => (hs x hx y hy z hz).1.2⟩
  replace hgi : IntervalIntegrable (fun x => C * ∥g x∥) volume a b
  · convert hgi.norm.smul C
    
  obtain ⟨c, hc, d, hd, hlt⟩ : ∃ c ∈ s, ∃ d ∈ s, (∥f c∥ + ∫ y in Ι a b, C * ∥g y∥) < ∥f d∥ := by
    rcases Filter.nonempty_of_mem hsl with ⟨c, hc⟩
    have : ∀ᶠ x in l, (∥f c∥ + ∫ y in Ι a b, C * ∥g y∥) < ∥f x∥ := hf.eventually (eventually_gt_at_top _)
    exact ⟨c, hc, (this.and hsl).exists.imp fun d hd => ⟨hd.2, hd.1⟩⟩
  specialize hsub c hc d hd
  specialize hfd c hc d hd
  replace hg : ∀, ∀ x ∈ Ι c d, ∀, ∥deriv f x∥ ≤ C * ∥g x∥
  exact fun z hz => hg c hc d hd z ⟨hz.1.le, hz.2⟩
  have hg_ae : ∀ᵐ x ∂volume.restrict (Ι c d), ∥deriv f x∥ ≤ C * ∥g x∥ :=
    (ae_restrict_mem measurable_set_interval_oc).mono hg
  have hsub' : Ι c d ⊆ Ι a b := interval_oc_subset_interval_oc_of_interval_subset_interval hsub
  have hfi : IntervalIntegrable (deriv f) volume c d :=
    (hgi.mono_set hsub).mono_fun' (ae_strongly_measurable_deriv _ _) hg_ae
  refine' hlt.not_le (sub_le_iff_le_add'.1 _)
  calc ∥f d∥ - ∥f c∥ ≤ ∥f d - f c∥ := norm_sub_norm_le _ _ _ = ∥∫ x in c..d, deriv f x∥ :=
      congr_arg _ (integral_deriv_eq_sub hfd hfi).symm _ = ∥∫ x in Ι c d, deriv f x∥ :=
      norm_integral_eq_norm_integral_Ioc _ _ ≤ ∫ x in Ι c d, ∥deriv f x∥ :=
      norm_integral_le_integral_norm _ _ ≤ ∫ x in Ι c d, C * ∥g x∥ :=
      set_integral_mono_on hfi.norm.def (hgi.def.mono_set hsub') measurable_set_interval_oc
        hg _ ≤ ∫ x in Ι a b, C * ∥g x∥ :=
      set_integral_mono_set hgi.def ((ae_of_all _) fun x => mul_nonneg hC₀ (norm_nonneg _)) hsub'.eventually_le

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- If `a ≠ b`, `c ∈ [a, b]`, `f` is differentiable in the neighborhood of `c` within
`[a, b] \ {c}`, `∥f x∥ → ∞` as `x → c` within `[a, b] \ {c}`, and `f' = O(g)` along
`𝓝[[a, b] \ {c}] c`, where `f'` is the derivative of `f`, then `g` is not interval integrable on
`a..b`. -/
theorem not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_within_diff_singleton {f : ℝ → E} {g : ℝ → F}
    {a b c : ℝ} (hne : a ≠ b) (hc : c ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (h_deriv :
      ∀ᶠ x in 𝓝["./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" \ {c}] c,
        DifferentiableAt ℝ f x)
    (h_infty :
      Tendsto (fun x => ∥f x∥)
        (𝓝["./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" \ {c}] c) atTop)
    (hg : deriv f =O[𝓝["./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" \ {c}] c] g) :
    ¬IntervalIntegrable g volume a b := by
  obtain ⟨l, hl, hl', hle, hmem⟩ :
    ∃ l : Filter ℝ,
      tendsto_Ixx_class Icc l l ∧
        l.ne_bot ∧ l ≤ 𝓝 c ∧ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" \ {c} ∈ l :=
    by
    cases' (min_lt_max.2 hne).lt_or_lt c with hlt hlt
    · refine' ⟨𝓝[<] c, inferInstance, inferInstance, inf_le_left, _⟩
      rw [← Iic_diff_right]
      exact diff_mem_nhds_within_diff (Icc_mem_nhds_within_Iic ⟨hlt, hc.2⟩) _
      
    · refine' ⟨𝓝[>] c, inferInstance, inferInstance, inf_le_left, _⟩
      rw [← Ici_diff_left]
      exact diff_mem_nhds_within_diff (Icc_mem_nhds_within_Ici ⟨hc.1, hlt⟩) _
      
  skip
  have : l ≤ 𝓝["./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" \ {c}] c :=
    le_inf hle (le_principal_iff.2 hmem)
  exact
    not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_filter l (mem_of_superset hmem (diff_subset _ _))
      (h_deriv.filter_mono this) (h_infty.mono_left this) (hg.mono this)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- If `f` is differentiable in a punctured neighborhood of `c`, `∥f x∥ → ∞` as `x → c` (more
formally, along the filter `𝓝[≠] c`), and `f' = O(g)` along `𝓝[≠] c`, where `f'` is the derivative
of `f`, then `g` is not interval integrable on any nontrivial interval `a..b` such that
`c ∈ [a, b]`. -/
theorem not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_punctured {f : ℝ → E} {g : ℝ → F} {a b c : ℝ}
    (h_deriv : ∀ᶠ x in 𝓝[≠] c, DifferentiableAt ℝ f x) (h_infty : Tendsto (fun x => ∥f x∥) (𝓝[≠] c) atTop)
    (hg : deriv f =O[𝓝[≠] c] g) (hne : a ≠ b)
    (hc : c ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    ¬IntervalIntegrable g volume a b :=
  have : 𝓝["./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" \ {c}] c ≤ 𝓝[≠] c :=
    nhds_within_mono _ (inter_subset_right _ _)
  not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_within_diff_singleton hne hc (h_deriv.filter_mono this)
    (h_infty.mono_left this) (hg.mono this)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- If `f` grows in the punctured neighborhood of `c : ℝ` at least as fast as `1 / (x - c)`,
then it is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`. -/
theorem not_interval_integrable_of_sub_inv_is_O_punctured {f : ℝ → F} {a b c : ℝ}
    (hf : (fun x => (x - c)⁻¹) =O[𝓝[≠] c] f) (hne : a ≠ b)
    (hc : c ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    ¬IntervalIntegrable f volume a b := by
  have A : ∀ᶠ x in 𝓝[≠] c, HasDerivAt (fun x => Real.log (x - c)) (x - c)⁻¹ x := by
    filter_upwards [self_mem_nhds_within] with x hx
    simpa using ((has_deriv_at_id x).sub_const c).log (sub_ne_zero.2 hx)
  have B : tendsto (fun x => ∥Real.log (x - c)∥) (𝓝[≠] c) at_top := by
    refine' tendsto_abs_at_bot_at_top.comp (real.tendsto_log_nhds_within_zero.comp _)
    rw [← sub_self c]
    exact ((has_deriv_at_id c).sub_const c).tendsto_punctured_nhds one_ne_zero
  exact
    not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_punctured (A.mono fun x hx => hx.DifferentiableAt) B
      (hf.congr' (A.mono fun x hx => hx.deriv.symm) eventually_eq.rfl) hne hc

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- The function `λ x, (x - c)⁻¹` is integrable on `a..b` if and only if `a = b` or `c ∉ [a, b]`. -/
@[simp]
theorem interval_integrable_sub_inv_iff {a b c : ℝ} :
    IntervalIntegrable (fun x => (x - c)⁻¹) volume a b ↔
      a = b ∨ c ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  constructor
  · refine' fun h => or_iff_not_imp_left.2 fun hne hc => _
    exact not_interval_integrable_of_sub_inv_is_O_punctured (is_O_refl _ _) hne hc h
    
  · rintro (rfl | h₀)
    exacts[IntervalIntegrable.refl,
      interval_integrable_inv (fun x hx => sub_ne_zero.2 <| ne_of_mem_of_not_mem hx h₀)
        (continuous_on_id.sub continuous_on_const)]
    

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- The function `λ x, x⁻¹` is integrable on `a..b` if and only if `a = b` or `0 ∉ [a, b]`. -/
@[simp]
theorem interval_integrable_inv_iff {a b : ℝ} :
    IntervalIntegrable (fun x => x⁻¹) volume a b ↔
      a = b ∨ (0 : ℝ) ∉ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp only [interval_integrable_sub_inv_iff, ← sub_zero]

