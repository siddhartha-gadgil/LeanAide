/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.Analysis.NormedSpace.Dual
import Mathbin.MeasureTheory.Function.StronglyMeasurableLp
import Mathbin.MeasureTheory.Integral.SetIntegral

/-! # From equality of integrals to equality of functions

This file provides various statements of the general form "if two functions have the same integral
on all sets, then they are equal almost everywhere".
The different lemmas use various hypotheses on the class of functions, on the target space or on the
possible finiteness of the measure.

## Main statements

All results listed below apply to two functions `f, g`, together with two main hypotheses,
* `f` and `g` are integrable on all measurable sets with finite measure,
* for all measurable sets `s` with finite measure, `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ`.
The conclusion is then `f =ᵐ[μ] g`. The main lemmas are:
* `ae_eq_of_forall_set_integral_eq_of_sigma_finite`: case of a sigma-finite measure.
* `ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq`: for functions which are
  `ae_fin_strongly_measurable`.
* `Lp.ae_eq_of_forall_set_integral_eq`: for elements of `Lp`, for `0 < p < ∞`.
* `integrable.ae_eq_of_forall_set_integral_eq`: for integrable functions.

For each of these results, we also provide a lemma about the equality of one function and 0. For
example, `Lp.ae_eq_zero_of_forall_set_integral_eq_zero`.

We also register the corresponding lemma for integrals of `ℝ≥0∞`-valued functions, in
`ae_eq_of_forall_set_lintegral_eq_of_sigma_finite`.

Generally useful lemmas which are not related to integrals:
* `ae_eq_zero_of_forall_inner`: if for all constants `c`, `λ x, inner c (f x) =ᵐ[μ] 0` then
  `f =ᵐ[μ] 0`.
* `ae_eq_zero_of_forall_dual`: if for all constants `c` in the dual space, `λ x, c (f x) =ᵐ[μ] 0`
  then `f =ᵐ[μ] 0`.

-/


open MeasureTheory TopologicalSpace NormedSpace Filter

open Ennreal Nnreal MeasureTheory

namespace MeasureTheory

section AeEqOfForall

variable {α E 𝕜 : Type _} {m : MeasurableSpace α} {μ : Measure α} [IsROrC 𝕜]

theorem ae_eq_zero_of_forall_inner [InnerProductSpace 𝕜 E] [SecondCountableTopology E] {f : α → E}
    (hf : ∀ c : E, (fun x => (inner c (f x) : 𝕜)) =ᵐ[μ] 0) : f =ᵐ[μ] 0 := by
  let s := dense_seq E
  have hs : DenseRange s := dense_range_dense_seq E
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, inner (s n) (f x) = (0 : 𝕜) := ae_all_iff.mpr fun n => hf (s n)
  refine' hf'.mono fun x hx => _
  rw [Pi.zero_apply, ← inner_self_eq_zero]
  have h_closed : IsClosed { c : E | inner c (f x) = (0 : 𝕜) } :=
    is_closed_eq (continuous_id.inner continuous_const) continuous_const
  exact @is_closed_property ℕ E _ s (fun c => inner c (f x) = (0 : 𝕜)) hs h_closed (fun n => hx n) _

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => y x

variable (𝕜)

theorem ae_eq_zero_of_forall_dual_of_is_separable [NormedGroup E] [NormedSpace 𝕜 E] {t : Set E}
    (ht : TopologicalSpace.IsSeparable t) {f : α → E} (hf : ∀ c : Dual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0)
    (h't : ∀ᵐ x ∂μ, f x ∈ t) : f =ᵐ[μ] 0 := by
  rcases ht with ⟨d, d_count, hd⟩
  have : Encodable d := d_count.to_encodable
  have : ∀ x : d, ∃ g : E →L[𝕜] 𝕜, ∥g∥ ≤ 1 ∧ g x = ∥(x : E)∥ := fun x => exists_dual_vector'' 𝕜 x
  choose s hs using this
  have A : ∀ a : E, a ∈ t → (∀ x, ⟪a, s x⟫ = (0 : 𝕜)) → a = 0 := by
    intro a hat ha
    contrapose! ha
    have a_pos : 0 < ∥a∥ := by
      simp only [← ha, ← norm_pos_iff, ← Ne.def, ← not_false_iff]
    have a_mem : a ∈ Closure d := hd hat
    obtain ⟨x, hx⟩ : ∃ x : d, dist a x < ∥a∥ / 2 := by
      rcases Metric.mem_closure_iff.1 a_mem (∥a∥ / 2) (half_pos a_pos) with ⟨x, h'x, hx⟩
      exact ⟨⟨x, h'x⟩, hx⟩
    use x
    have I : ∥a∥ / 2 < ∥(x : E)∥ := by
      have : ∥a∥ ≤ ∥(x : E)∥ + ∥a - x∥ := norm_le_insert' _ _
      have : ∥a - x∥ < ∥a∥ / 2 := by
        rwa [dist_eq_norm] at hx
      linarith
    intro h
    apply lt_irreflₓ ∥s x x∥
    calc ∥s x x∥ = ∥s x (x - a)∥ := by
        simp only [← h, ← sub_zero, ← ContinuousLinearMap.map_sub]_ ≤ 1 * ∥(x : E) - a∥ :=
        ContinuousLinearMap.le_of_op_norm_le _ (hs x).1 _ _ < ∥a∥ / 2 := by
        rw [one_mulₓ]
        rwa [dist_eq_norm'] at hx _ < ∥(x : E)∥ := I _ = ∥s x x∥ := by
        rw [(hs x).2, IsROrC.norm_coe_norm]
  have hfs : ∀ y : d, ∀ᵐ x ∂μ, ⟪f x, s y⟫ = (0 : 𝕜) := fun y => hf (s y)
  have hf' : ∀ᵐ x ∂μ, ∀ y : d, ⟪f x, s y⟫ = (0 : 𝕜) := by
    rwa [ae_all_iff]
  filter_upwards [hf', h't] with x hx h'x
  exact A (f x) h'x hx

theorem ae_eq_zero_of_forall_dual [NormedGroup E] [NormedSpace 𝕜 E] [SecondCountableTopology E] {f : α → E}
    (hf : ∀ c : Dual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0) : f =ᵐ[μ] 0 :=
  ae_eq_zero_of_forall_dual_of_is_separable 𝕜 (is_separable_of_separable_space (Set.Univ : Set E)) hf
    (eventually_of_forall fun x => Set.mem_univ _)

variable {𝕜}

end AeEqOfForall

variable {α E : Type _} {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α} [NormedGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {p : ℝ≥0∞}

section AeEqOfForallSetIntegralEq

theorem ae_const_le_iff_forall_lt_measure_zero {β} [LinearOrderₓ β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] (f : α → β) (c : β) : (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀, ∀ b < c, ∀, μ { x | f x ≤ b } = 0 := by
  rw [ae_iff]
  push_neg
  constructor
  · intro h b hb
    exact measure_mono_null (fun y hy => (lt_of_le_of_ltₓ hy hb : _)) h
    
  intro hc
  by_cases' h : ∀ b, c ≤ b
  · have : { a : α | f a < c } = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.2 fun x hx => _
      exact (lt_irreflₓ _ (lt_of_lt_of_leₓ hx (h (f x)))).elim
    simp [← this]
    
  by_cases' H : ¬IsLub (Set.Iio c) c
  · have : c ∈ UpperBounds (Set.Iio c) := fun y hy => le_of_ltₓ hy
    obtain ⟨b, b_up, bc⟩ : ∃ b : β, b ∈ UpperBounds (Set.Iio c) ∧ b < c := by
      simpa [← IsLub, ← IsLeast, ← this, ← LowerBounds] using H
    exact measure_mono_null (fun x hx => b_up hx) (hc b bc)
    
  push_neg  at H h
  obtain ⟨u, u_mono, u_lt, u_lim, -⟩ :
    ∃ u : ℕ → β, StrictMono u ∧ (∀ n : ℕ, u n < c) ∧ tendsto u at_top (nhds c) ∧ ∀ n : ℕ, u n ∈ Set.Iio c :=
    H.exists_seq_strict_mono_tendsto_of_not_mem (lt_irreflₓ c) h
  have h_Union : { x | f x < c } = ⋃ n : ℕ, { x | f x ≤ u n } := by
    ext1 x
    simp_rw [Set.mem_Union, Set.mem_set_of_eq]
    constructor <;> intro h
    · obtain ⟨n, hn⟩ := ((tendsto_order.1 u_lim).1 _ h).exists
      exact ⟨n, hn.le⟩
      
    · obtain ⟨n, hn⟩ := h
      exact hn.trans_lt (u_lt _)
      
  rw [h_Union, measure_Union_null_iff]
  intro n
  exact hc _ (u_lt n)

section Ennreal

open TopologicalSpace

theorem ae_le_of_forall_set_lintegral_le_of_sigma_finite [SigmaFinite μ] {f g : α → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (h : ∀ s, MeasurableSet s → μ s < ∞ → (∫⁻ x in s, f x ∂μ) ≤ ∫⁻ x in s, g x ∂μ) : f ≤ᵐ[μ] g := by
  have A : ∀ (ε N : ℝ≥0 ) (p : ℕ), 0 < ε → μ ({ x | g x + ε ≤ f x ∧ g x ≤ N } ∩ spanning_sets μ p) = 0 := by
    intro ε N p εpos
    let s := { x | g x + ε ≤ f x ∧ g x ≤ N } ∩ spanning_sets μ p
    have s_meas : MeasurableSet s := by
      have A : MeasurableSet { x | g x + ε ≤ f x } := measurable_set_le (hg.add measurable_const) hf
      have B : MeasurableSet { x | g x ≤ N } := measurable_set_le hg measurable_const
      exact (A.inter B).inter (measurable_spanning_sets μ p)
    have s_lt_top : μ s < ∞ := (measure_mono (Set.inter_subset_right _ _)).trans_lt (measure_spanning_sets_lt_top μ p)
    have A : (∫⁻ x in s, g x ∂μ) + ε * μ s ≤ (∫⁻ x in s, g x ∂μ) + 0 :=
      calc
        (∫⁻ x in s, g x ∂μ) + ε * μ s = (∫⁻ x in s, g x ∂μ) + ∫⁻ x in s, ε ∂μ := by
          simp only [← lintegral_const, ← Set.univ_inter, ← MeasurableSet.univ, ← measure.restrict_apply]
        _ = ∫⁻ x in s, g x + ε ∂μ := (lintegral_add_right _ measurable_const).symm
        _ ≤ ∫⁻ x in s, f x ∂μ := set_lintegral_mono (hg.add measurable_const) hf fun x hx => hx.1.1
        _ ≤ (∫⁻ x in s, g x ∂μ) + 0 := by
          rw [add_zeroₓ]
          exact h s s_meas s_lt_top
        
    have B : (∫⁻ x in s, g x ∂μ) ≠ ∞ := by
      apply ne_of_ltₓ
      calc (∫⁻ x in s, g x ∂μ) ≤ ∫⁻ x in s, N ∂μ :=
          set_lintegral_mono hg measurable_const fun x hx => hx.1.2_ = N * μ s := by
          simp only [← lintegral_const, ← Set.univ_inter, ← MeasurableSet.univ, ← measure.restrict_apply]_ < ∞ := by
          simp only [← lt_top_iff_ne_top, ← s_lt_top.ne, ← and_falseₓ, ← Ennreal.coe_ne_top, ← WithTop.mul_eq_top_iff, ←
            Ne.def, ← not_false_iff, ← false_andₓ, ← or_selfₓ]
    have : (ε : ℝ≥0∞) * μ s ≤ 0 := Ennreal.le_of_add_le_add_left B A
    simpa only [← Ennreal.coe_eq_zero, ← nonpos_iff_eq_zero, ← mul_eq_zero, ← εpos.ne', ← false_orₓ]
  obtain ⟨u, u_mono, u_pos, u_lim⟩ : ∃ u : ℕ → ℝ≥0 , StrictAnti u ∧ (∀ n, 0 < u n) ∧ tendsto u at_top (nhds 0) :=
    exists_seq_strict_anti_tendsto (0 : ℝ≥0 )
  let s := fun n : ℕ => { x | g x + u n ≤ f x ∧ g x ≤ (n : ℝ≥0 ) } ∩ spanning_sets μ n
  have μs : ∀ n, μ (s n) = 0 := fun n => A _ _ _ (u_pos n)
  have B : { x | f x ≤ g x }ᶜ ⊆ ⋃ n, s n := by
    intro x hx
    simp at hx
    have L1 : ∀ᶠ n in at_top, g x + u n ≤ f x := by
      have : tendsto (fun n => g x + u n) at_top (𝓝 (g x + (0 : ℝ≥0 ))) :=
        tendsto_const_nhds.add (Ennreal.tendsto_coe.2 u_lim)
      simp at this
      exact eventually_le_of_tendsto_lt hx this
    have L2 : ∀ᶠ n : ℕ in (at_top : Filter ℕ), g x ≤ (n : ℝ≥0 ) := by
      have : tendsto (fun n : ℕ => ((n : ℝ≥0 ) : ℝ≥0∞)) at_top (𝓝 ∞) := by
        simp only [← Ennreal.coe_nat]
        exact Ennreal.tendsto_nat_nhds_top
      exact eventually_ge_of_tendsto_gt (hx.trans_le le_top) this
    apply Set.mem_Union.2
    exact ((L1.and L2).And (eventually_mem_spanning_sets μ x)).exists
  refine' le_antisymmₓ _ bot_le
  calc μ ({ x : α | (fun x : α => f x ≤ g x) x }ᶜ) ≤ μ (⋃ n, s n) := measure_mono B _ ≤ ∑' n, μ (s n) :=
      measure_Union_le _ _ = 0 := by
      simp only [← μs, ← tsum_zero]

theorem ae_eq_of_forall_set_lintegral_eq_of_sigma_finite [SigmaFinite μ] {f g : α → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (h : ∀ s, MeasurableSet s → μ s < ∞ → (∫⁻ x in s, f x ∂μ) = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g := by
  have A : f ≤ᵐ[μ] g := ae_le_of_forall_set_lintegral_le_of_sigma_finite hf hg fun s hs h's => le_of_eqₓ (h s hs h's)
  have B : g ≤ᵐ[μ] f := ae_le_of_forall_set_lintegral_le_of_sigma_finite hg hf fun s hs h's => ge_of_eq (h s hs h's)
  filter_upwards [A, B] with x using le_antisymmₓ

end Ennreal

section Real

section RealFiniteMeasure

variable [IsFiniteMeasure μ] {f : α → ℝ}

/-- Don't use this lemma. Use `ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure`. -/
theorem ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_strongly_measurable (hfm : StronglyMeasurable f)
    (hf : Integrable f μ) (hf_zero : ∀ s, MeasurableSet s → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  simp_rw [eventually_le, Pi.zero_apply]
  rw [ae_const_le_iff_forall_lt_measure_zero]
  intro b hb_neg
  let s := { x | f x ≤ b }
  have hs : MeasurableSet s := hfm.measurable_set_le strongly_measurable_const
  have h_int_gt : (∫ x in s, f x ∂μ) ≤ b * (μ s).toReal := by
    have h_const_le : (∫ x in s, f x ∂μ) ≤ ∫ x in s, b ∂μ := by
      refine' set_integral_mono_ae_restrict hf.integrable_on (integrable_on_const.mpr (Or.inr (measure_lt_top μ s))) _
      rw [eventually_le, ae_restrict_iff hs]
      exact eventually_of_forall fun x hxs => hxs
    rwa [set_integral_const, smul_eq_mul, mul_comm] at h_const_le
  by_contra
  refine' (lt_self_iff_false (∫ x in s, f x ∂μ)).mp (h_int_gt.trans_lt _)
  refine' (mul_neg_iff.mpr (Or.inr ⟨hb_neg, _⟩)).trans_le _
  swap
  · simp_rw [measure.restrict_restrict hs]
    exact hf_zero s hs
    
  refine' Ennreal.to_real_nonneg.lt_of_ne fun h_eq => h _
  cases' (Ennreal.to_real_eq_zero_iff _).mp h_eq.symm with hμs_eq_zero hμs_eq_top
  · exact hμs_eq_zero
    
  · exact absurd hμs_eq_top (measure_lt_top μ s).Ne
    

theorem ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure (hf : Integrable f μ)
    (hf_zero : ∀ s, MeasurableSet s → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  rcases hf.1 with ⟨f', hf'_meas, hf_ae⟩
  have hf'_integrable : integrable f' μ := integrable.congr hf hf_ae
  have hf'_zero : ∀ s, MeasurableSet s → 0 ≤ ∫ x in s, f' x ∂μ := by
    intro s hs
    rw [set_integral_congr_ae hs (hf_ae.mono fun x hx hxs => hx.symm)]
    exact hf_zero s hs
  exact
    (ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_strongly_measurable hf'_meas hf'_integrable
          hf'_zero).trans
      hf_ae.symm.le

theorem ae_le_of_forall_set_integral_le {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf_le : ∀ s, MeasurableSet s → (∫ x in s, f x ∂μ) ≤ ∫ x in s, g x ∂μ) : f ≤ᵐ[μ] g := by
  rw [← eventually_sub_nonneg]
  refine' ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure (hg.sub hf) fun s hs => _
  rw [integral_sub' hg.integrable_on hf.integrable_on, sub_nonneg]
  exact hf_le s hs

end RealFiniteMeasure

theorem ae_nonneg_restrict_of_forall_set_integral_nonneg_inter {f : α → ℝ} {t : Set α} (hμt : μ t ≠ ∞)
    (hf : IntegrableOn f t μ) (hf_zero : ∀ s, MeasurableSet s → 0 ≤ ∫ x in s ∩ t, f x ∂μ) : 0 ≤ᵐ[μ.restrict t] f := by
  have : Fact (μ t < ∞) := ⟨lt_top_iff_ne_top.mpr hμt⟩
  refine' ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure hf fun s hs => _
  simp_rw [measure.restrict_restrict hs]
  exact hf_zero s hs

theorem ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite [SigmaFinite μ] {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  apply ae_of_forall_measure_lt_top_ae_restrict
  intro t t_meas t_lt_top
  apply ae_nonneg_restrict_of_forall_set_integral_nonneg_inter t_lt_top.ne (hf_int_finite t t_meas t_lt_top)
  intro s s_meas
  exact hf_zero _ (s_meas.inter t_meas) (lt_of_le_of_ltₓ (measure_mono (Set.inter_subset_right _ _)) t_lt_top)

theorem AeFinStronglyMeasurable.ae_nonneg_of_forall_set_integral_nonneg {f : α → ℝ} (hf : AeFinStronglyMeasurable f μ)
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  let t := hf.sigma_finite_set
  suffices : 0 ≤ᵐ[μ.restrict t] f
  exact ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl.symm.le
  have : sigma_finite (μ.restrict t) := hf.sigma_finite_restrict
  refine' ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite (fun s hs hμts => _) fun s hs hμts => _
  · rw [integrable_on, measure.restrict_restrict hs]
    rw [measure.restrict_apply hs] at hμts
    exact hf_int_finite (s ∩ t) (hs.inter hf.measurable_set) hμts
    
  · rw [measure.restrict_restrict hs]
    rw [measure.restrict_apply hs] at hμts
    exact hf_zero (s ∩ t) (hs.inter hf.measurable_set) hμts
    

theorem Integrable.ae_nonneg_of_forall_set_integral_nonneg {f : α → ℝ} (hf : Integrable f μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f :=
  AeFinStronglyMeasurable.ae_nonneg_of_forall_set_integral_nonneg hf.AeFinStronglyMeasurable
    (fun s hs hμs => hf.IntegrableOn) hf_zero

theorem ae_nonneg_restrict_of_forall_set_integral_nonneg {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) {t : Set α} (ht : MeasurableSet t)
    (hμt : μ t ≠ ∞) : 0 ≤ᵐ[μ.restrict t] f := by
  refine'
    ae_nonneg_restrict_of_forall_set_integral_nonneg_inter hμt (hf_int_finite t ht (lt_top_iff_ne_top.mpr hμt))
      fun s hs => _
  refine' hf_zero (s ∩ t) (hs.inter ht) _
  exact (measure_mono (Set.inter_subset_right s t)).trans_lt (lt_top_iff_ne_top.mpr hμt)

theorem ae_eq_zero_restrict_of_forall_set_integral_eq_zero_real {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0) {t : Set α} (ht : MeasurableSet t)
    (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] 0 := by
  suffices h_and : f ≤ᵐ[μ.restrict t] 0 ∧ 0 ≤ᵐ[μ.restrict t] f
  exact h_and.1.mp (h_and.2.mono fun x hx1 hx2 => le_antisymmₓ hx2 hx1)
  refine'
    ⟨_,
      ae_nonneg_restrict_of_forall_set_integral_nonneg hf_int_finite (fun s hs hμs => (hf_zero s hs hμs).symm.le) ht
        hμt⟩
  suffices h_neg : 0 ≤ᵐ[μ.restrict t] -f
  · refine' h_neg.mono fun x hx => _
    rw [Pi.neg_apply] at hx
    simpa using hx
    
  refine'
    ae_nonneg_restrict_of_forall_set_integral_nonneg (fun s hs hμs => (hf_int_finite s hs hμs).neg) (fun s hs hμs => _)
      ht hμt
  simp_rw [Pi.neg_apply]
  rw [integral_neg, neg_nonneg]
  exact (hf_zero s hs hμs).le

end Real

theorem ae_eq_zero_restrict_of_forall_set_integral_eq_zero {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0) {t : Set α} (ht : MeasurableSet t)
    (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] 0 := by
  rcases(hf_int_finite t ht hμt.lt_top).AeStronglyMeasurable.is_separable_ae_range with ⟨u, u_sep, hu⟩
  refine' ae_eq_zero_of_forall_dual_of_is_separable ℝ u_sep (fun c => _) hu
  refine' ae_eq_zero_restrict_of_forall_set_integral_eq_zero_real _ _ ht hμt
  · intro s hs hμs
    exact ContinuousLinearMap.integrable_comp c (hf_int_finite s hs hμs)
    
  · intro s hs hμs
    rw [ContinuousLinearMap.integral_comp_comm c (hf_int_finite s hs hμs), hf_zero s hs hμs]
    exact ContinuousLinearMap.map_zero _
    

theorem ae_eq_restrict_of_forall_set_integral_eq {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] g := by
  rw [← sub_ae_eq_zero]
  have hfg' : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg_zero s hs hμs)
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → integrable_on (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact ae_eq_zero_restrict_of_forall_set_integral_eq_zero hfg_int hfg' ht hμt

theorem ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite [SigmaFinite μ] {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0) : f =ᵐ[μ] 0 := by
  let S := spanning_sets μ
  rw [← @measure.restrict_univ _ _ μ, ← Union_spanning_sets μ, eventually_eq, ae_iff,
    measure.restrict_apply' (MeasurableSet.Union (measurable_spanning_sets μ))]
  rw [Set.inter_Union, measure_Union_null_iff]
  intro n
  have h_meas_n : MeasurableSet (S n) := measurable_spanning_sets μ n
  have hμn : μ (S n) < ∞ := measure_spanning_sets_lt_top μ n
  rw [← measure.restrict_apply' h_meas_n]
  exact ae_eq_zero_restrict_of_forall_set_integral_eq_zero hf_int_finite hf_zero h_meas_n hμn.ne

theorem ae_eq_of_forall_set_integral_eq_of_sigma_finite [SigmaFinite μ] {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ) : f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs), sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → integrable_on (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite hfg_int hfg

theorem AeFinStronglyMeasurable.ae_eq_zero_of_forall_set_integral_eq_zero {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0) (hf : AeFinStronglyMeasurable f μ) :
    f =ᵐ[μ] 0 := by
  let t := hf.sigma_finite_set
  suffices : f =ᵐ[μ.restrict t] 0
  exact ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl
  have : sigma_finite (μ.restrict t) := hf.sigma_finite_restrict
  refine' ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite _ _
  · intro s hs hμs
    rw [integrable_on, measure.restrict_restrict hs]
    rw [measure.restrict_apply hs] at hμs
    exact hf_int_finite _ (hs.inter hf.measurable_set) hμs
    
  · intro s hs hμs
    rw [measure.restrict_restrict hs]
    rw [measure.restrict_apply hs] at hμs
    exact hf_zero _ (hs.inter hf.measurable_set) hμs
    

theorem AeFinStronglyMeasurable.ae_eq_of_forall_set_integral_eq {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ)
    (hf : AeFinStronglyMeasurable f μ) (hg : AeFinStronglyMeasurable g μ) : f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs), sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → integrable_on (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact (hf.sub hg).ae_eq_zero_of_forall_set_integral_eq_zero hfg_int hfg

theorem lp.ae_eq_zero_of_forall_set_integral_eq_zero (f : lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0) : f =ᵐ[μ] 0 :=
  AeFinStronglyMeasurable.ae_eq_zero_of_forall_set_integral_eq_zero hf_int_finite hf_zero
    (lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).AeFinStronglyMeasurable

theorem lp.ae_eq_of_forall_set_integral_eq (f g : lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ) : f =ᵐ[μ] g :=
  AeFinStronglyMeasurable.ae_eq_of_forall_set_integral_eq hf_int_finite hg_int_finite hfg
    (lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).AeFinStronglyMeasurable
    (lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).AeFinStronglyMeasurable

theorem ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim (hm : m ≤ m0) {f : α → E}
    (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0)
    (hf : FinStronglyMeasurable f (μ.trim hm)) : f =ᵐ[μ] 0 := by
  obtain ⟨t, ht_meas, htf_zero, htμ⟩ := hf.exists_set_sigma_finite
  have : sigma_finite ((μ.restrict t).trim hm) := by
    rwa [restrict_trim hm μ ht_meas] at htμ
  have htf_zero : f =ᵐ[μ.restrict (tᶜ)] 0 := by
    rw [eventually_eq, ae_restrict_iff' (MeasurableSet.compl (hm _ ht_meas))]
    exact eventually_of_forall htf_zero
  have hf_meas_m : strongly_measurable[m] f := hf.strongly_measurable
  suffices : f =ᵐ[μ.restrict t] 0
  exact ae_of_ae_restrict_of_ae_restrict_compl _ this htf_zero
  refine' measure_eq_zero_of_trim_eq_zero hm _
  refine' ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite _ _
  · intro s hs hμs
    rw [integrable_on, restrict_trim hm (μ.restrict t) hs, measure.restrict_restrict (hm s hs)]
    rw [← restrict_trim hm μ ht_meas, measure.restrict_apply hs, trim_measurable_set_eq hm (hs.inter ht_meas)] at hμs
    refine' integrable.trim hm _ hf_meas_m
    exact hf_int_finite _ (hs.inter ht_meas) hμs
    
  · intro s hs hμs
    rw [restrict_trim hm (μ.restrict t) hs, measure.restrict_restrict (hm s hs)]
    rw [← restrict_trim hm μ ht_meas, measure.restrict_apply hs, trim_measurable_set_eq hm (hs.inter ht_meas)] at hμs
    rw [← integral_trim hm hf_meas_m]
    exact hf_zero _ (hs.inter ht_meas) hμs
    

theorem Integrable.ae_eq_zero_of_forall_set_integral_eq_zero {f : α → E} (hf : Integrable f μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0) : f =ᵐ[μ] 0 := by
  have hf_Lp : mem_ℒp f 1 μ := mem_ℒp_one_iff_integrable.mpr hf
  let f_Lp := hf_Lp.to_Lp f
  have hf_f_Lp : f =ᵐ[μ] f_Lp := (mem_ℒp.coe_fn_to_Lp hf_Lp).symm
  refine' hf_f_Lp.trans _
  refine' Lp.ae_eq_zero_of_forall_set_integral_eq_zero f_Lp one_ne_zero Ennreal.coe_ne_top _ _
  · exact fun s hs hμs => integrable.integrable_on (L1.integrable_coe_fn _)
    
  · intro s hs hμs
    rw [integral_congr_ae (ae_restrict_of_ae hf_f_Lp.symm)]
    exact hf_zero s hs hμs
    

theorem Integrable.ae_eq_of_forall_set_integral_eq (f g : α → E) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ) : f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg' : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' hf.integrable_on hg.integrable_on]
    exact sub_eq_zero.mpr (hfg s hs hμs)
  exact integrable.ae_eq_zero_of_forall_set_integral_eq_zero (hf.sub hg) hfg'

end AeEqOfForallSetIntegralEq

section Lintegral

theorem AeMeasurable.ae_eq_of_forall_set_lintegral_eq {f g : α → ℝ≥0∞} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ)
    (hfi : (∫⁻ x, f x ∂μ) ≠ ∞) (hgi : (∫⁻ x, g x ∂μ) ≠ ∞)
    (hfg : ∀ ⦃s⦄, MeasurableSet s → μ s < ∞ → (∫⁻ x in s, f x ∂μ) = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g := by
  refine'
    Ennreal.eventually_eq_of_to_real_eventually_eq (ae_lt_top' hf hfi).ne_of_lt (ae_lt_top' hg hgi).ne_of_lt
      (integrable.ae_eq_of_forall_set_integral_eq _ _ (integrable_to_real_of_lintegral_ne_top hf hfi)
        (integrable_to_real_of_lintegral_ne_top hg hgi) fun s hs hs' => _)
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
  · congr 1
    rw [lintegral_congr_ae (of_real_to_real_ae_eq _), lintegral_congr_ae (of_real_to_real_ae_eq _)]
    · exact hfg hs hs'
      
    · refine' ae_lt_top' hg.restrict (ne_of_ltₓ (lt_of_le_of_ltₓ _ hgi.lt_top))
      exact @set_lintegral_univ α _ μ g ▸ lintegral_mono_set (Set.subset_univ _)
      
    · refine' ae_lt_top' hf.restrict (ne_of_ltₓ (lt_of_le_of_ltₓ _ hfi.lt_top))
      exact @set_lintegral_univ α _ μ f ▸ lintegral_mono_set (Set.subset_univ _)
      
    
  -- putting the proofs where they are used is extremely slow
  exacts[ae_of_all _ fun x => Ennreal.to_real_nonneg, hg.ennreal_to_real.restrict.ae_strongly_measurable,
    ae_of_all _ fun x => Ennreal.to_real_nonneg, hf.ennreal_to_real.restrict.ae_strongly_measurable]

end Lintegral

end MeasureTheory

