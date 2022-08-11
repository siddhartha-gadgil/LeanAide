/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathbin.MeasureTheory.Integral.IntegrableOn
import Mathbin.MeasureTheory.Integral.Bochner
import Mathbin.Order.Filter.IndicatorFunction
import Mathbin.Topology.MetricSpace.ThickenedIndicator

/-!
# Set integral

In this file we prove some properties of `∫ x in s, f x ∂μ`. Recall that this notation
is defined as `∫ x, f x ∂(μ.restrict s)`. In `integral_indicator` we prove that for a measurable
function `f` and a measurable set `s` this definition coincides with another natural definition:
`∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ`, where `indicator s f x` is equal to `f x` for `x ∈ s`
and is zero otherwise.

Since `∫ x in s, f x ∂μ` is a notation, one can rewrite or apply any theorem about `∫ x, f x ∂μ`
directly. In this file we prove some theorems about dependence of `∫ x in s, f x ∂μ` on `s`, e.g.
`integral_union`, `integral_empty`, `integral_univ`.

We use the property `integrable_on f s μ := integrable f (μ.restrict s)`, defined in
`measure_theory.integrable_on`. We also defined in that same file a predicate
`integrable_at_filter (f : α → E) (l : filter α) (μ : measure α)` saying that `f` is integrable at
some set `s ∈ l`.

Finally, we prove a version of the
[Fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for set integral, see `filter.tendsto.integral_sub_linear_is_o_ae` and its corollaries.
Namely, consider a measurably generated filter `l`, a measure `μ` finite at this filter, and
a function `f` that has a finite limit `c` at `l ⊓ μ.ae`. Then `∫ x in s, f x ∂μ = μ s • c + o(μ s)`
as `s` tends to `l.small_sets`, i.e. for any `ε>0` there exists `t ∈ l` such that
`∥∫ x in s, f x ∂μ - μ s • c∥ ≤ ε * μ s` whenever `s ⊆ t`. We also formulate a version of this
theorem for a locally finite measure `μ` and a function `f` continuous at a point `a`.

## Notation

We provide the following notations for expressing the integral of a function on a set :
* `∫ a in s, f a ∂μ` is `measure_theory.integral (μ.restrict s) f`
* `∫ a in s, f a` is `∫ a in s, f a ∂volume`

Note that the set notations are defined in the file `measure_theory/integral/bochner`,
but we reference them here because all theorems about set integrals are in this file.

-/


noncomputable section

open Set Filter TopologicalSpace MeasureTheory Function

open Classical TopologicalSpace Interval BigOperators Filter Ennreal Nnreal MeasureTheory

variable {α β E F : Type _} [MeasurableSpace α]

namespace MeasureTheory

section NormedGroup

variable [NormedGroup E] {f g : α → E} {s t : Set α} {μ ν : Measure α} {l l' : Filter α}

variable [CompleteSpace E] [NormedSpace ℝ E]

theorem set_integral_congr_ae (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ :=
  integral_congr_ae ((ae_restrict_iff' hs).2 h)

theorem set_integral_congr (hs : MeasurableSet s) (h : EqOn f g s) : (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ :=
  set_integral_congr_ae hs <| eventually_of_forall h

theorem set_integral_congr_set_ae (hst : s =ᵐ[μ] t) : (∫ x in s, f x ∂μ) = ∫ x in t, f x ∂μ := by
  rw [measure.restrict_congr_set hst]

theorem integral_union_ae (hst : AeDisjoint μ s t) (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) : (∫ x in s ∪ t, f x ∂μ) = (∫ x in s, f x ∂μ) + ∫ x in t, f x ∂μ := by
  simp only [← integrable_on, ← measure.restrict_union₀ hst ht, ← integral_add_measure hfs hft]

theorem integral_union (hst : Disjoint s t) (ht : MeasurableSet t) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) : (∫ x in s ∪ t, f x ∂μ) = (∫ x in s, f x ∂μ) + ∫ x in t, f x ∂μ :=
  integral_union_ae hst.AeDisjoint ht.NullMeasurableSet hfs hft

theorem integral_diff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) (hts : t ⊆ s) :
    (∫ x in s \ t, f x ∂μ) = (∫ x in s, f x ∂μ) - ∫ x in t, f x ∂μ := by
  rw [eq_sub_iff_add_eq, ← integral_union, diff_union_of_subset hts]
  exacts[disjoint_diff.symm, ht, hfs.mono_set (diff_subset _ _), hft]

theorem integral_finset_bUnion {ι : Type _} (t : Finset ι) {s : ι → Set α} (hs : ∀, ∀ i ∈ t, ∀, MeasurableSet (s i))
    (h's : Set.Pairwise (↑t) (Disjoint on s)) (hf : ∀, ∀ i ∈ t, ∀, IntegrableOn f (s i) μ) :
    (∫ x in ⋃ i ∈ t, s i, f x ∂μ) = ∑ i in t, ∫ x in s i, f x ∂μ := by
  induction' t using Finset.induction_on with a t hat IH hs h's
  · simp
    
  · simp only [← Finset.coe_insert, ← Finset.forall_mem_insert, ← Set.pairwise_insert, ← Finset.set_bUnion_insert] at
      hs hf h's⊢
    rw [integral_union _ _ hf.1 (integrable_on_finset_Union.2 hf.2)]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
      
    · simp only [← disjoint_Union_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
      
    · exact Finset.measurable_set_bUnion _ hs.2
      
    

theorem integral_fintype_Union {ι : Type _} [Fintype ι] {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i))
    (h's : Pairwise (Disjoint on s)) (hf : ∀ i, IntegrableOn f (s i) μ) :
    (∫ x in ⋃ i, s i, f x ∂μ) = ∑ i, ∫ x in s i, f x ∂μ := by
  convert integral_finset_bUnion Finset.univ (fun i hi => hs i) _ fun i _ => hf i
  · simp
    
  · simp [← pairwise_univ, ← h's]
    

theorem integral_empty : (∫ x in ∅, f x ∂μ) = 0 := by
  rw [measure.restrict_empty, integral_zero_measure]

theorem integral_univ : (∫ x in univ, f x ∂μ) = ∫ x, f x ∂μ := by
  rw [measure.restrict_univ]

theorem integral_add_compl (hs : MeasurableSet s) (hfi : Integrable f μ) :
    ((∫ x in s, f x ∂μ) + ∫ x in sᶜ, f x ∂μ) = ∫ x, f x ∂μ := by
  rw [← integral_union (@disjoint_compl_right (Set α) _ _) hs.compl hfi.integrable_on hfi.integrable_on,
    union_compl_self, integral_univ]

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ x in s, f x ∂μ` defined as `∫ x, f x ∂(μ.restrict s)`. -/
theorem integral_indicator (hs : MeasurableSet s) : (∫ x, indicatorₓ s f x ∂μ) = ∫ x in s, f x ∂μ := by
  by_cases' hfi : integrable_on f s μ
  swap
  · rwa [integral_undef, integral_undef]
    rwa [integrable_indicator_iff hs]
    
  calc (∫ x, indicator s f x ∂μ) = (∫ x in s, indicator s f x ∂μ) + ∫ x in sᶜ, indicator s f x ∂μ :=
      (integral_add_compl hs (hfi.indicator hs)).symm _ = (∫ x in s, f x ∂μ) + ∫ x in sᶜ, 0 ∂μ :=
      congr_arg2ₓ (· + ·) (integral_congr_ae (indicator_ae_eq_restrict hs))
        (integral_congr_ae (indicator_ae_eq_restrict_compl hs))_ = ∫ x in s, f x ∂μ :=
      by
      simp

theorem set_integral_indicator (ht : MeasurableSet t) : (∫ x in s, t.indicator f x ∂μ) = ∫ x in s ∩ t, f x ∂μ := by
  rw [integral_indicator ht, measure.restrict_restrict ht, Set.inter_comm]

theorem of_real_set_integral_one_of_measure_ne_top {α : Type _} {m : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hs : μ s ≠ ∞) : Ennreal.ofReal (∫ x in s, (1 : ℝ) ∂μ) = μ s :=
  calc
    Ennreal.ofReal (∫ x in s, (1 : ℝ) ∂μ) = Ennreal.ofReal (∫ x in s, ∥(1 : ℝ)∥ ∂μ) := by
      simp only [← norm_one]
    _ = ∫⁻ x in s, 1 ∂μ := by
      rw [of_real_integral_norm_eq_lintegral_nnnorm (integrable_on_const.2 (Or.inr hs.lt_top))]
      simp only [← nnnorm_one, ← Ennreal.coe_one]
    _ = μ s := set_lintegral_one _
    

theorem of_real_set_integral_one {α : Type _} {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) :
    Ennreal.ofReal (∫ x in s, (1 : ℝ) ∂μ) = μ s :=
  of_real_set_integral_one_of_measure_ne_top (measure_ne_top μ s)

theorem integral_piecewise [DecidablePred (· ∈ s)] (hs : MeasurableSet s) {f g : α → E} (hf : IntegrableOn f s μ)
    (hg : IntegrableOn g (sᶜ) μ) : (∫ x, s.piecewise f g x ∂μ) = (∫ x in s, f x ∂μ) + ∫ x in sᶜ, g x ∂μ := by
  rw [← Set.indicator_add_compl_eq_piecewise, integral_add' (hf.indicator hs) (hg.indicator hs.compl),
    integral_indicator hs, integral_indicator hs.compl]

theorem tendsto_set_integral_of_monotone {ι : Type _} [Encodable ι] [SemilatticeSup ι] {s : ι → Set α} {f : α → E}
    (hsm : ∀ i, MeasurableSet (s i)) (h_mono : Monotone s) (hfi : IntegrableOn f (⋃ n, s n) μ) :
    Tendsto (fun i => ∫ a in s i, f a ∂μ) atTop (𝓝 (∫ a in ⋃ n, s n, f a ∂μ)) := by
  have hfi' : (∫⁻ x in ⋃ n, s n, ∥f x∥₊ ∂μ) < ∞ := hfi.2
  set S := ⋃ i, s i
  have hSm : MeasurableSet S := MeasurableSet.Union hsm
  have hsub : ∀ {i}, s i ⊆ S := subset_Union s
  rw [← with_density_apply _ hSm] at hfi'
  set ν := μ.with_density fun x => ∥f x∥₊ with hν
  refine' metric.nhds_basis_closed_ball.tendsto_right_iff.2 fun ε ε0 => _
  lift ε to ℝ≥0 using ε0.le
  have : ∀ᶠ i in at_top, ν (s i) ∈ Icc (ν S - ε) (ν S + ε) :=
    tendsto_measure_Union h_mono (Ennreal.Icc_mem_nhds hfi'.ne (Ennreal.coe_pos.2 ε0).ne')
  refine' this.mono fun i hi => _
  rw [mem_closed_ball_iff_norm', ← integral_diff (hsm i) hfi (hfi.mono_set hsub) hsub, ← coe_nnnorm, Nnreal.coe_le_coe,
    ← Ennreal.coe_le_coe]
  refine' (ennnorm_integral_le_lintegral_ennnorm _).trans _
  rw [← with_density_apply _ (hSm.diff (hsm _)), ← hν, measure_diff hsub (hsm _)]
  exacts[tsub_le_iff_tsub_le.mp hi.1, (hi.2.trans_lt <| Ennreal.add_lt_top.2 ⟨hfi', Ennreal.coe_lt_top⟩).Ne]

theorem has_sum_integral_Union_ae {ι : Type _} [Encodable ι] {s : ι → Set α} {f : α → E}
    (hm : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AeDisjoint μ on s)) (hfi : IntegrableOn f (⋃ i, s i) μ) :
    HasSum (fun n => ∫ a in s n, f a ∂μ) (∫ a in ⋃ n, s n, f a ∂μ) := by
  simp only [← integrable_on, ← measure.restrict_Union_ae hd hm] at hfi⊢
  exact has_sum_integral_measure hfi

theorem has_sum_integral_Union {ι : Type _} [Encodable ι] {s : ι → Set α} {f : α → E} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hfi : IntegrableOn f (⋃ i, s i) μ) :
    HasSum (fun n => ∫ a in s n, f a ∂μ) (∫ a in ⋃ n, s n, f a ∂μ) :=
  has_sum_integral_Union_ae (fun i => (hm i).NullMeasurableSet) (hd.mono fun i j h => h.AeDisjoint) hfi

theorem integral_Union {ι : Type _} [Encodable ι] {s : ι → Set α} {f : α → E} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hfi : IntegrableOn f (⋃ i, s i) μ) :
    (∫ a in ⋃ n, s n, f a ∂μ) = ∑' n, ∫ a in s n, f a ∂μ :=
  (HasSum.tsum_eq (has_sum_integral_Union hm hd hfi)).symm

theorem integral_Union_ae {ι : Type _} [Encodable ι] {s : ι → Set α} {f : α → E} (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : Pairwise (AeDisjoint μ on s)) (hfi : IntegrableOn f (⋃ i, s i) μ) :
    (∫ a in ⋃ n, s n, f a ∂μ) = ∑' n, ∫ a in s n, f a ∂μ :=
  (HasSum.tsum_eq (has_sum_integral_Union_ae hm hd hfi)).symm

theorem set_integral_eq_zero_of_forall_eq_zero {f : α → E} (hf : StronglyMeasurable f)
    (ht_eq : ∀, ∀ x ∈ t, ∀, f x = 0) : (∫ x in t, f x ∂μ) = 0 := by
  refine' integral_eq_zero_of_ae _
  rw [eventually_eq, ae_restrict_iff (hf.measurable_set_eq_fun strongly_measurable_zero)]
  refine' eventually_of_forall fun x hx => _
  rw [Pi.zero_apply]
  exact ht_eq x hx

theorem set_integral_union_eq_left {f : α → E} (hf : StronglyMeasurable f) (hfi : Integrable f μ) (hs : MeasurableSet s)
    (ht_eq : ∀, ∀ x ∈ t, ∀, f x = 0) : (∫ x in s ∪ t, f x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [← Set.union_diff_self, union_comm, integral_union,
    set_integral_eq_zero_of_forall_eq_zero _ fun x hx => ht_eq x (diff_subset _ _ hx), zero_addₓ]
  exacts[hf, disjoint_diff.symm, hs, hfi.integrable_on, hfi.integrable_on]

theorem set_integral_neg_eq_set_integral_nonpos [LinearOrderₓ E] [OrderClosedTopology E] {f : α → E}
    (hf : StronglyMeasurable f) (hfi : Integrable f μ) :
    (∫ x in { x | f x < 0 }, f x ∂μ) = ∫ x in { x | f x ≤ 0 }, f x ∂μ := by
  have h_union : { x | f x ≤ 0 } = { x | f x < 0 } ∪ { x | f x = 0 } := by
    ext
    simp_rw [Set.mem_union_eq, Set.mem_set_of_eq]
    exact le_iff_lt_or_eqₓ
  rw [h_union]
  exact (set_integral_union_eq_left hf hfi (hf.measurable_set_lt strongly_measurable_const) fun x hx => hx).symm

theorem integral_norm_eq_pos_sub_neg {f : α → ℝ} (hf : StronglyMeasurable f) (hfi : Integrable f μ) :
    (∫ x, ∥f x∥ ∂μ) = (∫ x in { x | 0 ≤ f x }, f x ∂μ) - ∫ x in { x | f x ≤ 0 }, f x ∂μ :=
  have h_meas : MeasurableSet { x | 0 ≤ f x } := strongly_measurable_const.measurable_set_le hf
  calc
    (∫ x, ∥f x∥ ∂μ) = (∫ x in { x | 0 ≤ f x }, ∥f x∥ ∂μ) + ∫ x in { x | 0 ≤ f x }ᶜ, ∥f x∥ ∂μ := by
      rw [← integral_add_compl h_meas hfi.norm]
    _ = (∫ x in { x | 0 ≤ f x }, f x ∂μ) + ∫ x in { x | 0 ≤ f x }ᶜ, ∥f x∥ ∂μ := by
      congr 1
      refine' set_integral_congr h_meas fun x hx => _
      dsimp' only
      rw [Real.norm_eq_abs, abs_eq_self.mpr _]
      exact hx
    _ = (∫ x in { x | 0 ≤ f x }, f x ∂μ) - ∫ x in { x | 0 ≤ f x }ᶜ, f x ∂μ := by
      congr 1
      rw [← integral_neg]
      refine' set_integral_congr h_meas.compl fun x hx => _
      dsimp' only
      rw [Real.norm_eq_abs, abs_eq_neg_self.mpr _]
      rw [Set.mem_compl_iff, Set.nmem_set_of_eq] at hx
      linarith
    _ = (∫ x in { x | 0 ≤ f x }, f x ∂μ) - ∫ x in { x | f x ≤ 0 }, f x ∂μ := by
      rw [← set_integral_neg_eq_set_integral_nonpos hf hfi]
      congr
      ext1 x
      simp
    

theorem set_integral_const (c : E) : (∫ x in s, c ∂μ) = (μ s).toReal • c := by
  rw [integral_const, measure.restrict_apply_univ]

@[simp]
theorem integral_indicator_const (e : E) ⦃s : Set α⦄ (s_meas : MeasurableSet s) :
    (∫ a : α, s.indicator (fun x : α => e) a ∂μ) = (μ s).toReal • e := by
  rw [integral_indicator s_meas, ← set_integral_const]

@[simp]
theorem integral_indicator_one ⦃s : Set α⦄ (hs : MeasurableSet s) : (∫ a, s.indicator 1 a ∂μ) = (μ s).toReal :=
  (integral_indicator_const 1 hs).trans ((smul_eq_mul _).trans (mul_oneₓ _))

theorem set_integral_indicator_const_Lp {p : ℝ≥0∞} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (x : E) : (∫ a in s, indicatorConstLp p ht hμt x a ∂μ) = (μ (t ∩ s)).toReal • x :=
  calc
    (∫ a in s, indicatorConstLp p ht hμt x a ∂μ) = ∫ a in s, t.indicator (fun _ => x) a ∂μ := by
      rw [set_integral_congr_ae hs (indicator_const_Lp_coe_fn.mono fun x hx hxs => hx)]
    _ = (μ (t ∩ s)).toReal • x := by
      rw [integral_indicator_const _ ht, measure.restrict_apply ht]
    

theorem integral_indicator_const_Lp {p : ℝ≥0∞} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (x : E) :
    (∫ a, indicatorConstLp p ht hμt x a ∂μ) = (μ t).toReal • x :=
  calc
    (∫ a, indicatorConstLp p ht hμt x a ∂μ) = ∫ a in univ, indicatorConstLp p ht hμt x a ∂μ := by
      rw [integral_univ]
    _ = (μ (t ∩ univ)).toReal • x := set_integral_indicator_const_Lp MeasurableSet.univ ht hμt x
    _ = (μ t).toReal • x := by
      rw [inter_univ]
    

theorem set_integral_map {β} [MeasurableSpace β] {g : α → β} {f : β → E} {s : Set β} (hs : MeasurableSet s)
    (hf : AeStronglyMeasurable f (Measure.map g μ)) (hg : AeMeasurable g μ) :
    (∫ y in s, f y ∂Measure.map g μ) = ∫ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [measure.restrict_map_of_ae_measurable hg hs,
    integral_map (hg.mono_measure measure.restrict_le_self) (hf.mono_measure _)]
  exact measure.map_mono_of_ae_measurable measure.restrict_le_self hg

theorem _root_.measurable_embedding.set_integral_map {β} {_ : MeasurableSpace β} {f : α → β}
    (hf : MeasurableEmbedding f) (g : β → E) (s : Set β) :
    (∫ y in s, g y ∂Measure.map f μ) = ∫ x in f ⁻¹' s, g (f x) ∂μ := by
  rw [hf.restrict_map, hf.integral_map]

theorem _root_.closed_embedding.set_integral_map [TopologicalSpace α] [BorelSpace α] {β} [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β] {g : α → β} {f : β → E} (s : Set β) (hg : ClosedEmbedding g) :
    (∫ y in s, f y ∂Measure.map g μ) = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
  hg.MeasurableEmbedding.set_integral_map _ _

theorem MeasurePreserving.set_integral_preimage_emb {β} {_ : MeasurableSpace β} {f : α → β} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β → E) (s : Set β) :
    (∫ x in f ⁻¹' s, g (f x) ∂μ) = ∫ y in s, g y ∂ν :=
  (h₁.restrict_preimage_emb h₂ s).integral_comp h₂ _

theorem MeasurePreserving.set_integral_image_emb {β} {_ : MeasurableSpace β} {f : α → β} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β → E) (s : Set α) :
    (∫ y in f '' s, g y ∂ν) = ∫ x in s, g (f x) ∂μ :=
  Eq.symm <| (h₁.restrict_image_emb h₂ s).integral_comp h₂ _

theorem set_integral_map_equiv {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β → E) (s : Set β) :
    (∫ y in s, f y ∂Measure.map e μ) = ∫ x in e ⁻¹' s, f (e x) ∂μ :=
  e.MeasurableEmbedding.set_integral_map f s

theorem norm_set_integral_le_of_norm_le_const_ae {C : ℝ} (hs : μ s < ∞) (hC : ∀ᵐ x ∂μ.restrict s, ∥f x∥ ≤ C) :
    ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).toReal := by
  rw [← measure.restrict_apply_univ] at *
  have : is_finite_measure (μ.restrict s) := ⟨‹_›⟩
  exact norm_integral_le_of_norm_le_const hC

theorem norm_set_integral_le_of_norm_le_const_ae' {C : ℝ} (hs : μ s < ∞) (hC : ∀ᵐ x ∂μ, x ∈ s → ∥f x∥ ≤ C)
    (hfm : AeStronglyMeasurable f (μ.restrict s)) : ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).toReal := by
  apply norm_set_integral_le_of_norm_le_const_ae hs
  have A : ∀ᵐ x : α ∂μ, x ∈ s → ∥ae_strongly_measurable.mk f hfm x∥ ≤ C := by
    filter_upwards [hC, hfm.ae_mem_imp_eq_mk] with _ h1 h2 h3
    rw [← h2 h3]
    exact h1 h3
  have B : MeasurableSet { x | ∥(hfm.mk f) x∥ ≤ C } := hfm.strongly_measurable_mk.norm.measurable measurable_set_Iic
  filter_upwards [hfm.ae_eq_mk, (ae_restrict_iff B).2 A] with _ h1 _
  rwa [h1]

theorem norm_set_integral_le_of_norm_le_const_ae'' {C : ℝ} (hs : μ s < ∞) (hsm : MeasurableSet s)
    (hC : ∀ᵐ x ∂μ, x ∈ s → ∥f x∥ ≤ C) : ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).toReal :=
  norm_set_integral_le_of_norm_le_const_ae hs <| by
    rwa [ae_restrict_eq hsm, eventually_inf_principal]

theorem norm_set_integral_le_of_norm_le_const {C : ℝ} (hs : μ s < ∞) (hC : ∀, ∀ x ∈ s, ∀, ∥f x∥ ≤ C)
    (hfm : AeStronglyMeasurable f (μ.restrict s)) : ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).toReal :=
  norm_set_integral_le_of_norm_le_const_ae' hs (eventually_of_forall hC) hfm

theorem norm_set_integral_le_of_norm_le_const' {C : ℝ} (hs : μ s < ∞) (hsm : MeasurableSet s)
    (hC : ∀, ∀ x ∈ s, ∀, ∥f x∥ ≤ C) : ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).toReal :=
  norm_set_integral_le_of_norm_le_const_ae'' hs hsm <| eventually_of_forall hC

theorem set_integral_eq_zero_iff_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f) (hfi : IntegrableOn f s μ) :
    (∫ x in s, f x ∂μ) = 0 ↔ f =ᵐ[μ.restrict s] 0 :=
  integral_eq_zero_iff_of_nonneg_ae hf hfi

theorem set_integral_pos_iff_support_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f) (hfi : IntegrableOn f s μ) :
    (0 < ∫ x in s, f x ∂μ) ↔ 0 < μ (Support f ∩ s) := by
  rw [integral_pos_iff_support_of_nonneg_ae hf hfi, measure.restrict_apply₀]
  rw [support_eq_preimage]
  exact hfi.ae_strongly_measurable.ae_measurable.null_measurable (measurable_set_singleton 0).compl

theorem set_integral_trim {α} {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0) {f : α → E}
    (hf_meas : strongly_measurable[m] f) {s : Set α} (hs : measurable_set[m] s) :
    (∫ x in s, f x ∂μ) = ∫ x in s, f x ∂μ.trim hm := by
  rwa [integral_trim hm hf_meas, restrict_trim hm μ]

theorem integral_Icc_eq_integral_Ioc' [PartialOrderₓ α] {f : α → E} {a b : α} (ha : μ {a} = 0) :
    (∫ t in Icc a b, f t ∂μ) = ∫ t in Ioc a b, f t ∂μ :=
  set_integral_congr_set_ae (Ioc_ae_eq_Icc' ha).symm

theorem integral_Ioc_eq_integral_Ioo' [PartialOrderₓ α] {f : α → E} {a b : α} (hb : μ {b} = 0) :
    (∫ t in Ioc a b, f t ∂μ) = ∫ t in Ioo a b, f t ∂μ :=
  set_integral_congr_set_ae (Ioo_ae_eq_Ioc' hb).symm

theorem integral_Icc_eq_integral_Ioc [PartialOrderₓ α] {f : α → E} {a b : α} [HasNoAtoms μ] :
    (∫ t in Icc a b, f t ∂μ) = ∫ t in Ioc a b, f t ∂μ :=
  integral_Icc_eq_integral_Ioc' <| measure_singleton a

theorem integral_Ioc_eq_integral_Ioo [PartialOrderₓ α] {f : α → E} {a b : α} [HasNoAtoms μ] :
    (∫ t in Ioc a b, f t ∂μ) = ∫ t in Ioo a b, f t ∂μ :=
  integral_Ioc_eq_integral_Ioo' <| measure_singleton b

end NormedGroup

section Mono

variable {μ : Measure α} {f g : α → ℝ} {s t : Set α} (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)

theorem set_integral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict s] g) : (∫ a in s, f a ∂μ) ≤ ∫ a in s, g a ∂μ :=
  integral_mono_ae hf hg h

theorem set_integral_mono_ae (h : f ≤ᵐ[μ] g) : (∫ a in s, f a ∂μ) ≤ ∫ a in s, g a ∂μ :=
  set_integral_mono_ae_restrict hf hg (ae_restrict_of_ae h)

theorem set_integral_mono_on (hs : MeasurableSet s) (h : ∀, ∀ x ∈ s, ∀, f x ≤ g x) :
    (∫ a in s, f a ∂μ) ≤ ∫ a in s, g a ∂μ :=
  set_integral_mono_ae_restrict hf hg
    (by
      simp [← hs, ← eventually_le, ← eventually_inf_principal, ← ae_of_all _ h])

include hf hg

-- why do I need this include, but we don't need it in other lemmas?
theorem set_integral_mono_on_ae (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
    (∫ a in s, f a ∂μ) ≤ ∫ a in s, g a ∂μ := by
  refine' set_integral_mono_ae_restrict hf hg _
  rwa [eventually_le, ae_restrict_iff' hs]

omit hf hg

theorem set_integral_mono (h : f ≤ g) : (∫ a in s, f a ∂μ) ≤ ∫ a in s, g a ∂μ :=
  integral_mono hf hg h

theorem set_integral_mono_set (hfi : IntegrableOn f t μ) (hf : 0 ≤ᵐ[μ.restrict t] f) (hst : s ≤ᵐ[μ] t) :
    (∫ x in s, f x ∂μ) ≤ ∫ x in t, f x ∂μ :=
  integral_mono_measure (Measure.restrict_mono_ae hst) hf hfi

theorem set_integral_ge_of_const_le {c : ℝ} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (hf : ∀, ∀ x ∈ s, ∀, c ≤ f x)
    (hfint : IntegrableOn (fun x : α => f x) s μ) : c * (μ s).toReal ≤ ∫ x in s, f x ∂μ := by
  rw [mul_comm, ← smul_eq_mul, ← set_integral_const c]
  exact set_integral_mono_on (integrable_on_const.2 (Or.inr hμs.lt_top)) hfint hs hf

end Mono

section Nonneg

variable {μ : Measure α} {f : α → ℝ} {s : Set α}

theorem set_integral_nonneg_of_ae_restrict (hf : 0 ≤ᵐ[μ.restrict s] f) : 0 ≤ ∫ a in s, f a ∂μ :=
  integral_nonneg_of_ae hf

theorem set_integral_nonneg_of_ae (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ a in s, f a ∂μ :=
  set_integral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)

theorem set_integral_nonneg (hs : MeasurableSet s) (hf : ∀ a, a ∈ s → 0 ≤ f a) : 0 ≤ ∫ a in s, f a ∂μ :=
  set_integral_nonneg_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

theorem set_integral_nonneg_ae (hs : MeasurableSet s) (hf : ∀ᵐ a ∂μ, a ∈ s → 0 ≤ f a) : 0 ≤ ∫ a in s, f a ∂μ :=
  set_integral_nonneg_of_ae_restrict <| by
    rwa [eventually_le, ae_restrict_iff' hs]

theorem set_integral_le_nonneg {s : Set α} (hs : MeasurableSet s) (hf : StronglyMeasurable f) (hfi : Integrable f μ) :
    (∫ x in s, f x ∂μ) ≤ ∫ x in { y | 0 ≤ f y }, f x ∂μ := by
  rw [← integral_indicator hs, ← integral_indicator (strongly_measurable_const.measurable_set_le hf)]
  exact
    integral_mono (hfi.indicator hs) (hfi.indicator (strongly_measurable_const.measurable_set_le hf))
      (indicator_le_indicator_nonneg s f)

theorem set_integral_nonpos_of_ae_restrict (hf : f ≤ᵐ[μ.restrict s] 0) : (∫ a in s, f a ∂μ) ≤ 0 :=
  integral_nonpos_of_ae hf

theorem set_integral_nonpos_of_ae (hf : f ≤ᵐ[μ] 0) : (∫ a in s, f a ∂μ) ≤ 0 :=
  set_integral_nonpos_of_ae_restrict (ae_restrict_of_ae hf)

theorem set_integral_nonpos (hs : MeasurableSet s) (hf : ∀ a, a ∈ s → f a ≤ 0) : (∫ a in s, f a ∂μ) ≤ 0 :=
  set_integral_nonpos_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

theorem set_integral_nonpos_ae (hs : MeasurableSet s) (hf : ∀ᵐ a ∂μ, a ∈ s → f a ≤ 0) : (∫ a in s, f a ∂μ) ≤ 0 :=
  set_integral_nonpos_of_ae_restrict <| by
    rwa [eventually_le, ae_restrict_iff' hs]

theorem set_integral_nonpos_le {s : Set α} (hs : MeasurableSet s) (hf : StronglyMeasurable f) (hfi : Integrable f μ) :
    (∫ x in { y | f y ≤ 0 }, f x ∂μ) ≤ ∫ x in s, f x ∂μ := by
  rw [← integral_indicator hs, ← integral_indicator (hf.measurable_set_le strongly_measurable_const)]
  exact
    integral_mono (hfi.indicator (hf.measurable_set_le strongly_measurable_const)) (hfi.indicator hs)
      (indicator_nonpos_le_indicator s f)

end Nonneg

section TendstoMono

variable {μ : Measure α} [NormedGroup E] [CompleteSpace E] [NormedSpace ℝ E] {s : ℕ → Set α} {f : α → E}

-- ./././Mathport/Syntax/Translate/Basic.lean:646:40: in filter_upwards #[[], ["with", ident a], ["using", expr le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)]]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: parse error
theorem _root_.antitone.tendsto_set_integral (hsm : ∀ i, MeasurableSet (s i)) (h_anti : Antitone s)
    (hfi : IntegrableOn f (s 0) μ) : Tendsto (fun i => ∫ a in s i, f a ∂μ) atTop (𝓝 (∫ a in ⋂ n, s n, f a ∂μ)) := by
  let bound : α → ℝ := indicator (s 0) fun a => ∥f a∥
  have h_int_eq : (fun i => ∫ a in s i, f a ∂μ) = fun i => ∫ a, (s i).indicator f a ∂μ :=
    funext fun i => (integral_indicator (hsm i)).symm
  rw [h_int_eq]
  rw [← integral_indicator (MeasurableSet.Inter hsm)]
  refine' tendsto_integral_of_dominated_convergence bound _ _ _ _
  · intro n
    rw [ae_strongly_measurable_indicator_iff (hsm n)]
    exact (integrable_on.mono_set hfi (h_anti (zero_le n))).1
    
  · rw [integrable_indicator_iff (hsm 0)]
    exact hfi.norm
    
  · simp_rw [norm_indicator_eq_indicator_norm]
    refine' fun n => eventually_of_forall fun x => _
    exact indicator_le_indicator_of_subset (h_anti (zero_le n)) (fun a => norm_nonneg _) _
    
  · trace
      "./././Mathport/Syntax/Translate/Basic.lean:646:40: in filter_upwards #[[], [\"with\", ident a], [\"using\", expr le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)]]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: parse error"
    

end TendstoMono

/-! ### Continuity of the set integral

We prove that for any set `s`, the function `λ f : α →₁[μ] E, ∫ x in s, f x ∂μ` is continuous. -/


section ContinuousSetIntegral

variable [NormedGroup E] {𝕜 : Type _} [NormedField 𝕜] [NormedGroup F] [NormedSpace 𝕜 F] {p : ℝ≥0∞} {μ : Measure α}

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map is additive. -/
theorem Lp_to_Lp_restrict_add (f g : lp E p μ) (s : Set α) :
    ((lp.mem_ℒp (f + g)).restrict s).toLp ⇑(f + g) =
      ((lp.mem_ℒp f).restrict s).toLp f + ((lp.mem_ℒp g).restrict s).toLp g :=
  by
  ext1
  refine' (ae_restrict_of_ae (Lp.coe_fn_add f g)).mp _
  refine' (Lp.coe_fn_add (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s)) (mem_ℒp.to_Lp g ((Lp.mem_ℒp g).restrict s))).mp _
  refine' (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _
  refine' (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp g).restrict s)).mp _
  refine' (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (f + g)).restrict s)).mono fun x hx1 hx2 hx3 hx4 hx5 => _
  rw [hx4, hx1, Pi.add_apply, hx2, hx3, hx5, Pi.add_apply]

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map commutes with scalar multiplication. -/
theorem Lp_to_Lp_restrict_smul (c : 𝕜) (f : lp F p μ) (s : Set α) :
    ((lp.mem_ℒp (c • f)).restrict s).toLp ⇑(c • f) = c • ((lp.mem_ℒp f).restrict s).toLp f := by
  ext1
  refine' (ae_restrict_of_ae (Lp.coe_fn_smul c f)).mp _
  refine' (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _
  refine' (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (c • f)).restrict s)).mp _
  refine' (Lp.coe_fn_smul c (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))).mono fun x hx1 hx2 hx3 hx4 => _
  rw [hx2, hx1, Pi.smul_apply, hx3, hx4, Pi.smul_apply]

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map is non-expansive. -/
theorem norm_Lp_to_Lp_restrict_le (s : Set α) (f : lp E p μ) : ∥((lp.mem_ℒp f).restrict s).toLp f∥ ≤ ∥f∥ := by
  rw [Lp.norm_def, Lp.norm_def, Ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _)]
  refine' (le_of_eqₓ _).trans (snorm_mono_measure _ measure.restrict_le_self)
  · exact s
    
  exact snorm_congr_ae (mem_ℒp.coe_fn_to_Lp _)

variable (α F 𝕜)

/-- Continuous linear map sending a function of `Lp F p μ` to the same function in
`Lp F p (μ.restrict s)`. -/
def lpToLpRestrictClm (μ : Measure α) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (s : Set α) :
    lp F p μ →L[𝕜] lp F p (μ.restrict s) :=
  @LinearMap.mkContinuous 𝕜 𝕜 (lp F p μ) (lp F p (μ.restrict s)) _ _ _ _ _ _ (RingHom.id 𝕜)
    ⟨fun f => Memℒp.toLp f ((lp.mem_ℒp f).restrict s), fun f g => Lp_to_Lp_restrict_add f g s, fun c f =>
      Lp_to_Lp_restrict_smul c f s⟩
    1
    (by
      intro f
      rw [one_mulₓ]
      exact norm_Lp_to_Lp_restrict_le s f)

variable {α F 𝕜}

variable (𝕜)

theorem Lp_to_Lp_restrict_clm_coe_fn [hp : Fact (1 ≤ p)] (s : Set α) (f : lp F p μ) :
    lpToLpRestrictClm α F 𝕜 μ p s f =ᵐ[μ.restrict s] f :=
  Memℒp.coe_fn_to_Lp ((lp.mem_ℒp f).restrict s)

variable {𝕜}

@[continuity]
theorem continuous_set_integral [NormedSpace ℝ E] [CompleteSpace E] (s : Set α) :
    Continuous fun f : α →₁[μ] E => ∫ x in s, f x ∂μ := by
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  have h_comp :
    (fun f : α →₁[μ] E => ∫ x in s, f x ∂μ) = integral (μ.restrict s) ∘ fun f => Lp_to_Lp_restrict_clm α E ℝ μ 1 s f :=
    by
    ext1 f
    rw [Function.comp_applyₓ, integral_congr_ae (Lp_to_Lp_restrict_clm_coe_fn ℝ s f)]
  rw [h_comp]
  exact continuous_integral.comp (Lp_to_Lp_restrict_clm α E ℝ μ 1 s).Continuous

end ContinuousSetIntegral

end MeasureTheory

open MeasureTheory Asymptotics Metric

variable {ι : Type _} [NormedGroup E]

/-- Fundamental theorem of calculus for set integrals: if `μ` is a measure that is finite at a
filter `l` and `f` is a measurable function that has a finite limit `b` at `l ⊓ μ.ae`, then `∫ x in
s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that `s i` tends to `l.small_sets`
along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem Filter.Tendsto.integral_sub_linear_is_o_ae [NormedSpace ℝ E] [CompleteSpace E] {μ : Measureₓ α} {l : Filter α}
    [l.IsMeasurablyGenerated] {f : α → E} {b : E} (h : Tendsto f (l⊓μ.ae) (𝓝 b))
    (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l) {s : ι → Set α} {li : Filter ι}
    (hs : Tendsto s li l.smallSets) (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by
      run_tac
        tactic.interactive.refl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • b) =o[li] m := by
  suffices : (fun s => (∫ x in s, f x ∂μ) - (μ s).toReal • b) =o[l.small_sets] fun s => (μ s).toReal
  exact (this.comp_tendsto hs).congr' (hsμ.mono fun a ha => ha ▸ rfl) hsμ
  refine' is_o_iff.2 fun ε ε₀ => _
  have : ∀ᶠ s in l.small_sets, ∀ᶠ x in μ.ae, x ∈ s → f x ∈ closed_ball b ε :=
    eventually_small_sets_eventually.2 (h.eventually <| closed_ball_mem_nhds _ ε₀)
  filter_upwards [hμ.eventually, (hμ.integrable_at_filter_of_tendsto_ae hfm h).Eventually, hfm.eventually, this]
  simp only [← mem_closed_ball, ← dist_eq_norm]
  intro s hμs h_integrable hfm h_norm
  rw [← set_integral_const, ← integral_sub h_integrable (integrable_on_const.2 <| Or.inr hμs), Real.norm_eq_abs,
    abs_of_nonneg Ennreal.to_real_nonneg]
  exact norm_set_integral_le_of_norm_le_const_ae' hμs h_norm (hfm.sub ae_strongly_measurable_const)

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure and `f` is an almost everywhere measurable function that is continuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).small_sets` along `li`.  Since `μ (s i)` is an `ℝ≥0∞`
number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem ContinuousWithinAt.integral_sub_linear_is_o_ae [TopologicalSpace α] [OpensMeasurableSpace α] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measureₓ α} [IsLocallyFiniteMeasure μ] {a : α} {t : Set α} {f : α → E}
    (ha : ContinuousWithinAt f t a) (ht : MeasurableSet t) (hfm : StronglyMeasurableAtFilter f (𝓝[t] a) μ)
    {s : ι → Set α} {li : Filter ι} (hs : Tendsto s li (𝓝[t] a).smallSets) (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by
      run_tac
        tactic.interactive.refl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f a) =o[li] m :=
  have : (𝓝[t] a).IsMeasurablyGenerated := ht.nhds_within_is_measurably_generated _
  (ha.mono_left inf_le_left).integral_sub_linear_is_o_ae hfm (μ.finite_at_nhds_within a t) hs m hsμ

/-- Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a locally finite
measure and `f` is an almost everywhere measurable function that is continuous at a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tends to
`(𝓝 a).small_sets` along `li.  Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in
the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem ContinuousAt.integral_sub_linear_is_o_ae [TopologicalSpace α] [OpensMeasurableSpace α] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measureₓ α} [IsLocallyFiniteMeasure μ] {a : α} {f : α → E} (ha : ContinuousAt f a)
    (hfm : StronglyMeasurableAtFilter f (𝓝 a) μ) {s : ι → Set α} {li : Filter ι} (hs : Tendsto s li (𝓝 a).smallSets)
    (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by
      run_tac
        tactic.interactive.refl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f a) =o[li] m :=
  (ha.mono_left inf_le_left).integral_sub_linear_is_o_ae hfm (μ.finite_at_nhds a) hs m hsμ

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).small_sets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem ContinuousOn.integral_sub_linear_is_o_ae [TopologicalSpace α] [OpensMeasurableSpace α] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopologyEither α E] {μ : Measureₓ α} [IsLocallyFiniteMeasure μ] {a : α}
    {t : Set α} {f : α → E} (hft : ContinuousOn f t) (ha : a ∈ t) (ht : MeasurableSet t) {s : ι → Set α} {li : Filter ι}
    (hs : Tendsto s li (𝓝[t] a).smallSets) (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by
      run_tac
        tactic.interactive.refl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f a) =o[li] m :=
  (hft a ha).integral_sub_linear_is_o_ae ht ⟨t, self_mem_nhds_within, hft.AeStronglyMeasurable ht⟩ hs m hsμ

section

/-! ### Continuous linear maps composed with integration

The goal of this section is to prove that integration commutes with continuous linear maps.
This holds for simple functions. The general result follows from the continuity of all involved
operations on the space `L¹`. Note that composition by a continuous linear map on `L¹` is not just
the composition, as we are dealing with classes of functions, but it has already been defined
as `continuous_linear_map.comp_Lp`. We take advantage of this construction here.
-/


open ComplexConjugate

variable {μ : Measureₓ α} {𝕜 : Type _} [IsROrC 𝕜] [NormedSpace 𝕜 E] [NormedGroup F] [NormedSpace 𝕜 F] {p : Ennreal}

namespace ContinuousLinearMap

variable [CompleteSpace F] [NormedSpace ℝ F]

theorem integral_comp_Lp (L : E →L[𝕜] F) (φ : lp E p μ) : (∫ a, (L.compLp φ) a ∂μ) = ∫ a, L (φ a) ∂μ :=
  integral_congr_ae <| coe_fn_comp_Lp _ _

theorem set_integral_comp_Lp (L : E →L[𝕜] F) (φ : lp E p μ) {s : Set α} (hs : MeasurableSet s) :
    (∫ a in s, (L.compLp φ) a ∂μ) = ∫ a in s, L (φ a) ∂μ :=
  set_integral_congr_ae hs ((L.coe_fn_comp_Lp φ).mono fun x hx hx2 => hx)

theorem continuous_integral_comp_L1 (L : E →L[𝕜] F) : Continuous fun φ : α →₁[μ] E => ∫ a : α, L (φ a) ∂μ := by
  rw [← funext L.integral_comp_Lp]
  exact continuous_integral.comp (L.comp_LpL 1 μ).Continuous

variable [CompleteSpace E] [NormedSpace ℝ E]

theorem integral_comp_comm (L : E →L[𝕜] F) {φ : α → E} (φ_int : Integrable φ μ) : (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ) :=
  by
  apply integrable.induction fun φ => (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ)
  · intro e s s_meas s_finite
    rw [integral_indicator_const e s_meas, ← @smul_one_smul E ℝ 𝕜 _ _ _ _ _ (μ s).toReal e,
      ContinuousLinearMap.map_smul, @smul_one_smul F ℝ 𝕜 _ _ _ _ _ (μ s).toReal (L e), ←
      integral_indicator_const (L e) s_meas]
    congr 1 with a
    rw [Set.indicator_comp_of_zero L.map_zero]
    
  · intro f g H f_int g_int hf hg
    simp [← L.map_add, ← integral_add f_int g_int, ← integral_add (L.integrable_comp f_int) (L.integrable_comp g_int), ←
      hf, ← hg]
    
  · exact is_closed_eq L.continuous_integral_comp_L1 (L.continuous.comp continuous_integral)
    
  · intro f g hfg f_int hf
    convert hf using 1 <;> clear hf
    · exact integral_congr_ae (hfg.fun_comp L).symm
      
    · rw [integral_congr_ae hfg.symm]
      
    
  all_goals
    assumption

theorem integral_apply {H : Type _} [NormedGroup H] [NormedSpace 𝕜 H] {φ : α → H →L[𝕜] E} (φ_int : Integrable φ μ)
    (v : H) : (∫ a, φ a ∂μ) v = ∫ a, φ a v ∂μ :=
  ((ContinuousLinearMap.apply 𝕜 E v).integral_comp_comm φ_int).symm

theorem integral_comp_comm' (L : E →L[𝕜] F) {K} (hL : AntilipschitzWith K L) (φ : α → E) :
    (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ) := by
  by_cases' h : integrable φ μ
  · exact integral_comp_comm L h
    
  have : ¬integrable (L ∘ φ) μ := by
    rwa [lipschitz_with.integrable_comp_iff_of_antilipschitz L.lipschitz hL L.map_zero]
  simp [← integral_undef, ← h, ← this]

theorem integral_comp_L1_comm (L : E →L[𝕜] F) (φ : α →₁[μ] E) : (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ) :=
  L.integral_comp_comm (L1.integrable_coe_fn φ)

end ContinuousLinearMap

namespace LinearIsometry

variable [CompleteSpace F] [NormedSpace ℝ F] [CompleteSpace E] [NormedSpace ℝ E]

theorem integral_comp_comm (L : E →ₗᵢ[𝕜] F) (φ : α → E) : (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ) :=
  L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _

end LinearIsometry

variable [CompleteSpace E] [NormedSpace ℝ E] [CompleteSpace F] [NormedSpace ℝ F]

@[norm_cast]
theorem integral_of_real {f : α → ℝ} : (∫ a, (f a : 𝕜) ∂μ) = ↑(∫ a, f a ∂μ) :=
  (@IsROrC.ofRealLi 𝕜 _).integral_comp_comm f

theorem integral_re {f : α → 𝕜} (hf : Integrable f μ) : (∫ a, IsROrC.re (f a) ∂μ) = IsROrC.re (∫ a, f a ∂μ) :=
  (@IsROrC.reClm 𝕜 _).integral_comp_comm hf

theorem integral_im {f : α → 𝕜} (hf : Integrable f μ) : (∫ a, IsROrC.im (f a) ∂μ) = IsROrC.im (∫ a, f a ∂μ) :=
  (@IsROrC.imClm 𝕜 _).integral_comp_comm hf

theorem integral_conj {f : α → 𝕜} : (∫ a, conj (f a) ∂μ) = conj (∫ a, f a ∂μ) :=
  (@IsROrC.conjLie 𝕜 _).toLinearIsometry.integral_comp_comm f

theorem integral_coe_re_add_coe_im {f : α → 𝕜} (hf : Integrable f μ) :
    (∫ x, (IsROrC.re (f x) : 𝕜) ∂μ) + (∫ x, IsROrC.im (f x) ∂μ) * IsROrC.i = ∫ x, f x ∂μ := by
  rw [mul_comm, ← smul_eq_mul, ← integral_smul, ← integral_add]
  · congr
    ext1 x
    rw [smul_eq_mul, mul_comm, IsROrC.re_add_im]
    
  · exact hf.re.of_real
    
  · exact hf.im.of_real.smul IsROrC.i
    

theorem integral_re_add_im {f : α → 𝕜} (hf : Integrable f μ) :
    ((∫ x, IsROrC.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x, IsROrC.im (f x) ∂μ : ℝ) * IsROrC.i = ∫ x, f x ∂μ := by
  rw [← integral_of_real, ← integral_of_real, integral_coe_re_add_coe_im hf]

theorem set_integral_re_add_im {f : α → 𝕜} {i : Set α} (hf : IntegrableOn f i μ) :
    ((∫ x in i, IsROrC.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x in i, IsROrC.im (f x) ∂μ : ℝ) * IsROrC.i = ∫ x in i, f x ∂μ :=
  integral_re_add_im hf

theorem fst_integral {f : α → E × F} (hf : Integrable f μ) : (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ :=
  ((ContinuousLinearMap.fst ℝ E F).integral_comp_comm hf).symm

theorem snd_integral {f : α → E × F} (hf : Integrable f μ) : (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ :=
  ((ContinuousLinearMap.snd ℝ E F).integral_comp_comm hf).symm

theorem integral_pair {f : α → E} {g : α → F} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, (f x, g x) ∂μ) = (∫ x, f x ∂μ, ∫ x, g x ∂μ) :=
  have := hf.prod_mk hg
  Prod.extₓ (fst_integral this) (snd_integral this)

theorem integral_smul_const {𝕜 : Type _} [IsROrC 𝕜] [NormedSpace 𝕜 E] (f : α → 𝕜) (c : E) :
    (∫ x, f x • c ∂μ) = (∫ x, f x ∂μ) • c := by
  by_cases' hf : integrable f μ
  · exact ((1 : 𝕜 →L[𝕜] 𝕜).smul_right c).integral_comp_comm hf
    
  · by_cases' hc : c = 0
    · simp only [← hc, ← integral_zero, ← smul_zero]
      
    rw [integral_undef hf, integral_undef, zero_smul]
    simp_rw [integrable_smul_const hc, hf, not_false_iff]
    

section Inner

variable {E' : Type _} [InnerProductSpace 𝕜 E'] [CompleteSpace E'] [NormedSpace ℝ E']

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 E' _ x y

theorem integral_inner {f : α → E'} (hf : Integrable f μ) (c : E') : (∫ x, ⟪c, f x⟫ ∂μ) = ⟪c, ∫ x, f x ∂μ⟫ :=
  ((@innerSL 𝕜 E' _ _ c).restrictScalars ℝ).integral_comp_comm hf

theorem integral_eq_zero_of_forall_integral_inner_eq_zero (f : α → E') (hf : Integrable f μ)
    (hf_int : ∀ c : E', (∫ x, ⟪c, f x⟫ ∂μ) = 0) : (∫ x, f x ∂μ) = 0 := by
  specialize hf_int (∫ x, f x ∂μ)
  rwa [integral_inner hf, inner_self_eq_zero] at hf_int

end Inner

theorem integral_with_density_eq_integral_smul {f : α → ℝ≥0 } (f_meas : Measurable f) (g : α → E) :
    (∫ a, g a ∂μ.withDensity fun x => f x) = ∫ a, f a • g a ∂μ := by
  by_cases' hg : integrable g (μ.with_density fun x => f x)
  swap
  · rw [integral_undef hg, integral_undef]
    rwa [← integrable_with_density_iff_integrable_smul f_meas] <;> infer_instance
    
  refine' integrable.induction _ _ _ _ _ hg
  · intro c s s_meas hs
    rw [integral_indicator s_meas]
    simp_rw [← indicator_smul_apply, integral_indicator s_meas]
    simp only [← s_meas, ← integral_const, ← measure.restrict_apply', ← univ_inter, ← with_density_apply]
    rw [lintegral_coe_eq_integral, Ennreal.to_real_of_real, ← integral_smul_const]
    · rfl
      
    · exact integral_nonneg fun x => Nnreal.coe_nonneg _
      
    · refine' ⟨f_meas.coe_nnreal_real.AeMeasurable.AeStronglyMeasurable, _⟩
      rw [with_density_apply _ s_meas] at hs
      rw [has_finite_integral]
      convert hs
      ext1 x
      simp only [← Nnreal.nnnorm_eq]
      
    
  · intro u u' h_disj u_int u'_int h h'
    change (∫ a : α, u a + u' a ∂μ.with_density fun x : α => ↑(f x)) = ∫ a : α, f a • (u a + u' a) ∂μ
    simp_rw [smul_add]
    rw [integral_add u_int u'_int, h, h', integral_add]
    · exact (integrable_with_density_iff_integrable_smul f_meas).1 u_int
      
    · exact (integrable_with_density_iff_integrable_smul f_meas).1 u'_int
      
    
  · have C1 : Continuous fun u : Lp E 1 (μ.with_density fun x => f x) => ∫ x, u x ∂μ.with_density fun x => f x :=
      continuous_integral
    have C2 : Continuous fun u : Lp E 1 (μ.with_density fun x => f x) => ∫ x, f x • u x ∂μ := by
      have : Continuous ((fun u : Lp E 1 μ => ∫ x, u x ∂μ) ∘ with_density_smul_li μ f_meas) :=
        continuous_integral.comp (with_density_smul_li μ f_meas).Continuous
      convert this
      ext1 u
      simp only [← Function.comp_app, ← with_density_smul_li_apply]
      exact integral_congr_ae (mem_ℒ1_smul_of_L1_with_density f_meas u).coe_fn_to_Lp.symm
    exact is_closed_eq C1 C2
    
  · intro u v huv u_int hu
    rw [← integral_congr_ae huv, hu]
    apply integral_congr_ae
    filter_upwards [(ae_with_density_iff f_meas.coe_nnreal_ennreal).1 huv] with x hx
    rcases eq_or_ne (f x) 0 with (h'x | h'x)
    · simp only [← h'x, ← zero_smul]
      
    · rw [hx _]
      simpa only [← Ne.def, ← Ennreal.coe_eq_zero] using h'x
      
    

theorem integral_with_density_eq_integral_smul₀ {f : α → ℝ≥0 } (hf : AeMeasurable f μ) (g : α → E) :
    (∫ a, g a ∂μ.withDensity fun x => f x) = ∫ a, f a • g a ∂μ := by
  let f' := hf.mk _
  calc (∫ a, g a ∂μ.with_density fun x => f x) = ∫ a, g a ∂μ.with_density fun x => f' x := by
      congr 1
      apply with_density_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]_ = ∫ a, f' a • g a ∂μ :=
      integral_with_density_eq_integral_smul hf.measurable_mk _ _ = ∫ a, f a • g a ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]

theorem set_integral_with_density_eq_set_integral_smul {f : α → ℝ≥0 } (f_meas : Measurable f) (g : α → E) {s : Set α}
    (hs : MeasurableSet s) : (∫ a in s, g a ∂μ.withDensity fun x => f x) = ∫ a in s, f a • g a ∂μ := by
  rw [restrict_with_density hs, integral_with_density_eq_integral_smul f_meas]

theorem set_integral_with_density_eq_set_integral_smul₀ {f : α → ℝ≥0 } {s : Set α} (hf : AeMeasurable f (μ.restrict s))
    (g : α → E) (hs : MeasurableSet s) : (∫ a in s, g a ∂μ.withDensity fun x => f x) = ∫ a in s, f a • g a ∂μ := by
  rw [restrict_with_density hs, integral_with_density_eq_integral_smul₀ hf]

end

section thickenedIndicator

variable [PseudoEmetricSpace α]

theorem measure_le_lintegral_thickened_indicator_aux (μ : Measureₓ α) {E : Set α} (E_mble : MeasurableSet E) (δ : ℝ) :
    μ E ≤ ∫⁻ a, (thickenedIndicatorAux δ E a : ℝ≥0∞) ∂μ := by
  convert_to lintegral μ (E.indicator fun _ => (1 : ℝ≥0∞)) ≤ lintegral μ (thickenedIndicatorAux δ E)
  · rw [lintegral_indicator _ E_mble]
    simp only [← lintegral_one, ← measure.restrict_apply, ← MeasurableSet.univ, ← univ_inter]
    
  · apply lintegral_mono
    apply indicator_le_thickened_indicator_aux
    

theorem measure_le_lintegral_thickened_indicator (μ : Measureₓ α) {E : Set α} (E_mble : MeasurableSet E) {δ : ℝ}
    (δ_pos : 0 < δ) : μ E ≤ ∫⁻ a, (thickenedIndicator δ_pos E a : ℝ≥0∞) ∂μ := by
  convert measure_le_lintegral_thickened_indicator_aux μ E_mble δ
  dsimp'
  simp only [← thickened_indicator_aux_lt_top.ne, ← Ennreal.coe_to_nnreal, ← Ne.def, ← not_false_iff]

end thickenedIndicator

