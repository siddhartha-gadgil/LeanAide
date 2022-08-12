/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathbin.MeasureTheory.Integral.SetIntegral

/-!
# Egorov theorem

This file contains the Egorov theorem which states that an almost everywhere convergent
sequence on a finite measure space converges uniformly except on an arbitrarily small set.
This theorem is useful for the Vitali convergence theorem as well as theorems regarding
convergence in measure.

## Main results

* `measure_theory.egorov`: Egorov's theorem which shows that a sequence of almost everywhere
  convergent functions converges uniformly except on an arbitrarily small set.

-/


noncomputable section

open Classical MeasureTheory Nnreal Ennreal TopologicalSpace

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type _} {m : MeasurableSpace α} [MetricSpace β] {μ : Measure α}

namespace Egorov

/-- Given a sequence of functions `f` and a function `g`, `not_convergent_seq f g n j` is the
set of elements such that `f k x` and `g x` are separated by at least `1 / (n + 1)` for some
`k ≥ j`.

This definition is useful for Egorov's theorem. -/
def NotConvergentSeq [Preorderₓ ι] (f : ι → α → β) (g : α → β) (n : ℕ) (j : ι) : Set α :=
  ⋃ (k) (hk : j ≤ k), { x | 1 / (n + 1 : ℝ) < dist (f k x) (g x) }

variable {n : ℕ} {i j : ι} {s : Set α} {ε : ℝ} {f : ι → α → β} {g : α → β}

theorem mem_not_convergent_seq_iff [Preorderₓ ι] {x : α} :
    x ∈ NotConvergentSeq f g n j ↔ ∃ (k : _)(hk : j ≤ k), 1 / (n + 1 : ℝ) < dist (f k x) (g x) := by
  simp_rw [not_convergent_seq, mem_Union]
  rfl

theorem not_convergent_seq_antitone [Preorderₓ ι] : Antitone (NotConvergentSeq f g n) := fun j k hjk =>
  Union₂_mono' fun l hl => ⟨l, le_transₓ hjk hl, Subset.rfl⟩

theorem measure_inter_not_convergent_seq_eq_zero [SemilatticeSup ι] [Nonempty ι]
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ ⋂ j, NotConvergentSeq f g n j) = 0 := by
  simp_rw [Metric.tendsto_at_top, ae_iff] at hfg
  rw [← nonpos_iff_eq_zero, ← hfg]
  refine' measure_mono fun x => _
  simp only [← mem_inter_eq, ← mem_Inter, ← ge_iff_le, ← mem_not_convergent_seq_iff]
  push_neg
  rintro ⟨hmem, hx⟩
  refine' ⟨hmem, 1 / (n + 1 : ℝ), Nat.one_div_pos_of_nat, fun N => _⟩
  obtain ⟨n, hn₁, hn₂⟩ := hx N
  exact ⟨n, hn₁, hn₂.le⟩

theorem not_convergent_seq_measurable_set [Preorderₓ ι] [Encodable ι] (hf : ∀ n, strongly_measurable[m] (f n))
    (hg : StronglyMeasurable g) : MeasurableSet (NotConvergentSeq f g n j) :=
  MeasurableSet.Union fun k =>
    MeasurableSet.Union_Prop fun hk => StronglyMeasurable.measurable_set_lt strongly_measurable_const <| (hf k).dist hg

theorem measure_not_convergent_seq_tendsto_zero [SemilatticeSup ι] [Encodable ι] (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    Tendsto (fun j => μ (s ∩ NotConvergentSeq f g n j)) atTop (𝓝 0) := by
  cases is_empty_or_nonempty ι
  · have : (fun j => μ (s ∩ not_convergent_seq f g n j)) = fun j => 0 := by
      simp only [← eq_iff_true_of_subsingleton]
    rw [this]
    exact tendsto_const_nhds
    
  rw [← measure_inter_not_convergent_seq_eq_zero hfg n, inter_Inter]
  refine'
    tendsto_measure_Inter (fun n => hsm.inter <| not_convergent_seq_measurable_set hf hg)
      (fun k l hkl => inter_subset_inter_right _ <| not_convergent_seq_antitone hkl)
      ⟨h.some, (lt_of_le_of_ltₓ (measure_mono <| inter_subset_left _ _) (lt_top_iff_ne_top.2 hs)).Ne⟩

variable [SemilatticeSup ι] [Nonempty ι] [Encodable ι]

theorem exists_not_convergent_seq_lt (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    ∃ j : ι, μ (s ∩ NotConvergentSeq f g n j) ≤ Ennreal.ofReal (ε * 2⁻¹ ^ n) := by
  obtain ⟨N, hN⟩ :=
    (Ennreal.tendsto_at_top Ennreal.zero_ne_top).1 (measure_not_convergent_seq_tendsto_zero hf hg hsm hs hfg n)
      (Ennreal.ofReal (ε * 2⁻¹ ^ n)) _
  · rw [zero_addₓ] at hN
    exact ⟨N, (hN N le_rfl).2⟩
    
  · rw [gt_iff_lt, Ennreal.of_real_pos]
    exact
      mul_pos hε
        (pow_pos
          (by
            norm_num)
          n)
    

/-- Given some `ε > 0`, `not_convergent_seq_lt_index` provides the index such that
`not_convergent_seq` (intersected with a set of finite measure) has measure less than
`ε * 2⁻¹ ^ n`.

This definition is useful for Egorov's theorem. -/
def notConvergentSeqLtIndex (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    ι :=
  Classical.some <| exists_not_convergent_seq_lt hε hf hg hsm hs hfg n

theorem not_convergent_seq_lt_index_spec (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ NotConvergentSeq f g n (notConvergentSeqLtIndex hε hf hg hsm hs hfg n)) ≤ Ennreal.ofReal (ε * 2⁻¹ ^ n) :=
  Classical.some_spec <| exists_not_convergent_seq_lt hε hf hg hsm hs hfg n

/-- Given some `ε > 0`, `Union_not_convergent_seq` is the union of `not_convergent_seq` with
specific indicies such that `Union_not_convergent_seq` has measure less equal than `ε`.

This definition is useful for Egorov's theorem. -/
def UnionNotConvergentSeq (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Set α :=
  ⋃ n, s ∩ NotConvergentSeq f g n (notConvergentSeqLtIndex (half_pos hε) hf hg hsm hs hfg n)

theorem Union_not_convergent_seq_measurable_set (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MeasurableSet <| UnionNotConvergentSeq hε hf hg hsm hs hfg :=
  MeasurableSet.Union fun n => hsm.inter <| not_convergent_seq_measurable_set hf hg

theorem measure_Union_not_convergent_seq (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    μ (UnionNotConvergentSeq hε hf hg hsm hs hfg) ≤ Ennreal.ofReal ε := by
  refine'
    le_transₓ (measure_Union_le _)
      (le_transₓ (Ennreal.tsum_le_tsum <| not_convergent_seq_lt_index_spec (half_pos hε) hf hg hsm hs hfg) _)
  simp_rw [Ennreal.of_real_mul (half_pos hε).le]
  rw [Ennreal.tsum_mul_left, ← Ennreal.of_real_tsum_of_nonneg, inv_eq_one_div, tsum_geometric_two, ←
    Ennreal.of_real_mul (half_pos hε).le, div_mul_cancel ε two_ne_zero]
  · exact le_rfl
    
  · exact fun n =>
      pow_nonneg
        (by
          norm_num)
        _
    
  · rw [inv_eq_one_div]
    exact summable_geometric_two
    

theorem Union_not_convergent_seq_subset (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    UnionNotConvergentSeq hε hf hg hsm hs hfg ⊆ s := by
  rw [Union_not_convergent_seq, ← inter_Union]
  exact inter_subset_left _ _

theorem tendsto_uniformly_on_diff_Union_not_convergent_seq (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop (s \ Egorov.UnionNotConvergentSeq hε hf hg hsm hs hfg) := by
  rw [Metric.tendsto_uniformly_on_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  rw [eventually_at_top]
  refine' ⟨egorov.not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg N, fun n hn x hx => _⟩
  simp only [← mem_diff, ← egorov.Union_not_convergent_seq, ← not_exists, ← mem_Union, ← mem_inter_eq, ← not_and, ←
    exists_and_distrib_left] at hx
  obtain ⟨hxs, hx⟩ := hx
  specialize hx hxs N
  rw [egorov.mem_not_convergent_seq_iff] at hx
  push_neg  at hx
  rw [dist_comm]
  exact lt_of_le_of_ltₓ (hx n hn) hN

end Egorov

variable [SemilatticeSup ι] [Nonempty ι] [Encodable ι] {γ : Type _} [TopologicalSpace γ] {f : ι → α → β} {g : α → β}
  {s : Set α}

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- **Egorov's theorem**: If `f : ι → α → β` is a sequence of strongly measurable functions that
converges to `g : α → β` almost everywhere on a measurable set `s` of finite measure,
then for all `ε > 0`, there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` converges to `g`
uniformly on `s \ t`. We require the index type `ι` to be encodable, and usually `ι = ℕ`.

In other words, a sequence of almost everywhere convergent functions converges uniformly except on
an arbitrarily small set. -/
theorem tendsto_uniformly_on_of_ae_tendsto (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (t : _)(_ : t ⊆ s), MeasurableSet t ∧ μ t ≤ Ennreal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  ⟨Egorov.UnionNotConvergentSeq hε hf hg hsm hs hfg, Egorov.Union_not_convergent_seq_subset hε hf hg hsm hs hfg,
    Egorov.Union_not_convergent_seq_measurable_set hε hf hg hsm hs hfg,
    Egorov.measure_Union_not_convergent_seq hε hf hg hsm hs hfg,
    Egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq hε hf hg hsm hs hfg⟩

/-- Egorov's theorem for finite measure spaces. -/
theorem tendsto_uniformly_on_of_ae_tendsto' [IsFiniteMeasure μ] (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, MeasurableSet t ∧ μ t ≤ Ennreal.ofReal ε ∧ TendstoUniformlyOn f g atTop (tᶜ) := by
  obtain ⟨t, _, ht, htendsto⟩ :=
    tendsto_uniformly_on_of_ae_tendsto hf hg MeasurableSet.univ (measure_ne_top μ univ) _ hε
  · refine' ⟨_, ht, _⟩
    rwa [compl_eq_univ_diff]
    
  · filter_upwards [hfg] with _ htendsto _ using htendsto
    

end MeasureTheory

