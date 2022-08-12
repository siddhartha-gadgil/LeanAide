/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.Logic.Equiv.List
import Mathbin.MeasureTheory.Constructions.BorelSpace
import Mathbin.MeasureTheory.Measure.Lebesgue
import Mathbin.Topology.MetricSpace.Holder
import Mathbin.Topology.MetricSpace.MetricSeparated

/-!
# Hausdorff measure and metric (outer) measures

In this file we define the `d`-dimensional Hausdorff measure on an (extended) metric space `X` and
the Hausdorff dimension of a set in an (extended) metric space. Let `μ d δ` be the maximal outer
measure such that `μ d δ s ≤ (emetric.diam s) ^ d` for every set of diameter less than `δ`. Then
the Hausdorff measure `μH[d] s` of `s` is defined as `⨆ δ > 0, μ d δ s`. By Caratheodory theorem
`measure_theory.outer_measure.is_metric.borel_le_caratheodory`, this is a Borel measure on `X`.

The value of `μH[d]`, `d > 0`, on a set `s` (measurable or not) is given by
```
μH[d] s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, emetric.diam (t n) ≤ r), ∑' n, emetric.diam (t n) ^ d
```

For every set `s` for any `d < d'` we have either `μH[d] s = ∞` or `μH[d'] s = 0`, see
`measure_theory.measure.hausdorff_measure_zero_or_top`. In
`topology.metric_space.hausdorff_dimension` we use this fact to define the Hausdorff dimension
`dimH` of a set in an (extended) metric space.

We also define two generalizations of the Hausdorff measure. In one generalization (see
`measure_theory.measure.mk_metric`) we take any function `m (diam s)` instead of `(diam s) ^ d`. In
an even more general definition (see `measure_theory.measure.mk_metric'`) we use any function
of `m : set X → ℝ≥0∞`. Some authors start with a partial function `m` defined only on some sets
`s : set X` (e.g., only on balls or only on measurable sets). This is equivalent to our definition
applied to `measure_theory.extend m`.

We also define a predicate `measure_theory.outer_measure.is_metric` which says that an outer measure
is additive on metric separated pairs of sets: `μ (s ∪ t) = μ s + μ t` provided that
`⨅ (x ∈ s) (y ∈ t), edist x y ≠ 0`. This is the property required for the Caratheodory theorem
`measure_theory.outer_measure.is_metric.borel_le_caratheodory`, so we prove this theorem for any
metric outer measure, then prove that outer measures constructed using `mk_metric'` are metric outer
measures.

## Main definitions

* `measure_theory.outer_measure.is_metric`: an outer measure `μ` is called *metric* if
  `μ (s ∪ t) = μ s + μ t` for any two metric separated sets `s` and `t`. A metric outer measure in a
  Borel extended metric space is guaranteed to satisfy the Caratheodory condition, see
  `measure_theory.outer_measure.is_metric.borel_le_caratheodory`.
* `measure_theory.outer_measure.mk_metric'` and its particular case
  `measure_theory.outer_measure.mk_metric`: a construction of an outer measure that is guaranteed to
  be metric. Both constructions are generalizations of the Hausdorff measure. The same measures
  interpreted as Borel measures are called `measure_theory.measure.mk_metric'` and
  `measure_theory.measure.mk_metric`.
* `measure_theory.measure.hausdorff_measure` a.k.a. `μH[d]`: the `d`-dimensional Hausdorff measure.
  There are many definitions of the Hausdorff measure that differ from each other by a
  multiplicative constant. We put
  `μH[d] s = ⨆ r > 0, ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n) (ht : ∀ n, emetric.diam (t n) ≤ r),
    ∑' n, ⨆ (ht : ¬set.subsingleton (t n)), (emetric.diam (t n)) ^ d`,
  see `measure_theory.measure.hausdorff_measure_apply'`. In the most interesting case `0 < d` one
  can omit the `⨆ (ht : ¬set.subsingleton (t n))` part.

## Main statements

### Basic properties

* `measure_theory.outer_measure.is_metric.borel_le_caratheodory`: if `μ` is a metric outer measure
  on an extended metric space `X` (that is, it is additive on pairs of metric separated sets), then
  every Borel set is Caratheodory measurable (hence, `μ` defines an actual
  `measure_theory.measure`). See also `measure_theory.measure.mk_metric`.
* `measure_theory.measure.hausdorff_measure_mono`: `μH[d] s` is an antitone function
  of `d`.
* `measure_theory.measure.hausdorff_measure_zero_or_top`: if `d₁ < d₂`, then for any `s`, either
  `μH[d₂] s = 0` or `μH[d₁] s = ∞`. Together with the previous lemma, this means that `μH[d] s` is
  equal to infinity on some ray `(-∞, D)` and is equal to zero on `(D, +∞)`, where `D` is a possibly
  infinite number called the *Hausdorff dimension* of `s`; `μH[D] s` can be zero, infinity, or
  anything in between.
* `measure_theory.measure.no_atoms_hausdorff`: Hausdorff measure has no atoms.

### Hausdorff measure in `ℝⁿ`

* `measure_theory.hausdorff_measure_pi_real`: for a nonempty `ι`, `μH[card ι]` on `ι → ℝ` equals
  Lebesgue measure.

## Notations

We use the following notation localized in `measure_theory`.

- `μH[d]` : `measure_theory.measure.hausdorff_measure d`

## Implementation notes

There are a few similar constructions called the `d`-dimensional Hausdorff measure. E.g., some
sources only allow coverings by balls and use `r ^ d` instead of `(diam s) ^ d`. While these
construction lead to different Hausdorff measures, they lead to the same notion of the Hausdorff
dimension.

## TODO

* prove that `1`-dimensional Hausdorff measure on `ℝ` equals `volume`;
* prove a similar statement for `ℝ × ℝ`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.10][Federer1996]

## Tags

Hausdorff measure, measure, metric measure
-/


open Nnreal Ennreal TopologicalSpace BigOperators

open Emetric Set Function Filter Encodable FiniteDimensional TopologicalSpace

noncomputable section

variable {ι X Y : Type _} [EmetricSpace X] [EmetricSpace Y]

namespace MeasureTheory

namespace OuterMeasure

/-!
### Metric outer measures

In this section we define metric outer measures and prove Caratheodory theorem: a metric outer
measure has the Caratheodory property.
-/


/-- We say that an outer measure `μ` in an (e)metric space is *metric* if `μ (s ∪ t) = μ s + μ t`
for any two metric separated sets `s`, `t`. -/
def IsMetric (μ : OuterMeasure X) : Prop :=
  ∀ s t : Set X, IsMetricSeparated s t → μ (s ∪ t) = μ s + μ t

namespace IsMetric

variable {μ : OuterMeasure X}

/-- A metric outer measure is additive on a finite set of pairwise metric separated sets. -/
theorem finset_Union_of_pairwise_separated (hm : IsMetric μ) {I : Finset ι} {s : ι → Set X}
    (hI : ∀, ∀ i ∈ I, ∀, ∀ j ∈ I, ∀, i ≠ j → IsMetricSeparated (s i) (s j)) : μ (⋃ i ∈ I, s i) = ∑ i in I, μ (s i) := by
  classical
  induction' I using Finset.induction_on with i I hiI ihI hI
  · simp
    
  simp only [← Finset.mem_insert] at hI
  rw [Finset.set_bUnion_insert, hm, ihI, Finset.sum_insert hiI]
  exacts[fun i hi j hj hij => hI i (Or.inr hi) j (Or.inr hj) hij,
    IsMetricSeparated.finset_Union_right fun j hj => hI i (Or.inl rfl) j (Or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm]

/-- Caratheodory theorem. If `m` is a metric outer measure, then every Borel measurable set `t` is
Caratheodory measurable: for any (not necessarily measurable) set `s` we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
theorem borel_le_caratheodory (hm : IsMetric μ) : borel X ≤ μ.caratheodory := by
  rw [borel_eq_generate_from_is_closed]
  refine' MeasurableSpace.generate_from_le fun t ht => μ.is_caratheodory_iff_le.2 fun s => _
  set S : ℕ → Set X := fun n => { x ∈ s | (↑n)⁻¹ ≤ inf_edist x t }
  have n0 : ∀ {n : ℕ}, (n⁻¹ : ℝ≥0∞) ≠ 0 := fun n => Ennreal.inv_ne_zero.2 Ennreal.coe_nat_ne_top
  have Ssep : ∀ n, IsMetricSeparated (S n) t := fun n =>
    ⟨n⁻¹, n0, fun x hx y hy => hx.2.trans <| inf_edist_le_edist_of_mem hy⟩
  have Ssep' : ∀ n, IsMetricSeparated (S n) (s ∩ t) := fun n => (Ssep n).mono subset.rfl (inter_subset_right _ _)
  have S_sub : ∀ n, S n ⊆ s \ t := fun n => subset_inter (inter_subset_left _ _) (Ssep n).subset_compl_right
  have hSs : ∀ n, μ (s ∩ t) + μ (S n) ≤ μ s := fun n =>
    calc
      μ (s ∩ t) + μ (S n) = μ (s ∩ t ∪ S n) := Eq.symm <| hm _ _ <| (Ssep' n).symm
      _ ≤ μ (s ∩ t ∪ s \ t) := by
        mono*
        exact le_rfl
      _ = μ s := by
        rw [inter_union_diff]
      
  have Union_S : (⋃ n, S n) = s \ t := by
    refine' subset.antisymm (Union_subset S_sub) _
    rintro x ⟨hxs, hxt⟩
    rw [mem_iff_inf_edist_zero_of_closed ht] at hxt
    rcases Ennreal.exists_inv_nat_lt hxt with ⟨n, hn⟩
    exact mem_Union.2 ⟨n, hxs, hn.le⟩
  /- Now we have `∀ n, μ (s ∩ t) + μ (S n) ≤ μ s` and we need to prove
    `μ (s ∩ t) + μ (⋃ n, S n) ≤ μ s`. We can't pass to the limit because
    `μ` is only an outer measure. -/
  by_cases' htop : μ (s \ t) = ∞
  · rw [htop, Ennreal.add_top, ← htop]
    exact μ.mono (diff_subset _ _)
    
  suffices : μ (⋃ n, S n) ≤ ⨆ n, μ (S n)
  calc μ (s ∩ t) + μ (s \ t) = μ (s ∩ t) + μ (⋃ n, S n) := by
      rw [Union_S]_ ≤ μ (s ∩ t) + ⨆ n, μ (S n) := add_le_add le_rfl this _ = ⨆ n, μ (s ∩ t) + μ (S n) :=
      Ennreal.add_supr _ ≤ μ s := supr_le hSs
  /- It suffices to show that `∑' k, μ (S (k + 1) \ S k) ≠ ∞`. Indeed, if we have this,
    then for all `N` we have `μ (⋃ n, S n) ≤ μ (S N) + ∑' k, m (S (N + k + 1) \ S (N + k))`
    and the second term tends to zero, see `outer_measure.Union_nat_of_monotone_of_tsum_ne_top`
    for details. -/
  have : ∀ n, S n ⊆ S (n + 1) := fun n x hx =>
    ⟨hx.1, le_transₓ (Ennreal.inv_le_inv.2 <| Ennreal.coe_nat_le_coe_nat.2 n.le_succ) hx.2⟩
  refine' (μ.Union_nat_of_monotone_of_tsum_ne_top this _).le
  clear this
  /- While the sets `S (k + 1) \ S k` are not pairwise metric separated, the sets in each
    subsequence `S (2 * k + 1) \ S (2 * k)` and `S (2 * k + 2) \ S (2 * k)` are metric separated,
    so `m` is additive on each of those sequences. -/
  rw [← tsum_even_add_odd Ennreal.summable Ennreal.summable, Ennreal.add_ne_top]
  suffices : ∀ a, (∑' k : ℕ, μ (S (2 * k + 1 + a) \ S (2 * k + a))) ≠ ∞
  exact
    ⟨by
      simpa using this 0, by
      simpa using this 1⟩
  refine' fun r => ne_top_of_le_ne_top htop _
  rw [← Union_S, Ennreal.tsum_eq_supr_nat, supr_le_iff]
  intro n
  rw [← hm.finset_Union_of_pairwise_separated]
  · exact μ.mono (Union_subset fun i => Union_subset fun hi x hx => mem_Union.2 ⟨_, hx.1⟩)
    
  suffices : ∀ i j, i < j → IsMetricSeparated (S (2 * i + 1 + r)) (s \ S (2 * j + r))
  exact fun i _ j _ hij =>
    hij.lt_or_lt.elim (fun h => (this i j h).mono (inter_subset_left _ _) fun x hx => ⟨hx.1.1, hx.2⟩) fun h =>
      (this j i h).symm.mono (fun x hx => ⟨hx.1.1, hx.2⟩) (inter_subset_left _ _)
  intro i j hj
  have A : ((↑(2 * j + r))⁻¹ : ℝ≥0∞) < (↑(2 * i + 1 + r))⁻¹ := by
    rw [Ennreal.inv_lt_inv, Ennreal.coe_nat_lt_coe_nat]
    linarith
  refine'
    ⟨(↑(2 * i + 1 + r))⁻¹ - (↑(2 * j + r))⁻¹, by
      simpa using A, fun x hx y hy => _⟩
  have : inf_edist y t < (↑(2 * j + r))⁻¹ := not_leₓ.1 fun hle => hy.2 ⟨hy.1, hle⟩
  rcases inf_edist_lt_iff.mp this with ⟨z, hzt, hyz⟩
  have hxz : (↑(2 * i + 1 + r))⁻¹ ≤ edist x z := le_inf_edist.1 hx.2 _ hzt
  apply Ennreal.le_of_add_le_add_right hyz.ne_top
  refine' le_transₓ _ (edist_triangle _ _ _)
  refine' (add_le_add le_rfl hyz.le).trans (Eq.trans_le _ hxz)
  rw [tsub_add_cancel_of_le A.le]

theorem le_caratheodory [MeasurableSpace X] [BorelSpace X] (hm : IsMetric μ) : ‹MeasurableSpace X› ≤ μ.caratheodory :=
  by
  rw [@BorelSpace.measurable_eq X _ _]
  exact hm.borel_le_caratheodory

end IsMetric

/-!
### Constructors of metric outer measures

In this section we provide constructors `measure_theory.outer_measure.mk_metric'` and
`measure_theory.outer_measure.mk_metric` and prove that these outer measures are metric outer
measures. We also prove basic lemmas about `map`/`comap` of these measures.
-/


/-- Auxiliary definition for `outer_measure.mk_metric'`: given a function on sets
`m : set X → ℝ≥0∞`, returns the maximal outer measure `μ` such that `μ s ≤ m s`
for any set `s` of diameter at most `r`.-/
def MkMetric'.pre (m : Set X → ℝ≥0∞) (r : ℝ≥0∞) : OuterMeasure X :=
  bounded_by <| extend fun s (hs : diam s ≤ r) => m s

/-- Given a function `m : set X → ℝ≥0∞`, `mk_metric' m` is the supremum of `mk_metric'.pre m r`
over `r > 0`. Equivalently, it is the limit of `mk_metric'.pre m r` as `r` tends to zero from
the right. -/
def mkMetric' (m : Set X → ℝ≥0∞) : OuterMeasure X :=
  ⨆ r > 0, MkMetric'.pre m r

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞` and `r > 0`, let `μ r` be the maximal outer measure such that
`μ s ≤ m (emetric.diam s)` whenever `emetric.diam s < r`. Then
`mk_metric m = ⨆ r > 0, μ r`. -/
def mkMetric (m : ℝ≥0∞ → ℝ≥0∞) : OuterMeasure X :=
  mkMetric' fun s => m (diam s)

namespace MkMetric'

variable {m : Set X → ℝ≥0∞} {r : ℝ≥0∞} {μ : OuterMeasure X} {s : Set X}

theorem le_pre : μ ≤ pre m r ↔ ∀ s : Set X, diam s ≤ r → μ s ≤ m s := by
  simp only [← pre, ← le_bounded_by, ← extend, ← le_infi_iff]

theorem pre_le (hs : diam s ≤ r) : pre m r s ≤ m s :=
  (bounded_by_le _).trans <| infi_le _ hs

theorem mono_pre (m : Set X → ℝ≥0∞) {r r' : ℝ≥0∞} (h : r ≤ r') : pre m r' ≤ pre m r :=
  le_pre.2 fun s hs => pre_le (hs.trans h)

theorem mono_pre_nat (m : Set X → ℝ≥0∞) : Monotone fun k : ℕ => pre m k⁻¹ := fun k l h =>
  le_pre.2 fun s hs =>
    pre_le
      (hs.trans <| by
        simpa)

theorem tendsto_pre (m : Set X → ℝ≥0∞) (s : Set X) : Tendsto (fun r => pre m r s) (𝓝[>] 0) (𝓝 <| mkMetric' m s) := by
  rw [← map_coe_Ioi_at_bot, tendsto_map'_iff]
  simp only [← mk_metric', ← outer_measure.supr_apply, ← supr_subtype']
  exact tendsto_at_bot_supr fun r r' hr => mono_pre _ hr _

theorem tendsto_pre_nat (m : Set X → ℝ≥0∞) (s : Set X) :
    Tendsto (fun n : ℕ => pre m n⁻¹ s) atTop (𝓝 <| mkMetric' m s) := by
  refine' (tendsto_pre m s).comp (tendsto_inf.2 ⟨Ennreal.tendsto_inv_nat_nhds_zero, _⟩)
  refine' tendsto_principal.2 (eventually_of_forall fun n => _)
  simp

theorem eq_supr_nat (m : Set X → ℝ≥0∞) : mkMetric' m = ⨆ n : ℕ, MkMetric'.pre m n⁻¹ := by
  ext1 s
  rw [supr_apply]
  refine'
    tendsto_nhds_unique (mk_metric'.tendsto_pre_nat m s)
      (tendsto_at_top_supr fun k l hkl => mk_metric'.mono_pre_nat m hkl s)

/-- `measure_theory.outer_measure.mk_metric'.pre m r` is a trimmed measure provided that
`m (closure s) = m s` for any set `s`. -/
theorem trim_pre [MeasurableSpace X] [OpensMeasurableSpace X] (m : Set X → ℝ≥0∞) (hcl : ∀ s, m (Closure s) = m s)
    (r : ℝ≥0∞) : (pre m r).trim = pre m r := by
  refine' le_antisymmₓ (le_pre.2 fun s hs => _) (le_trim _)
  rw [trim_eq_infi]
  refine'
    infi_le_of_le (Closure s) <|
      infi_le_of_le subset_closure <| infi_le_of_le measurable_set_closure ((pre_le _).trans_eq (hcl _))
  rwa [diam_closure]

end MkMetric'

/-- An outer measure constructed using `outer_measure.mk_metric'` is a metric outer measure. -/
theorem mk_metric'_is_metric (m : Set X → ℝ≥0∞) : (mkMetric' m).IsMetric := by
  rintro s t ⟨r, r0, hr⟩
  refine'
    tendsto_nhds_unique_of_eventually_eq (mk_metric'.tendsto_pre _ _)
      ((mk_metric'.tendsto_pre _ _).add (mk_metric'.tendsto_pre _ _)) _
  rw [← pos_iff_ne_zero] at r0
  filter_upwards [Ioo_mem_nhds_within_Ioi ⟨le_rfl, r0⟩]
  rintro ε ⟨ε0, εr⟩
  refine' bounded_by_union_of_top_of_nonempty_inter _
  rintro u ⟨x, hxs, hxu⟩ ⟨y, hyt, hyu⟩
  have : ε < diam u := εr.trans_le ((hr x hxs y hyt).trans <| edist_le_diam_of_mem hxu hyu)
  exact infi_eq_top.2 fun h => (this.not_le h).elim

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[≥] 0]` to state this), then `mk_metric m₁ hm₁ ≤ c • mk_metric m₂ hm₂`. -/
theorem mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0) (hle : m₁ ≤ᶠ[𝓝[≥] 0] c • m₂) :
    (mkMetric m₁ : OuterMeasure X) ≤ c • mkMetric m₂ := by
  classical
  rcases(mem_nhds_within_Ici_iff_exists_Ico_subset' Ennreal.zero_lt_one).1 hle with ⟨r, hr0, hr⟩
  refine' fun s =>
    le_of_tendsto_of_tendsto (mk_metric'.tendsto_pre _ s)
      (Ennreal.Tendsto.const_mul (mk_metric'.tendsto_pre _ s) (Or.inr hc))
      (mem_of_superset (Ioo_mem_nhds_within_Ioi ⟨le_rfl, hr0⟩) fun r' hr' => _)
  simp only [← mem_set_of_eq, ← mk_metric'.pre, ← RingHom.id_apply]
  rw [← smul_eq_mul, ← smul_apply, smul_bounded_by hc]
  refine' le_bounded_by.2 (fun t => (bounded_by_le _).trans _) _
  simp only [← smul_eq_mul, ← Pi.smul_apply, ← extend, ← infi_eq_if]
  split_ifs with ht ht
  · apply hr
    exact ⟨zero_le _, ht.trans_lt hr'.2⟩
    
  · simp [← h0]
    

/-- If `m₁ d ≤ m₂ d` for `d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝[≥] 0]` to state this), then
`mk_metric m₁ hm₁ ≤ mk_metric m₂ hm₂`-/
theorem mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝[≥] 0] m₂) : (mkMetric m₁ : OuterMeasure X) ≤ mkMetric m₂ :=
  by
  convert mk_metric_mono_smul Ennreal.one_ne_top ennreal.zero_lt_one.ne' _ <;> simp [*]

theorem isometry_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) {f : X → Y} (hf : Isometry f) (H : Monotone m ∨ Surjective f) :
    comap f (mkMetric m) = mkMetric m := by
  simp only [← mk_metric, ← mk_metric', ← mk_metric'.pre, ← induced_outer_measure, ← comap_supr]
  refine' surjective_id.supr_congr id fun ε => (surjective_id.supr_congr id) fun hε => _
  rw [comap_bounded_by _ (H.imp (fun h_mono => _) id)]
  · congr with s : 1
    apply extend_congr
    · simp [← hf.ediam_image]
      
    · intros
      simp [← hf.injective.subsingleton_image_iff, ← hf.ediam_image]
      
    
  · intro s t hst
    simp only [← extend, ← le_infi_iff]
    intro ht
    apply le_transₓ _ (h_mono (diam_mono hst))
    simp only [← (diam_mono hst).trans ht, ← le_reflₓ, ← cinfi_pos]
    

theorem isometry_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) {f : X → Y} (hf : Isometry f) (H : Monotone m ∨ Surjective f) :
    map f (mkMetric m) = restrict (Range f) (mkMetric m) := by
  rw [← isometry_comap_mk_metric _ hf H, map_comap]

theorem isometric_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) : comap f (mkMetric m) = mkMetric m :=
  isometry_comap_mk_metric _ f.Isometry (Or.inr f.Surjective)

theorem isometric_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) : map f (mkMetric m) = mkMetric m := by
  rw [← isometric_comap_mk_metric _ f, map_comap_of_surjective f.surjective]

theorem trim_mk_metric [MeasurableSpace X] [BorelSpace X] (m : ℝ≥0∞ → ℝ≥0∞) :
    (mkMetric m : OuterMeasure X).trim = mkMetric m := by
  simp only [← mk_metric, ← mk_metric'.eq_supr_nat, ← trim_supr]
  congr 1 with n : 1
  refine' mk_metric'.trim_pre _ (fun s => _) _
  simp

theorem le_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (μ : OuterMeasure X) (r : ℝ≥0∞) (h0 : 0 < r)
    (hr : ∀ s, diam s ≤ r → μ s ≤ m (diam s)) : μ ≤ mkMetric m :=
  le_supr₂_of_le r h0 <| mkMetric'.le_pre.2 fun s hs => hr _ hs

end OuterMeasure

/-!
### Metric measures

In this section we use `measure_theory.outer_measure.to_measure` and theorems about
`measure_theory.outer_measure.mk_metric'`/`measure_theory.outer_measure.mk_metric` to define
`measure_theory.measure.mk_metric'`/`measure_theory.measure.mk_metric`. We also restate some lemmas
about metric outer measures for metric measures.
-/


namespace Measureₓ

variable [MeasurableSpace X] [BorelSpace X]

/-- Given a function `m : set X → ℝ≥0∞`, `mk_metric' m` is the supremum of `μ r`
over `r > 0`, where `μ r` is the maximal outer measure `μ` such that `μ s ≤ m s`
for all `s`. While each `μ r` is an *outer* measure, the supremum is a measure. -/
def mkMetric' (m : Set X → ℝ≥0∞) : Measure X :=
  (OuterMeasure.mkMetric' m).toMeasure (OuterMeasure.mk_metric'_is_metric _).le_caratheodory

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞`, `mk_metric m` is the supremum of `μ r` over `r > 0`, where
`μ r` is the maximal outer measure `μ` such that `μ s ≤ m s` for all sets `s` that contain at least
two points. While each `mk_metric'.pre` is an *outer* measure, the supremum is a measure. -/
def mkMetric (m : ℝ≥0∞ → ℝ≥0∞) : Measure X :=
  (OuterMeasure.mkMetric m).toMeasure (OuterMeasure.mk_metric'_is_metric _).le_caratheodory

@[simp]
theorem mk_metric'_to_outer_measure (m : Set X → ℝ≥0∞) :
    (mkMetric' m).toOuterMeasure = (OuterMeasure.mkMetric' m).trim :=
  rfl

@[simp]
theorem mk_metric_to_outer_measure (m : ℝ≥0∞ → ℝ≥0∞) :
    (mkMetric m : Measure X).toOuterMeasure = OuterMeasure.mkMetric m :=
  OuterMeasure.trim_mk_metric m

end Measureₓ

theorem OuterMeasure.coe_mk_metric [MeasurableSpace X] [BorelSpace X] (m : ℝ≥0∞ → ℝ≥0∞) :
    ⇑(OuterMeasure.mkMetric m : OuterMeasure X) = Measure.mkMetric m := by
  rw [← measure.mk_metric_to_outer_measure, coe_to_outer_measure]

namespace Measureₓ

variable [MeasurableSpace X] [BorelSpace X]

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[≥] 0]` to state this), then `mk_metric m₁ hm₁ ≤ c • mk_metric m₂ hm₂`. -/
theorem mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0) (hle : m₁ ≤ᶠ[𝓝[≥] 0] c • m₂) :
    (mkMetric m₁ : Measure X) ≤ c • mkMetric m₂ := by
  intro s hs
  rw [← outer_measure.coe_mk_metric, coe_smul, ← outer_measure.coe_mk_metric]
  exact outer_measure.mk_metric_mono_smul hc h0 hle s

/-- If `m₁ d ≤ m₂ d` for `d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝[≥] 0]` to state this), then
`mk_metric m₁ hm₁ ≤ mk_metric m₂ hm₂`-/
theorem mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝[≥] 0] m₂) : (mkMetric m₁ : Measure X) ≤ mkMetric m₂ := by
  convert mk_metric_mono_smul Ennreal.one_ne_top ennreal.zero_lt_one.ne' _ <;> simp [*]

/-- A formula for `measure_theory.measure.mk_metric`. -/
theorem mk_metric_apply (m : ℝ≥0∞ → ℝ≥0∞) (s : Set X) :
    mkMetric m s =
      ⨆ (r : ℝ≥0∞) (hr : 0 < r),
        ⨅ (t : ℕ → Set X) (h : s ⊆ Union t) (h' : ∀ n, diam (t n) ≤ r), ∑' n, ⨆ h : (t n).Nonempty, m (diam (t n)) :=
  by
  -- We mostly unfold the definitions but we need to switch the order of `∑'` and `⨅`
  classical
  simp only [outer_measure.coe_mk_metric, ← outer_measure.mk_metric, ← outer_measure.mk_metric', ←
    outer_measure.supr_apply, ← outer_measure.mk_metric'.pre, ← outer_measure.bounded_by_apply, ← extend]
  refine'
    surjective_id.supr_congr (fun r => r) fun r =>
      (supr_congr_Prop Iff.rfl) fun hr => (surjective_id.infi_congr _) fun t => (infi_congr_Prop Iff.rfl) fun ht => _
  dsimp'
  by_cases' htr : ∀ n, diam (t n) ≤ r
  · rw [infi_eq_if, if_pos htr]
    congr 1 with n : 1
    simp only [← infi_eq_if, ← htr n, ← id, ← if_true, ← supr_and']
    
  · rw [infi_eq_if, if_neg htr]
    push_neg  at htr
    rcases htr with ⟨n, hn⟩
    refine' Ennreal.tsum_eq_top_of_eq_top ⟨n, _⟩
    rw [supr_eq_if, if_pos, infi_eq_if, if_neg]
    exact hn.not_le
    rcases diam_pos_iff.1 ((zero_le r).trans_lt hn) with ⟨x, hx, -⟩
    exact ⟨x, hx⟩
    

theorem le_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (μ : Measure X) (ε : ℝ≥0∞) (h₀ : 0 < ε)
    (h : ∀ s : Set X, diam s ≤ ε → μ s ≤ m (diam s)) : μ ≤ mkMetric m := by
  rw [← to_outer_measure_le, mk_metric_to_outer_measure]
  exact outer_measure.le_mk_metric m μ.to_outer_measure ε h₀ h

/-- To bound the Hausdorff measure (or, more generally, for a measure defined using
`measure_theory.measure.mk_metric`) of a set, one may use coverings with maximum diameter tending to
`0`, indexed by any sequence of encodable types. -/
theorem mk_metric_le_liminf_tsum {β : Type _} {ι : β → Type _} [∀ n, Encodable (ι n)] (s : Set X) {l : Filter β}
    (r : β → ℝ≥0∞) (hr : Tendsto r l (𝓝 0)) (t : ∀ n : β, ι n → Set X) (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n)
    (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) (m : ℝ≥0∞ → ℝ≥0∞) : mkMetric m s ≤ liminfₓ l fun n => ∑' i, m (diam (t n i)) := by
  simp only [← mk_metric_apply]
  refine' supr₂_le fun ε hε => _
  refine' le_of_forall_le_of_dense fun c hc => _
  rcases((frequently_lt_of_liminf_lt
            (by
              infer_auto_param)
            hc).and_eventually
        ((hr.eventually (gt_mem_nhds hε)).And (ht.and hst))).exists with
    ⟨n, hn, hrn, htn, hstn⟩
  set u : ℕ → Set X := fun j => ⋃ b ∈ decode₂ (ι n) j, t n b
  refine'
    infi₂_le_of_le u
      (by
        rwa [Union_decode₂])
      _
  refine' infi_le_of_le (fun j => _) _
  · rw [Emetric.diam_Union_mem_option]
    exact supr₂_le fun _ _ => (htn _).trans hrn.le
    
  · calc (∑' j : ℕ, ⨆ h : (u j).Nonempty, m (diam (u j))) = _ :=
        tsum_Union_decode₂ (fun t : Set X => ⨆ h : t.Nonempty, m (diam t))
          (by
            simp )
          _ _ ≤ ∑' i : ι n, m (diam (t n i)) :=
        Ennreal.tsum_le_tsum fun b => supr_le fun htb => le_rfl _ ≤ c := hn.le
    

/-- To bound the Hausdorff measure (or, more generally, for a measure defined using
`measure_theory.measure.mk_metric`) of a set, one may use coverings with maximum diameter tending to
`0`, indexed by any sequence of finite types. -/
theorem mk_metric_le_liminf_sum {β : Type _} {ι : β → Type _} [hι : ∀ n, Fintype (ι n)] (s : Set X) {l : Filter β}
    (r : β → ℝ≥0∞) (hr : Tendsto r l (𝓝 0)) (t : ∀ n : β, ι n → Set X) (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n)
    (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) (m : ℝ≥0∞ → ℝ≥0∞) : mkMetric m s ≤ liminfₓ l fun n => ∑ i, m (diam (t n i)) := by
  have : ∀ n, Encodable (ι n) := fun n => Fintype.toEncodable _
  simpa only [← tsum_fintype] using mk_metric_le_liminf_tsum s r hr t ht hst m

/-!
### Hausdorff measure and Hausdorff dimension
-/


/-- Hausdorff measure on an (e)metric space. -/
def hausdorffMeasure (d : ℝ) : Measure X :=
  mkMetric fun r => r ^ d

-- mathport name: «exprμH[ ]»
localized [MeasureTheory] notation "μH[" d "]" => MeasureTheory.Measure.hausdorffMeasure d

theorem le_hausdorff_measure (d : ℝ) (μ : Measure X) (ε : ℝ≥0∞) (h₀ : 0 < ε)
    (h : ∀ s : Set X, diam s ≤ ε → μ s ≤ diam s ^ d) : μ ≤ μH[d] :=
  le_mk_metric _ μ ε h₀ h

/-- A formula for `μH[d] s`. -/
theorem hausdorff_measure_apply (d : ℝ) (s : Set X) :
    μH[d] s =
      ⨆ (r : ℝ≥0∞) (hr : 0 < r),
        ⨅ (t : ℕ → Set X) (hts : s ⊆ ⋃ n, t n) (ht : ∀ n, diam (t n) ≤ r), ∑' n, ⨆ h : (t n).Nonempty, diam (t n) ^ d :=
  mk_metric_apply _ _

/-- To bound the Hausdorff measure of a set, one may use coverings with maximum diameter tending
to `0`, indexed by any sequence of encodable types. -/
theorem hausdorff_measure_le_liminf_tsum {β : Type _} {ι : β → Type _} [hι : ∀ n, Encodable (ι n)] (d : ℝ) (s : Set X)
    {l : Filter β} (r : β → ℝ≥0∞) (hr : Tendsto r l (𝓝 0)) (t : ∀ n : β, ι n → Set X)
    (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) :
    μH[d] s ≤ liminfₓ l fun n => ∑' i, diam (t n i) ^ d :=
  mk_metric_le_liminf_tsum s r hr t ht hst _

/-- To bound the Hausdorff measure of a set, one may use coverings with maximum diameter tending
to `0`, indexed by any sequence of finite types. -/
theorem hausdorff_measure_le_liminf_sum {β : Type _} {ι : β → Type _} [hι : ∀ n, Fintype (ι n)] (d : ℝ) (s : Set X)
    {l : Filter β} (r : β → ℝ≥0∞) (hr : Tendsto r l (𝓝 0)) (t : ∀ n : β, ι n → Set X)
    (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) :
    μH[d] s ≤ liminfₓ l fun n => ∑ i, diam (t n i) ^ d :=
  mk_metric_le_liminf_sum s r hr t ht hst _

/-- If `d₁ < d₂`, then for any set `s` we have either `μH[d₂] s = 0`, or `μH[d₁] s = ∞`. -/
theorem hausdorff_measure_zero_or_top {d₁ d₂ : ℝ} (h : d₁ < d₂) (s : Set X) : μH[d₂] s = 0 ∨ μH[d₁] s = ∞ := by
  by_contra' H
  suffices ∀ c : ℝ≥0 , c ≠ 0 → μH[d₂] s ≤ c * μH[d₁] s by
    rcases Ennreal.exists_nnreal_pos_mul_lt H.2 H.1 with ⟨c, hc0, hc⟩
    exact hc.not_le (this c (pos_iff_ne_zero.1 hc0))
  intro c hc
  refine'
    le_iff'.1
      (mk_metric_mono_smul Ennreal.coe_ne_top
        (by
          exact_mod_cast hc)
        _)
      s
  have : 0 < (c ^ (d₂ - d₁)⁻¹ : ℝ≥0∞) := by
    rw [Ennreal.coe_rpow_of_ne_zero hc, pos_iff_ne_zero, Ne.def, Ennreal.coe_eq_zero, Nnreal.rpow_eq_zero_iff]
    exact mt And.left hc
  filter_upwards [Ico_mem_nhds_within_Ici ⟨le_rfl, this⟩]
  rintro r ⟨hr₀, hrc⟩
  lift r to ℝ≥0 using ne_top_of_lt hrc
  rw [Pi.smul_apply, smul_eq_mul, ←
    Ennreal.div_le_iff_le_mul (Or.inr Ennreal.coe_ne_top) (Or.inr <| mt Ennreal.coe_eq_zero.1 hc)]
  rcases eq_or_ne r 0 with (rfl | hr₀)
  · rcases lt_or_leₓ 0 d₂ with (h₂ | h₂)
    · simp only [← h₂, ← Ennreal.zero_rpow_of_pos, ← zero_le', ← Ennreal.coe_nonneg, ← Ennreal.zero_div, ←
        Ennreal.coe_zero]
      
    · simp only [← h.trans_le h₂, ← Ennreal.div_top, ← zero_le', ← Ennreal.coe_nonneg, ← Ennreal.zero_rpow_of_neg, ←
        Ennreal.coe_zero]
      
    
  · have : (r : ℝ≥0∞) ≠ 0 := by
      simpa only [← Ennreal.coe_eq_zero, ← Ne.def] using hr₀
    rw [← Ennreal.rpow_sub _ _ this Ennreal.coe_ne_top]
    refine' (Ennreal.rpow_lt_rpow hrc (sub_pos.2 h)).le.trans _
    rw [← Ennreal.rpow_mul, inv_mul_cancel (sub_pos.2 h).ne', Ennreal.rpow_one]
    exact le_rfl
    

/-- Hausdorff measure `μH[d] s` is monotone in `d`. -/
theorem hausdorff_measure_mono {d₁ d₂ : ℝ} (h : d₁ ≤ d₂) (s : Set X) : μH[d₂] s ≤ μH[d₁] s := by
  rcases h.eq_or_lt with (rfl | h)
  · exact le_rfl
    
  cases' hausdorff_measure_zero_or_top h s with hs hs
  · rw [hs]
    exact zero_le _
    
  · rw [hs]
    exact le_top
    

variable (X)

theorem no_atoms_hausdorff {d : ℝ} (hd : 0 < d) : HasNoAtoms (hausdorffMeasure d : Measure X) := by
  refine' ⟨fun x => _⟩
  rw [← nonpos_iff_eq_zero, hausdorff_measure_apply]
  refine' supr₂_le fun ε ε0 => infi₂_le_of_le (fun n => {x}) _ <| infi_le_of_le (fun n => _) _
  · exact subset_Union (fun n => {x} : ℕ → Set X) 0
    
  · simp only [← Emetric.diam_singleton, ← zero_le]
    
  · simp [← hd]
    

variable {X}

@[simp]
theorem hausdorff_measure_zero_singleton (x : X) : μH[0] ({x} : Set X) = 1 := by
  apply le_antisymmₓ
  · let r : ℕ → ℝ≥0∞ := fun _ => 0
    let t : ℕ → Unit → Set X := fun n _ => {x}
    have ht : ∀ᶠ n in at_top, ∀ i, diam (t n i) ≤ r n := by
      simp only [← implies_true_iff, ← eq_self_iff_true, ← diam_singleton, ← eventually_at_top, ← nonpos_iff_eq_zero, ←
        exists_const]
    simpa [← liminf_const] using hausdorff_measure_le_liminf_sum 0 {x} r tendsto_const_nhds t ht
    
  · rw [hausdorff_measure_apply]
    suffices
      (1 : ℝ≥0∞) ≤
        ⨅ (t : ℕ → Set X) (hts : {x} ⊆ ⋃ n, t n) (ht : ∀ n, diam (t n) ≤ 1),
          ∑' n, ⨆ h : (t n).Nonempty, diam (t n) ^ (0 : ℝ)
      by
      apply le_transₓ this _
      convert le_supr₂ (1 : ℝ≥0∞) Ennreal.zero_lt_one
      rfl
    simp only [← Ennreal.rpow_zero, ← le_infi_iff]
    intro t hst h't
    rcases mem_Union.1 (hst (mem_singleton x)) with ⟨m, hm⟩
    have A : (t m).Nonempty := ⟨x, hm⟩
    calc (1 : ℝ≥0∞) = ⨆ h : (t m).Nonempty, 1 := by
        simp only [← A, ← csupr_pos]_ ≤ ∑' n, ⨆ h : (t n).Nonempty, 1 := Ennreal.le_tsum _
    

theorem one_le_hausdorff_measure_zero_of_nonempty {s : Set X} (h : s.Nonempty) : 1 ≤ μH[0] s := by
  rcases h with ⟨x, hx⟩
  calc (1 : ℝ≥0∞) = μH[0] ({x} : Set X) := (hausdorff_measure_zero_singleton x).symm _ ≤ μH[0] s :=
      measure_mono (singleton_subset_iff.2 hx)

theorem hausdorff_measure_le_one_of_subsingleton {s : Set X} (hs : s.Subsingleton) {d : ℝ} (hd : 0 ≤ d) : μH[d] s ≤ 1 :=
  by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  · simp only [← measure_empty, ← zero_le]
    
  · rw [(subsingleton_iff_singleton hx).1 hs]
    rcases eq_or_lt_of_le hd with (rfl | dpos)
    · simp only [← le_reflₓ, ← hausdorff_measure_zero_singleton]
      
    · have := no_atoms_hausdorff X dpos
      simp only [← zero_le, ← measure_singleton]
      
    

end Measureₓ

open MeasureTheory

open Measureₓ

/-!
### Hausdorff measure and Lebesgue measure
-/


/-- In the space `ι → ℝ`, Hausdorff measure coincides exactly with Lebesgue measure. -/
@[simp]
theorem hausdorff_measure_pi_real {ι : Type _} [Fintype ι] : (μH[Fintype.card ι] : Measure (ι → ℝ)) = volume := by
  classical
  -- it suffices to check that the two measures coincide on products of rational intervals
  refine'
    (pi_eq_generate_from (fun i => real.borel_eq_generate_from_Ioo_rat.symm) (fun i => Real.is_pi_system_Ioo_rat)
        (fun i => Real.finiteSpanningSetsInIooRat _) _).symm
  simp only [← mem_Union, ← mem_singleton_iff]
  -- fix such a product `s` of rational intervals, of the form `Π (a i, b i)`.
  intro s hs
  choose a b H using hs
  obtain rfl : s = fun i => Ioo (a i) (b i)
  exact funext fun i => (H i).2
  replace H := fun i => (H i).1
  apply le_antisymmₓ _
  -- first check that `volume s ≤ μH s`
  · have Hle : volume ≤ (μH[Fintype.card ι] : Measureₓ (ι → ℝ)) := by
      refine' le_hausdorff_measure _ _ ∞ Ennreal.coe_lt_top fun s _ => _
      rw [Ennreal.rpow_nat_cast]
      exact Real.volume_pi_le_diam_pow s
    rw [← volume_pi_pi fun i => Ioo (a i : ℝ) (b i)]
    exact measure.le_iff'.1 Hle _
    
  /- For the other inequality `μH s ≤ volume s`, we use a covering of `s` by sets of small diameter
    `1/n`, namely cubes with left-most point of the form `a i + f i / n` with `f i` ranging between
    `0` and `⌈(b i - a i) * n⌉`. Their number is asymptotic to `n^d * Π (b i - a i)`. -/
  have I : ∀ i, 0 ≤ (b i : ℝ) - a i := fun i => by
    simpa only [← sub_nonneg, ← Rat.cast_le] using (H i).le
  let γ := fun n : ℕ => ∀ i : ι, Finₓ ⌈((b i : ℝ) - a i) * n⌉₊
  let t : ∀ n : ℕ, γ n → Set (ι → ℝ) := fun n f => Set.Pi univ fun i => Icc (a i + f i / n) (a i + (f i + 1) / n)
  have A : tendsto (fun n : ℕ => 1 / (n : ℝ≥0∞)) at_top (𝓝 0) := by
    simp only [← one_div, ← Ennreal.tendsto_inv_nat_nhds_zero]
  have B : ∀ᶠ n in at_top, ∀ i : γ n, diam (t n i) ≤ 1 / n := by
    apply eventually_at_top.2 ⟨1, fun n hn => _⟩
    intro f
    apply diam_pi_le_of_le fun b => _
    simp only [← Real.ediam_Icc, ← add_div, ← Ennreal.of_real_div_of_pos (nat.cast_pos.mpr hn), ← le_reflₓ, ←
      add_sub_add_left_eq_sub, ← add_sub_cancel', ← Ennreal.of_real_one, ← Ennreal.of_real_coe_nat]
  have C : ∀ᶠ n in at_top, (Set.Pi univ fun i : ι => Ioo (a i : ℝ) (b i)) ⊆ ⋃ i : γ n, t n i := by
    apply eventually_at_top.2 ⟨1, fun n hn => _⟩
    have npos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    intro x hx
    simp only [← mem_Ioo, ← mem_univ_pi] at hx
    simp only [← mem_Union, ← mem_Ioo, ← mem_univ_pi, ← coe_coe]
    let f : γ n := fun i =>
      ⟨⌊(x i - a i) * n⌋₊, by
        apply Nat.floor_lt_ceil_of_lt_of_pos
        · refine' (mul_lt_mul_right npos).2 _
          simp only [← (hx i).right, ← sub_lt_sub_iff_right]
          
        · refine' mul_pos _ npos
          simpa only [← Rat.cast_lt, ← sub_pos] using H i
          ⟩
    refine' ⟨f, fun i => ⟨_, _⟩⟩
    · calc (a i : ℝ) + ⌊(x i - a i) * n⌋₊ / n ≤ (a i : ℝ) + (x i - a i) * n / n := by
          refine' add_le_add le_rfl ((div_le_div_right npos).2 _)
          exact Nat.floor_le (mul_nonneg (sub_nonneg.2 (hx i).1.le) npos.le)_ = x i := by
          field_simp [← npos.ne']
      
    · calc x i = (a i : ℝ) + (x i - a i) * n / n := by
          field_simp [← npos.ne']_ ≤ (a i : ℝ) + (⌊(x i - a i) * n⌋₊ + 1) / n :=
          add_le_add le_rfl ((div_le_div_right npos).2 (Nat.lt_floor_add_one _).le)
      
  calc
    μH[Fintype.card ι] (Set.Pi univ fun i : ι => Ioo (a i : ℝ) (b i)) ≤
        liminf at_top fun n : ℕ => ∑ i : γ n, diam (t n i) ^ ↑(Fintype.card ι) :=
      hausdorff_measure_le_liminf_sum _ (Set.Pi univ fun i => Ioo (a i : ℝ) (b i)) (fun n : ℕ => 1 / (n : ℝ≥0∞)) A t B
        C _ ≤ liminf at_top fun n : ℕ => ∑ i : γ n, (1 / n) ^ Fintype.card ι :=
      by
      refine'
        liminf_le_liminf _
          (by
            run_tac
              is_bounded_default)
      filter_upwards [B] with _ hn
      apply Finset.sum_le_sum fun i _ => _
      rw [Ennreal.rpow_nat_cast]
      exact
        pow_le_pow_of_le_left' (hn i) _ _ = liminf at_top fun n : ℕ => ∏ i : ι, (⌈((b i : ℝ) - a i) * n⌉₊ : ℝ≥0∞) / n :=
      by
      simp only [← Finset.card_univ, ← Nat.cast_prod, ← one_mulₓ, ← Fintype.card_fin, ← Finset.sum_const, ←
        nsmul_eq_mul, ← Fintype.card_pi, ← div_eq_mul_inv, ← Finset.prod_mul_distrib, ←
        Finset.prod_const]_ = ∏ i : ι, volume (Ioo (a i : ℝ) (b i)) :=
      by
      simp only [← Real.volume_Ioo]
      apply tendsto.liminf_eq
      refine' Ennreal.tendsto_finset_prod_of_ne_top _ (fun i hi => _) fun i hi => _
      · apply
          tendsto.congr' _
            ((ennreal.continuous_of_real.tendsto _).comp
              ((tendsto_nat_ceil_mul_div_at_top (I i)).comp tendsto_coe_nat_at_top_at_top))
        apply eventually_at_top.2 ⟨1, fun n hn => _⟩
        simp only [← Ennreal.of_real_div_of_pos (nat.cast_pos.mpr hn), ← comp_app, ← Ennreal.of_real_coe_nat]
        
      · simp only [← Ennreal.of_real_ne_top, ← Ne.def, ← not_false_iff]
        

end MeasureTheory

/-!
### Hausdorff measure, Hausdorff dimension, and Hölder or Lipschitz continuous maps
-/


open MeasureTheory

open MeasureTheory MeasureTheory.Measure

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

namespace HolderOnWith

variable {C r : ℝ≥0 } {f : X → Y} {s t : Set X}

/-- If `f : X → Y` is Hölder continuous on `s` with a positive exponent `r`, then
`μH[d] (f '' s) ≤ C ^ d * μH[r * d] s`. -/
theorem hausdorff_measure_image_le (h : HolderOnWith C r f s) (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
    μH[d] (f '' s) ≤ C ^ d * μH[r * d] s := by
  -- We start with the trivial case `C = 0`
  rcases(zero_le C).eq_or_lt with (rfl | hC0)
  · rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    · simp only [← measure_empty, ← nonpos_iff_eq_zero, ← mul_zero, ← image_empty]
      
    have : f '' s = {f x} := by
      have : (f '' s).Subsingleton := by
        simpa [← diam_eq_zero_iff] using h.ediam_image_le
      exact (subsingleton_iff_singleton (mem_image_of_mem f hx)).1 this
    rw [this]
    rcases eq_or_lt_of_le hd with (rfl | h'd)
    · simp only [← Ennreal.rpow_zero, ← one_mulₓ, ← mul_zero]
      rw [hausdorff_measure_zero_singleton]
      exact one_le_hausdorff_measure_zero_of_nonempty ⟨x, hx⟩
      
    · have := no_atoms_hausdorff Y h'd
      simp only [← zero_le, ← measure_singleton]
      
    
  -- Now assume `C ≠ 0`
  · have hCd0 : (C : ℝ≥0∞) ^ d ≠ 0 := by
      simp [← hC0.ne']
    have hCd : (C : ℝ≥0∞) ^ d ≠ ∞ := by
      simp [← hd]
    simp only [← hausdorff_measure_apply, ← Ennreal.mul_supr, ← Ennreal.mul_infi_of_ne hCd0 hCd, Ennreal.tsum_mul_left]
    refine' supr_le fun R => supr_le fun hR => _
    have : tendsto (fun d : ℝ≥0∞ => (C : ℝ≥0∞) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0) :=
      Ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos Ennreal.coe_ne_top hr
    rcases ennreal.nhds_zero_basis_Iic.eventually_iff.1 (this.eventually (gt_mem_nhds hR)) with ⟨δ, δ0, H⟩
    refine'
      le_supr₂_of_le δ δ0
        (infi₂_mono' fun t hst =>
          ⟨fun n => f '' (t n ∩ s), _,
            infi_mono' fun htδ => ⟨fun n => (h.ediam_image_inter_le (t n)).trans (H (htδ n)).le, _⟩⟩)
    · rw [← image_Union, ← Union_inter]
      exact image_subset _ (subset_inter hst subset.rfl)
      
    · apply Ennreal.tsum_le_tsum fun n => _
      simp only [← supr_le_iff, ← nonempty_image_iff]
      intro hft
      simp only [← nonempty.mono ((t n).inter_subset_left s) hft, ← csupr_pos]
      rw [Ennreal.rpow_mul, ← Ennreal.mul_rpow_of_nonneg _ _ hd]
      exact Ennreal.rpow_le_rpow (h.ediam_image_inter_le _) hd
      
    

end HolderOnWith

namespace LipschitzOnWith

variable {K : ℝ≥0 } {f : X → Y} {s t : Set X}

/-- If `f : X → Y` is `K`-Lipschitz on `s`, then `μH[d] (f '' s) ≤ K ^ d * μH[d] s`. -/
theorem hausdorff_measure_image_le (h : LipschitzOnWith K f s) {d : ℝ} (hd : 0 ≤ d) :
    μH[d] (f '' s) ≤ K ^ d * μH[d] s := by
  simpa only [← Nnreal.coe_one, ← one_mulₓ] using h.holder_on_with.hausdorff_measure_image_le zero_lt_one hd

end LipschitzOnWith

namespace LipschitzWith

variable {K : ℝ≥0 } {f : X → Y}

/-- If `f` is a `K`-Lipschitz map, then it increases the Hausdorff `d`-measures of sets at most
by the factor of `K ^ d`.-/
theorem hausdorff_measure_image_le (h : LipschitzWith K f) {d : ℝ} (hd : 0 ≤ d) (s : Set X) :
    μH[d] (f '' s) ≤ K ^ d * μH[d] s :=
  (h.LipschitzOnWith s).hausdorff_measure_image_le hd

end LipschitzWith

/-!
### Antilipschitz maps do not decrease Hausdorff measures and dimension
-/


namespace AntilipschitzWith

variable {f : X → Y} {K : ℝ≥0 } {d : ℝ}

theorem hausdorff_measure_preimage_le (hf : AntilipschitzWith K f) (hd : 0 ≤ d) (s : Set Y) :
    μH[d] (f ⁻¹' s) ≤ K ^ d * μH[d] s := by
  rcases eq_or_ne K 0 with (rfl | h0)
  · rcases eq_empty_or_nonempty (f ⁻¹' s) with (hs | ⟨x, hx⟩)
    · simp only [← hs, ← measure_empty, ← zero_le]
      
    have : f ⁻¹' s = {x} := by
      have : Subsingleton X := hf.subsingleton
      have : (f ⁻¹' s).Subsingleton := subsingleton_univ.mono (subset_univ _)
      exact (subsingleton_iff_singleton hx).1 this
    rw [this]
    rcases eq_or_lt_of_le hd with (rfl | h'd)
    · simp only [← Ennreal.rpow_zero, ← one_mulₓ, ← mul_zero]
      rw [hausdorff_measure_zero_singleton]
      exact one_le_hausdorff_measure_zero_of_nonempty ⟨f x, hx⟩
      
    · have := no_atoms_hausdorff X h'd
      simp only [← zero_le, ← measure_singleton]
      
    
  have hKd0 : (K : ℝ≥0∞) ^ d ≠ 0 := by
    simp [← h0]
  have hKd : (K : ℝ≥0∞) ^ d ≠ ∞ := by
    simp [← hd]
  simp only [← hausdorff_measure_apply, ← Ennreal.mul_supr, ← Ennreal.mul_infi_of_ne hKd0 hKd, Ennreal.tsum_mul_left]
  refine' supr₂_le fun ε ε0 => _
  refine'
    le_supr₂_of_le (ε / K)
      (by
        simp [← ε0.ne'])
      _
  refine' le_infi₂ fun t hst => le_infi fun htε => _
  replace hst : f ⁻¹' s ⊆ _ := preimage_mono hst
  rw [preimage_Union] at hst
  refine' infi₂_le_of_le _ hst (infi_le_of_le (fun n => _) _)
  · exact (hf.ediam_preimage_le _).trans (Ennreal.mul_le_of_le_div' <| htε n)
    
  · refine' Ennreal.tsum_le_tsum fun n => supr_le_iff.2 fun hft => _
    simp only [← nonempty_of_nonempty_preimage hft, ← csupr_pos]
    rw [← Ennreal.mul_rpow_of_nonneg _ _ hd]
    exact Ennreal.rpow_le_rpow (hf.ediam_preimage_le _) hd
    

theorem le_hausdorff_measure_image (hf : AntilipschitzWith K f) (hd : 0 ≤ d) (s : Set X) :
    μH[d] s ≤ K ^ d * μH[d] (f '' s) :=
  calc
    μH[d] s ≤ μH[d] (f ⁻¹' (f '' s)) := measure_mono (subset_preimage_image _ _)
    _ ≤ K ^ d * μH[d] (f '' s) := hf.hausdorff_measure_preimage_le hd (f '' s)
    

end AntilipschitzWith

/-!
### Isometries preserve the Hausdorff measure and Hausdorff dimension
-/


namespace Isometry

variable {f : X → Y} {d : ℝ}

theorem hausdorff_measure_image (hf : Isometry f) (hd : 0 ≤ d ∨ Surjective f) (s : Set X) : μH[d] (f '' s) = μH[d] s :=
  by
  simp only [← hausdorff_measure, outer_measure.coe_mk_metric, outer_measure.comap_apply]
  rw [outer_measure.isometry_comap_mk_metric _ hf (hd.imp_left _)]
  exact fun hd x y hxy => Ennreal.rpow_le_rpow hxy hd

theorem hausdorff_measure_preimage (hf : Isometry f) (hd : 0 ≤ d ∨ Surjective f) (s : Set Y) :
    μH[d] (f ⁻¹' s) = μH[d] (s ∩ Range f) := by
  rw [← hf.hausdorff_measure_image hd, image_preimage_eq_inter_range]

theorem map_hausdorff_measure (hf : Isometry f) (hd : 0 ≤ d ∨ Surjective f) :
    Measure.map f μH[d] = μH[d].restrict (Range f) := by
  ext1 s hs
  rw [map_apply hf.continuous.measurable hs, restrict_apply hs, hf.hausdorff_measure_preimage hd]

end Isometry

namespace Isometric

@[simp]
theorem hausdorff_measure_image (e : X ≃ᵢ Y) (d : ℝ) (s : Set X) : μH[d] (e '' s) = μH[d] s :=
  e.Isometry.hausdorff_measure_image (Or.inr e.Surjective) s

@[simp]
theorem hausdorff_measure_preimage (e : X ≃ᵢ Y) (d : ℝ) (s : Set Y) : μH[d] (e ⁻¹' s) = μH[d] s := by
  rw [← e.image_symm, e.symm.hausdorff_measure_image]

end Isometric

