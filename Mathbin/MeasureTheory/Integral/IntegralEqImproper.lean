/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Bhavik Mehta
-/
import Mathbin.MeasureTheory.Integral.IntervalIntegral
import Mathbin.Order.Filter.AtTopBot

/-!
# Links between an integral and its "improper" version

In its current state, mathlib only knows how to talk about definite ("proper") integrals,
in the sense that it treats integrals over `[x, +∞)` the same as it treats integrals over
`[y, z]`. For example, the integral over `[1, +∞)` is **not** defined to be the limit of
the integral over `[1, x]` as `x` tends to `+∞`, which is known as an **improper integral**.

Indeed, the "proper" definition is stronger than the "improper" one. The usual counterexample
is `x ↦ sin(x)/x`, which has an improper integral over `[1, +∞)` but no definite integral.

Although definite integrals have better properties, they are hardly usable when it comes to
computing integrals on unbounded sets, which is much easier using limits. Thus, in this file,
we prove various ways of studying the proper integral by studying the improper one.

## Definitions

The main definition of this file is `measure_theory.ae_cover`. It is a rather technical
definition whose sole purpose is generalizing and factoring proofs. Given an index type `ι`, a
countably generated filter `l` over `ι`, and an `ι`-indexed family `φ` of subsets of a measurable
space `α` equipped with a measure `μ`, one should think of a hypothesis `hφ : ae_cover μ l φ` as
a sufficient condition for being able to interpret `∫ x, f x ∂μ` (if it exists) as the limit
of `∫ x in φ i, f x ∂μ` as `i` tends to `l`.

When using this definition with a measure restricted to a set `s`, which happens fairly often,
one should not try too hard to use a `ae_cover` of subsets of `s`, as it often makes proofs
more complicated than necessary. See for example the proof of
`measure_theory.integrable_on_Iic_of_interval_integral_norm_tendsto` where we use `(λ x, Ioi x)`
as an `ae_cover` w.r.t. `μ.restrict (Iic b)`, instead of using `(λ x, Ioc x b)`.

## Main statements

- `measure_theory.ae_cover.lintegral_tendsto_of_countably_generated` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, and if `f` is a measurable `ennreal`-valued function,
  then `∫⁻ x in φ n, f x ∂μ` tends to `∫⁻ x, f x ∂μ` as `n` tends to `l`
- `measure_theory.ae_cover.integrable_of_integral_norm_tendsto` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, if `f` is measurable and integrable on each `φ n`,
  and if `∫ x in φ n, ∥f x∥ ∂μ` tends to some `I : ℝ` as n tends to `l`, then `f` is integrable
- `measure_theory.ae_cover.integral_tendsto_of_countably_generated` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, and if `f` is measurable and integrable (globally),
  then `∫ x in φ n, f x ∂μ` tends to `∫ x, f x ∂μ` as `n` tends to `+∞`.

We then specialize these lemmas to various use cases involving intervals, which are frequent
in analysis.
-/


open MeasureTheory Filter Set TopologicalSpace

open Ennreal Nnreal TopologicalSpace

namespace MeasureTheory

section AeCover

variable {α ι : Type _} [MeasurableSpace α] (μ : Measure α) (l : Filter ι)

/-- A sequence `φ` of subsets of `α` is a `ae_cover` w.r.t. a measure `μ` and a filter `l`
    if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n` (w.r.t. `l`), and if
    each `φ n` is measurable.
    This definition is a technical way to avoid duplicating a lot of proofs.
    It should be thought of as a sufficient condition for being able to interpret
    `∫ x, f x ∂μ` (if it exists) as the limit of `∫ x in φ n, f x ∂μ` as `n` tends to `l`.

    See for example `measure_theory.ae_cover.lintegral_tendsto_of_countably_generated`,
    `measure_theory.ae_cover.integrable_of_integral_norm_tendsto` and
    `measure_theory.ae_cover.integral_tendsto_of_countably_generated`. -/
structure AeCover (φ : ι → Set α) : Prop where
  ae_eventually_mem : ∀ᵐ x ∂μ, ∀ᶠ i in l, x ∈ φ i
  Measurable : ∀ i, MeasurableSet <| φ i

variable {μ} {l}

section Preorderα

variable [Preorderₓ α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α] {a b : ι → α}
  (ha : Tendsto a l atBot) (hb : Tendsto b l atTop)

theorem ae_cover_Icc : AeCover μ l fun i => Icc (a i) (b i) :=
  { ae_eventually_mem :=
      ae_of_all μ fun x =>
        (ha.Eventually <| eventually_le_at_bot x).mp <|
          (hb.Eventually <| eventually_ge_at_top x).mono fun i hbi hai => ⟨hai, hbi⟩,
    Measurable := fun i => measurable_set_Icc }

theorem ae_cover_Ici : AeCover μ l fun i => Ici <| a i :=
  { ae_eventually_mem := ae_of_all μ fun x => (ha.Eventually <| eventually_le_at_bot x).mono fun i hai => hai,
    Measurable := fun i => measurable_set_Ici }

theorem ae_cover_Iic : AeCover μ l fun i => Iic <| b i :=
  { ae_eventually_mem := ae_of_all μ fun x => (hb.Eventually <| eventually_ge_at_top x).mono fun i hbi => hbi,
    Measurable := fun i => measurable_set_Iic }

end Preorderα

section LinearOrderα

variable [LinearOrderₓ α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α] {a b : ι → α}
  (ha : Tendsto a l atBot) (hb : Tendsto b l atTop)

theorem ae_cover_Ioo [NoMinOrder α] [NoMaxOrder α] : AeCover μ l fun i => Ioo (a i) (b i) :=
  { ae_eventually_mem :=
      ae_of_all μ fun x =>
        (ha.Eventually <| eventually_lt_at_bot x).mp <|
          (hb.Eventually <| eventually_gt_at_top x).mono fun i hbi hai => ⟨hai, hbi⟩,
    Measurable := fun i => measurable_set_Ioo }

theorem ae_cover_Ioc [NoMinOrder α] : AeCover μ l fun i => Ioc (a i) (b i) :=
  { ae_eventually_mem :=
      ae_of_all μ fun x =>
        (ha.Eventually <| eventually_lt_at_bot x).mp <|
          (hb.Eventually <| eventually_ge_at_top x).mono fun i hbi hai => ⟨hai, hbi⟩,
    Measurable := fun i => measurable_set_Ioc }

theorem ae_cover_Ico [NoMaxOrder α] : AeCover μ l fun i => Ico (a i) (b i) :=
  { ae_eventually_mem :=
      ae_of_all μ fun x =>
        (ha.Eventually <| eventually_le_at_bot x).mp <|
          (hb.Eventually <| eventually_gt_at_top x).mono fun i hbi hai => ⟨hai, hbi⟩,
    Measurable := fun i => measurable_set_Ico }

theorem ae_cover_Ioi [NoMinOrder α] : AeCover μ l fun i => Ioi <| a i :=
  { ae_eventually_mem := ae_of_all μ fun x => (ha.Eventually <| eventually_lt_at_bot x).mono fun i hai => hai,
    Measurable := fun i => measurable_set_Ioi }

theorem ae_cover_Iio [NoMaxOrder α] : AeCover μ l fun i => Iio <| b i :=
  { ae_eventually_mem := ae_of_all μ fun x => (hb.Eventually <| eventually_gt_at_top x).mono fun i hbi => hbi,
    Measurable := fun i => measurable_set_Iio }

end LinearOrderα

section FiniteIntervals

variable [LinearOrderₓ α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α] {a b : ι → α} {A B : α}
  (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))

theorem ae_cover_Ioo_of_Icc : AeCover (μ.restrict <| Ioo A B) l fun i => Icc (a i) (b i) :=
  { ae_eventually_mem :=
      (ae_restrict_iff' measurable_set_Ioo).mpr
        (ae_of_all μ fun x hx =>
          (ha.Eventually <| eventually_le_nhds hx.left).mp <|
            (hb.Eventually <| eventually_ge_nhds hx.right).mono fun i hbi hai => ⟨hai, hbi⟩),
    Measurable := fun i => measurable_set_Icc }

theorem ae_cover_Ioo_of_Ico : AeCover (μ.restrict <| Ioo A B) l fun i => Ico (a i) (b i) :=
  { ae_eventually_mem :=
      (ae_restrict_iff' measurable_set_Ioo).mpr
        (ae_of_all μ fun x hx =>
          (ha.Eventually <| eventually_le_nhds hx.left).mp <|
            (hb.Eventually <| eventually_gt_nhds hx.right).mono fun i hbi hai => ⟨hai, hbi⟩),
    Measurable := fun i => measurable_set_Ico }

theorem ae_cover_Ioo_of_Ioc : AeCover (μ.restrict <| Ioo A B) l fun i => Ioc (a i) (b i) :=
  { ae_eventually_mem :=
      (ae_restrict_iff' measurable_set_Ioo).mpr
        (ae_of_all μ fun x hx =>
          (ha.Eventually <| eventually_lt_nhds hx.left).mp <|
            (hb.Eventually <| eventually_ge_nhds hx.right).mono fun i hbi hai => ⟨hai, hbi⟩),
    Measurable := fun i => measurable_set_Ioc }

theorem ae_cover_Ioo_of_Ioo : AeCover (μ.restrict <| Ioo A B) l fun i => Ioo (a i) (b i) :=
  { ae_eventually_mem :=
      (ae_restrict_iff' measurable_set_Ioo).mpr
        (ae_of_all μ fun x hx =>
          (ha.Eventually <| eventually_lt_nhds hx.left).mp <|
            (hb.Eventually <| eventually_gt_nhds hx.right).mono fun i hbi hai => ⟨hai, hbi⟩),
    Measurable := fun i => measurable_set_Ioo }

variable [HasNoAtoms μ]

theorem ae_cover_Ioc_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Ioc A B) l fun i => Icc (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, ← ae_cover_Ioo_of_Icc ha hb]

theorem ae_cover_Ioc_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Ioc A B) l fun i => Ico (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, ← ae_cover_Ioo_of_Ico ha hb]

theorem ae_cover_Ioc_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Ioc A B) l fun i => Ioc (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, ← ae_cover_Ioo_of_Ioc ha hb]

theorem ae_cover_Ioc_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Ioc A B) l fun i => Ioo (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, ← ae_cover_Ioo_of_Ioo ha hb]

theorem ae_cover_Ico_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Ico A B) l fun i => Icc (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Ico.symm, ← ae_cover_Ioo_of_Icc ha hb]

theorem ae_cover_Ico_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Ico A B) l fun i => Ico (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Ico.symm, ← ae_cover_Ioo_of_Ico ha hb]

theorem ae_cover_Ico_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Ico A B) l fun i => Ioc (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Ico.symm, ← ae_cover_Ioo_of_Ioc ha hb]

theorem ae_cover_Ico_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Ico A B) l fun i => Ioo (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Ico.symm, ← ae_cover_Ioo_of_Ioo ha hb]

theorem ae_cover_Icc_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Icc A B) l fun i => Icc (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Icc.symm, ← ae_cover_Ioo_of_Icc ha hb]

theorem ae_cover_Icc_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Icc A B) l fun i => Ico (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Icc.symm, ← ae_cover_Ioo_of_Ico ha hb]

theorem ae_cover_Icc_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Icc A B) l fun i => Ioc (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Icc.symm, ← ae_cover_Ioo_of_Ioc ha hb]

theorem ae_cover_Icc_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AeCover (μ.restrict <| Icc A B) l fun i => Ioo (a i) (b i) := by
  simp [← measure.restrict_congr_set Ioo_ae_eq_Icc.symm, ← ae_cover_Ioo_of_Ioo ha hb]

end FiniteIntervals

theorem AeCover.restrict {φ : ι → Set α} (hφ : AeCover μ l φ) {s : Set α} : AeCover (μ.restrict s) l φ :=
  { ae_eventually_mem := ae_restrict_of_ae hφ.ae_eventually_mem, Measurable := hφ.Measurable }

theorem ae_cover_restrict_of_ae_imp {s : Set α} {φ : ι → Set α} (hs : MeasurableSet s)
    (ae_eventually_mem : ∀ᵐ x ∂μ, x ∈ s → ∀ᶠ n in l, x ∈ φ n) (measurable : ∀ n, MeasurableSet <| φ n) :
    AeCover (μ.restrict s) l φ :=
  { ae_eventually_mem := by
      rwa [ae_restrict_iff' hs],
    Measurable }

theorem AeCover.inter_restrict {φ : ι → Set α} (hφ : AeCover μ l φ) {s : Set α} (hs : MeasurableSet s) :
    AeCover (μ.restrict s) l fun i => φ i ∩ s :=
  ae_cover_restrict_of_ae_imp hs (hφ.ae_eventually_mem.mono fun x hx hxs => hx.mono fun i hi => ⟨hi, hxs⟩) fun i =>
    (hφ.Measurable i).inter hs

theorem AeCover.ae_tendsto_indicator {β : Type _} [Zero β] [TopologicalSpace β] (f : α → β) {φ : ι → Set α}
    (hφ : AeCover μ l φ) : ∀ᵐ x ∂μ, Tendsto (fun i => (φ i).indicator f x) l (𝓝 <| f x) :=
  hφ.ae_eventually_mem.mono fun x hx => tendsto_const_nhds.congr' <| hx.mono fun n hn => (indicator_of_mem hn _).symm

theorem AeCover.ae_measurable {β : Type _} [MeasurableSpace β] [l.IsCountablyGenerated] [l.ne_bot] {f : α → β}
    {φ : ι → Set α} (hφ : AeCover μ l φ) (hfm : ∀ i, AeMeasurable f (μ.restrict <| φ i)) : AeMeasurable f μ := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := ae_measurable_Union_iff.mpr fun n : ℕ => hfm (u n)
  rwa [measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using let ⟨i, hi⟩ := (hu.eventually hx).exists
    mem_Union.mpr ⟨i, hi⟩

theorem AeCover.ae_strongly_measurable {β : Type _} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [l.IsCountablyGenerated] [l.ne_bot] {f : α → β} {φ : ι → Set α} (hφ : AeCover μ l φ)
    (hfm : ∀ i, AeStronglyMeasurable f (μ.restrict <| φ i)) : AeStronglyMeasurable f μ := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := ae_strongly_measurable_Union_iff.mpr fun n : ℕ => hfm (u n)
  rwa [measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using let ⟨i, hi⟩ := (hu.eventually hx).exists
    mem_Union.mpr ⟨i, hi⟩

end AeCover

theorem AeCover.comp_tendsto {α ι ι' : Type _} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} {l' : Filter ι'}
    {φ : ι → Set α} (hφ : AeCover μ l φ) {u : ι' → ι} (hu : Tendsto u l' l) : AeCover μ l' (φ ∘ u) :=
  { ae_eventually_mem := hφ.ae_eventually_mem.mono fun x hx => hu.Eventually hx,
    Measurable := fun i => hφ.Measurable (u i) }

section AeCoverUnionInterEncodable

variable {α ι : Type _} [Encodable ι] [MeasurableSpace α] {μ : Measure α}

theorem AeCover.bUnion_Iic_ae_cover [Preorderₓ ι] {φ : ι → Set α} (hφ : AeCover μ atTop φ) :
    AeCover μ atTop fun n : ι => ⋃ (k) (h : k ∈ Iic n), φ k :=
  { ae_eventually_mem := hφ.ae_eventually_mem.mono fun x h => h.mono fun i hi => mem_bUnion right_mem_Iic hi,
    Measurable := fun i => MeasurableSet.bUnion (countable_encodable _) fun n _ => hφ.Measurable n }

theorem AeCover.bInter_Ici_ae_cover [SemilatticeSup ι] [Nonempty ι] {φ : ι → Set α} (hφ : AeCover μ atTop φ) :
    AeCover μ atTop fun n : ι => ⋂ (k) (h : k ∈ Ici n), φ k :=
  { ae_eventually_mem :=
      hφ.ae_eventually_mem.mono
        (by
          intro x h
          rw [eventually_at_top] at *
          rcases h with ⟨i, hi⟩
          use i
          intro j hj
          exact mem_bInter fun k hk => hi k (le_transₓ hj hk)),
    Measurable := fun i => MeasurableSet.bInter (countable_encodable _) fun n _ => hφ.Measurable n }

end AeCoverUnionInterEncodable

section Lintegral

variable {α ι : Type _} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}

private theorem lintegral_tendsto_of_monotone_of_nat {φ : ℕ → Set α} (hφ : AeCover μ atTop φ) (hmono : Monotone φ)
    {f : α → ℝ≥0∞} (hfm : AeMeasurable f μ) : Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) atTop (𝓝 <| ∫⁻ x, f x ∂μ) :=
  let F := fun n => (φ n).indicator f
  have key₁ : ∀ n, AeMeasurable (F n) μ := fun n => hfm.indicator (hφ.Measurable n)
  have key₂ : ∀ᵐ x : α ∂μ, Monotone fun n => F n x :=
    ae_of_all _ fun x i j hij => indicator_le_indicator_of_subset (hmono hij) (fun x => zero_le <| f x) x
  have key₃ : ∀ᵐ x : α ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := hφ.ae_tendsto_indicator f
  (lintegral_tendsto_of_tendsto_of_monotone key₁ key₂ key₃).congr fun n => lintegral_indicator f (hφ.Measurable n)

theorem AeCover.lintegral_tendsto_of_nat {φ : ℕ → Set α} (hφ : AeCover μ atTop φ) {f : α → ℝ≥0∞}
    (hfm : AeMeasurable f μ) : Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) atTop (𝓝 <| ∫⁻ x, f x ∂μ) := by
  have lim₁ :=
    lintegral_tendsto_of_monotone_of_nat hφ.bInter_Ici_ae_cover
      (fun i j hij => bInter_subset_bInter_left (Ici_subset_Ici.mpr hij)) hfm
  have lim₂ :=
    lintegral_tendsto_of_monotone_of_nat hφ.bUnion_Iic_ae_cover
      (fun i j hij => bUnion_subset_bUnion_left (Iic_subset_Iic.mpr hij)) hfm
  have le₁ := fun n => lintegral_mono_set (bInter_subset_of_mem left_mem_Ici)
  have le₂ := fun n => lintegral_mono_set (subset_bUnion_of_mem right_mem_Iic)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le lim₁ lim₂ le₁ le₂

theorem AeCover.lintegral_tendsto_of_countably_generated [l.IsCountablyGenerated] {φ : ι → Set α} (hφ : AeCover μ l φ)
    {f : α → ℝ≥0∞} (hfm : AeMeasurable f μ) : Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) l (𝓝 <| ∫⁻ x, f x ∂μ) :=
  tendsto_of_seq_tendsto fun u hu => (hφ.comp_tendsto hu).lintegral_tendsto_of_nat hfm

theorem AeCover.lintegral_eq_of_tendsto [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α} (hφ : AeCover μ l φ)
    {f : α → ℝ≥0∞} (I : ℝ≥0∞) (hfm : AeMeasurable f μ) (htendsto : Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) l (𝓝 I)) :
    (∫⁻ x, f x ∂μ) = I :=
  tendsto_nhds_unique (hφ.lintegral_tendsto_of_countably_generated hfm) htendsto

theorem AeCover.supr_lintegral_eq_of_countably_generated [Nonempty ι] [l.ne_bot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AeCover μ l φ) {f : α → ℝ≥0∞} (hfm : AeMeasurable f μ) :
    (⨆ i : ι, ∫⁻ x in φ i, f x ∂μ) = ∫⁻ x, f x ∂μ := by
  have := hφ.lintegral_tendsto_of_countably_generated hfm
  refine'
    csupr_eq_of_forall_le_of_forall_lt_exists_gt (fun i => lintegral_mono' measure.restrict_le_self le_rfl) fun w hw =>
      _
  rcases exists_between hw with ⟨m, hm₁, hm₂⟩
  rcases(eventually_ge_of_tendsto_gt hm₂ this).exists with ⟨i, hi⟩
  exact ⟨i, lt_of_lt_of_leₓ hm₁ hi⟩

end Lintegral

section Integrable

variable {α ι E : Type _} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [NormedGroup E]

theorem AeCover.integrable_of_lintegral_nnnorm_bounded [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AeCover μ l φ) {f : α → E} (I : ℝ) (hfm : AeStronglyMeasurable f μ)
    (hbounded : ∀ᶠ i in l, (∫⁻ x in φ i, ∥f x∥₊ ∂μ) ≤ Ennreal.ofReal I) : Integrable f μ := by
  refine' ⟨hfm, (le_of_tendsto _ hbounded).trans_lt Ennreal.of_real_lt_top⟩
  exact hφ.lintegral_tendsto_of_countably_generated hfm.ennnorm

theorem AeCover.integrable_of_lintegral_nnnorm_tendsto [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AeCover μ l φ) {f : α → E} (I : ℝ) (hfm : AeStronglyMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, ∥f x∥₊ ∂μ) l (𝓝 <| Ennreal.ofReal I)) : Integrable f μ := by
  refine' hφ.integrable_of_lintegral_nnnorm_bounded (max 1 (I + 1)) hfm _
  refine' htendsto.eventually (ge_mem_nhds _)
  refine' (Ennreal.of_real_lt_of_real_iff (lt_max_of_lt_left zero_lt_one)).2 _
  exact lt_max_of_lt_right (lt_add_one I)

theorem AeCover.integrable_of_lintegral_nnnorm_bounded' [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AeCover μ l φ) {f : α → E} (I : ℝ≥0 ) (hfm : AeStronglyMeasurable f μ)
    (hbounded : ∀ᶠ i in l, (∫⁻ x in φ i, ∥f x∥₊ ∂μ) ≤ I) : Integrable f μ :=
  hφ.integrable_of_lintegral_nnnorm_bounded I hfm
    (by
      simpa only [← Ennreal.of_real_coe_nnreal] using hbounded)

theorem AeCover.integrable_of_lintegral_nnnorm_tendsto' [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AeCover μ l φ) {f : α → E} (I : ℝ≥0 ) (hfm : AeStronglyMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, ∥f x∥₊ ∂μ) l (𝓝 I)) : Integrable f μ :=
  hφ.integrable_of_lintegral_nnnorm_tendsto I hfm
    (by
      simpa only [← Ennreal.of_real_coe_nnreal] using htendsto)

theorem AeCover.integrable_of_integral_norm_bounded [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AeCover μ l φ) {f : α → E} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (hbounded : ∀ᶠ i in l, (∫ x in φ i, ∥f x∥ ∂μ) ≤ I) : Integrable f μ := by
  have hfm : ae_strongly_measurable f μ := hφ.ae_strongly_measurable fun i => (hfi i).AeStronglyMeasurable
  refine' hφ.integrable_of_lintegral_nnnorm_bounded I hfm _
  conv at hbounded in integral _ _ =>
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => @norm_nonneg E _ (f x)) hfm.norm.restrict]
  conv at hbounded in Ennreal.ofReal _ => dsimp rw [← coe_nnnorm]rw [Ennreal.of_real_coe_nnreal]
  refine' hbounded.mono fun i hi => _
  rw [← Ennreal.of_real_to_real (ne_top_of_lt (hfi i).2)]
  apply Ennreal.of_real_le_of_real hi

theorem AeCover.integrable_of_integral_norm_tendsto [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AeCover μ l φ) {f : α → E} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (htendsto : Tendsto (fun i => ∫ x in φ i, ∥f x∥ ∂μ) l (𝓝 I)) : Integrable f μ :=
  let ⟨I', hI'⟩ := htendsto.is_bounded_under_le
  hφ.integrable_of_integral_norm_bounded I' hfi hI'

theorem AeCover.integrable_of_integral_bounded_of_nonneg_ae [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AeCover μ l φ) {f : α → ℝ} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ) (hnng : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hbounded : ∀ᶠ i in l, (∫ x in φ i, f x ∂μ) ≤ I) : Integrable f μ :=
  hφ.integrable_of_integral_norm_bounded I hfi <|
    hbounded.mono fun i hi =>
      (integral_congr_ae <| ae_restrict_of_ae <| hnng.mono fun x => Real.norm_of_nonneg).le.trans hi

theorem AeCover.integrable_of_integral_tendsto_of_nonneg_ae [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AeCover μ l φ) {f : α → ℝ} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ) (hnng : ∀ᵐ x ∂μ, 0 ≤ f x)
    (htendsto : Tendsto (fun i => ∫ x in φ i, f x ∂μ) l (𝓝 I)) : Integrable f μ :=
  let ⟨I', hI'⟩ := htendsto.is_bounded_under_le
  hφ.integrable_of_integral_bounded_of_nonneg_ae I' hfi hnng hI'

end Integrable

section Integral

variable {α ι E : Type _} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [NormedGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

theorem AeCover.integral_tendsto_of_countably_generated [l.IsCountablyGenerated] {φ : ι → Set α} (hφ : AeCover μ l φ)
    {f : α → E} (hfi : Integrable f μ) : Tendsto (fun i => ∫ x in φ i, f x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) :=
  suffices h : Tendsto (fun i => ∫ x : α, (φ i).indicator f x ∂μ) l (𝓝 (∫ x : α, f x ∂μ)) from by
    convert h
    ext n
    rw [integral_indicator (hφ.measurable n)]
  tendsto_integral_filter_of_dominated_convergence (fun x => ∥f x∥)
    (eventually_of_forall fun i => hfi.AeStronglyMeasurable.indicator <| hφ.Measurable i)
    (eventually_of_forall fun i => (ae_of_all _) fun x => norm_indicator_le_norm_self _ _) hfi.norm
    (hφ.ae_tendsto_indicator f)

/-- Slight reformulation of
    `measure_theory.ae_cover.integral_tendsto_of_countably_generated`. -/
theorem AeCover.integral_eq_of_tendsto [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α} (hφ : AeCover μ l φ)
    {f : α → E} (I : E) (hfi : Integrable f μ) (h : Tendsto (fun n => ∫ x in φ n, f x ∂μ) l (𝓝 I)) :
    (∫ x, f x ∂μ) = I :=
  tendsto_nhds_unique (hφ.integral_tendsto_of_countably_generated hfi) h

theorem AeCover.integral_eq_of_tendsto_of_nonneg_ae [l.ne_bot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AeCover μ l φ) {f : α → ℝ} (I : ℝ) (hnng : 0 ≤ᵐ[μ] f) (hfi : ∀ n, IntegrableOn f (φ n) μ)
    (htendsto : Tendsto (fun n => ∫ x in φ n, f x ∂μ) l (𝓝 I)) : (∫ x, f x ∂μ) = I :=
  have hfi' : Integrable f μ := hφ.integrable_of_integral_tendsto_of_nonneg_ae I hfi hnng htendsto
  hφ.integral_eq_of_tendsto I hfi' htendsto

end Integral

section IntegrableOfIntervalIntegral

variable {ι E : Type _} {μ : Measure ℝ} {l : Filter ι} [Filter.NeBot l] [IsCountablyGenerated l] [NormedGroup E]
  {a b : ι → ℝ} {f : ℝ → E}

theorem integrable_of_interval_integral_norm_bounded (I : ℝ) (hfi : ∀ i, IntegrableOn f (Ioc (a i) (b i)) μ)
    (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) (h : ∀ᶠ i in l, (∫ x in a i..b i, ∥f x∥ ∂μ) ≤ I) :
    Integrable f μ := by
  have hφ : ae_cover μ l _ := ae_cover_Ioc ha hb
  refine' hφ.integrable_of_integral_norm_bounded I hfi (h.mp _)
  filter_upwards [ha.eventually (eventually_le_at_bot 0), hb.eventually (eventually_ge_at_top 0)] with i hai hbi ht
  rwa [← intervalIntegral.integral_of_le (hai.trans hbi)]

theorem integrable_of_interval_integral_norm_tendsto (I : ℝ) (hfi : ∀ i, IntegrableOn f (Ioc (a i) (b i)) μ)
    (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) (h : Tendsto (fun i => ∫ x in a i..b i, ∥f x∥ ∂μ) l (𝓝 I)) :
    Integrable f μ :=
  let ⟨I', hI'⟩ := h.is_bounded_under_le
  integrable_of_interval_integral_norm_bounded I' hfi ha hb hI'

theorem integrable_on_Iic_of_interval_integral_norm_bounded (I b : ℝ) (hfi : ∀ i, IntegrableOn f (Ioc (a i) b) μ)
    (ha : Tendsto a l atBot) (h : ∀ᶠ i in l, (∫ x in a i..b, ∥f x∥ ∂μ) ≤ I) : IntegrableOn f (Iic b) μ := by
  have hφ : ae_cover (μ.restrict <| Iic b) l _ := ae_cover_Ioi ha
  have hfi : ∀ i, integrable_on f (Ioi (a i)) (μ.restrict <| Iic b) := by
    intro i
    rw [integrable_on, measure.restrict_restrict (hφ.measurable i)]
    exact hfi i
  refine' hφ.integrable_of_integral_norm_bounded I hfi (h.mp _)
  filter_upwards [ha.eventually (eventually_le_at_bot b)] with i hai
  rw [intervalIntegral.integral_of_le hai, measure.restrict_restrict (hφ.measurable i)]
  exact id

theorem integrable_on_Iic_of_interval_integral_norm_tendsto (I b : ℝ) (hfi : ∀ i, IntegrableOn f (Ioc (a i) b) μ)
    (ha : Tendsto a l atBot) (h : Tendsto (fun i => ∫ x in a i..b, ∥f x∥ ∂μ) l (𝓝 I)) : IntegrableOn f (Iic b) μ :=
  let ⟨I', hI'⟩ := h.is_bounded_under_le
  integrable_on_Iic_of_interval_integral_norm_bounded I' b hfi ha hI'

theorem integrable_on_Ioi_of_interval_integral_norm_bounded (I a : ℝ) (hfi : ∀ i, IntegrableOn f (Ioc a (b i)) μ)
    (hb : Tendsto b l atTop) (h : ∀ᶠ i in l, (∫ x in a..b i, ∥f x∥ ∂μ) ≤ I) : IntegrableOn f (Ioi a) μ := by
  have hφ : ae_cover (μ.restrict <| Ioi a) l _ := ae_cover_Iic hb
  have hfi : ∀ i, integrable_on f (Iic (b i)) (μ.restrict <| Ioi a) := by
    intro i
    rw [integrable_on, measure.restrict_restrict (hφ.measurable i), inter_comm]
    exact hfi i
  refine' hφ.integrable_of_integral_norm_bounded I hfi (h.mp _)
  filter_upwards [hb.eventually (eventually_ge_at_top a)] with i hbi
  rw [intervalIntegral.integral_of_le hbi, measure.restrict_restrict (hφ.measurable i), inter_comm]
  exact id

theorem integrable_on_Ioi_of_interval_integral_norm_tendsto (I a : ℝ) (hfi : ∀ i, IntegrableOn f (Ioc a (b i)) μ)
    (hb : Tendsto b l atTop) (h : Tendsto (fun i => ∫ x in a..b i, ∥f x∥ ∂μ) l (𝓝 <| I)) : IntegrableOn f (Ioi a) μ :=
  let ⟨I', hI'⟩ := h.is_bounded_under_le
  integrable_on_Ioi_of_interval_integral_norm_bounded I' a hfi hb hI'

theorem integrable_on_Ioc_of_interval_integral_norm_bounded {I a₀ b₀ : ℝ} (hfi : ∀ i, IntegrableOn f <| Ioc (a i) (b i))
    (ha : Tendsto a l <| 𝓝 a₀) (hb : Tendsto b l <| 𝓝 b₀) (h : ∀ᶠ i in l, (∫ x in Ioc (a i) (b i), ∥f x∥) ≤ I) :
    IntegrableOn f (Ioc a₀ b₀) := by
  refine'
    (ae_cover_Ioc_of_Ioc ha hb).integrable_of_integral_norm_bounded I (fun i => (hfi i).restrict measurable_set_Ioc)
      (eventually.mono h _)
  intro i hi
  simp only [← measure.restrict_restrict measurable_set_Ioc]
  refine' le_transₓ (set_integral_mono_set (hfi i).norm _ _) hi
  · apply ae_of_all
    simp only [← Pi.zero_apply, ← norm_nonneg, ← forall_const]
    
  · apply ae_of_all
    intro c hc
    exact hc.1
    

theorem integrable_on_Ioc_of_interval_integral_norm_bounded_left {I a₀ b : ℝ} (hfi : ∀ i, IntegrableOn f <| Ioc (a i) b)
    (ha : Tendsto a l <| 𝓝 a₀) (h : ∀ᶠ i in l, (∫ x in Ioc (a i) b, ∥f x∥) ≤ I) : IntegrableOn f (Ioc a₀ b) :=
  integrable_on_Ioc_of_interval_integral_norm_bounded hfi ha tendsto_const_nhds h

theorem integrable_on_Ioc_of_interval_integral_norm_bounded_right {I a b₀ : ℝ}
    (hfi : ∀ i, IntegrableOn f <| Ioc a (b i)) (hb : Tendsto b l <| 𝓝 b₀)
    (h : ∀ᶠ i in l, (∫ x in Ioc a (b i), ∥f x∥) ≤ I) : IntegrableOn f (Ioc a b₀) :=
  integrable_on_Ioc_of_interval_integral_norm_bounded hfi tendsto_const_nhds hb h

end IntegrableOfIntervalIntegral

section IntegralOfIntervalIntegral

variable {ι E : Type _} {μ : Measure ℝ} {l : Filter ι} [IsCountablyGenerated l] [NormedGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {a b : ι → ℝ} {f : ℝ → E}

theorem interval_integral_tendsto_integral (hfi : Integrable f μ) (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∫ x in a i..b i, f x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) := by
  let φ := fun i => Ioc (a i) (b i)
  have hφ : ae_cover μ l φ := ae_cover_Ioc ha hb
  refine' (hφ.integral_tendsto_of_countably_generated hfi).congr' _
  filter_upwards [ha.eventually (eventually_le_at_bot 0), hb.eventually (eventually_ge_at_top 0)] with i hai hbi
  exact (intervalIntegral.integral_of_le (hai.trans hbi)).symm

theorem interval_integral_tendsto_integral_Iic (b : ℝ) (hfi : IntegrableOn f (Iic b) μ) (ha : Tendsto a l atBot) :
    Tendsto (fun i => ∫ x in a i..b, f x ∂μ) l (𝓝 <| ∫ x in Iic b, f x ∂μ) := by
  let φ := fun i => Ioi (a i)
  have hφ : ae_cover (μ.restrict <| Iic b) l φ := ae_cover_Ioi ha
  refine' (hφ.integral_tendsto_of_countably_generated hfi).congr' _
  filter_upwards [ha.eventually (eventually_le_at_bot <| b)] with i hai
  rw [intervalIntegral.integral_of_le hai, measure.restrict_restrict (hφ.measurable i)]
  rfl

theorem interval_integral_tendsto_integral_Ioi (a : ℝ) (hfi : IntegrableOn f (Ioi a) μ) (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∫ x in a..b i, f x ∂μ) l (𝓝 <| ∫ x in Ioi a, f x ∂μ) := by
  let φ := fun i => Iic (b i)
  have hφ : ae_cover (μ.restrict <| Ioi a) l φ := ae_cover_Iic hb
  refine' (hφ.integral_tendsto_of_countably_generated hfi).congr' _
  filter_upwards [hb.eventually (eventually_ge_at_top <| a)] with i hbi
  rw [intervalIntegral.integral_of_le hbi, measure.restrict_restrict (hφ.measurable i), inter_comm]
  rfl

end IntegralOfIntervalIntegral

end MeasureTheory

