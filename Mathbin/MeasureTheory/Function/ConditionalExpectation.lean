/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.MeasureTheory.Function.L2Space
import Mathbin.MeasureTheory.Decomposition.RadonNikodym
import Mathbin.MeasureTheory.Function.UniformIntegrable

/-! # Conditional expectation

We build the conditional expectation of an integrable function `f` with value in a Banach space
with respect to a measure `μ` (defined on a measurable space structure `m0`) and a measurable space
structure `m` with `hm : m ≤ m0` (a sub-sigma-algebra). This is an `m`-strongly measurable
function `μ[f|hm]` which is integrable and verifies `∫ x in s, μ[f|hm] x ∂μ = ∫ x in s, f x ∂μ`
for all `m`-measurable sets `s`. It is unique as an element of `L¹`.

The construction is done in four steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condexp_L1_clm : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `measure_theory/integral/set_to_L1`).
* Define the conditional expectation of a function `f : α → E`, which is an integrable function
  `α → E` equal to 0 if `f` is not integrable, and equal to an `m`-measurable representative of
  `condexp_L1_clm` applied to `[f]`, the equivalence class of `f` in `L¹`.

## Main results

The conditional expectation and its properties

* `condexp (m : measurable_space α) (μ : measure α) (f : α → E)`: conditional expectation of `f`
  with respect to `m`.
* `integrable_condexp` : `condexp` is integrable.
* `strongly_measurable_condexp` : `condexp` is `m`-strongly-measurable.
* `set_integral_condexp (hf : integrable f μ) (hs : measurable_set[m] s)` : if `m ≤ m0` (the
  σ-algebra over which the measure is defined), then the conditional expectation verifies
  `∫ x in s, condexp m μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable set `s`.

While `condexp` is function-valued, we also define `condexp_L1` with value in `L1` and a continuous
linear map `condexp_L1_clm` from `L1` to `L1`. `condexp` should be used in most cases.

Uniqueness of the conditional expectation

* `Lp.ae_eq_of_forall_set_integral_eq'`: two `Lp` functions verifying the equality of integrals
  defining the conditional expectation are equal.
* `ae_eq_of_forall_set_integral_eq_of_sigma_finite'`: two functions verifying the equality of
  integrals defining the conditional expectation are equal almost everywhere.
  Requires `[sigma_finite (μ.trim hm)]`.
* `ae_eq_condexp_of_forall_set_integral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condexp`.

## Notations

For a measure `μ` defined on a measurable space structure `m0`, another measurable space structure
`m` with `hm : m ≤ m0` (a sub-σ-algebra) and a function `f`, we define the notation
* `μ[f|m] = condexp m μ f`.

## Implementation notes

Most of the results in this file are valid for a complete real normed space `F`.
However, some lemmas also use `𝕜 : is_R_or_C`:
* `condexp_L2` is defined only for an `inner_product_space` for now, and we use `𝕜` for its field.
* results about scalar multiplication are stated not only for `ℝ` but also for `𝕜` if we happen to
  have `normed_space 𝕜 F`.

TODO: split this file in two with one containing constructions and the other with basic
properties.

## Tags

conditional expectation, conditional expected value

-/


noncomputable section

open TopologicalSpace MeasureTheory.lp Filter ContinuousLinearMap

open Nnreal Ennreal TopologicalSpace BigOperators MeasureTheory

namespace MeasureTheory

/-- A function `f` verifies `ae_strongly_measurable' m f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `ae_strongly_measurable`, but the
`measurable_space` structures used for the measurability statement and for the measure are
different. -/
def AeStronglyMeasurable' {α β} [TopologicalSpace β] (m : MeasurableSpace α) {m0 : MeasurableSpace α} (f : α → β)
    (μ : Measure α) : Prop :=
  ∃ g : α → β, strongly_measurable[m] g ∧ f =ᵐ[μ] g

namespace AeStronglyMeasurable'

variable {α β 𝕜 : Type _} {m m0 : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] {f g : α → β}

theorem congr (hf : AeStronglyMeasurable' m f μ) (hfg : f =ᵐ[μ] g) : AeStronglyMeasurable' m g μ := by
  obtain ⟨f', hf'_meas, hff'⟩ := hf
  exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩

theorem add [Add β] [HasContinuousAdd β] (hf : AeStronglyMeasurable' m f μ) (hg : AeStronglyMeasurable' m g μ) :
    AeStronglyMeasurable' m (f + g) μ := by
  rcases hf with ⟨f', h_f'_meas, hff'⟩
  rcases hg with ⟨g', h_g'_meas, hgg'⟩
  exact ⟨f' + g', h_f'_meas.add h_g'_meas, hff'.add hgg'⟩

theorem neg [AddGroupₓ β] [TopologicalAddGroup β] {f : α → β} (hfm : AeStronglyMeasurable' m f μ) :
    AeStronglyMeasurable' m (-f) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  refine' ⟨-f', hf'_meas.neg, hf_ae.mono fun x hx => _⟩
  simp_rw [Pi.neg_apply]
  rw [hx]

theorem sub [AddGroupₓ β] [TopologicalAddGroup β] {f g : α → β} (hfm : AeStronglyMeasurable' m f μ)
    (hgm : AeStronglyMeasurable' m g μ) : AeStronglyMeasurable' m (f - g) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  rcases hgm with ⟨g', hg'_meas, hg_ae⟩
  refine' ⟨f' - g', hf'_meas.sub hg'_meas, hf_ae.mp (hg_ae.mono fun x hx1 hx2 => _)⟩
  simp_rw [Pi.sub_apply]
  rw [hx1, hx2]

theorem const_smul [HasSmul 𝕜 β] [HasContinuousConstSmul 𝕜 β] (c : 𝕜) (hf : AeStronglyMeasurable' m f μ) :
    AeStronglyMeasurable' m (c • f) μ := by
  rcases hf with ⟨f', h_f'_meas, hff'⟩
  refine' ⟨c • f', h_f'_meas.const_smul c, _⟩
  exact eventually_eq.fun_comp hff' fun x => c • x

theorem const_inner {𝕜 β} [IsROrC 𝕜] [InnerProductSpace 𝕜 β] {f : α → β} (hfm : AeStronglyMeasurable' m f μ) (c : β) :
    AeStronglyMeasurable' m (fun x => (inner c (f x) : 𝕜)) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  refine'
    ⟨fun x => (inner c (f' x) : 𝕜), (@strongly_measurable_const _ _ m _ _).inner hf'_meas, hf_ae.mono fun x hx => _⟩
  dsimp' only
  rw [hx]

/-- An `m`-strongly measurable function almost everywhere equal to `f`. -/
def mk (f : α → β) (hfm : AeStronglyMeasurable' m f μ) : α → β :=
  hfm.some

theorem strongly_measurable_mk {f : α → β} (hfm : AeStronglyMeasurable' m f μ) : strongly_measurable[m] (hfm.mk f) :=
  hfm.some_spec.1

theorem ae_eq_mk {f : α → β} (hfm : AeStronglyMeasurable' m f μ) : f =ᵐ[μ] hfm.mk f :=
  hfm.some_spec.2

theorem continuous_comp {γ} [TopologicalSpace γ] {f : α → β} {g : β → γ} (hg : Continuous g)
    (hf : AeStronglyMeasurable' m f μ) : AeStronglyMeasurable' m (g ∘ f) μ :=
  ⟨fun x => g (hf.mk _ x), @Continuous.comp_strongly_measurable _ _ _ m _ _ _ _ hg hf.strongly_measurable_mk,
    hf.ae_eq_mk.mono fun x hx => by
      rw [Function.comp_applyₓ, hx]⟩

end AeStronglyMeasurable'

theorem ae_strongly_measurable'_of_ae_strongly_measurable'_trim {α β} {m m0 m0' : MeasurableSpace α}
    [TopologicalSpace β] (hm0 : m0 ≤ m0') {μ : Measure α} {f : α → β} (hf : AeStronglyMeasurable' m f (μ.trim hm0)) :
    AeStronglyMeasurable' m f μ := by
  obtain ⟨g, hg_meas, hfg⟩ := hf
  exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩

theorem StronglyMeasurable.ae_strongly_measurable' {α β} {m m0 : MeasurableSpace α} [TopologicalSpace β] {μ : Measure α}
    {f : α → β} (hf : strongly_measurable[m] f) : AeStronglyMeasurable' m f μ :=
  ⟨f, hf, ae_eq_refl _⟩

theorem ae_eq_trim_iff_of_ae_strongly_measurable' {α β} [TopologicalSpace β] [MetrizableSpace β]
    {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β} (hm : m ≤ m0) (hfm : AeStronglyMeasurable' m f μ)
    (hgm : AeStronglyMeasurable' m g μ) : hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
  (ae_eq_trim_iff hm hfm.strongly_measurable_mk hgm.strongly_measurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h => hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` almost
everywhere supported on `s` is `m`-ae-strongly-measurable, then `f` is also
`m₂`-ae-strongly-measurable. -/
theorem AeStronglyMeasurable'.ae_strongly_measurable'_of_measurable_space_le_on {α E} {m m₂ m0 : MeasurableSpace α}
    {μ : Measure α} [TopologicalSpace E] [Zero E] (hm : m ≤ m0) {s : Set α} {f : α → E} (hs_m : measurable_set[m] s)
    (hs : ∀ t, measurable_set[m] (s ∩ t) → measurable_set[m₂] (s ∩ t)) (hf : AeStronglyMeasurable' m f μ)
    (hf_zero : f =ᵐ[μ.restrict (sᶜ)] 0) : AeStronglyMeasurable' m₂ f μ := by
  let f' := hf.mk f
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f := by
    refine' Filter.EventuallyEq.trans _ (indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero)
    filter_upwards [hf.ae_eq_mk] with x hx
    by_cases' hxs : x ∈ s
    · simp [← hxs, ← hx]
      
    · simp [← hxs]
      
  suffices : strongly_measurable[m₂] (s.indicator (hf.mk f))
  exact ae_strongly_measurable'.congr this.ae_strongly_measurable' h_ind_eq
  have hf_ind : strongly_measurable[m] (s.indicator (hf.mk f)) := hf.strongly_measurable_mk.indicator hs_m
  exact hf_ind.strongly_measurable_of_measurable_space_le_on hs_m hs fun x hxs => Set.indicator_of_not_mem hxs _

variable {α β γ E E' F F' G G' H 𝕜 : Type _} {p : ℝ≥0∞} [IsROrC 𝕜]
  -- 𝕜 for ℝ or ℂ
  [TopologicalSpace β]
  -- β for a generic topological space
  -- E for an inner product space
  [InnerProductSpace 𝕜 E]
  -- E' for an inner product space on which we compute integrals
  [InnerProductSpace 𝕜 E']
  [CompleteSpace E'] [NormedSpace ℝ E']
  -- F for a Lp submodule
  [NormedGroup F]
  [NormedSpace 𝕜 F]
  -- F' for integrals on a Lp submodule
  [NormedGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']
  -- G for a Lp add_subgroup
  [NormedGroup G]
  -- G' for integrals on a Lp add_subgroup
  [NormedGroup G']
  [NormedSpace ℝ G'] [CompleteSpace G']
  -- H for a normed group (hypotheses of mem_ℒp)
  [NormedGroup H]

section LpMeas

/-! ## The subset `Lp_meas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/


variable (F)

/-- `Lp_meas_subgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_strongly_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def lpMeasSubgroup (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) : AddSubgroup (lp F p μ) where
  Carrier := { f : lp F p μ | AeStronglyMeasurable' m f μ }
  zero_mem' := ⟨(0 : α → F), @strongly_measurable_zero _ _ m _ _, lp.coe_fn_zero _ _ _⟩
  add_mem' := fun f g hf hg => (hf.add hg).congr (lp.coe_fn_add f g).symm
  neg_mem' := fun f hf => AeStronglyMeasurable'.congr hf.neg (lp.coe_fn_neg f).symm

variable (𝕜)

/-- `Lp_meas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_strongly_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def lpMeas (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) : Submodule 𝕜 (lp F p μ) where
  Carrier := { f : lp F p μ | AeStronglyMeasurable' m f μ }
  zero_mem' := ⟨(0 : α → F), @strongly_measurable_zero _ _ m _ _, lp.coe_fn_zero _ _ _⟩
  add_mem' := fun f g hf hg => (hf.add hg).congr (lp.coe_fn_add f g).symm
  smul_mem' := fun c f hf => (hf.const_smul c).congr (lp.coe_fn_smul c f).symm

variable {F 𝕜}

variable ()

theorem mem_Lp_meas_subgroup_iff_ae_strongly_measurable' {m m0 : MeasurableSpace α} {μ : Measure α} {f : lp F p μ} :
    f ∈ lpMeasSubgroup F m p μ ↔ AeStronglyMeasurable' m f μ := by
  rw [← AddSubgroup.mem_carrier, Lp_meas_subgroup, Set.mem_set_of_eq]

theorem mem_Lp_meas_iff_ae_strongly_measurable' {m m0 : MeasurableSpace α} {μ : Measure α} {f : lp F p μ} :
    f ∈ lpMeas F 𝕜 m p μ ↔ AeStronglyMeasurable' m f μ := by
  rw [← SetLike.mem_coe, ← Submodule.mem_carrier, Lp_meas, Set.mem_set_of_eq]

theorem lpMeas.ae_strongly_measurable' {m m0 : MeasurableSpace α} {μ : Measure α} (f : lpMeas F 𝕜 m p μ) :
    AeStronglyMeasurable' m f μ :=
  mem_Lp_meas_iff_ae_strongly_measurable'.mp f.Mem

theorem mem_Lp_meas_self {m0 : MeasurableSpace α} (μ : Measure α) (f : lp F p μ) : f ∈ lpMeas F 𝕜 m0 p μ :=
  mem_Lp_meas_iff_ae_strongly_measurable'.mpr (lp.ae_strongly_measurable f)

theorem Lp_meas_subgroup_coe {m m0 : MeasurableSpace α} {μ : Measure α} {f : lpMeasSubgroup F m p μ} :
    ⇑f = (f : lp F p μ) :=
  coe_fn_coe_base f

theorem Lp_meas_coe {m m0 : MeasurableSpace α} {μ : Measure α} {f : lpMeas F 𝕜 m p μ} : ⇑f = (f : lp F p μ) :=
  coe_fn_coe_base f

theorem mem_Lp_meas_indicator_const_Lp {m m0 : MeasurableSpace α} (hm : m ≤ m0) {μ : Measure α} {s : Set α}
    (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) {c : F} : indicatorConstLp p (hm s hs) hμs c ∈ lpMeas F 𝕜 m p μ :=
  ⟨s.indicator fun x : α => c, (@strongly_measurable_const _ _ m _ _).indicator hs, indicator_const_Lp_coe_fn⟩

section CompleteSubspace

/-! ## The subspace `Lp_meas` is complete.

We define an `isometric` between `Lp_meas_subgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`Lp_meas_subgroup` (and `Lp_meas`). -/


variable {ι : Type _} {m m0 : MeasurableSpace α} {μ : Measure α}

/-- If `f` belongs to `Lp_meas_subgroup F m p μ`, then the measurable function it is almost
everywhere equal to (given by `ae_measurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
theorem mem_ℒp_trim_of_mem_Lp_meas_subgroup (hm : m ≤ m0) (f : lp F p μ) (hf_meas : f ∈ lpMeasSubgroup F m p μ) :
    Memℒp (mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp hf_meas).some p (μ.trim hm) := by
  have hf : ae_strongly_measurable' m f μ := mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp hf_meas
  let g := hf.some
  obtain ⟨hg, hfg⟩ := hf.some_spec
  change mem_ℒp g p (μ.trim hm)
  refine' ⟨hg.ae_strongly_measurable, _⟩
  have h_snorm_fg : snorm g p (μ.trim hm) = snorm f p μ := by
    rw [snorm_trim hm hg]
    exact snorm_congr_ae hfg.symm
  rw [h_snorm_fg]
  exact Lp.snorm_lt_top f

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subgroup
`Lp_meas_subgroup F m p μ`. -/
theorem mem_Lp_meas_subgroup_to_Lp_of_trim (hm : m ≤ m0) (f : lp F p (μ.trim hm)) :
    (mem_ℒp_of_mem_ℒp_trim hm (lp.mem_ℒp f)).toLp f ∈ lpMeasSubgroup F m p μ := by
  let hf_mem_ℒp := mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)
  rw [mem_Lp_meas_subgroup_iff_ae_strongly_measurable']
  refine' ae_strongly_measurable'.congr _ (mem_ℒp.coe_fn_to_Lp hf_mem_ℒp).symm
  refine' ae_strongly_measurable'_of_ae_strongly_measurable'_trim hm _
  exact Lp.ae_strongly_measurable f

variable (F p μ)

/-- Map from `Lp_meas_subgroup` to `Lp F p (μ.trim hm)`. -/
def lpMeasSubgroupToLpTrim (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) : lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp f.Mem).some
    (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm f f.Mem)

variable (𝕜)

/-- Map from `Lp_meas` to `Lp F p (μ.trim hm)`. -/
def lpMeasToLpTrim (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) : lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_Lp_meas_iff_ae_strongly_measurable'.mp f.Mem).some (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm f f.Mem)

variable {𝕜}

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas_subgroup`, inverse of
`Lp_meas_subgroup_to_Lp_trim`. -/
def lpTrimToLpMeasSubgroup (hm : m ≤ m0) (f : lp F p (μ.trim hm)) : lpMeasSubgroup F m p μ :=
  ⟨(mem_ℒp_of_mem_ℒp_trim hm (lp.mem_ℒp f)).toLp f, mem_Lp_meas_subgroup_to_Lp_of_trim hm f⟩

variable (𝕜)

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas`, inverse of `Lp_meas_to_Lp_trim`. -/
def lpTrimToLpMeas (hm : m ≤ m0) (f : lp F p (μ.trim hm)) : lpMeas F 𝕜 m p μ :=
  ⟨(mem_ℒp_of_mem_ℒp_trim hm (lp.mem_ℒp f)).toLp f, mem_Lp_meas_subgroup_to_Lp_of_trim hm f⟩

variable {F 𝕜 p μ}

theorem Lp_meas_subgroup_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (Memℒp.coe_fn_to_Lp (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm (↑f) f.Mem))).trans
    (mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp f.Mem).some_spec.2.symm

theorem Lp_trim_to_Lp_meas_subgroup_ae_eq (hm : m ≤ m0) (f : lp F p (μ.trim hm)) :
    lpTrimToLpMeasSubgroup F p μ hm f =ᵐ[μ] f :=
  Memℒp.coe_fn_to_Lp _

theorem Lp_meas_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) : lpMeasToLpTrim F 𝕜 p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (Memℒp.coe_fn_to_Lp (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm (↑f) f.Mem))).trans
    (mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp f.Mem).some_spec.2.symm

theorem Lp_trim_to_Lp_meas_ae_eq (hm : m ≤ m0) (f : lp F p (μ.trim hm)) : lpTrimToLpMeas F 𝕜 p μ hm f =ᵐ[μ] f :=
  Memℒp.coe_fn_to_Lp _

/-- `Lp_trim_to_Lp_meas_subgroup` is a right inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
theorem Lp_meas_subgroup_to_Lp_trim_right_inv (hm : m ≤ m0) :
    Function.RightInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  refine' ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) (Lp.strongly_measurable _) _
  exact (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans (Lp_trim_to_Lp_meas_subgroup_ae_eq hm _)

/-- `Lp_trim_to_Lp_meas_subgroup` is a left inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
theorem Lp_meas_subgroup_to_Lp_trim_left_inv (hm : m ≤ m0) :
    Function.LeftInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  ext1
  rw [← Lp_meas_subgroup_coe]
  exact (Lp_trim_to_Lp_meas_subgroup_ae_eq hm _).trans (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _)

theorem Lp_meas_subgroup_to_Lp_trim_add (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f + g) = lpMeasSubgroupToLpTrim F p μ hm f + lpMeasSubgroupToLpTrim F p μ hm g :=
  by
  ext1
  refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm
  refine' ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) _ _
  · exact (Lp.strongly_measurable _).add (Lp.strongly_measurable _)
    
  refine' (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans _
  refine'
    eventually_eq.trans _
      (eventually_eq.add (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm (Lp_meas_subgroup_to_Lp_trim_ae_eq hm g).symm)
  refine' (Lp.coe_fn_add _ _).trans _
  simp_rw [Lp_meas_subgroup_coe]
  exact
    eventually_of_forall fun x => by
      rfl

theorem Lp_meas_subgroup_to_Lp_trim_neg (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (-f) = -lpMeasSubgroupToLpTrim F p μ hm f := by
  ext1
  refine' eventually_eq.trans _ (Lp.coe_fn_neg _).symm
  refine' ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) _ _
  · exact @strongly_measurable.neg _ _ _ m _ _ _ (Lp.strongly_measurable _)
    
  refine' (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans _
  refine' eventually_eq.trans _ (eventually_eq.neg (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm)
  refine' (Lp.coe_fn_neg _).trans _
  simp_rw [Lp_meas_subgroup_coe]
  exact
    eventually_of_forall fun x => by
      rfl

theorem Lp_meas_subgroup_to_Lp_trim_sub (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f - g) = lpMeasSubgroupToLpTrim F p μ hm f - lpMeasSubgroupToLpTrim F p μ hm g :=
  by
  rw [sub_eq_add_neg, sub_eq_add_neg, Lp_meas_subgroup_to_Lp_trim_add, Lp_meas_subgroup_to_Lp_trim_neg]

theorem Lp_meas_to_Lp_trim_smul (hm : m ≤ m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm (c • f) = c • lpMeasToLpTrim F 𝕜 p μ hm f := by
  ext1
  refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm
  refine' ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) _ _
  · exact (Lp.strongly_measurable _).const_smul c
    
  refine' (Lp_meas_to_Lp_trim_ae_eq hm _).trans _
  refine' (Lp.coe_fn_smul _ _).trans _
  refine' (Lp_meas_to_Lp_trim_ae_eq hm f).mono fun x hx => _
  rw [Pi.smul_apply, Pi.smul_apply, hx]
  rfl

/-- `Lp_meas_subgroup_to_Lp_trim` preserves the norm. -/
theorem Lp_meas_subgroup_to_Lp_trim_norm_map [hp : Fact (1 ≤ p)] (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    ∥lpMeasSubgroupToLpTrim F p μ hm f∥ = ∥f∥ := by
  rw [Lp.norm_def, snorm_trim hm (Lp.strongly_measurable _), snorm_congr_ae (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _),
    Lp_meas_subgroup_coe, ← Lp.norm_def]
  congr

theorem isometry_Lp_meas_subgroup_to_Lp_trim [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
    Isometry (lpMeasSubgroupToLpTrim F p μ hm) := by
  rw [isometry_emetric_iff_metric]
  intro f g
  rw [dist_eq_norm, ← Lp_meas_subgroup_to_Lp_trim_sub, Lp_meas_subgroup_to_Lp_trim_norm_map, dist_eq_norm]

variable (F p μ)

/-- `Lp_meas_subgroup` and `Lp F p (μ.trim hm)` are isometric. -/
def lpMeasSubgroupToLpTrimIso [hp : Fact (1 ≤ p)] (hm : m ≤ m0) : lpMeasSubgroup F m p μ ≃ᵢ lp F p (μ.trim hm) where
  toFun := lpMeasSubgroupToLpTrim F p μ hm
  invFun := lpTrimToLpMeasSubgroup F p μ hm
  left_inv := Lp_meas_subgroup_to_Lp_trim_left_inv hm
  right_inv := Lp_meas_subgroup_to_Lp_trim_right_inv hm
  isometry_to_fun := isometry_Lp_meas_subgroup_to_Lp_trim hm

variable (𝕜)

/-- `Lp_meas_subgroup` and `Lp_meas` are isometric. -/
def lpMeasSubgroupToLpMeasIso [hp : Fact (1 ≤ p)] : lpMeasSubgroup F m p μ ≃ᵢ lpMeas F 𝕜 m p μ :=
  Isometric.refl (lpMeasSubgroup F m p μ)

/-- `Lp_meas` and `Lp F p (μ.trim hm)` are isometric, with a linear equivalence. -/
def lpMeasToLpTrimLie [hp : Fact (1 ≤ p)] (hm : m ≤ m0) : lpMeas F 𝕜 m p μ ≃ₗᵢ[𝕜] lp F p (μ.trim hm) where
  toFun := lpMeasToLpTrim F 𝕜 p μ hm
  invFun := lpTrimToLpMeas F 𝕜 p μ hm
  left_inv := Lp_meas_subgroup_to_Lp_trim_left_inv hm
  right_inv := Lp_meas_subgroup_to_Lp_trim_right_inv hm
  map_add' := Lp_meas_subgroup_to_Lp_trim_add hm
  map_smul' := Lp_meas_to_Lp_trim_smul hm
  norm_map' := Lp_meas_subgroup_to_Lp_trim_norm_map hm

variable {F 𝕜 p μ}

instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] : CompleteSpace (lpMeasSubgroup F m p μ) := by
  rw [(Lp_meas_subgroup_to_Lp_trim_iso F p μ hm.elim).complete_space_iff]
  infer_instance

instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] : CompleteSpace (lpMeas F 𝕜 m p μ) := by
  rw [(Lp_meas_subgroup_to_Lp_meas_iso F 𝕜 p μ).symm.complete_space_iff]
  infer_instance

theorem is_complete_ae_strongly_measurable' [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsComplete { f : lp F p μ | AeStronglyMeasurable' m f μ } := by
  rw [← complete_space_coe_iff_is_complete]
  have : Fact (m ≤ m0) := ⟨hm⟩
  change CompleteSpace (Lp_meas_subgroup F m p μ)
  infer_instance

theorem is_closed_ae_strongly_measurable' [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsClosed { f : lp F p μ | AeStronglyMeasurable' m f μ } :=
  IsComplete.is_closed (is_complete_ae_strongly_measurable' hm)

end CompleteSubspace

section StronglyMeasurable

variable {m m0 : MeasurableSpace α} {μ : Measure α}

/-- We do not get `ae_fin_strongly_measurable f (μ.trim hm)`, since we don't have
`f =ᵐ[μ.trim hm] Lp_meas_to_Lp_trim F 𝕜 p μ hm f` but only the weaker
`f =ᵐ[μ] Lp_meas_to_Lp_trim F 𝕜 p μ hm f`. -/
theorem lpMeas.ae_fin_strongly_measurable' (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : ∃ g, FinStronglyMeasurable g (μ.trim hm) ∧ f =ᵐ[μ] g :=
  ⟨lpMeasSubgroupToLpTrim F p μ hm f, lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top,
    (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm⟩

/-- When applying the inverse of `Lp_meas_to_Lp_trim_lie` (which takes a function in the Lp space of
the sub-sigma algebra and returns its version in the larger Lp space) to an indicator of the
sub-sigma-algebra, we obtain an indicator in the Lp space of the larger sigma-algebra. -/
theorem Lp_meas_to_Lp_trim_lie_symm_indicator [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] {hm : m ≤ m0} {s : Set α}
    {μ : Measure α} (hs : measurable_set[m] s) (hμs : μ.trim hm s ≠ ∞) (c : F) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (indicatorConstLp p hs hμs c) : lp F p μ) =
      indicatorConstLp p (hm s hs) ((le_trim hm).trans_lt hμs.lt_top).Ne c :=
  by
  ext1
  rw [← Lp_meas_coe]
  change Lp_trim_to_Lp_meas F ℝ p μ hm (indicator_const_Lp p hs hμs c) =ᵐ[μ] (indicator_const_Lp p _ _ c : α → F)
  refine' (Lp_trim_to_Lp_meas_ae_eq hm _).trans _
  exact (ae_eq_of_ae_eq_trim indicator_const_Lp_coe_fn).trans indicator_const_Lp_coe_fn.symm

theorem Lp_meas_to_Lp_trim_lie_symm_to_Lp [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] (hm : m ≤ m0) (f : α → F)
    (hf : Memℒp f p (μ.trim hm)) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (hf.toLp f) : lp F p μ) = (mem_ℒp_of_mem_ℒp_trim hm hf).toLp f := by
  ext1
  rw [← Lp_meas_coe]
  refine' (Lp_trim_to_Lp_meas_ae_eq hm _).trans _
  exact (ae_eq_of_ae_eq_trim (mem_ℒp.coe_fn_to_Lp hf)).trans (mem_ℒp.coe_fn_to_Lp _).symm

end StronglyMeasurable

end LpMeas

section Induction

variable {m m0 : MeasurableSpace α} {μ : Measure α} [Fact (1 ≤ p)] [NormedSpace ℝ F]

/-- Auxiliary lemma for `Lp.induction_strongly_measurable`. -/
@[elab_as_eliminator]
theorem lp.induction_strongly_measurable_aux (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : lp F p μ → Prop)
    (h_ind :
      ∀ (c : F) {s : Set α} (hs : measurable_set[m] s) (hμs : μ s < ∞),
        P (lp.simpleFunc.indicatorConst p (hm s hs) hμs.Ne c))
    (h_add :
      ∀ ⦃f g⦄,
        ∀ hf : Memℒp f p μ,
          ∀ hg : Memℒp g p μ,
            ∀ hfm : AeStronglyMeasurable' m f μ,
              ∀ hgm : AeStronglyMeasurable' m g μ,
                Disjoint (Function.Support f) (Function.Support g) →
                  P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed { f : lpMeas F ℝ m p μ | P f }) : ∀ f : lp F p μ, AeStronglyMeasurable' m f μ → P f := by
  intro f hf
  let f' := (⟨f, hf⟩ : Lp_meas F ℝ m p μ)
  let g := Lp_meas_to_Lp_trim_lie F ℝ p μ hm f'
  have hfg : f' = (Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm g := by
    simp only [← LinearIsometryEquiv.symm_apply_apply]
  change P ↑f'
  rw [hfg]
  refine'
    @Lp.induction α F m _ p (μ.trim hm) _ hp_ne_top (fun g => P ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm g)) _ _ _ g
  · intro b t ht hμt
    rw [Lp.simple_func.coe_indicator_const, Lp_meas_to_Lp_trim_lie_symm_indicator ht hμt.ne b]
    have hμt' : μ t < ∞ := (le_trim hm).trans_lt hμt
    specialize h_ind b ht hμt'
    rwa [Lp.simple_func.coe_indicator_const] at h_ind
    
  · intro f g hf hg h_disj hfP hgP
    rw [LinearIsometryEquiv.map_add]
    push_cast
    have h_eq :
      ∀ (f : α → F) (hf : mem_ℒp f p (μ.trim hm)),
        ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm (mem_ℒp.to_Lp f hf) : Lp F p μ) =
          (mem_ℒp_of_mem_ℒp_trim hm hf).toLp f :=
      Lp_meas_to_Lp_trim_lie_symm_to_Lp hm
    rw [h_eq f hf] at hfP⊢
    rw [h_eq g hg] at hgP⊢
    exact
      h_add (mem_ℒp_of_mem_ℒp_trim hm hf) (mem_ℒp_of_mem_ℒp_trim hm hg)
        (ae_strongly_measurable'_of_ae_strongly_measurable'_trim hm hf.ae_strongly_measurable)
        (ae_strongly_measurable'_of_ae_strongly_measurable'_trim hm hg.ae_strongly_measurable) h_disj hfP hgP
    
  · change IsClosed ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm ⁻¹' { g : Lp_meas F ℝ m p μ | P ↑g })
    exact IsClosed.preimage (LinearIsometryEquiv.continuous _) h_closed
    

/-- To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.
-/
@[elab_as_eliminator]
theorem lp.induction_strongly_measurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : lp F p μ → Prop)
    (h_ind :
      ∀ (c : F) {s : Set α} (hs : measurable_set[m] s) (hμs : μ s < ∞),
        P (lp.simpleFunc.indicatorConst p (hm s hs) hμs.Ne c))
    (h_add :
      ∀ ⦃f g⦄,
        ∀ hf : Memℒp f p μ,
          ∀ hg : Memℒp g p μ,
            ∀ hfm : strongly_measurable[m] f,
              ∀ hgm : strongly_measurable[m] g,
                Disjoint (Function.Support f) (Function.Support g) →
                  P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed { f : lpMeas F ℝ m p μ | P f }) : ∀ f : lp F p μ, AeStronglyMeasurable' m f μ → P f := by
  intro f hf
  suffices h_add_ae :
    ∀ ⦃f g⦄,
      ∀ hf : mem_ℒp f p μ,
        ∀ hg : mem_ℒp g p μ,
          ∀ hfm : ae_strongly_measurable' m f μ,
            ∀ hgm : ae_strongly_measurable' m g μ,
              Disjoint (Function.Support f) (Function.Support g) →
                P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g)
  exact Lp.induction_strongly_measurable_aux hm hp_ne_top P h_ind h_add_ae h_closed f hf
  intro f g hf hg hfm hgm h_disj hPf hPg
  let s_f : Set α := Function.Support (hfm.mk f)
  have hs_f : measurable_set[m] s_f := hfm.strongly_measurable_mk.measurable_set_support
  have hs_f_eq : s_f =ᵐ[μ] Function.Support f := hfm.ae_eq_mk.symm.support
  let s_g : Set α := Function.Support (hgm.mk g)
  have hs_g : measurable_set[m] s_g := hgm.strongly_measurable_mk.measurable_set_support
  have hs_g_eq : s_g =ᵐ[μ] Function.Support g := hgm.ae_eq_mk.symm.support
  have h_inter_empty : (s_f ∩ s_g : Set α) =ᵐ[μ] (∅ : Set α) := by
    refine' (hs_f_eq.inter hs_g_eq).trans _
    suffices Function.Support f ∩ Function.Support g = ∅ by
      rw [this]
    exact set.disjoint_iff_inter_eq_empty.mp h_disj
  let f' := (s_f \ s_g).indicator (hfm.mk f)
  have hff' : f =ᵐ[μ] f' := by
    have : s_f \ s_g =ᵐ[μ] s_f := by
      rw [← Set.diff_inter_self_eq_diff, Set.inter_comm]
      refine' ((ae_eq_refl s_f).diff h_inter_empty).trans _
      rw [Set.diff_empty]
    refine' ((indicator_ae_eq_of_ae_eq_set this).trans _).symm
    rw [Set.indicator_support]
    exact hfm.ae_eq_mk.symm
  have hf'_meas : strongly_measurable[m] f' := hfm.strongly_measurable_mk.indicator (hs_f.diff hs_g)
  have hf'_Lp : mem_ℒp f' p μ := hf.ae_eq hff'
  let g' := (s_g \ s_f).indicator (hgm.mk g)
  have hgg' : g =ᵐ[μ] g' := by
    have : s_g \ s_f =ᵐ[μ] s_g := by
      rw [← Set.diff_inter_self_eq_diff]
      refine' ((ae_eq_refl s_g).diff h_inter_empty).trans _
      rw [Set.diff_empty]
    refine' ((indicator_ae_eq_of_ae_eq_set this).trans _).symm
    rw [Set.indicator_support]
    exact hgm.ae_eq_mk.symm
  have hg'_meas : strongly_measurable[m] g' := hgm.strongly_measurable_mk.indicator (hs_g.diff hs_f)
  have hg'_Lp : mem_ℒp g' p μ := hg.ae_eq hgg'
  have h_disj : Disjoint (Function.Support f') (Function.Support g') := by
    have : Disjoint (s_f \ s_g) (s_g \ s_f) := disjoint_sdiff_sdiff
    exact this.mono Set.support_indicator_subset Set.support_indicator_subset
  rw [← mem_ℒp.to_Lp_congr hf'_Lp hf hff'.symm] at hPf⊢
  rw [← mem_ℒp.to_Lp_congr hg'_Lp hg hgg'.symm] at hPg⊢
  exact h_add hf'_Lp hg'_Lp hf'_meas hg'_meas h_disj hPf hPg

/-- To prove something for an arbitrary `mem_ℒp` function a.e. strongly measurable with respect
to a sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in the `Lᵖ` space strongly measurable w.r.t. `m` for which the property
  holds is closed.
* the property is closed under the almost-everywhere equal relation.
-/
@[elab_as_eliminator]
theorem Memℒp.induction_strongly_measurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : (α → F) → Prop)
    (h_ind : ∀ (c : F) ⦃s⦄, measurable_set[m] s → μ s < ∞ → P (s.indicator fun _ => c))
    (h_add :
      ∀ ⦃f g : α → F⦄,
        Disjoint (Function.Support f) (Function.Support g) →
          Memℒp f p μ → Memℒp g p μ → strongly_measurable[m] f → strongly_measurable[m] g → P f → P g → P (f + g))
    (h_closed : IsClosed { f : lpMeas F ℝ m p μ | P f }) (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → Memℒp f p μ → P f → P g) :
    ∀ ⦃f : α → F⦄ (hf : Memℒp f p μ) (hfm : AeStronglyMeasurable' m f μ), P f := by
  intro f hf hfm
  let f_Lp := hf.to_Lp f
  have hfm_Lp : ae_strongly_measurable' m f_Lp μ := hfm.congr hf.coe_fn_to_Lp.symm
  refine' h_ae hf.coe_fn_to_Lp (Lp.mem_ℒp _) _
  change P f_Lp
  refine' Lp.induction_strongly_measurable hm hp_ne_top (fun f => P ⇑f) _ _ h_closed f_Lp hfm_Lp
  · intro c s hs hμs
    rw [Lp.simple_func.coe_indicator_const]
    refine' h_ae indicator_const_Lp_coe_fn.symm _ (h_ind c hs hμs)
    exact mem_ℒp_indicator_const p (hm s hs) c (Or.inr hμs.ne)
    
  · intro f g hf_mem hg_mem hfm hgm h_disj hfP hgP
    have hfP' : P f := h_ae hf_mem.coe_fn_to_Lp (Lp.mem_ℒp _) hfP
    have hgP' : P g := h_ae hg_mem.coe_fn_to_Lp (Lp.mem_ℒp _) hgP
    specialize h_add h_disj hf_mem hg_mem hfm hgm hfP' hgP'
    refine' h_ae _ (hf_mem.add hg_mem) h_add
    exact (hf_mem.coe_fn_to_Lp.symm.add hg_mem.coe_fn_to_Lp.symm).trans (Lp.coe_fn_add _ _).symm
    

end Induction

section UniquenessOfConditionalExpectation

/-! ## Uniqueness of the conditional expectation -/


variable {m m0 : MeasurableSpace α} {μ : Measure α}

theorem lpMeas.ae_eq_zero_of_forall_set_integral_eq_zero (hm : m ≤ m0) (f : lpMeas E' 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0) : f =ᵐ[μ] 0 := by
  obtain ⟨g, hg_sm, hfg⟩ := Lp_meas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top
  refine' hfg.trans _
  refine' ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim hm _ _ hg_sm
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integrable_on, integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
    
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs
    

include 𝕜

theorem lp.ae_eq_zero_of_forall_set_integral_eq_zero' (hm : m ≤ m0) (f : lp E' p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0)
    (hf_meas : AeStronglyMeasurable' m f μ) : f =ᵐ[μ] 0 := by
  let f_meas : Lp_meas E' 𝕜 m p μ := ⟨f, hf_meas⟩
  have hf_f_meas : f =ᵐ[μ] f_meas := by
    simp only [← coe_fn_coe_base', ← Subtype.coe_mk]
  refine' hf_f_meas.trans _
  refine' Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero hm f_meas hp_ne_zero hp_ne_top _ _
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas := ae_restrict_of_ae hf_f_meas
    rw [integrable_on, integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
    
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas := ae_restrict_of_ae hf_f_meas
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs
    

/-- **Uniqueness of the conditional expectation** -/
theorem lp.ae_eq_of_forall_set_integral_eq' (hm : m ≤ m0) (f g : lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ)
    (hf_meas : AeStronglyMeasurable' m f μ) (hg_meas : AeStronglyMeasurable' m g μ) : f =ᵐ[μ] g := by
  suffices h_sub : ⇑(f - g) =ᵐ[μ] 0
  · rw [← sub_ae_eq_zero]
    exact (Lp.coe_fn_sub f g).symm.trans h_sub
    
  have hfg' : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coe_fn_sub f g))]
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg s hs hμs)
  have hfg_int : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on (⇑(f - g)) s μ := by
    intro s hs hμs
    rw [integrable_on, integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub f g))]
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  have hfg_meas : ae_strongly_measurable' m (⇑(f - g)) μ :=
    ae_strongly_measurable'.congr (hf_meas.sub hg_meas) (Lp.coe_fn_sub f g).symm
  exact Lp.ae_eq_zero_of_forall_set_integral_eq_zero' hm (f - g) hp_ne_zero hp_ne_top hfg_int hfg' hfg_meas

omit 𝕜

theorem ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] {f g : α → F'}
    (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ)
    (hfm : AeStronglyMeasurable' m f μ) (hgm : AeStronglyMeasurable' m g μ) : f =ᵐ[μ] g := by
  rw [← ae_eq_trim_iff_of_ae_strongly_measurable' hm hfm hgm]
  have hf_mk_int_finite :
    ∀ s, measurable_set[m] s → μ.trim hm s < ∞ → @integrable_on _ _ m _ (hfm.mk f) s (μ.trim hm) := by
    intro s hs hμs
    rw [trim_measurable_set_eq hm hs] at hμs
    rw [integrable_on, restrict_trim hm _ hs]
    refine' integrable.trim hm _ hfm.strongly_measurable_mk
    exact integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk)
  have hg_mk_int_finite :
    ∀ s, measurable_set[m] s → μ.trim hm s < ∞ → @integrable_on _ _ m _ (hgm.mk g) s (μ.trim hm) := by
    intro s hs hμs
    rw [trim_measurable_set_eq hm hs] at hμs
    rw [integrable_on, restrict_trim hm _ hs]
    refine' integrable.trim hm _ hgm.strongly_measurable_mk
    exact integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk)
  have hfg_mk_eq :
    ∀ s : Set α,
      measurable_set[m] s → μ.trim hm s < ∞ → (∫ x in s, hfm.mk f x ∂μ.trim hm) = ∫ x in s, hgm.mk g x ∂μ.trim hm :=
    by
    intro s hs hμs
    rw [trim_measurable_set_eq hm hs] at hμs
    rw [restrict_trim hm _ hs, ← integral_trim hm hfm.strongly_measurable_mk, ←
      integral_trim hm hgm.strongly_measurable_mk, integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm),
      integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)]
    exact hfg_eq s hs hμs
  exact ae_eq_of_forall_set_integral_eq_of_sigma_finite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq

end UniquenessOfConditionalExpectation

section IntegralNormLe

variable {m m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫ x in s, ∥g x∥ ∂μ ≤ ∫ x in s, ∥f x∥ ∂μ` on all `m`-measurable sets with finite measure. -/
theorem integral_norm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ} (hf : StronglyMeasurable f)
    (hfi : IntegrableOn f s μ) (hg : strongly_measurable[m] g) (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → (∫ x in t, g x ∂μ) = ∫ x in t, f x ∂μ) (hs : measurable_set[m] s)
    (hμs : μ s ≠ ∞) : (∫ x in s, ∥g x∥ ∂μ) ≤ ∫ x in s, ∥f x∥ ∂μ := by
  rw [integral_norm_eq_pos_sub_neg (hg.mono hm) hgi, integral_norm_eq_pos_sub_neg hf hfi]
  have h_meas_nonneg_g : measurable_set[m] { x | 0 ≤ g x } :=
    (@strongly_measurable_const _ _ m _ _).measurable_set_le hg
  have h_meas_nonneg_f : MeasurableSet { x | 0 ≤ f x } := strongly_measurable_const.measurable_set_le hf
  have h_meas_nonpos_g : measurable_set[m] { x | g x ≤ 0 } :=
    hg.measurable_set_le (@strongly_measurable_const _ _ m _ _)
  have h_meas_nonpos_f : MeasurableSet { x | f x ≤ 0 } := hf.measurable_set_le strongly_measurable_const
  refine' sub_le_sub _ _
  · rw [measure.restrict_restrict (hm _ h_meas_nonneg_g), measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono (Set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← measure.restrict_restrict (hm _ h_meas_nonneg_g), ← measure.restrict_restrict h_meas_nonneg_f]
    exact set_integral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi
    
  · rw [measure.restrict_restrict (hm _ h_meas_nonpos_g), measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono (Set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← measure.restrict_restrict (hm _ h_meas_nonpos_g), ← measure.restrict_restrict h_meas_nonpos_f]
    exact set_integral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi
    

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫⁻ x in s, ∥g x∥₊ ∂μ ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ` on all `m`-measurable sets with finite
measure. -/
theorem lintegral_nnnorm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ} (hf : StronglyMeasurable f)
    (hfi : IntegrableOn f s μ) (hg : strongly_measurable[m] g) (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → (∫ x in t, g x ∂μ) = ∫ x in t, f x ∂μ) (hs : measurable_set[m] s)
    (hμs : μ s ≠ ∞) : (∫⁻ x in s, ∥g x∥₊ ∂μ) ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ := by
  rw [← of_real_integral_norm_eq_lintegral_nnnorm hfi, ← of_real_integral_norm_eq_lintegral_nnnorm hgi,
    Ennreal.of_real_le_of_real_iff]
  · exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs
    
  · exact integral_nonneg fun x => norm_nonneg _
    

end IntegralNormLe

/-! ## Conditional expectation in L2

We define a conditional expectation in `L2`: it is the orthogonal projection on the subspace
`Lp_meas`. -/


section CondexpL2

variable [CompleteSpace E] {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

-- mathport name: «expr⟪ , ⟫₂»
local notation "⟪" x ", " y "⟫₂" => @inner 𝕜 (α →₂[μ] E) _ x y

variable (𝕜)

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexpL2 (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] lpMeas E 𝕜 m 2 μ :=
  @orthogonalProjection 𝕜 (α →₂[μ] E) _ _ (lpMeas E 𝕜 m 2 μ)
    (by
      have : Fact (m ≤ m0) := ⟨hm⟩
      exact inferInstance)

variable {𝕜}

theorem ae_strongly_measurable'_condexp_L2 (hm : m ≤ m0) (f : α →₂[μ] E) :
    AeStronglyMeasurable' m (condexpL2 𝕜 hm f) μ :=
  lpMeas.ae_strongly_measurable' _

theorem integrable_on_condexp_L2_of_measure_ne_top (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
    IntegrableOn (condexpL2 𝕜 hm f) s μ :=
  integrable_on_Lp_of_measure_ne_top (condexpL2 𝕜 hm f : α →₂[μ] E) fact_one_le_two_ennreal.elim hμs

theorem integrable_condexp_L2_of_is_finite_measure (hm : m ≤ m0) [IsFiniteMeasure μ] {f : α →₂[μ] E} :
    Integrable (condexpL2 𝕜 hm f) μ :=
  integrable_on_univ.mp <| integrable_on_condexp_L2_of_measure_ne_top hm (measure_ne_top _ _) f

theorem norm_condexp_L2_le_one (hm : m ≤ m0) : ∥@condexpL2 α E 𝕜 _ _ _ _ _ μ hm∥ ≤ 1 := by
  have : Fact (m ≤ m0) := ⟨hm⟩
  exact orthogonal_projection_norm_le _

theorem norm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ∥condexpL2 𝕜 hm f∥ ≤ ∥f∥ :=
  ((@condexpL2 _ E 𝕜 _ _ _ _ _ μ hm).le_op_norm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condexp_L2_le_one hm))

theorem snorm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) : snorm (condexpL2 𝕜 hm f) 2 μ ≤ snorm f 2 μ := by
  rw [Lp_meas_coe, ← Ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _), ← Lp.norm_def, ← Lp.norm_def,
    Submodule.norm_coe]
  exact norm_condexp_L2_le hm f

theorem norm_condexp_L2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) : ∥(condexpL2 𝕜 hm f : α →₂[μ] E)∥ ≤ ∥f∥ := by
  rw [Lp.norm_def, Lp.norm_def, ← Lp_meas_coe]
  refine' (Ennreal.to_real_le_to_real _ (Lp.snorm_ne_top _)).mpr (snorm_condexp_L2_le hm f)
  exact Lp.snorm_ne_top _

theorem inner_condexp_L2_left_eq_right (hm : m ≤ m0) {f g : α →₂[μ] E} :
    ⟪(condexpL2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, (condexpL2 𝕜 hm g : α →₂[μ] E)⟫₂ := by
  have : Fact (m ≤ m0) := ⟨hm⟩
  exact inner_orthogonal_projection_left_eq_right _ f g

theorem condexp_L2_indicator_of_measurable (hm : m ≤ m0) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (c : E) :
    (condexpL2 𝕜 hm (indicatorConstLp 2 (hm s hs) hμs c) : α →₂[μ] E) = indicatorConstLp 2 (hm s hs) hμs c := by
  rw [condexp_L2]
  have : Fact (m ≤ m0) := ⟨hm⟩
  have h_mem : indicator_const_Lp 2 (hm s hs) hμs c ∈ Lp_meas E 𝕜 m 2 μ := mem_Lp_meas_indicator_const_Lp hm hs hμs
  let ind := (⟨indicator_const_Lp 2 (hm s hs) hμs c, h_mem⟩ : Lp_meas E 𝕜 m 2 μ)
  have h_coe_ind : (ind : α →₂[μ] E) = indicator_const_Lp 2 (hm s hs) hμs c := by
    rfl
  have h_orth_mem := orthogonal_projection_mem_subspace_eq_self ind
  rw [← h_coe_ind, h_orth_mem]

theorem inner_condexp_L2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E) (hg : AeStronglyMeasurable' m g μ) :
    ⟪(condexpL2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, g⟫₂ := by
  symm
  rw [← sub_eq_zero, ← inner_sub_left, condexp_L2]
  simp only [← mem_Lp_meas_iff_ae_strongly_measurable'.mpr hg, ← orthogonal_projection_inner_eq_zero]

section Real

variable {hm : m ≤ m0}

theorem integral_condexp_L2_eq_of_fin_meas_real (f : lp 𝕜 2 μ) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
    (∫ x in s, condexpL2 𝕜 hm f x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [← L2.inner_indicator_const_Lp_one (hm s hs) hμs]
  have h_eq_inner :
    (∫ x in s, condexp_L2 𝕜 hm f x ∂μ) = inner (indicator_const_Lp 2 (hm s hs) hμs (1 : 𝕜)) (condexp_L2 𝕜 hm f) := by
    rw [L2.inner_indicator_const_Lp_one (hm s hs) hμs]
    congr
  rw [h_eq_inner, ← inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable hm hs hμs]

theorem lintegral_nnnorm_condexp_L2_le (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (f : lp ℝ 2 μ) :
    (∫⁻ x in s, ∥condexpL2 ℝ hm f x∥₊ ∂μ) ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ := by
  let h_meas := Lp_meas.ae_strongly_measurable' (condexp_L2 ℝ hm f)
  let g := h_meas.some
  have hg_meas : strongly_measurable[m] g := h_meas.some_spec.1
  have hg_eq : g =ᵐ[μ] condexp_L2 ℝ hm f := h_meas.some_spec.2.symm
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condexp_L2 ℝ hm f := ae_restrict_of_ae hg_eq
  have hg_nnnorm_eq : (fun x => (∥g x∥₊ : ℝ≥0∞)) =ᵐ[μ.restrict s] fun x => (∥condexp_L2 ℝ hm f x∥₊ : ℝ≥0∞) := by
    refine' hg_eq_restrict.mono fun x hx => _
    dsimp' only
    rw [hx]
  rw [lintegral_congr_ae hg_nnnorm_eq.symm]
  refine' lintegral_nnnorm_le_of_forall_fin_meas_integral_eq hm (Lp.strongly_measurable f) _ _ _ _ hs hμs
  · exact integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs
    
  · exact hg_meas
    
  · rw [integrable_on, integrable_congr hg_eq_restrict]
    exact integrable_on_condexp_L2_of_measure_ne_top hm hμs f
    
  · intro t ht hμt
    rw [← integral_condexp_L2_eq_of_fin_meas_real f ht hμt.ne]
    exact set_integral_congr_ae (hm t ht) (hg_eq.mono fun x hx _ => hx)
    

theorem condexp_L2_ae_eq_zero_of_ae_eq_zero (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) {f : lp ℝ 2 μ}
    (hf : f =ᵐ[μ.restrict s] 0) : condexpL2 ℝ hm f =ᵐ[μ.restrict s] 0 := by
  suffices h_nnnorm_eq_zero : (∫⁻ x in s, ∥condexp_L2 ℝ hm f x∥₊ ∂μ) = 0
  · rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero
    refine' h_nnnorm_eq_zero.mono fun x hx => _
    dsimp' only  at hx
    rw [Pi.zero_apply] at hx⊢
    · rwa [Ennreal.coe_eq_zero, nnnorm_eq_zero] at hx
      
    · refine' Measurable.coe_nnreal_ennreal (Measurable.nnnorm _)
      rw [Lp_meas_coe]
      exact (Lp.strongly_measurable _).Measurable
      
    
  refine' le_antisymmₓ _ (zero_le _)
  refine' (lintegral_nnnorm_condexp_L2_le hs hμs f).trans (le_of_eqₓ _)
  rw [lintegral_eq_zero_iff]
  · refine' hf.mono fun x hx => _
    dsimp' only
    rw [hx]
    simp
    
  · exact (Lp.strongly_measurable _).ennnorm
    

theorem lintegral_nnnorm_condexp_L2_indicator_le_real (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : measurable_set[m] t)
    (hμt : μ t ≠ ∞) : (∫⁻ a in t, ∥condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ) ≤ μ (s ∩ t) := by
  refine' (lintegral_nnnorm_condexp_L2_le ht hμt _).trans (le_of_eqₓ _)
  have h_eq :
    (∫⁻ x in t, ∥(indicator_const_Lp 2 hs hμs (1 : ℝ)) x∥₊ ∂μ) = ∫⁻ x in t, s.indicator (fun x => (1 : ℝ≥0∞)) x ∂μ := by
    refine' lintegral_congr_ae (ae_restrict_of_ae _)
    refine' (@indicator_const_Lp_coe_fn _ _ _ 2 _ _ _ hs hμs (1 : ℝ)).mono fun x hx => _
    rw [hx]
    classical
    simp_rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [h_eq, lintegral_indicator _ hs, lintegral_const, measure.restrict_restrict hs]
  simp only [← one_mulₓ, ← Set.univ_inter, ← MeasurableSet.univ, ← measure.restrict_apply]

end Real

/-- `condexp_L2` commutes with taking inner products with constants. See the lemma
`condexp_L2_comp_continuous_linear_map` for a more general result about commuting with continuous
linear maps. -/
theorem condexp_L2_const_inner (hm : m ≤ m0) (f : lp E 2 μ) (c : E) :
    condexpL2 𝕜 hm (((lp.mem_ℒp f).const_inner c).toLp fun a => ⟪c, f a⟫) =ᵐ[μ] fun a => ⟪c, condexpL2 𝕜 hm f a⟫ := by
  rw [Lp_meas_coe]
  have h_mem_Lp : mem_ℒp (fun a => ⟪c, condexp_L2 𝕜 hm f a⟫) 2 μ := by
    refine' mem_ℒp.const_inner _ _
    rw [Lp_meas_coe]
    exact Lp.mem_ℒp _
  have h_eq : h_mem_Lp.to_Lp _ =ᵐ[μ] fun a => ⟪c, condexp_L2 𝕜 hm f a⟫ := h_mem_Lp.coe_fn_to_Lp
  refine' eventually_eq.trans _ h_eq
  refine'
    Lp.ae_eq_of_forall_set_integral_eq' hm _ _ ennreal.zero_lt_two.ne.symm Ennreal.coe_ne_top
      (fun s hs hμs => integrable_on_condexp_L2_of_measure_ne_top hm hμs.Ne _) _ _ _ _
  · intro s hs hμs
    rw [integrable_on, integrable_congr (ae_restrict_of_ae h_eq)]
    exact (integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _).const_inner _
    
  · intro s hs hμs
    rw [← Lp_meas_coe, integral_condexp_L2_eq_of_fin_meas_real _ hs hμs.ne, integral_congr_ae (ae_restrict_of_ae h_eq),
      Lp_meas_coe, ← L2.inner_indicator_const_Lp_eq_set_integral_inner 𝕜 (↑(condexp_L2 𝕜 hm f)) (hm s hs) c hμs.ne, ←
      inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable,
      L2.inner_indicator_const_Lp_eq_set_integral_inner 𝕜 f (hm s hs) c hμs.ne,
      set_integral_congr_ae (hm s hs) ((mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)).mono fun x hx hxs => hx)]
    
  · rw [← Lp_meas_coe]
    exact Lp_meas.ae_strongly_measurable' _
    
  · refine' ae_strongly_measurable'.congr _ h_eq.symm
    exact (Lp_meas.ae_strongly_measurable' _).const_inner _
    

/-- `condexp_L2` verifies the equality of integrals defining the conditional expectation. -/
theorem integral_condexp_L2_eq (hm : m ≤ m0) (f : lp E' 2 μ) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
    (∫ x in s, condexpL2 𝕜 hm f x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [← sub_eq_zero, Lp_meas_coe, ←
    integral_sub' (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)]
  refine' integral_eq_zero_of_forall_integral_inner_eq_zero _ _ _
  · rw [integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub (↑(condexp_L2 𝕜 hm f)) f).symm)]
    exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs
    
  intro c
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw
    [integral_sub ((integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)
      ((integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)]
  have h_ae_eq_f := mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)
  rw [← Lp_meas_coe, sub_eq_zero, ←
    set_integral_congr_ae (hm s hs) ((condexp_L2_const_inner hm f c).mono fun x hx _ => hx), ←
    set_integral_congr_ae (hm s hs) (h_ae_eq_f.mono fun x hx _ => hx)]
  exact integral_condexp_L2_eq_of_fin_meas_real _ hs hμs

variable {E'' 𝕜' : Type _} [IsROrC 𝕜'] [InnerProductSpace 𝕜' E''] [CompleteSpace E''] [NormedSpace ℝ E'']

variable (𝕜 𝕜')

theorem condexp_L2_comp_continuous_linear_map (hm : m ≤ m0) (T : E' →L[ℝ] E'') (f : α →₂[μ] E') :
    (condexpL2 𝕜' hm (T.compLp f) : α →₂[μ] E'') =ᵐ[μ] T.compLp (condexpL2 𝕜 hm f : α →₂[μ] E') := by
  refine'
    Lp.ae_eq_of_forall_set_integral_eq' hm _ _ ennreal.zero_lt_two.ne.symm Ennreal.coe_ne_top
      (fun s hs hμs => integrable_on_condexp_L2_of_measure_ne_top hm hμs.Ne _)
      (fun s hs hμs => integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.Ne) _ _ _
  · intro s hs hμs
    rw [T.set_integral_comp_Lp _ (hm s hs),
      T.integral_comp_comm (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne), ← Lp_meas_coe, ←
      Lp_meas_coe, integral_condexp_L2_eq hm f hs hμs.ne, integral_condexp_L2_eq hm (T.comp_Lp f) hs hμs.ne,
      T.set_integral_comp_Lp _ (hm s hs),
      T.integral_comp_comm (integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne)]
    
  · rw [← Lp_meas_coe]
    exact Lp_meas.ae_strongly_measurable' _
    
  · have h_coe := T.coe_fn_comp_Lp (condexp_L2 𝕜 hm f : α →₂[μ] E')
    rw [← eventually_eq] at h_coe
    refine' ae_strongly_measurable'.congr _ h_coe.symm
    exact (Lp_meas.ae_strongly_measurable' (condexp_L2 𝕜 hm f)).continuous_comp T.continuous
    

variable {𝕜 𝕜'}

section CondexpL2Indicator

variable (𝕜)

theorem condexp_L2_indicator_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E') :
    condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) =ᵐ[μ] fun a =>
      condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x :=
  by
  rw [indicator_const_Lp_eq_to_span_singleton_comp_Lp hs hμs x]
  have h_comp :=
    condexp_L2_comp_continuous_linear_map ℝ 𝕜 hm (to_span_singleton ℝ x) (indicator_const_Lp 2 hs hμs (1 : ℝ))
  rw [← Lp_meas_coe] at h_comp
  refine' h_comp.trans _
  exact (to_span_singleton ℝ x).coe_fn_comp_Lp _

theorem condexp_L2_indicator_eq_to_span_singleton_comp (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E') :
    (condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) : α →₂[μ] E') =
      (toSpanSingleton ℝ x).compLp (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ))) :=
  by
  ext1
  rw [← Lp_meas_coe]
  refine' (condexp_L2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans _
  have h_comp :=
    (to_span_singleton ℝ x).coe_fn_comp_Lp (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) : α →₂[μ] ℝ)
  rw [← eventually_eq] at h_comp
  refine' eventually_eq.trans _ h_comp.symm
  refine' eventually_of_forall fun y => _
  rfl

variable {𝕜}

theorem set_lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E')
    {t : Set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
    (∫⁻ a in t, ∥condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a∥₊ ∂μ) ≤ μ (s ∩ t) * ∥x∥₊ :=
  calc
    (∫⁻ a in t, ∥condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a∥₊ ∂μ) =
        ∫⁻ a in t, ∥condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x∥₊ ∂μ :=
      set_lintegral_congr_fun (hm t ht)
        ((condexp_L2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono fun a ha hat => by
          rw [ha])
    _ = (∫⁻ a in t, ∥condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ) * ∥x∥₊ := by
      simp_rw [nnnorm_smul, Ennreal.coe_mul]
      rw [lintegral_mul_const, Lp_meas_coe]
      exact (Lp.strongly_measurable _).ennnorm
    _ ≤ μ (s ∩ t) * ∥x∥₊ := Ennreal.mul_le_mul (lintegral_nnnorm_condexp_L2_indicator_le_real hs hμs ht hμt) le_rfl
    

theorem lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E')
    [SigmaFinite (μ.trim hm)] : (∫⁻ a, ∥condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a∥₊ ∂μ) ≤ μ s * ∥x∥₊ := by
  refine' lintegral_le_of_forall_fin_meas_le' hm (μ s * ∥x∥₊) _ fun t ht hμt => _
  · rw [Lp_meas_coe]
    exact (Lp.ae_strongly_measurable _).ennnorm
    
  refine' (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _
  refine' Ennreal.mul_le_mul _ le_rfl
  exact measure_mono (Set.inter_subset_left _ _)

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condexp_L2_indicator (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') : Integrable (condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x)) μ := by
  refine' integrable_of_forall_fin_meas_le' hm (μ s * ∥x∥₊) (Ennreal.mul_lt_top hμs Ennreal.coe_ne_top) _ _
  · rw [Lp_meas_coe]
    exact Lp.ae_strongly_measurable _
    
  · refine' fun t ht hμt => (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _
    exact Ennreal.mul_le_mul (measure_mono (Set.inter_subset_left _ _)) le_rfl
    

end CondexpL2Indicator

section CondexpIndSmul

variable [NormedSpace ℝ G] {hm : m ≤ m0}

/-- Conditional expectation of the indicator of a measurable set with finite measure, in L2. -/
def condexpIndSmul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) : lp G 2 μ :=
  (toSpanSingleton ℝ x).compLpL 2 μ (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)))

theorem ae_strongly_measurable'_condexp_ind_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AeStronglyMeasurable' m (condexpIndSmul hm hs hμs x) μ := by
  have h : ae_strongly_measurable' m (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ :=
    ae_strongly_measurable'_condexp_L2 _ _
  rw [condexp_ind_smul]
  suffices ae_strongly_measurable' m (to_span_singleton ℝ x ∘ condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ
    by
    refine' ae_strongly_measurable'.congr this _
    refine' eventually_eq.trans _ (coe_fn_comp_LpL _ _).symm
    rw [Lp_meas_coe]
  exact ae_strongly_measurable'.continuous_comp (to_span_singleton ℝ x).Continuous h

theorem condexp_ind_smul_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndSmul hm hs hμs (x + y) = condexpIndSmul hm hs hμs x + condexpIndSmul hm hs hμs y := by
  simp_rw [condexp_ind_smul]
  rw [to_span_singleton_add, add_comp_LpL, add_apply]

theorem condexp_ind_smul_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndSmul hm hs hμs (c • x) = c • condexpIndSmul hm hs hμs x := by
  simp_rw [condexp_ind_smul]
  rw [to_span_singleton_smul, smul_comp_LpL, smul_apply]

theorem condexp_ind_smul_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : 𝕜)
    (x : F) : condexpIndSmul hm hs hμs (c • x) = c • condexpIndSmul hm hs hμs x := by
  rw [condexp_ind_smul, condexp_ind_smul, to_span_singleton_smul',
    (to_span_singleton ℝ x).smul_comp_LpL_apply c ↑(condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)))]

theorem condexp_ind_smul_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndSmul hm hs hμs x =ᵐ[μ] fun a => condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x :=
  (toSpanSingleton ℝ x).coe_fn_comp_LpL _

theorem set_lintegral_nnnorm_condexp_ind_smul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G)
    {t : Set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
    (∫⁻ a in t, ∥condexpIndSmul hm hs hμs x a∥₊ ∂μ) ≤ μ (s ∩ t) * ∥x∥₊ :=
  calc
    (∫⁻ a in t, ∥condexpIndSmul hm hs hμs x a∥₊ ∂μ) =
        ∫⁻ a in t, ∥condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x∥₊ ∂μ :=
      set_lintegral_congr_fun (hm t ht)
        ((condexp_ind_smul_ae_eq_smul hm hs hμs x).mono fun a ha hat => by
          rw [ha])
    _ = (∫⁻ a in t, ∥condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ) * ∥x∥₊ := by
      simp_rw [nnnorm_smul, Ennreal.coe_mul]
      rw [lintegral_mul_const, Lp_meas_coe]
      exact (Lp.strongly_measurable _).ennnorm
    _ ≤ μ (s ∩ t) * ∥x∥₊ := Ennreal.mul_le_mul (lintegral_nnnorm_condexp_L2_indicator_le_real hs hμs ht hμt) le_rfl
    

theorem lintegral_nnnorm_condexp_ind_smul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G)
    [SigmaFinite (μ.trim hm)] : (∫⁻ a, ∥condexpIndSmul hm hs hμs x a∥₊ ∂μ) ≤ μ s * ∥x∥₊ := by
  refine' lintegral_le_of_forall_fin_meas_le' hm (μ s * ∥x∥₊) _ fun t ht hμt => _
  · exact (Lp.ae_strongly_measurable _).ennnorm
    
  refine' (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _
  refine' Ennreal.mul_le_mul _ le_rfl
  exact measure_mono (Set.inter_subset_left _ _)

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condexp_ind_smul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : Integrable (condexpIndSmul hm hs hμs x) μ := by
  refine' integrable_of_forall_fin_meas_le' hm (μ s * ∥x∥₊) (Ennreal.mul_lt_top hμs Ennreal.coe_ne_top) _ _
  · exact Lp.ae_strongly_measurable _
    
  · refine' fun t ht hμt => (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _
    exact Ennreal.mul_le_mul (measure_mono (Set.inter_subset_left _ _)) le_rfl
    

theorem condexp_ind_smul_empty {x : G} :
    condexpIndSmul hm MeasurableSet.empty ((@measure_empty _ _ μ).le.trans_lt Ennreal.coe_lt_top).Ne x = 0 := by
  rw [condexp_ind_smul, indicator_const_empty]
  simp only [← coe_fn_coe_base, ← Submodule.coe_zero, ← ContinuousLinearMap.map_zero]

theorem set_integral_condexp_L2_indicator (hs : measurable_set[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) : (∫ x in s, (condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ))) x ∂μ) = (μ (t ∩ s)).toReal :=
  calc
    (∫ x in s, (condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ))) x ∂μ) =
        ∫ x in s, indicatorConstLp 2 ht hμt (1 : ℝ) x ∂μ :=
      @integral_condexp_L2_eq α _ ℝ _ _ _ _ _ _ _ _ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) hs hμs
    _ = (μ (t ∩ s)).toReal • 1 := set_integral_indicator_const_Lp (hm s hs) ht hμt (1 : ℝ)
    _ = (μ (t ∩ s)).toReal := by
      rw [smul_eq_mul, mul_oneₓ]
    

theorem set_integral_condexp_ind_smul (hs : measurable_set[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (x : G') : (∫ a in s, (condexpIndSmul hm ht hμt x) a ∂μ) = (μ (t ∩ s)).toReal • x :=
  calc
    (∫ a in s, (condexpIndSmul hm ht hμt x) a ∂μ) =
        ∫ a in s, condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) a • x ∂μ :=
      set_integral_congr_ae (hm s hs) ((condexp_ind_smul_ae_eq_smul hm ht hμt x).mono fun x hx hxs => hx)
    _ = (∫ a in s, condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) a ∂μ) • x := integral_smul_const _ x
    _ = (μ (t ∩ s)).toReal • x := by
      rw [set_integral_condexp_L2_indicator hs ht hμs hμt]
    

theorem condexp_L2_indicator_nonneg (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) [SigmaFinite (μ.trim hm)] :
    0 ≤ᵐ[μ] condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) := by
  have h : ae_strongly_measurable' m (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ :=
    ae_strongly_measurable'_condexp_L2 _ _
  refine' eventually_le.trans_eq _ h.ae_eq_mk.symm
  refine' @ae_le_of_ae_le_trim _ _ _ _ _ _ hm _ _ _
  refine' ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite _ _
  · intro t ht hμt
    refine' @integrable.integrable_on _ _ m _ _ _ _ _
    refine' integrable.trim hm _ _
    · rw [integrable_congr h.ae_eq_mk.symm]
      exact integrable_condexp_L2_indicator hm hs hμs _
      
    · exact h.strongly_measurable_mk
      
    
  · intro t ht hμt
    rw [← set_integral_trim hm h.strongly_measurable_mk ht]
    have h_ae : ∀ᵐ x ∂μ, x ∈ t → h.mk _ x = condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) x := by
      filter_upwards [h.ae_eq_mk] with x hx
      exact fun _ => hx.symm
    rw [set_integral_congr_ae (hm t ht) h_ae,
      set_integral_condexp_L2_indicator ht hs ((le_trim hm).trans_lt hμt).Ne hμs]
    exact Ennreal.to_real_nonneg
    

theorem condexp_ind_smul_nonneg {E} [NormedLatticeAddCommGroup E] [NormedSpace ℝ E] [OrderedSmul ℝ E]
    [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) :
    0 ≤ᵐ[μ] condexpIndSmul hm hs hμs x := by
  refine' eventually_le.trans_eq _ (condexp_ind_smul_ae_eq_smul hm hs hμs x).symm
  filter_upwards [condexp_L2_indicator_nonneg hm hs hμs] with a ha
  exact smul_nonneg ha hx

end CondexpIndSmul

end CondexpL2

section CondexpInd

/-! ## Conditional expectation of an indicator as a continuous linear map.

The goal of this section is to build
`condexp_ind (hm : m ≤ m0) (μ : measure α) (s : set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/


variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α} [NormedSpace ℝ G]

section CondexpIndL1Fin

/-- Conditional expectation of the indicator of a measurable set with finite measure,
as a function in L1. -/
def condexpIndL1Fin (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    α →₁[μ] G :=
  (integrable_condexp_ind_smul hm hs hμs x).toL1 _

theorem condexp_ind_L1_fin_ae_eq_condexp_ind_smul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) : condexpIndL1Fin hm hs hμs x =ᵐ[μ] condexpIndSmul hm hs hμs x :=
  (integrable_condexp_ind_smul hm hs hμs x).coe_fn_to_L1

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condexp_ind_L1_fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndL1Fin hm hs hμs (x + y) = condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm hs hμs y := by
  ext1
  refine' (mem_ℒp.coe_fn_to_Lp _).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm
  refine' eventually_eq.trans _ (eventually_eq.add (mem_ℒp.coe_fn_to_Lp _).symm (mem_ℒp.coe_fn_to_Lp _).symm)
  rw [condexp_ind_smul_add]
  refine' (Lp.coe_fn_add _ _).trans (eventually_of_forall fun a => _)
  rfl

theorem condexp_ind_L1_fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x := by
  ext1
  refine' (mem_ℒp.coe_fn_to_Lp _).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm
  rw [condexp_ind_smul_smul hs hμs c x]
  refine' (Lp.coe_fn_smul _ _).trans _
  refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun y hy => _
  rw [Pi.smul_apply, Pi.smul_apply, hy]

theorem condexp_ind_L1_fin_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : 𝕜)
    (x : F) : condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x := by
  ext1
  refine' (mem_ℒp.coe_fn_to_Lp _).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm
  rw [condexp_ind_smul_smul' hs hμs c x]
  refine' (Lp.coe_fn_smul _ _).trans _
  refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun y hy => _
  rw [Pi.smul_apply, Pi.smul_apply, hy]

theorem norm_condexp_ind_L1_fin_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ∥condexpIndL1Fin hm hs hμs x∥ ≤ (μ s).toReal * ∥x∥ := by
  have : 0 ≤ ∫ a : α, ∥condexp_ind_L1_fin hm hs hμs x a∥ ∂μ := integral_nonneg fun a => norm_nonneg _
  rw [L1.norm_eq_integral_norm, ← Ennreal.to_real_of_real (norm_nonneg x), ← Ennreal.to_real_mul, ←
    Ennreal.to_real_of_real this,
    Ennreal.to_real_le_to_real Ennreal.of_real_ne_top (Ennreal.mul_ne_top hμs Ennreal.of_real_ne_top),
    of_real_integral_norm_eq_lintegral_nnnorm]
  swap
  · rw [← mem_ℒp_one_iff_integrable]
    exact Lp.mem_ℒp _
    
  have h_eq : (∫⁻ a, ∥condexp_ind_L1_fin hm hs hμs x a∥₊ ∂μ) = ∫⁻ a, ∥condexp_ind_smul hm hs hμs x a∥₊ ∂μ := by
    refine' lintegral_congr_ae _
    refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun z hz => _
    dsimp' only
    rw [hz]
  rw [h_eq, of_real_norm_eq_coe_nnnorm]
  exact lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x

theorem condexp_ind_L1_fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (hst : s ∩ t = ∅) (x : G) :
    condexpIndL1Fin hm (hs.union ht)
        ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (Ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne x =
      condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm ht hμt x :=
  by
  ext1
  have hμst := ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne
  refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm (hs.union ht) hμst x).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm
  have hs_eq := condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x
  have ht_eq := condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm ht hμt x
  refine' eventually_eq.trans _ (eventually_eq.add hs_eq.symm ht_eq.symm)
  rw [condexp_ind_smul]
  rw [indicator_const_Lp_disjoint_union hs ht hμs hμt hst (1 : ℝ)]
  rw [(condexp_L2 ℝ hm).map_add]
  push_cast
  rw [((to_span_singleton ℝ x).compLpL 2 μ).map_add]
  refine' (Lp.coe_fn_add _ _).trans _
  refine' eventually_of_forall fun y => _
  rfl

end CondexpIndL1Fin

open Classical

section CondexpIndL1

/-- Conditional expectation of the indicator of a set, as a function in L1. Its value for sets
which are not both measurable and of finite measure is not used: we set it to 0. -/
def condexpIndL1 {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) (s : Set α) [SigmaFinite (μ.trim hm)]
    (x : G) : α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condexpIndL1Fin hm hs.1 hs.2 x else 0

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condexp_ind_L1_of_measurable_set_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndL1 hm μ s x = condexpIndL1Fin hm hs hμs x := by
  simp only [← condexp_ind_L1, ← And.intro hs hμs, ← dif_pos, ← Ne.def, ← not_false_iff, ← and_selfₓ]

theorem condexp_ind_L1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condexpIndL1 hm μ s x = 0 := by
  simp only [← condexp_ind_L1, ← hμs, ← eq_self_iff_true, ← not_true, ← Ne.def, ← dif_neg, ← not_false_iff, ←
    and_falseₓ]

theorem condexp_ind_L1_of_not_measurable_set (hs : ¬MeasurableSet s) (x : G) : condexpIndL1 hm μ s x = 0 := by
  simp only [← condexp_ind_L1, ← hs, ← dif_neg, ← not_false_iff, ← false_andₓ]

theorem condexp_ind_L1_add (x y : G) : condexpIndL1 hm μ s (x + y) = condexpIndL1 hm μ s x + condexpIndL1 hm μ s y := by
  by_cases' hs : MeasurableSet s
  swap
  · simp_rw [condexp_ind_L1_of_not_measurable_set hs]
    rw [zero_addₓ]
    
  by_cases' hμs : μ s = ∞
  · simp_rw [condexp_ind_L1_of_measure_eq_top hμs]
    rw [zero_addₓ]
    
  · simp_rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
    exact condexp_ind_L1_fin_add hs hμs x y
    

theorem condexp_ind_L1_smul (c : ℝ) (x : G) : condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x := by
  by_cases' hs : MeasurableSet s
  swap
  · simp_rw [condexp_ind_L1_of_not_measurable_set hs]
    rw [smul_zero]
    
  by_cases' hμs : μ s = ∞
  · simp_rw [condexp_ind_L1_of_measure_eq_top hμs]
    rw [smul_zero]
    
  · simp_rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
    exact condexp_ind_L1_fin_smul hs hμs c x
    

theorem condexp_ind_L1_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x := by
  by_cases' hs : MeasurableSet s
  swap
  · simp_rw [condexp_ind_L1_of_not_measurable_set hs]
    rw [smul_zero]
    
  by_cases' hμs : μ s = ∞
  · simp_rw [condexp_ind_L1_of_measure_eq_top hμs]
    rw [smul_zero]
    
  · simp_rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
    exact condexp_ind_L1_fin_smul' hs hμs c x
    

theorem norm_condexp_ind_L1_le (x : G) : ∥condexpIndL1 hm μ s x∥ ≤ (μ s).toReal * ∥x∥ := by
  by_cases' hs : MeasurableSet s
  swap
  · simp_rw [condexp_ind_L1_of_not_measurable_set hs]
    rw [Lp.norm_zero]
    exact mul_nonneg Ennreal.to_real_nonneg (norm_nonneg _)
    
  by_cases' hμs : μ s = ∞
  · rw [condexp_ind_L1_of_measure_eq_top hμs x, Lp.norm_zero]
    exact mul_nonneg Ennreal.to_real_nonneg (norm_nonneg _)
    
  · rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs x]
    exact norm_condexp_ind_L1_fin_le hs hμs x
    

theorem continuous_condexp_ind_L1 : Continuous fun x : G => condexpIndL1 hm μ s x :=
  continuous_of_linear_of_bound condexp_ind_L1_add condexp_ind_L1_smul norm_condexp_ind_L1_le

theorem condexp_ind_L1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (hst : s ∩ t = ∅) (x : G) : condexpIndL1 hm μ (s ∪ t) x = condexpIndL1 hm μ s x + condexpIndL1 hm μ t x := by
  have hμst : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne
  rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs x,
    condexp_ind_L1_of_measurable_set_of_measure_ne_top ht hμt x,
    condexp_ind_L1_of_measurable_set_of_measure_ne_top (hs.union ht) hμst x]
  exact condexp_ind_L1_fin_disjoint_union hs ht hμs hμt hst x

end CondexpIndL1

/-- Conditional expectation of the indicator of a set, as a linear map from `G` to L1. -/
def condexpInd {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (s : Set α) :
    G →L[ℝ] α →₁[μ] G where
  toFun := condexpIndL1 hm μ s
  map_add' := condexp_ind_L1_add
  map_smul' := condexp_ind_L1_smul
  cont := continuous_condexp_ind_L1

theorem condexp_ind_ae_eq_condexp_ind_smul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) : condexpInd hm μ s x =ᵐ[μ] condexpIndSmul hm hs hμs x := by
  refine' eventually_eq.trans _ (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x)
  simp [← condexp_ind, ← condexp_ind_L1, ← hs, ← hμs]

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem ae_strongly_measurable'_condexp_ind (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AeStronglyMeasurable' m (condexpInd hm μ s x) μ :=
  AeStronglyMeasurable'.congr (ae_strongly_measurable'_condexp_ind_smul hm hs hμs x)
    (condexp_ind_ae_eq_condexp_ind_smul hm hs hμs x).symm

@[simp]
theorem condexp_ind_empty : condexpInd hm μ ∅ = (0 : G →L[ℝ] α →₁[μ] G) := by
  ext1
  ext1
  refine'
    (condexp_ind_ae_eq_condexp_ind_smul hm MeasurableSet.empty
          (by
            simp )
          x).trans
      _
  rw [condexp_ind_smul_empty]
  refine' (Lp.coe_fn_zero G 2 μ).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_zero G 1 μ).symm
  rfl

theorem condexp_ind_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpInd hm μ s (c • x) = c • condexpInd hm μ s x :=
  condexp_ind_L1_smul' c x

theorem norm_condexp_ind_apply_le (x : G) : ∥condexpInd hm μ s x∥ ≤ (μ s).toReal * ∥x∥ :=
  norm_condexp_ind_L1_le x

theorem norm_condexp_ind_le : ∥(condexpInd hm μ s : G →L[ℝ] α →₁[μ] G)∥ ≤ (μ s).toReal :=
  ContinuousLinearMap.op_norm_le_bound _ Ennreal.to_real_nonneg norm_condexp_ind_apply_le

theorem condexp_ind_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (hst : s ∩ t = ∅) (x : G) : condexpInd hm μ (s ∪ t) x = condexpInd hm μ s x + condexpInd hm μ t x :=
  condexp_ind_L1_disjoint_union hs ht hμs hμt hst x

theorem condexp_ind_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (hst : s ∩ t = ∅) : (condexpInd hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) = condexpInd hm μ s + condexpInd hm μ t := by
  ext1
  push_cast
  exact condexp_ind_disjoint_union_apply hs ht hμs hμt hst x

variable (G)

theorem dominated_fin_meas_additive_condexp_ind (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    DominatedFinMeasAdditive μ (condexpInd hm μ : Set α → G →L[ℝ] α →₁[μ] G) 1 :=
  ⟨fun s t => condexp_ind_disjoint_union, fun s _ _ => norm_condexp_ind_le.trans (one_mulₓ _).symm.le⟩

variable {G}

theorem set_integral_condexp_ind (hs : measurable_set[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (x : G') : (∫ a in s, condexpInd hm μ t x a ∂μ) = (μ (t ∩ s)).toReal • x :=
  calc
    (∫ a in s, condexpInd hm μ t x a ∂μ) = ∫ a in s, condexpIndSmul hm ht hμt x a ∂μ :=
      set_integral_congr_ae (hm s hs) ((condexp_ind_ae_eq_condexp_ind_smul hm ht hμt x).mono fun x hx hxs => hx)
    _ = (μ (t ∩ s)).toReal • x := set_integral_condexp_ind_smul hs ht hμs hμt x
    

theorem condexp_ind_of_measurable (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (c : G) :
    condexpInd hm μ s c = indicatorConstLp 1 (hm s hs) hμs c := by
  ext1
  refine' eventually_eq.trans _ indicator_const_Lp_coe_fn.symm
  refine' (condexp_ind_ae_eq_condexp_ind_smul hm (hm s hs) hμs c).trans _
  refine' (condexp_ind_smul_ae_eq_smul hm (hm s hs) hμs c).trans _
  rw [Lp_meas_coe, condexp_L2_indicator_of_measurable hm hs hμs (1 : ℝ)]
  refine' (@indicator_const_Lp_coe_fn α _ _ 2 μ _ s (hm s hs) hμs (1 : ℝ)).mono fun x hx => _
  dsimp' only
  rw [hx]
  by_cases' hx_mem : x ∈ s <;> simp [← hx_mem]

theorem condexp_ind_nonneg {E} [NormedLatticeAddCommGroup E] [NormedSpace ℝ E] [OrderedSmul ℝ E] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) : 0 ≤ condexpInd hm μ s x := by
  rw [← coe_fn_le]
  refine' eventually_le.trans_eq _ (condexp_ind_ae_eq_condexp_ind_smul hm hs hμs x).symm
  exact (coe_fn_zero E 1 μ).trans_le (condexp_ind_smul_nonneg hs hμs x hx)

end CondexpInd

section CondexpL1

variable {m m0 : MeasurableSpace α} {μ : Measure α} {hm : m ≤ m0} [SigmaFinite (μ.trim hm)] {f g : α → F'} {s : Set α}

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
def condexpL1Clm (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
  L1.setToL1 (dominated_fin_meas_additive_condexp_ind F' hm μ)

theorem condexp_L1_clm_smul (c : 𝕜) (f : α →₁[μ] F') : condexpL1Clm hm μ (c • f) = c • condexpL1Clm hm μ f :=
  L1.set_to_L1_smul (dominated_fin_meas_additive_condexp_ind F' hm μ) (fun c s x => condexp_ind_smul' c x) c f

theorem condexp_L1_clm_indicator_const_Lp (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1Clm hm μ) (indicatorConstLp 1 hs hμs x) = condexpInd hm μ s x :=
  L1.set_to_L1_indicator_const_Lp (dominated_fin_meas_additive_condexp_ind F' hm μ) hs hμs x

theorem condexp_L1_clm_indicator_const (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1Clm hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) = condexpInd hm μ s x := by
  rw [Lp.simple_func.coe_indicator_const]
  exact condexp_L1_clm_indicator_const_Lp hs hμs x

/-- Auxiliary lemma used in the proof of `set_integral_condexp_L1_clm`. -/
theorem set_integral_condexp_L1_clm_of_measure_ne_top (f : α →₁[μ] F') (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
    (∫ x in s, condexpL1Clm hm μ f x ∂μ) = ∫ x in s, f x ∂μ := by
  refine'
    Lp.induction Ennreal.one_ne_top (fun f : α →₁[μ] F' => (∫ x in s, condexp_L1_clm hm μ f x ∂μ) = ∫ x in s, f x ∂μ) _
      _ (is_closed_eq _ _) f
  · intro x t ht hμt
    simp_rw [condexp_L1_clm_indicator_const ht hμt.ne x]
    rw [Lp.simple_func.coe_indicator_const, set_integral_indicator_const_Lp (hm _ hs)]
    exact set_integral_condexp_ind hs ht hμs hμt.ne x
    
  · intro f g hf_Lp hg_Lp hfg_disj hf hg
    simp_rw [(condexp_L1_clm hm μ).map_add]
    rw
      [set_integral_congr_ae (hm s hs)
        ((Lp.coe_fn_add (condexp_L1_clm hm μ (hf_Lp.to_Lp f)) (condexp_L1_clm hm μ (hg_Lp.to_Lp g))).mono
          fun x hx hxs => hx)]
    rw [set_integral_congr_ae (hm s hs) ((Lp.coe_fn_add (hf_Lp.to_Lp f) (hg_Lp.to_Lp g)).mono fun x hx hxs => hx)]
    simp_rw [Pi.add_apply]
    rw [integral_add (L1.integrable_coe_fn _).IntegrableOn (L1.integrable_coe_fn _).IntegrableOn,
      integral_add (L1.integrable_coe_fn _).IntegrableOn (L1.integrable_coe_fn _).IntegrableOn, hf, hg]
    
  · exact (continuous_set_integral s).comp (condexp_L1_clm hm μ).Continuous
    
  · exact continuous_set_integral s
    

/-- The integral of the conditional expectation `condexp_L1_clm` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexp_L1_clm (f : α →₁[μ] F') (hs : measurable_set[m] s) :
    (∫ x in s, condexpL1Clm hm μ f x ∂μ) = ∫ x in s, f x ∂μ := by
  let S := spanning_sets (μ.trim hm)
  have hS_meas : ∀ i, measurable_set[m] (S i) := measurable_spanning_sets (μ.trim hm)
  have hS_meas0 : ∀ i, MeasurableSet (S i) := fun i => hm _ (hS_meas i)
  have hs_eq : s = ⋃ i, S i ∩ s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_Union, Union_spanning_sets (μ.trim hm), Set.inter_univ]
  have hS_finite : ∀ i, μ (S i ∩ s) < ∞ := by
    refine' fun i => (measure_mono (Set.inter_subset_left _ _)).trans_lt _
    have hS_finite_trim := measure_spanning_sets_lt_top (μ.trim hm) i
    rwa [trim_measurable_set_eq hm (hS_meas i)] at hS_finite_trim
  have h_mono : Monotone fun i => S i ∩ s := by
    intro i j hij x
    simp_rw [Set.mem_inter_iff]
    exact fun h => ⟨monotone_spanning_sets (μ.trim hm) hij h.1, h.2⟩
  have h_eq_forall : (fun i => ∫ x in S i ∩ s, condexp_L1_clm hm μ f x ∂μ) = fun i => ∫ x in S i ∩ s, f x ∂μ :=
    funext fun i =>
      set_integral_condexp_L1_clm_of_measure_ne_top f (@MeasurableSet.inter α m _ _ (hS_meas i) hs) (hS_finite i).Ne
  have h_right : tendsto (fun i => ∫ x in S i ∩ s, f x ∂μ) at_top (𝓝 (∫ x in s, f x ∂μ)) := by
    have h :=
      tendsto_set_integral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coe_fn f).IntegrableOn
    rwa [← hs_eq] at h
  have h_left :
    tendsto (fun i => ∫ x in S i ∩ s, condexp_L1_clm hm μ f x ∂μ) at_top (𝓝 (∫ x in s, condexp_L1_clm hm μ f x ∂μ)) :=
    by
    have h :=
      tendsto_set_integral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coe_fn (condexp_L1_clm hm μ f)).IntegrableOn
    rwa [← hs_eq] at h
  rw [h_eq_forall] at h_left
  exact tendsto_nhds_unique h_left h_right

theorem ae_strongly_measurable'_condexp_L1_clm (f : α →₁[μ] F') : AeStronglyMeasurable' m (condexpL1Clm hm μ f) μ := by
  refine'
    Lp.induction Ennreal.one_ne_top (fun f : α →₁[μ] F' => ae_strongly_measurable' m (condexp_L1_clm hm μ f) μ) _ _ _ f
  · intro c s hs hμs
    rw [condexp_L1_clm_indicator_const hs hμs.ne c]
    exact ae_strongly_measurable'_condexp_ind hs hμs.ne c
    
  · intro f g hf hg h_disj hfm hgm
    rw [(condexp_L1_clm hm μ).map_add]
    refine' ae_strongly_measurable'.congr _ (coe_fn_add _ _).symm
    exact ae_strongly_measurable'.add hfm hgm
    
  · have :
      { f : Lp F' 1 μ | ae_strongly_measurable' m (condexp_L1_clm hm μ f) μ } =
        condexp_L1_clm hm μ ⁻¹' { f | ae_strongly_measurable' m f μ } :=
      by
      rfl
    rw [this]
    refine' IsClosed.preimage (condexp_L1_clm hm μ).Continuous _
    exact is_closed_ae_strongly_measurable' hm
    

theorem condexp_L1_clm_Lp_meas (f : lpMeas F' ℝ m 1 μ) : condexpL1Clm hm μ (f : α →₁[μ] F') = ↑f := by
  let g := Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm f
  have hfg : f = (Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g := by
    simp only [← LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine'
    @Lp.induction α F' m _ 1 (μ.trim hm) _ Ennreal.coe_ne_top
      (fun g : α →₁[μ.trim hm] F' =>
        condexp_L1_clm hm μ ((Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g : α →₁[μ] F') =
          ↑((Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g))
      _ _ _ g
  · intro c s hs hμs
    rw [Lp.simple_func.coe_indicator_const, Lp_meas_to_Lp_trim_lie_symm_indicator hs hμs.ne c,
      condexp_L1_clm_indicator_const_Lp]
    exact condexp_ind_of_measurable hs ((le_trim hm).trans_lt hμs).Ne c
    
  · intro f g hf hg hfg_disj hf_eq hg_eq
    rw [LinearIsometryEquiv.map_add]
    push_cast
    rw [map_add, hf_eq, hg_eq]
    
  · refine' is_closed_eq _ _
    · refine' (condexp_L1_clm hm μ).Continuous.comp (continuous_induced_dom.comp _)
      exact LinearIsometryEquiv.continuous _
      
    · refine' continuous_induced_dom.comp _
      exact LinearIsometryEquiv.continuous _
      
    

theorem condexp_L1_clm_of_ae_strongly_measurable' (f : α →₁[μ] F') (hfm : AeStronglyMeasurable' m f μ) :
    condexpL1Clm hm μ f = f :=
  condexp_L1_clm_Lp_meas (⟨f, hfm⟩ : lpMeas F' ℝ m 1 μ)

/-- Conditional expectation of a function, in L1. Its value is 0 if the function is not
integrable. The function-valued `condexp` should be used instead in most cases. -/
def condexpL1 (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (f : α → F') : α →₁[μ] F' :=
  setToFun μ (condexpInd hm μ) (dominated_fin_meas_additive_condexp_ind F' hm μ) f

theorem condexp_L1_undef (hf : ¬Integrable f μ) : condexpL1 hm μ f = 0 :=
  set_to_fun_undef (dominated_fin_meas_additive_condexp_ind F' hm μ) hf

theorem condexp_L1_eq (hf : Integrable f μ) : condexpL1 hm μ f = condexpL1Clm hm μ (hf.toL1 f) :=
  set_to_fun_eq (dominated_fin_meas_additive_condexp_ind F' hm μ) hf

theorem condexp_L1_zero : condexpL1 hm μ (0 : α → F') = 0 :=
  set_to_fun_zero _

theorem ae_strongly_measurable'_condexp_L1 {f : α → F'} : AeStronglyMeasurable' m (condexpL1 hm μ f) μ := by
  by_cases' hf : integrable f μ
  · rw [condexp_L1_eq hf]
    exact ae_strongly_measurable'_condexp_L1_clm _
    
  · rw [condexp_L1_undef hf]
    refine' ae_strongly_measurable'.congr _ (coe_fn_zero _ _ _).symm
    exact strongly_measurable.ae_strongly_measurable' (@strongly_measurable_zero _ _ m _ _)
    

theorem condexp_L1_congr_ae (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (h : f =ᵐ[μ] g) :
    condexpL1 hm μ f = condexpL1 hm μ g :=
  set_to_fun_congr_ae _ h

theorem integrable_condexp_L1 (f : α → F') : Integrable (condexpL1 hm μ f) μ :=
  L1.integrable_coe_fn _

/-- The integral of the conditional expectation `condexp_L1` over an `m`-measurable set is equal to
the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexp_L1 (hf : Integrable f μ) (hs : measurable_set[m] s) :
    (∫ x in s, condexpL1 hm μ f x ∂μ) = ∫ x in s, f x ∂μ := by
  simp_rw [condexp_L1_eq hf]
  rw [set_integral_condexp_L1_clm (hf.to_L1 f) hs]
  exact set_integral_congr_ae (hm s hs) (hf.coe_fn_to_L1.mono fun x hx hxs => hx)

theorem condexp_L1_add (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f + g) = condexpL1 hm μ f + condexpL1 hm μ g :=
  set_to_fun_add _ hf hg

theorem condexp_L1_neg (f : α → F') : condexpL1 hm μ (-f) = -condexpL1 hm μ f :=
  set_to_fun_neg _ f

theorem condexp_L1_smul (c : 𝕜) (f : α → F') : condexpL1 hm μ (c • f) = c • condexpL1 hm μ f :=
  set_to_fun_smul _ (fun c _ x => condexp_ind_smul' c x) c f

theorem condexp_L1_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f - g) = condexpL1 hm μ f - condexpL1 hm μ g :=
  set_to_fun_sub _ hf hg

theorem condexp_L1_of_ae_strongly_measurable' (hfm : AeStronglyMeasurable' m f μ) (hfi : Integrable f μ) :
    condexpL1 hm μ f =ᵐ[μ] f := by
  rw [condexp_L1_eq hfi]
  refine' eventually_eq.trans _ (integrable.coe_fn_to_L1 hfi)
  rw [condexp_L1_clm_of_ae_strongly_measurable']
  exact ae_strongly_measurable'.congr hfm (integrable.coe_fn_to_L1 hfi).symm

theorem condexp_L1_mono {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E] [OrderedSmul ℝ E]
    {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    condexpL1 hm μ f ≤ᵐ[μ] condexpL1 hm μ g := by
  rw [coe_fn_le]
  have h_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x : E, 0 ≤ x → 0 ≤ condexp_ind hm μ s x := fun s hs hμs x hx =>
    condexp_ind_nonneg hs hμs.Ne x hx
  exact set_to_fun_mono (dominated_fin_meas_additive_condexp_ind E hm μ) h_nonneg hf hg hfg

end CondexpL1

section Condexp

/-! ### Conditional expectation of a function -/


open Classical

variable {𝕜} {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → F'} {s : Set α}

/-- Conditional expectation of a function. Its value is 0 if the function is not integrable, if
the σ-algebra is not a sub-σ-algebra or if the measure is not σ-finite on that σ-algebra. -/
irreducible_def condexp (m : MeasurableSpace α) {m0 : MeasurableSpace α} (μ : Measure α) (f : α → F') : α → F' :=
  if hm : m ≤ m0 then
    if hμ : SigmaFinite (μ.trim hm) then
      if strongly_measurable[m] f ∧ Integrable f μ then f
      else (@ae_strongly_measurable'_condexp_L1 _ _ _ _ _ m m0 μ hm hμ _).mk (@condexpL1 _ _ _ _ _ _ _ hm μ hμ f)
    else 0
  else 0

-- mathport name: «expr [ | ]»
-- We define notation `μ[f|m]` for the conditional expectation of `f` with respect to `m`.
localized [MeasureTheory] notation μ "[" f "|" m "]" => MeasureTheory.condexp m μ f

theorem condexp_of_not_le (hm_not : ¬m ≤ m0) : μ[f|m] = 0 := by
  rw [condexp, dif_neg hm_not]

theorem condexp_of_not_sigma_finite (hm : m ≤ m0) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f|m] = 0 := by
  rw [condexp, dif_pos hm, dif_neg hμm_not]

theorem condexp_of_sigma_finite (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] :
    μ[f|m] =
      if strongly_measurable[m] f ∧ Integrable f μ then f
      else ae_strongly_measurable'_condexp_L1.mk (condexpL1 hm μ f) :=
  by
  rw [condexp, dif_pos hm, dif_pos hμm]

theorem condexp_of_strongly_measurable (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] {f : α → F'}
    (hf : strongly_measurable[m] f) (hfi : Integrable f μ) : μ[f|m] = f := by
  rw [condexp_of_sigma_finite hm, if_pos (⟨hf, hfi⟩ : strongly_measurable[m] f ∧ integrable f μ)]
  infer_instance

theorem condexp_const (hm : m ≤ m0) (c : F') [IsFiniteMeasure μ] : μ[fun x : α => c|m] = fun _ => c :=
  condexp_of_strongly_measurable hm (@strongly_measurable_const _ _ m _ _) (integrable_const c)

theorem condexp_ae_eq_condexp_L1 (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] (f : α → F') :
    μ[f|m] =ᵐ[μ] condexpL1 hm μ f := by
  rw [condexp_of_sigma_finite hm]
  by_cases' hfm : strongly_measurable[m] f
  · by_cases' hfi : integrable f μ
    · rw [if_pos (⟨hfm, hfi⟩ : strongly_measurable[m] f ∧ integrable f μ)]
      exact (condexp_L1_of_ae_strongly_measurable' (strongly_measurable.ae_strongly_measurable' hfm) hfi).symm
      
    · simp only [← hfi, ← if_false, ← and_falseₓ]
      exact (ae_strongly_measurable'.ae_eq_mk ae_strongly_measurable'_condexp_L1).symm
      
    
  simp only [← hfm, ← if_false, ← false_andₓ]
  exact (ae_strongly_measurable'.ae_eq_mk ae_strongly_measurable'_condexp_L1).symm

theorem condexp_ae_eq_condexp_L1_clm (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    μ[f|m] =ᵐ[μ] condexpL1Clm hm μ (hf.toL1 f) := by
  refine' (condexp_ae_eq_condexp_L1 hm f).trans (eventually_of_forall fun x => _)
  rw [condexp_L1_eq hf]

theorem condexp_undef (hf : ¬Integrable f μ) : μ[f|m] =ᵐ[μ] 0 := by
  by_cases' hm : m ≤ m0
  swap
  · rw [condexp_of_not_le hm]
    
  by_cases' hμm : sigma_finite (μ.trim hm)
  swap
  · rw [condexp_of_not_sigma_finite hm hμm]
    
  have : sigma_finite (μ.trim hm) := hμm
  refine' (condexp_ae_eq_condexp_L1 hm f).trans (eventually_eq.trans _ (coe_fn_zero _ 1 _))
  rw [condexp_L1_undef hf]

@[simp]
theorem condexp_zero : μ[(0 : α → F')|m] = 0 := by
  by_cases' hm : m ≤ m0
  swap
  · rw [condexp_of_not_le hm]
    
  by_cases' hμm : sigma_finite (μ.trim hm)
  swap
  · rw [condexp_of_not_sigma_finite hm hμm]
    
  have : sigma_finite (μ.trim hm) := hμm
  exact condexp_of_strongly_measurable hm (@strongly_measurable_zero _ _ m _ _) (integrable_zero _ _ _)

theorem strongly_measurable_condexp : strongly_measurable[m] (μ[f|m]) := by
  by_cases' hm : m ≤ m0
  swap
  · rw [condexp_of_not_le hm]
    exact strongly_measurable_zero
    
  by_cases' hμm : sigma_finite (μ.trim hm)
  swap
  · rw [condexp_of_not_sigma_finite hm hμm]
    exact strongly_measurable_zero
    
  have : sigma_finite (μ.trim hm) := hμm
  rw [condexp_of_sigma_finite hm]
  swap
  · infer_instance
    
  by_cases' hfm : strongly_measurable[m] f
  · by_cases' hfi : integrable f μ
    · rwa [if_pos (⟨hfm, hfi⟩ : strongly_measurable[m] f ∧ integrable f μ)]
      
    · simp only [← hfi, ← if_false, ← and_falseₓ]
      exact ae_strongly_measurable'.strongly_measurable_mk _
      
    
  simp only [← hfm, ← if_false, ← false_andₓ]
  exact ae_strongly_measurable'.strongly_measurable_mk _

theorem condexp_congr_ae (h : f =ᵐ[μ] g) : μ[f|m] =ᵐ[μ] μ[g|m] := by
  by_cases' hm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hm]
    
  by_cases' hμm : sigma_finite (μ.trim hm)
  swap
  · simp_rw [condexp_of_not_sigma_finite hm hμm]
    
  have : sigma_finite (μ.trim hm) := hμm
  exact
    (condexp_ae_eq_condexp_L1 hm f).trans
      (Filter.EventuallyEq.trans
        (by
          rw [condexp_L1_congr_ae hm h])
        (condexp_ae_eq_condexp_L1 hm g).symm)

theorem condexp_of_ae_strongly_measurable' (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] {f : α → F'}
    (hf : AeStronglyMeasurable' m f μ) (hfi : Integrable f μ) : μ[f|m] =ᵐ[μ] f := by
  refine' ((condexp_congr_ae hf.ae_eq_mk).trans _).trans hf.ae_eq_mk.symm
  rw [condexp_of_strongly_measurable hm hf.strongly_measurable_mk ((integrable_congr hf.ae_eq_mk).mp hfi)]

theorem integrable_condexp : Integrable (μ[f|m]) μ := by
  by_cases' hm : m ≤ m0
  swap
  · rw [condexp_of_not_le hm]
    exact integrable_zero _ _ _
    
  by_cases' hμm : sigma_finite (μ.trim hm)
  swap
  · rw [condexp_of_not_sigma_finite hm hμm]
    exact integrable_zero _ _ _
    
  have : sigma_finite (μ.trim hm) := hμm
  exact (integrable_condexp_L1 f).congr (condexp_ae_eq_condexp_L1 hm f).symm

/-- The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set is equal to
the integral of `f` on that set. -/
theorem set_integral_condexp (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : measurable_set[m] s) :
    (∫ x in s, (μ[f|m]) x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [set_integral_congr_ae (hm s hs) ((condexp_ae_eq_condexp_L1 hm f).mono fun x hx _ => hx)]
  exact set_integral_condexp_L1 hf hs

theorem integral_condexp {hm : m ≤ m0} [hμm : SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    (∫ x, (μ[f|m]) x ∂μ) = ∫ x, f x ∂μ := by
  suffices (∫ x in Set.Univ, (μ[f|m]) x ∂μ) = ∫ x in Set.Univ, f x ∂μ by
    simp_rw [integral_univ] at this
    exact this
  exact set_integral_condexp hm hf (@MeasurableSet.univ _ m)

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem ae_eq_condexp_of_forall_set_integral_eq (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] {f g : α → F'}
    (hf : Integrable f μ) (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hg_eq : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, g x ∂μ) = ∫ x in s, f x ∂μ)
    (hgm : AeStronglyMeasurable' m g μ) : g =ᵐ[μ] μ[f|m] := by
  refine'
    ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm hg_int_finite (fun s hs hμs => integrable_condexp.integrable_on)
      (fun s hs hμs => _) hgm (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp)
  rw [hg_eq s hs hμs, set_integral_condexp hm hf hs]

theorem condexp_add (hf : Integrable f μ) (hg : Integrable g μ) : μ[f + g|m] =ᵐ[μ] μ[f|m] + μ[g|m] := by
  by_cases' hm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hm]
    simp
    
  by_cases' hμm : sigma_finite (μ.trim hm)
  swap
  · simp_rw [condexp_of_not_sigma_finite hm hμm]
    simp
    
  have : sigma_finite (μ.trim hm) := hμm
  refine' (condexp_ae_eq_condexp_L1 hm _).trans _
  rw [condexp_L1_add hf hg]
  exact (coe_fn_add _ _).trans ((condexp_ae_eq_condexp_L1 hm _).symm.add (condexp_ae_eq_condexp_L1 hm _).symm)

theorem condexp_smul (c : 𝕜) (f : α → F') : μ[c • f|m] =ᵐ[μ] c • μ[f|m] := by
  by_cases' hm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hm]
    simp
    
  by_cases' hμm : sigma_finite (μ.trim hm)
  swap
  · simp_rw [condexp_of_not_sigma_finite hm hμm]
    simp
    
  have : sigma_finite (μ.trim hm) := hμm
  refine' (condexp_ae_eq_condexp_L1 hm _).trans _
  rw [condexp_L1_smul c f]
  refine' (@condexp_ae_eq_condexp_L1 _ _ _ _ _ m _ _ hm _ f).mp _
  refine' (coe_fn_smul c (condexp_L1 hm μ f)).mono fun x hx1 hx2 => _
  rw [hx1, Pi.smul_apply, Pi.smul_apply, hx2]

theorem condexp_neg (f : α → F') : μ[-f|m] =ᵐ[μ] -μ[f|m] := by
  let this : Module ℝ (α → F') := @Pi.module α (fun _ => F') ℝ _ _ fun _ => inferInstance <;>
    calc μ[-f|m] = μ[(-1 : ℝ) • f|m] := by
        rw [neg_one_smul ℝ f]_ =ᵐ[μ] (-1 : ℝ) • μ[f|m] := condexp_smul (-1) f _ = -μ[f|m] := neg_one_smul ℝ (μ[f|m])

theorem condexp_sub (hf : Integrable f μ) (hg : Integrable g μ) : μ[f - g|m] =ᵐ[μ] μ[f|m] - μ[g|m] := by
  simp_rw [sub_eq_add_neg]
  exact (condexp_add hf hg.neg).trans (eventually_eq.rfl.add (condexp_neg g))

theorem condexp_condexp_of_le {m₁ m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m0)
    [SigmaFinite (μ.trim hm₂)] : μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁] := by
  by_cases' hμm₁ : sigma_finite (μ.trim (hm₁₂.trans hm₂))
  swap
  · simp_rw [condexp_of_not_sigma_finite (hm₁₂.trans hm₂) hμm₁]
    
  have : sigma_finite (μ.trim (hm₁₂.trans hm₂)) := hμm₁
  refine'
    ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm₁₂.trans hm₂) (fun s hs hμs => integrable_condexp.integrable_on)
      (fun s hs hμs => integrable_condexp.integrable_on) _
      (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp)
      (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp)
  intro s hs hμs
  rw [set_integral_condexp (hm₁₂.trans hm₂) integrable_condexp hs]
  swap
  · infer_instance
    
  by_cases' hf : integrable f μ
  · rw [set_integral_condexp (hm₁₂.trans hm₂) hf hs, set_integral_condexp hm₂ hf (hm₁₂ s hs)]
    
  · simp_rw [integral_congr_ae (ae_restrict_of_ae (condexp_undef hf))]
    

theorem condexp_mono {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E] [OrderedSmul ℝ E]
    {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) : μ[f|m] ≤ᵐ[μ] μ[g|m] := by
  by_cases' hm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hm]
    
  by_cases' hμm : sigma_finite (μ.trim hm)
  swap
  · simp_rw [condexp_of_not_sigma_finite hm hμm]
    
  have : sigma_finite (μ.trim hm) := hμm
  exact
    (condexp_ae_eq_condexp_L1 hm _).trans_le ((condexp_L1_mono hf hg hfg).trans_eq (condexp_ae_eq_condexp_L1 hm _).symm)

section Indicator

theorem condexp_ae_eq_restrict_zero (hs : measurable_set[m] s) (hf : f =ᵐ[μ.restrict s] 0) :
    μ[f|m] =ᵐ[μ.restrict s] 0 := by
  by_cases' hm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hm]
    
  by_cases' hμm : sigma_finite (μ.trim hm)
  swap
  · simp_rw [condexp_of_not_sigma_finite hm hμm]
    
  have : sigma_finite (μ.trim hm) := hμm
  have : sigma_finite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs]
    exact restrict.sigma_finite _ s
  by_cases' hf_int : integrable f μ
  swap
  · exact ae_restrict_of_ae (condexp_undef hf_int)
    
  refine' ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm _ _ _ _ _
  · exact fun t ht hμt => integrable_condexp.integrable_on.integrable_on
    
  · exact fun t ht hμt => (integrable_zero _ _ _).IntegrableOn
    
  · intro t ht hμt
    rw [measure.restrict_restrict (hm _ ht), set_integral_condexp hm hf_int (ht.inter hs), ←
      measure.restrict_restrict (hm _ ht)]
    refine' set_integral_congr_ae (hm _ ht) _
    filter_upwards [hf] with x hx h using hx
    
  · exact strongly_measurable_condexp.ae_strongly_measurable'
    
  · exact strongly_measurable_zero.ae_strongly_measurable'
    

/-- Auxiliary lemma for `condexp_indicator`. -/
theorem condexp_indicator_aux (hs : measurable_set[m] s) (hf : f =ᵐ[μ.restrict (sᶜ)] 0) :
    μ[s.indicator f|m] =ᵐ[μ] s.indicator (μ[f|m]) := by
  by_cases' hm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hm, Set.indicator_zero']
    
  have hsf_zero : ∀ g : α → F', g =ᵐ[μ.restrict (sᶜ)] 0 → s.indicator g =ᵐ[μ] g := fun g =>
    indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs)
  refine' ((hsf_zero (μ[f|m]) (condexp_ae_eq_restrict_zero hs.compl hf)).trans _).symm
  exact condexp_congr_ae (hsf_zero f hf).symm

/-- The conditional expectation of the indicator of a function over an `m`-measurable set with
respect to the σ-algebra `m` is a.e. equal to the indicator of the conditional expectation. -/
theorem condexp_indicator (hf_int : Integrable f μ) (hs : measurable_set[m] s) :
    μ[s.indicator f|m] =ᵐ[μ] s.indicator (μ[f|m]) := by
  by_cases' hm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hm, Set.indicator_zero']
    
  by_cases' hμm : sigma_finite (μ.trim hm)
  swap
  · simp_rw [condexp_of_not_sigma_finite hm hμm, Set.indicator_zero']
    
  have : sigma_finite (μ.trim hm) := hμm
  -- use `have` to perform what should be the first calc step because of an error I don't
  -- understand
  have : s.indicator (μ[f|m]) =ᵐ[μ] s.indicator (μ[s.indicator f + sᶜ.indicator f|m]) := by
    rw [Set.indicator_self_add_compl s f]
  refine' (this.trans _).symm
  calc s.indicator (μ[s.indicator f + sᶜ.indicator f|m]) =ᵐ[μ] s.indicator (μ[s.indicator f|m] + μ[sᶜ.indicator f|m]) :=
      by
      have : μ[s.indicator f + sᶜ.indicator f|m] =ᵐ[μ] μ[s.indicator f|m] + μ[sᶜ.indicator f|m] :=
        condexp_add (hf_int.indicator (hm _ hs)) (hf_int.indicator (hm _ hs.compl))
      filter_upwards [this] with x hx
      classical
      rw [Set.indicator_apply, Set.indicator_apply,
        hx]_ = s.indicator (μ[s.indicator f|m]) + s.indicator (μ[sᶜ.indicator f|m]) :=
      s.indicator_add' _
        _ _ =ᵐ[μ] s.indicator (μ[s.indicator f|m]) + s.indicator (sᶜ.indicator (μ[sᶜ.indicator f|m])) :=
      by
      refine' filter.eventually_eq.rfl.add _
      have : sᶜ.indicator (μ[sᶜ.indicator f|m]) =ᵐ[μ] μ[sᶜ.indicator f|m] := by
        refine' (condexp_indicator_aux hs.compl _).symm.trans _
        · exact indicator_ae_eq_restrict_compl (hm _ hs.compl)
          
        · rw [Set.indicator_indicator, Set.inter_self]
          
      filter_upwards [this] with x hx
      by_cases' hxs : x ∈ s
      · simp only [← hx, ← hxs, ← Set.indicator_of_mem]
        
      · simp only [← hxs, ← Set.indicator_of_not_mem, ← not_false_iff]
        _ =ᵐ[μ] s.indicator (μ[s.indicator f|m]) :=
      by
      rw [Set.indicator_indicator, Set.inter_compl_self, Set.indicator_empty', add_zeroₓ]_ =ᵐ[μ] μ[s.indicator f|m] :=
      by
      refine' (condexp_indicator_aux hs _).symm.trans _
      · exact indicator_ae_eq_restrict_compl (hm _ hs)
        
      · rw [Set.indicator_indicator, Set.inter_self]
        

theorem condexp_restrict_ae_eq_restrict (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs_m : measurable_set[m] s)
    (hf_int : Integrable f μ) : μ.restrict s[f|m] =ᵐ[μ.restrict s] μ[f|m] := by
  have : sigma_finite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs_m]
    infer_instance
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  swap
  · infer_instance
    
  refine' eventually_eq.trans _ (condexp_indicator hf_int hs_m)
  refine' ae_eq_condexp_of_forall_set_integral_eq hm (hf_int.indicator (hm _ hs_m)) _ _ _
  · intro t ht hμt
    rw [← integrable_indicator_iff (hm _ ht), Set.indicator_indicator, Set.inter_comm, ← Set.indicator_indicator]
    suffices h_int_restrict : integrable (t.indicator (μ.restrict s[f|m])) (μ.restrict s)
    · rw [integrable_indicator_iff (hm _ hs_m), integrable_on]
      rw [integrable_indicator_iff (hm _ ht), integrable_on] at h_int_restrict⊢
      exact h_int_restrict
      
    exact integrable_condexp.indicator (hm _ ht)
    
  · intro t ht hμt
    calc (∫ x in t, s.indicator (μ.restrict s[f|m]) x ∂μ) = ∫ x in t, (μ.restrict s[f|m]) x ∂μ.restrict s := by
        rw [integral_indicator (hm _ hs_m), measure.restrict_restrict (hm _ hs_m), measure.restrict_restrict (hm _ ht),
          Set.inter_comm]_ = ∫ x in t, f x ∂μ.restrict s :=
        set_integral_condexp hm hf_int.integrable_on ht _ = ∫ x in t, s.indicator f x ∂μ := by
        rw [integral_indicator (hm _ hs_m), measure.restrict_restrict (hm _ hs_m), measure.restrict_restrict (hm _ ht),
          Set.inter_comm]
    
  · exact (strongly_measurable_condexp.indicator hs_m).ae_strongly_measurable'
    

/-- If the restriction to a `m`-measurable set `s` of a σ-algebra `m` is equal to the restriction
to `s` of another σ-algebra `m₂` (hypothesis `hs`), then `μ[f | m] =ᵐ[μ.restrict s] μ[f | m₂]`. -/
theorem condexp_ae_eq_restrict_of_measurable_space_eq_on {m m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0)
    (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm)] [SigmaFinite (μ.trim hm₂)] (hs_m : measurable_set[m] s)
    (hs : ∀ t, measurable_set[m] (s ∩ t) ↔ measurable_set[m₂] (s ∩ t)) : μ[f|m] =ᵐ[μ.restrict s] μ[f|m₂] := by
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  have hs_m₂ : measurable_set[m₂] s := by
    rwa [← Set.inter_univ s, ← hs Set.Univ, Set.inter_univ]
  by_cases' hf_int : integrable f μ
  swap
  · filter_upwards [@condexp_undef _ _ _ _ _ m _ μ _ hf_int, @condexp_undef _ _ _ _ _ m₂ _ μ _ hf_int] with x hxm hxm₂
    simp only [← Set.indicator_apply, ← hxm, ← hxm₂]
    
  refine' ((condexp_indicator hf_int hs_m).symm.trans _).trans (condexp_indicator hf_int hs_m₂)
  refine'
    ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm₂ (fun s hs hμs => integrable_condexp.integrable_on)
      (fun s hs hμs => integrable_condexp.integrable_on) _ _ strongly_measurable_condexp.ae_strongly_measurable'
  swap
  · have : strongly_measurable[m] (μ[s.indicator f|m]) := strongly_measurable_condexp
    refine'
      this.ae_strongly_measurable'.ae_strongly_measurable'_of_measurable_space_le_on hm hs_m (fun t => (hs t).mp) _
    exact condexp_ae_eq_restrict_zero hs_m.compl (indicator_ae_eq_restrict_compl (hm _ hs_m))
    
  intro t ht hμt
  have : (∫ x in t, (μ[s.indicator f|m]) x ∂μ) = ∫ x in s ∩ t, (μ[s.indicator f|m]) x ∂μ := by
    rw [← integral_add_compl (hm _ hs_m) integrable_condexp.integrable_on]
    suffices (∫ x in sᶜ, (μ[s.indicator f|m]) x ∂μ.restrict t) = 0 by
      rw [this, add_zeroₓ, measure.restrict_restrict (hm _ hs_m)]
    rw [measure.restrict_restrict (MeasurableSet.compl (hm _ hs_m))]
    suffices μ[s.indicator f|m] =ᵐ[μ.restrict (sᶜ)] 0 by
      rw [Set.inter_comm, ← measure.restrict_restrict (hm₂ _ ht)]
      calc (∫ x : α in t, (μ[s.indicator f|m]) x ∂μ.restrict (sᶜ)) = ∫ x : α in t, 0 ∂μ.restrict (sᶜ) := by
          refine' set_integral_congr_ae (hm₂ _ ht) _
          filter_upwards [this] with x hx h using hx _ = 0 := integral_zero _ _
    refine' condexp_ae_eq_restrict_zero hs_m.compl _
    exact indicator_ae_eq_restrict_compl (hm _ hs_m)
  have hst_m : measurable_set[m] (s ∩ t) := (hs _).mpr (hs_m₂.inter ht)
  simp_rw [this, set_integral_condexp hm₂ (hf_int.indicator (hm _ hs_m)) ht,
    set_integral_condexp hm (hf_int.indicator (hm _ hs_m)) hst_m, integral_indicator (hm _ hs_m),
    measure.restrict_restrict (hm _ hs_m), ← Set.inter_assoc, Set.inter_self]

end Indicator

section Real

theorem rn_deriv_ae_eq_condexp {hm : m ≤ m0} [hμm : SigmaFinite (μ.trim hm)] {f : α → ℝ} (hf : Integrable f μ) :
    SignedMeasure.rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm) =ᵐ[μ] μ[f|m] := by
  refine' ae_eq_condexp_of_forall_set_integral_eq hm hf _ _ _
  · exact fun _ _ _ =>
      (integrable_of_integrable_trim hm
          (signed_measure.integrable_rn_deriv ((μ.with_densityᵥ f).trim hm) (μ.trim hm))).IntegrableOn
    
  · intro s hs hlt
    conv_rhs =>
      rw [← hf.with_densityᵥ_trim_eq_integral hm hs, ←
        signed_measure.with_densityᵥ_rn_deriv_eq ((μ.with_densityᵥ f).trim hm) (μ.trim hm)
          (hf.with_densityᵥ_trim_absolutely_continuous hm)]
    rw [with_densityᵥ_apply (signed_measure.integrable_rn_deriv ((μ.with_densityᵥ f).trim hm) (μ.trim hm)) hs, ←
      set_integral_trim hm _ hs]
    exact (signed_measure.measurable_rn_deriv _ _).StronglyMeasurable
    
  · exact strongly_measurable.ae_strongly_measurable' (signed_measure.measurable_rn_deriv _ _).StronglyMeasurable
    

/-- TODO: this should be generalized and proved using Jensen's inequality
for the conditional expectation (not in mathlib yet) .-/
theorem snorm_one_condexp_le_snorm (f : α → ℝ) : snorm (μ[f|m]) 1 μ ≤ snorm f 1 μ := by
  by_cases' hf : integrable f μ
  swap
  · rw [snorm_congr_ae (condexp_undef hf), snorm_zero]
    exact zero_le _
    
  by_cases' hm : m ≤ m0
  swap
  · rw [condexp_of_not_le hm, snorm_zero]
    exact zero_le _
    
  by_cases' hsig : sigma_finite (μ.trim hm)
  swap
  · rw [condexp_of_not_sigma_finite hm hsig, snorm_zero]
    exact zero_le _
    
  calc snorm (μ[f|m]) 1 μ ≤ snorm (μ[abs f|m]) 1 μ := by
      refine' snorm_mono_ae _
      filter_upwards [@condexp_mono _ m m0 _ _ _ _ _ _ _ _ hf hf.abs
          (@ae_of_all _ m0 _ μ (fun x => le_abs_self (f x) : ∀ x, f x ≤ abs (f x))),
        eventually_le.trans (condexp_neg f).symm.le
          (@condexp_mono _ m m0 _ _ _ _ _ _ _ _ hf.neg hf.abs
            (@ae_of_all _ m0 _ μ (fun x => neg_le_abs_self (f x) : ∀ x, -f x ≤ abs (f x))))] with x hx₁ hx₂
      exact abs_le_abs hx₁ hx₂ _ = snorm f 1 μ := by
      rw [snorm_one_eq_lintegral_nnnorm, snorm_one_eq_lintegral_nnnorm, ←
        Ennreal.to_real_eq_to_real (ne_of_ltₓ integrable_condexp.2) (ne_of_ltₓ hf.2), ←
        integral_norm_eq_lintegral_nnnorm (strongly_measurable_condexp.mono hm).AeStronglyMeasurable, ←
        integral_norm_eq_lintegral_nnnorm hf.1]
      simp_rw [Real.norm_eq_abs]
      rw [← @integral_condexp _ _ _ _ _ m m0 μ _ hm hsig hf.abs]
      refine' integral_congr_ae _
      have : 0 ≤ᵐ[μ] μ[abs f|m] := by
        rw [← @condexp_zero α ℝ _ _ _ m m0 μ]
        exact
          condexp_mono (integrable_zero _ _ _) hf.abs
            (@ae_of_all _ m0 _ μ (fun x => abs_nonneg (f x) : ∀ x, 0 ≤ abs (f x)))
      filter_upwards [this] with x hx
      exact abs_eq_self.2 hx

/-- Given a integrable function `g`, the conditional expectations of `g` with respect to
a sequence of sub-σ-algebras is uniformly integrable. -/
theorem Integrable.uniform_integrable_condexp {ι : Type _} [IsFiniteMeasure μ] {g : α → ℝ} (hint : Integrable g μ)
    {ℱ : ι → MeasurableSpace α} (hℱ : ∀ i, ℱ i ≤ m0) : UniformIntegrable (fun i => μ[g|ℱ i]) 1 μ := by
  have hmeas : ∀ n, ∀ C, MeasurableSet { x | C ≤ ∥(μ[g|ℱ n]) x∥₊ } := fun n C =>
    measurable_set_le measurable_const (strongly_measurable_condexp.mono (hℱ n)).Measurable.nnnorm
  have hg : mem_ℒp g 1 μ := mem_ℒp_one_iff_integrable.2 hint
  refine'
    uniform_integrable_of le_rfl Ennreal.one_ne_top (fun n => strongly_measurable_condexp.mono (hℱ n)) fun ε hε => _
  by_cases' hne : snorm g 1 μ = 0
  · rw [snorm_eq_zero_iff hg.1 one_ne_zero] at hne
    refine'
      ⟨0, fun n =>
        (le_of_eqₓ <|
              (snorm_eq_zero_iff ((strongly_measurable_condexp.mono (hℱ n)).AeStronglyMeasurable.indicator (hmeas n 0))
                    one_ne_zero).2
                _).trans
          (zero_le _)⟩
    filter_upwards [@condexp_congr_ae _ _ _ _ _ (ℱ n) m0 μ _ _ hne] with x hx
    simp only [← zero_le', ← Set.set_of_true, ← Set.indicator_univ, ← Pi.zero_apply, ← hx, ← condexp_zero]
    
  obtain ⟨δ, hδ, h⟩ := hg.snorm_indicator_le μ le_rfl Ennreal.one_ne_top hε
  set C : ℝ≥0 := ⟨δ, hδ.le⟩⁻¹ * (snorm g 1 μ).toNnreal with hC
  have hCpos : 0 < C := mul_pos (Nnreal.inv_pos.2 hδ) (Ennreal.to_nnreal_pos hne hg.snorm_lt_top.ne)
  have : ∀ n, μ { x : α | C ≤ ∥(μ[g|ℱ n]) x∥₊ } ≤ Ennreal.ofReal δ := by
    intro n
    have :=
      mul_meas_ge_le_pow_snorm' μ one_ne_zero Ennreal.one_ne_top
        ((@strongly_measurable_condexp _ _ _ _ _ (ℱ n) _ μ g).mono (hℱ n)).AeStronglyMeasurable C
    rw [Ennreal.one_to_real, Ennreal.rpow_one, Ennreal.rpow_one, mul_comm, ←
      Ennreal.le_div_iff_mul_le (Or.inl (Ennreal.coe_ne_zero.2 hCpos.ne.symm)) (Or.inl ennreal.coe_lt_top.ne)] at this
    simp_rw [Ennreal.coe_le_coe] at this
    refine' this.trans _
    rw [Ennreal.div_le_iff_le_mul (Or.inl (Ennreal.coe_ne_zero.2 hCpos.ne.symm)) (Or.inl ennreal.coe_lt_top.ne), hC,
      Nonneg.inv_mk, Ennreal.coe_mul, Ennreal.coe_to_nnreal hg.snorm_lt_top.ne, ← mul_assoc, ←
      Ennreal.of_real_eq_coe_nnreal, ← Ennreal.of_real_mul hδ.le, mul_inv_cancel hδ.ne.symm, Ennreal.of_real_one,
      one_mulₓ]
    exact snorm_one_condexp_le_snorm _
  refine' ⟨C, fun n => le_transₓ _ (h { x : α | C ≤ ∥(μ[g|ℱ n]) x∥₊ } (hmeas n C) (this n))⟩
  have hmeasℱ : measurable_set[ℱ n] { x : α | C ≤ ∥(μ[g|ℱ n]) x∥₊ } :=
    @measurable_set_le _ _ _ _ _ (ℱ n) _ _ _ _ _ measurable_const
      (@Measurable.nnnorm _ _ _ _ _ (ℱ n) _ strongly_measurable_condexp.measurable)
  rw [← snorm_congr_ae (condexp_indicator hint hmeasℱ)]
  exact snorm_one_condexp_le_snorm _

end Real

end Condexp

end MeasureTheory

