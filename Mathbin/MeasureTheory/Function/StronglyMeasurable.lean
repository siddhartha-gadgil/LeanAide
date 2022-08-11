/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathbin.MeasureTheory.Function.EssSup
import Mathbin.MeasureTheory.Integral.MeanInequalities
import Mathbin.Topology.ContinuousFunction.Compact
import Mathbin.Topology.MetricSpace.Metrizable
import Mathbin.MeasureTheory.Function.SimpleFuncDense

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be strongly measurable if `f` is the sequential limit of simple functions.
It is said to be finitely strongly measurable with respect to a measure `μ` if the supports
of those simple functions have finite measure. We also provide almost everywhere versions of
these notions.

Almost everywhere strongly measurable functions form the largest class of functions that can be
integrated using the Bochner integral.

If the target space has a second countable topology, strongly measurable and measurable are
equivalent.

If the measure is sigma-finite, strongly measurable and finitely strongly measurable are equivalent.

The main property of finitely strongly measurable functions is
`fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that the
function is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some
results for those functions as if the measure was sigma-finite.

## Main definitions

* `strongly_measurable f`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`.
* `fin_strongly_measurable f μ`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.
* `ae_strongly_measurable f μ`: `f` is almost everywhere equal to a `strongly_measurable` function.
* `ae_fin_strongly_measurable f μ`: `f` is almost everywhere equal to a `fin_strongly_measurable`
  function.

* `ae_fin_strongly_measurable.sigma_finite_set`: a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

## Main statements

* `ae_fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

We provide a solid API for strongly measurable functions, and for almost everywhere strongly
measurable functions, as a basis for the Bochner integral.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.

-/


open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open Ennreal TopologicalSpace MeasureTheory Nnreal BigOperators

/-- The typeclass `second_countable_topology_either α β` registers the fact that at least one of
the two spaces has second countable topology. This is the right assumption to ensure that continuous
maps from `α` to `β` are strongly measurable. -/
class SecondCountableTopologyEither (α β : Type _) [TopologicalSpace α] [TopologicalSpace β] : Prop where
  out : SecondCountableTopology α ∨ SecondCountableTopology β

instance (priority := 100) second_countable_topology_either_of_left (α β : Type _) [TopologicalSpace α]
    [TopologicalSpace β] [SecondCountableTopology α] :
    SecondCountableTopologyEither α β where out :=
    Or.inl
      (by
        infer_instance)

instance (priority := 100) second_countable_topology_either_of_right (α β : Type _) [TopologicalSpace α]
    [TopologicalSpace β] [SecondCountableTopology β] :
    SecondCountableTopologyEither α β where out :=
    Or.inr
      (by
        infer_instance)

variable {α β γ ι : Type _} [Encodable ι]

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

/-- A function is `strongly_measurable` if it is the limit of simple functions. -/
def StronglyMeasurable [MeasurableSpace α] (f : α → β) : Prop :=
  ∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

-- mathport name: «exprstrongly_measurable[ ]»
localized [MeasureTheory] notation "strongly_measurable[" m "]" => @MeasureTheory.StronglyMeasurable _ _ _ m

/-- A function is `fin_strongly_measurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def FinStronglyMeasurable [Zero β] {m0 : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ fs : ℕ → α →ₛ β, (∀ n, μ (Support (fs n)) < ∞) ∧ ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

/-- A function is `ae_strongly_measurable` with respect to a measure `μ` if it is almost everywhere
equal to the limit of a sequence of simple functions. -/
def AeStronglyMeasurable {m0 : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ g, StronglyMeasurable g ∧ f =ᵐ[μ] g

/-- A function is `ae_fin_strongly_measurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
def AeFinStronglyMeasurable [Zero β] {m0 : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ g, FinStronglyMeasurable g μ ∧ f =ᵐ[μ] g

end Definitions

open MeasureTheory

/-! ## Strongly measurable functions -/


theorem StronglyMeasurable.ae_strongly_measurable {α β} {m0 : MeasurableSpace α} [TopologicalSpace β] {f : α → β}
    {μ : Measure α} (hf : StronglyMeasurable f) : AeStronglyMeasurable f μ :=
  ⟨f, hf, EventuallyEq.refl _ _⟩

@[simp]
theorem Subsingleton.strongly_measurable {α β} [MeasurableSpace α] [TopologicalSpace β] [Subsingleton β] (f : α → β) :
    StronglyMeasurable f := by
  let f_sf : α →ₛ β := ⟨f, fun x => _, Set.Subsingleton.finite Set.subsingleton_of_subsingleton⟩
  · exact ⟨fun n => f_sf, fun x => tendsto_const_nhds⟩
    
  · have h_univ : f ⁻¹' {x} = Set.Univ := by
      ext1 y
      simp
    rw [h_univ]
    exact MeasurableSet.univ
    

theorem SimpleFunc.strongly_measurable {α β} {m : MeasurableSpace α} [TopologicalSpace β] (f : α →ₛ β) :
    StronglyMeasurable f :=
  ⟨fun _ => f, fun x => tendsto_const_nhds⟩

theorem strongly_measurable_of_is_empty [IsEmpty α] {m : MeasurableSpace α} [TopologicalSpace β] (f : α → β) :
    StronglyMeasurable f :=
  ⟨fun n => SimpleFunc.ofIsEmpty, isEmptyElim⟩

theorem strongly_measurable_const {α β} {m : MeasurableSpace α} [TopologicalSpace β] {b : β} :
    StronglyMeasurable fun a : α => b :=
  ⟨fun n => SimpleFunc.const α b, fun a => tendsto_const_nhds⟩

@[to_additive]
theorem strongly_measurable_one {α β} {m : MeasurableSpace α} [TopologicalSpace β] [One β] :
    StronglyMeasurable (1 : α → β) :=
  @strongly_measurable_const _ _ _ _ 1

/-- A version of `strongly_measurable_const` that assumes `f x = f y` for all `x, y`.
This version works for functions between empty types. -/
theorem strongly_measurable_const' {α β} {m : MeasurableSpace α} [TopologicalSpace β] {f : α → β}
    (hf : ∀ x y, f x = f y) : StronglyMeasurable f := by
  cases is_empty_or_nonempty α
  · exact strongly_measurable_of_is_empty f
    
  · convert strongly_measurable_const
    exact funext fun x => hf x h.some
    

@[simp]
theorem Subsingleton.strongly_measurable' {α β} [MeasurableSpace α] [TopologicalSpace β] [Subsingleton α] (f : α → β) :
    StronglyMeasurable f :=
  strongly_measurable_const' fun x y => by
    rw [Subsingleton.elimₓ x y]

namespace StronglyMeasurable

variable {f g : α → β}

section BasicPropertiesInAnyTopologicalSpace

variable [TopologicalSpace β]

/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`.
That property is given by `strongly_measurable.tendsto_approx`. -/
protected noncomputable def approx {m : MeasurableSpace α} (hf : StronglyMeasurable f) : ℕ → α →ₛ β :=
  hf.some

protected theorem tendsto_approx {m : MeasurableSpace α} (hf : StronglyMeasurable f) :
    ∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.some_spec

end BasicPropertiesInAnyTopologicalSpace

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » t)
theorem fin_strongly_measurable_of_set_sigma_finite [TopologicalSpace β] [Zero β] {m : MeasurableSpace α}
    {μ : Measure α} (hf_meas : StronglyMeasurable f) {t : Set α} (ht : MeasurableSet t)
    (hft_zero : ∀, ∀ x ∈ tᶜ, ∀, f x = 0) (htμ : SigmaFinite (μ.restrict t)) : FinStronglyMeasurable f μ := by
  have : sigma_finite (μ.restrict t) := htμ
  let S := spanning_sets (μ.restrict t)
  have hS_meas : ∀ n, MeasurableSet (S n) := measurable_spanning_sets (μ.restrict t)
  let f_approx := hf_meas.approx
  let fs := fun n => simple_func.restrict (f_approx n) (S n ∩ t)
  have h_fs_t_compl : ∀ n, ∀ (x) (_ : x ∉ t), fs n x = 0 := by
    intro n x hxt
    rw [simple_func.restrict_apply _ ((hS_meas n).inter ht)]
    refine' Set.indicator_of_not_mem _ _
    simp [← hxt]
  refine' ⟨fs, _, fun x => _⟩
  · simp_rw [simple_func.support_eq]
    refine' fun n => (measure_bUnion_finset_le _ _).trans_lt _
    refine' ennreal.sum_lt_top_iff.mpr fun y hy => _
    rw [simple_func.restrict_preimage_singleton _ ((hS_meas n).inter ht)]
    swap
    · rw [Finset.mem_filter] at hy
      exact hy.2
      
    refine' (measure_mono (Set.inter_subset_left _ _)).trans_lt _
    have h_lt_top := measure_spanning_sets_lt_top (μ.restrict t) n
    rwa [measure.restrict_apply' ht] at h_lt_top
    
  · by_cases' hxt : x ∈ t
    swap
    · rw [funext fun n => h_fs_t_compl n x hxt, hft_zero x hxt]
      exact tendsto_const_nhds
      
    have h : tendsto (fun n => (f_approx n) x) at_top (𝓝 (f x)) := hf_meas.tendsto_approx x
    obtain ⟨n₁, hn₁⟩ : ∃ n, ∀ m, n ≤ m → fs m x = f_approx m x := by
      obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m ∩ t := by
        suffices ∃ n, ∀ m, n ≤ m → x ∈ S m by
          obtain ⟨n, hn⟩ := this
          exact ⟨n, fun m hnm => Set.mem_inter (hn m hnm) hxt⟩
        suffices ∃ n, x ∈ S n by
          rcases this with ⟨n, hn⟩
          exact ⟨n, fun m hnm => monotone_spanning_sets (μ.restrict t) hnm hn⟩
        rw [← Set.mem_Union, Union_spanning_sets (μ.restrict t)]
        trivial
      refine' ⟨n, fun m hnm => _⟩
      simp_rw [fs, simple_func.restrict_apply _ ((hS_meas m).inter ht), Set.indicator_of_mem (hn m hnm)]
    rw [tendsto_at_top'] at h⊢
    intro s hs
    obtain ⟨n₂, hn₂⟩ := h s hs
    refine' ⟨max n₁ n₂, fun m hm => _⟩
    rw [hn₁ m ((le_max_leftₓ _ _).trans hm.le)]
    exact hn₂ m ((le_max_rightₓ _ _).trans hm.le)
    

/-- If the measure is sigma-finite, all strongly measurable functions are
  `fin_strongly_measurable`. -/
protected theorem fin_strongly_measurable [TopologicalSpace β] [Zero β] {m0 : MeasurableSpace α}
    (hf : StronglyMeasurable f) (μ : Measure α) [SigmaFinite μ] : FinStronglyMeasurable f μ :=
  hf.fin_strongly_measurable_of_set_sigma_finite MeasurableSet.univ
    (by
      simp )
    (by
      rwa [measure.restrict_univ])

/-- A strongly measurable function is measurable. -/
protected theorem measurable {m : MeasurableSpace α} [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β] (hf : StronglyMeasurable f) : Measurable f :=
  measurable_of_tendsto_metrizable (fun n => (hf.approx n).Measurable) (tendsto_pi_nhds.mpr hf.tendsto_approx)

/-- A strongly measurable function is almost everywhere measurable. -/
protected theorem ae_measurable {m : MeasurableSpace α} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] {μ : Measure α} (hf : StronglyMeasurable f) : AeMeasurable f μ :=
  hf.Measurable.AeMeasurable

theorem _root_.continuous.comp_strongly_measurable {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {g : β → γ} {f : α → β} (hg : Continuous g) (hf : StronglyMeasurable f) : StronglyMeasurable fun x => g (f x) :=
  ⟨fun n => SimpleFunc.map g (hf.approx n), fun x => (hg.Tendsto _).comp (hf.tendsto_approx x)⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]
@[to_additive]
theorem measurable_set_mul_support {m : MeasurableSpace α} [One β] [TopologicalSpace β] [MetrizableSpace β]
    (hf : StronglyMeasurable f) : MeasurableSet (MulSupport f) := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]"
  exact measurable_set_mul_support hf.measurable

protected theorem mono {m m' : MeasurableSpace α} [TopologicalSpace β] (hf : strongly_measurable[m'] f)
    (h_mono : m' ≤ m) : strongly_measurable[m] f := by
  let f_approx : ℕ → @simple_func α m β := fun n =>
    { toFun := hf.approx n, measurable_set_fiber' := fun x => h_mono _ (simple_func.measurable_set_fiber' _ x),
      finite_range' := simple_func.finite_range (hf.approx n) }
  exact ⟨f_approx, hf.tendsto_approx⟩

protected theorem prod_mk {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ] {f : α → β} {g : α → γ}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) : StronglyMeasurable fun x => (f x, g x) := by
  refine' ⟨fun n => simple_func.pair (hf.approx n) (hg.approx n), fun x => _⟩
  rw [nhds_prod_eq]
  exact tendsto.prod_mk (hf.tendsto_approx x) (hg.tendsto_approx x)

theorem comp_measurable [TopologicalSpace β] {m : MeasurableSpace α} {m' : MeasurableSpace γ} {f : α → β} {g : γ → α}
    (hf : StronglyMeasurable f) (hg : Measurable g) : StronglyMeasurable (f ∘ g) :=
  ⟨fun n => SimpleFunc.comp (hf.approx n) g hg, fun x => hf.tendsto_approx (g x)⟩

theorem of_uncurry_left [TopologicalSpace β] {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {f : α → γ → β}
    (hf : StronglyMeasurable (uncurry f)) {x : α} : StronglyMeasurable (f x) :=
  hf.comp_measurable measurable_prod_mk_left

theorem of_uncurry_right [TopologicalSpace β] {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {f : α → γ → β}
    (hf : StronglyMeasurable (uncurry f)) {y : γ} : StronglyMeasurable fun x => f x y :=
  hf.comp_measurable measurable_prod_mk_right

section Arithmetic

variable {mα : MeasurableSpace α} [TopologicalSpace β]

include mα

@[to_additive]
protected theorem mul [Mul β] [HasContinuousMul β] (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (f * g) :=
  ⟨fun n => hf.approx n * hg.approx n, fun x => (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩

@[to_additive]
theorem mul_const [Mul β] [HasContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => f x * c :=
  hf.mul strongly_measurable_const

@[to_additive]
theorem const_mul [Mul β] [HasContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => c * f x :=
  strongly_measurable_const.mul hf

@[to_additive]
protected theorem inv [Groupₓ β] [TopologicalGroup β] (hf : StronglyMeasurable f) : StronglyMeasurable f⁻¹ :=
  ⟨fun n => (hf.approx n)⁻¹, fun x => (hf.tendsto_approx x).inv⟩

@[to_additive]
protected theorem div [Div β] [HasContinuousDiv β] (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (f / g) :=
  ⟨fun n => hf.approx n / hg.approx n, fun x => (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩

@[to_additive]
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [HasSmul 𝕜 β] [HasContinuousSmul 𝕜 β] {f : α → 𝕜} {g : α → β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) : StronglyMeasurable fun x => f x • g x :=
  continuous_smul.comp_strongly_measurable (hf.prod_mk hg)

protected theorem const_smul {𝕜} [HasSmul 𝕜 β] [HasContinuousConstSmul 𝕜 β] (hf : StronglyMeasurable f) (c : 𝕜) :
    StronglyMeasurable (c • f) :=
  ⟨fun n => c • hf.approx n, fun x => (hf.tendsto_approx x).const_smul c⟩

protected theorem const_smul' {𝕜} [HasSmul 𝕜 β] [HasContinuousConstSmul 𝕜 β] (hf : StronglyMeasurable f) (c : 𝕜) :
    StronglyMeasurable fun x => c • f x :=
  hf.const_smul c

@[to_additive]
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [HasSmul 𝕜 β] [HasContinuousSmul 𝕜 β] {f : α → 𝕜}
    (hf : StronglyMeasurable f) (c : β) : StronglyMeasurable fun x => f x • c :=
  continuous_smul.comp_strongly_measurable (hf.prod_mk strongly_measurable_const)

end Arithmetic

section MulAction

variable [TopologicalSpace β] {G : Type _} [Groupₓ G] [MulAction G β] [HasContinuousConstSmul G β]

theorem _root_.strongly_measurable_const_smul_iff {m : MeasurableSpace α} (c : G) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  ⟨fun h => by
    simpa only [← inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩

variable {G₀ : Type _} [GroupWithZeroₓ G₀] [MulAction G₀ β] [HasContinuousConstSmul G₀ β]

theorem _root_.strongly_measurable_const_smul_iff₀ {m : MeasurableSpace α} {c : G₀} (hc : c ≠ 0) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f := by
  refine' ⟨fun h => _, fun h => h.const_smul c⟩
  convert h.const_smul' c⁻¹
  simp [← smul_smul, ← inv_mul_cancel hc]

end MulAction

section Order

variable [MeasurableSpace α] [TopologicalSpace β]

open Filter

open Filter

protected theorem sup [HasSup β] [HasContinuousSup β] (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (f⊔g) :=
  ⟨fun n => hf.approx n⊔hg.approx n, fun x => (hf.tendsto_approx x).sup_right_nhds (hg.tendsto_approx x)⟩

protected theorem inf [HasInf β] [HasContinuousInf β] (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (f⊓g) :=
  ⟨fun n => hf.approx n⊓hg.approx n, fun x => (hf.tendsto_approx x).inf_right_nhds (hg.tendsto_approx x)⟩

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoidₓ

variable {M : Type _} [Monoidₓ M] [TopologicalSpace M] [HasContinuousMul M] {m : MeasurableSpace α}

include m

@[to_additive]
theorem _root_.list.strongly_measurable_prod' (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, StronglyMeasurable f) :
    StronglyMeasurable l.Prod := by
  induction' l with f l ihl
  · exact strongly_measurable_one
    
  rw [List.forall_mem_consₓ] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)

@[to_additive]
theorem _root_.list.strongly_measurable_prod (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, StronglyMeasurable f) :
    StronglyMeasurable fun x => (l.map fun f : α → M => f x).Prod := by
  simpa only [Pi.list_prod_apply] using l.strongly_measurable_prod' hl

end Monoidₓ

section CommMonoidₓ

variable {M : Type _} [CommMonoidₓ M] [TopologicalSpace M] [HasContinuousMul M] {m : MeasurableSpace α}

include m

@[to_additive]
theorem _root_.multiset.strongly_measurable_prod' (l : Multiset (α → M)) (hl : ∀, ∀ f ∈ l, ∀, StronglyMeasurable f) :
    StronglyMeasurable l.Prod := by
  rcases l with ⟨l⟩
  simpa using
    l.strongly_measurable_prod'
      (by
        simpa using hl)

@[to_additive]
theorem _root_.multiset.strongly_measurable_prod (s : Multiset (α → M)) (hs : ∀, ∀ f ∈ s, ∀, StronglyMeasurable f) :
    StronglyMeasurable fun x => (s.map fun f : α → M => f x).Prod := by
  simpa only [Pi.multiset_prod_apply] using s.strongly_measurable_prod' hs

@[to_additive]
theorem _root_.finset.strongly_measurable_prod' {ι : Type _} {f : ι → α → M} (s : Finset ι)
    (hf : ∀, ∀ i ∈ s, ∀, StronglyMeasurable (f i)) : StronglyMeasurable (∏ i in s, f i) :=
  Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) (@strongly_measurable_one α M _ _ _) hf

@[to_additive]
theorem _root_.finset.strongly_measurable_prod {ι : Type _} {f : ι → α → M} (s : Finset ι)
    (hf : ∀, ∀ i ∈ s, ∀, StronglyMeasurable (f i)) : StronglyMeasurable fun a => ∏ i in s, f i a := by
  simpa only [Finset.prod_apply] using s.strongly_measurable_prod' hf

end CommMonoidₓ

/-- The range of a strongly measurable function is separable. -/
theorem is_separable_range {m : MeasurableSpace α} [TopologicalSpace β] (hf : StronglyMeasurable f) :
    TopologicalSpace.IsSeparable (Range f) := by
  have : IsSeparable (Closure (⋃ n, range (hf.approx n))) :=
    (is_separable_Union fun n => (simple_func.finite_range (hf.approx n)).IsSeparable).closure
  apply this.mono
  rintro _ ⟨x, rfl⟩
  apply mem_closure_of_tendsto (hf.tendsto_approx x)
  apply eventually_of_forall fun n => _
  apply mem_Union_of_mem n
  exact mem_range_self _

theorem separable_space_range_union_singleton {m : MeasurableSpace α} [TopologicalSpace β] [PseudoMetrizableSpace β]
    (hf : StronglyMeasurable f) {b : β} : SeparableSpace (Range f ∪ {b} : Set β) := by
  let this := pseudo_metrizable_space_pseudo_metric β
  exact (hf.is_separable_range.union (finite_singleton _).IsSeparable).SeparableSpace

section SecondCountableStronglyMeasurable

variable {mα : MeasurableSpace α} [MeasurableSpace β]

include mα

/-- In a space with second countable topology, measurable implies strongly measurable. -/
theorem _root_.measurable.strongly_measurable [TopologicalSpace β] [PseudoMetrizableSpace β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] (hf : Measurable f) : StronglyMeasurable f := by
  let this := pseudo_metrizable_space_pseudo_metric β
  rcases is_empty_or_nonempty β with ⟨⟩ <;> skip
  · exact subsingleton.strongly_measurable f
    
  · inhabit β
    exact
      ⟨simple_func.approx_on f hf Set.Univ default (Set.mem_univ _), fun x =>
        simple_func.tendsto_approx_on hf (Set.mem_univ _)
          (by
            simp )⟩
    

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem _root_.strongly_measurable_iff_measurable [TopologicalSpace β] [MetrizableSpace β] [BorelSpace β]
    [SecondCountableTopology β] : StronglyMeasurable f ↔ Measurable f :=
  ⟨fun h => h.Measurable, fun h => Measurable.strongly_measurable h⟩

theorem _root_.strongly_measurable_id [TopologicalSpace α] [PseudoMetrizableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] : StronglyMeasurable (id : α → α) :=
  measurable_id.StronglyMeasurable

end SecondCountableStronglyMeasurable

/-- A function is strongly measurable if and only if it is measurable and has separable
range. -/
theorem _root_.strongly_measurable_iff_measurable_separable {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] :
    StronglyMeasurable f ↔ Measurable f ∧ IsSeparable (Range f) := by
  refine' ⟨fun H => ⟨H.Measurable, H.is_separable_range⟩, _⟩
  rintro ⟨H, H'⟩
  let this := pseudo_metrizable_space_pseudo_metric β
  let g := cod_restrict f (Closure (range f)) fun x => subset_closure (mem_range_self x)
  have fg : f = (coe : Closure (range f) → β) ∘ g := by
    ext x
    rfl
  have T : MeasurableEmbedding (coe : Closure (range f) → β) := by
    apply ClosedEmbedding.measurable_embedding
    exact closed_embedding_subtype_coe is_closed_closure
  have g_meas : Measurable g := by
    rw [fg] at H
    exact T.measurable_comp_iff.1 H
  have : second_countable_topology (Closure (range f)) := by
    suffices separable_space (Closure (range f)) by
      exact UniformSpace.second_countable_of_separable _
    exact (is_separable.closure H').SeparableSpace
  have g_smeas : strongly_measurable g := Measurable.strongly_measurable g_meas
  rw [fg]
  exact continuous_subtype_coe.comp_strongly_measurable g_smeas

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]
/-- A continuous function is strongly measurable when either the source space or the target space
is second-countable. -/
theorem _root_.continuous.strongly_measurable [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    {β : Type _} [TopologicalSpace β] [PseudoMetrizableSpace β] [h : SecondCountableTopologyEither α β] {f : α → β}
    (hf : Continuous f) : StronglyMeasurable f := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]"
  cases h.out
  · rw [strongly_measurable_iff_measurable_separable]
    refine' ⟨hf.measurable, _⟩
    rw [← image_univ]
    exact (is_separable_of_separable_space univ).Image hf
    
  · exact hf.measurable.strongly_measurable
    

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[["[", expr β, ",", expr γ, "]"]]
/-- If `g` is a topological embedding, then `f` is strongly measurable iff `g ∘ f` is. -/
theorem _root_.embedding.comp_strongly_measurable_iff {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [TopologicalSpace γ] [PseudoMetrizableSpace γ] {g : β → γ} {f : α → β}
    (hg : Embedding g) : (StronglyMeasurable fun x => g (f x)) ↔ StronglyMeasurable f := by
  let this := pseudo_metrizable_space_pseudo_metric γ
  trace
    "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[\"[\", expr β, \",\", expr γ, \"]\"]]"
  refine'
    ⟨fun H => strongly_measurable_iff_measurable_separable.2 ⟨_, _⟩, fun H => hg.continuous.comp_strongly_measurable H⟩
  · let G : β → range g := cod_restrict g (range g) mem_range_self
    have hG : ClosedEmbedding G :=
      { hg.cod_restrict _ _ with
        closed_range := by
          convert is_closed_univ
          apply eq_univ_of_forall
          rintro ⟨-, ⟨x, rfl⟩⟩
          exact mem_range_self x }
    have : Measurable (G ∘ f) := Measurable.subtype_mk H.measurable
    exact hG.measurable_embedding.measurable_comp_iff.1 this
    
  · have : IsSeparable (g ⁻¹' range (g ∘ f)) := hg.is_separable_preimage H.is_separable_range
    convert this
    ext x
    simp [← hg.inj.eq_iff]
    

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]
/-- A sequential limit of strongly measurable functions is strongly measurable. -/
theorem _root_.strongly_measurable_of_tendsto {ι : Type _} {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (u : Filter ι) [NeBot u] [IsCountablyGenerated u] {f : ι → α → β} {g : α → β}
    (hf : ∀ i, StronglyMeasurable (f i)) (lim : Tendsto f u (𝓝 g)) : StronglyMeasurable g := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]"
  refine' strongly_measurable_iff_measurable_separable.2 ⟨_, _⟩
  · exact measurable_of_tendsto_metrizable' u (fun i => (hf i).Measurable) limₓ
    
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : IsSeparable (Closure (⋃ i, range (f (v i)))) :=
      (is_separable_Union fun i => (hf (v i)).is_separable_range).closure
    apply this.mono
    rintro _ ⟨x, rfl⟩
    rw [tendsto_pi_nhds] at lim
    apply mem_closure_of_tendsto ((limₓ x).comp hv)
    apply eventually_of_forall fun n => _
    apply mem_Union_of_mem n
    exact mem_range_self _
    

protected theorem piecewise {m : MeasurableSpace α} [TopologicalSpace β] {s : Set α} {_ : DecidablePred (· ∈ s)}
    (hs : MeasurableSet s) (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (Set.piecewise s f g) := by
  refine' ⟨fun n => simple_func.piecewise s hs (hf.approx n) (hg.approx n), fun x => _⟩
  by_cases' hx : x ∈ s
  · simpa [← hx] using hf.tendsto_approx x
    
  · simpa [← hx] using hg.tendsto_approx x
    

/-- this is slightly different from `strongly_measurable.piecewise`. It can be used to show
`strongly_measurable (ite (x=0) 0 1)` by
`exact strongly_measurable.ite (measurable_set_singleton 0) strongly_measurable_const
strongly_measurable_const`, but replacing `strongly_measurable.ite` by
`strongly_measurable.piecewise` in that example proof does not work. -/
protected theorem ite {m : MeasurableSpace α} [TopologicalSpace β] {p : α → Prop} {_ : DecidablePred p}
    (hp : MeasurableSet { a : α | p a }) (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => ite (p x) (f x) (g x) :=
  StronglyMeasurable.piecewise hp hf hg

theorem _root_.strongly_measurable_of_strongly_measurable_union_cover {m : MeasurableSpace α} [TopologicalSpace β]
    {f : α → β} (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) (h : univ ⊆ s ∪ t)
    (hc : StronglyMeasurable fun a : s => f a) (hd : StronglyMeasurable fun a : t => f a) : StronglyMeasurable f := by
  classical
  let f : ℕ → α →ₛ β := fun n =>
    { toFun := fun x =>
        if hx : x ∈ s then hc.approx n ⟨x, hx⟩
        else
          hd.approx n
            ⟨x, by
              simpa [← hx] using h (mem_univ x)⟩,
      measurable_set_fiber' := by
        intro x
        convert
          (hs.subtype_image ((hc.approx n).measurable_set_fiber x)).union
            ((ht.subtype_image ((hd.approx n).measurable_set_fiber x)).diff hs)
        ext1 y
        simp only [← mem_union_eq, ← mem_preimage, ← mem_singleton_iff, ← mem_image, ← SetCoe.exists, ← Subtype.coe_mk,
          ← exists_and_distrib_right, ← exists_eq_right, ← mem_diff]
        by_cases' hy : y ∈ s
        · rw [dif_pos hy]
          simp only [← hy, ← exists_true_left, ← not_true, ← and_falseₓ, ← or_falseₓ]
          
        · rw [dif_neg hy]
          have A : y ∈ t := by
            simpa [← hy] using h (mem_univ y)
          simp only [← A, ← hy, ← false_orₓ, ← IsEmpty.exists_iff, ← not_false_iff, ← and_trueₓ, ← exists_true_left]
          ,
      finite_range' := by
        apply ((hc.approx n).finite_range.union (hd.approx n).finite_range).Subset
        rintro - ⟨y, rfl⟩
        dsimp'
        by_cases' hy : y ∈ s
        · left
          rw [dif_pos hy]
          exact mem_range_self _
          
        · right
          rw [dif_neg hy]
          exact mem_range_self _
           }
  refine' ⟨f, fun y => _⟩
  by_cases' hy : y ∈ s
  · convert hc.tendsto_approx ⟨y, hy⟩ using 1
    ext1 n
    simp only [← dif_pos hy, ← simple_func.apply_mk]
    
  · have A : y ∈ t := by
      simpa [← hy] using h (mem_univ y)
    convert hd.tendsto_approx ⟨y, A⟩ using 1
    ext1 n
    simp only [← dif_neg hy, ← simple_func.apply_mk]
    

theorem _root_.strongly_measurable_of_restrict_of_restrict_compl {m : MeasurableSpace α} [TopologicalSpace β]
    {f : α → β} {s : Set α} (hs : MeasurableSet s) (h₁ : StronglyMeasurable (s.restrict f))
    (h₂ : StronglyMeasurable (sᶜ.restrict f)) : StronglyMeasurable f :=
  strongly_measurable_of_strongly_measurable_union_cover s (sᶜ) hs hs.compl (union_compl_self s).Ge h₁ h₂

protected theorem indicator {m : MeasurableSpace α} [TopologicalSpace β] [Zero β] (hf : StronglyMeasurable f)
    {s : Set α} (hs : MeasurableSet s) : StronglyMeasurable (s.indicator f) :=
  hf.piecewise hs strongly_measurable_const

protected theorem dist {m : MeasurableSpace α} {β : Type _} [PseudoMetricSpace β] {f g : α → β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) : StronglyMeasurable fun x => dist (f x) (g x) :=
  continuous_dist.comp_strongly_measurable (hf.prod_mk hg)

protected theorem norm {m : MeasurableSpace α} {β : Type _} [NormedGroup β] {f : α → β} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => ∥f x∥ :=
  continuous_norm.comp_strongly_measurable hf

protected theorem nnnorm {m : MeasurableSpace α} {β : Type _} [NormedGroup β] {f : α → β} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => ∥f x∥₊ :=
  continuous_nnnorm.comp_strongly_measurable hf

protected theorem ennnorm {m : MeasurableSpace α} {β : Type _} [NormedGroup β] {f : α → β} (hf : StronglyMeasurable f) :
    Measurable fun a => (∥f a∥₊ : ℝ≥0∞) :=
  (Ennreal.continuous_coe.comp_strongly_measurable hf.nnnorm).Measurable

protected theorem real_to_nnreal {m : MeasurableSpace α} {f : α → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => (f x).toNnreal :=
  continuous_real_to_nnreal.comp_strongly_measurable hf

theorem _root_.measurable_embedding.strongly_measurable_extend {f : α → β} {g : α → γ} {g' : γ → β}
    {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} [TopologicalSpace β] (hg : MeasurableEmbedding g)
    (hf : StronglyMeasurable f) (hg' : StronglyMeasurable g') : StronglyMeasurable (Function.extendₓ g f g') := by
  refine' ⟨fun n => simple_func.extend (hf.approx n) g hg (hg'.approx n), _⟩
  intro x
  by_cases' hx : ∃ y, g y = x
  · rcases hx with ⟨y, rfl⟩
    simpa only [← simple_func.extend_apply, ← hg.injective, ← extend_apply] using hf.tendsto_approx y
    
  · simpa only [← hx, ← simple_func.extend_apply', ← not_false_iff, ← extend_apply'] using hg'.tendsto_approx x
    

theorem _root_.measurable_embedding.exists_strongly_measurable_extend {f : α → β} {g : α → γ} {mα : MeasurableSpace α}
    {mγ : MeasurableSpace γ} [TopologicalSpace β] (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f)
    (hne : γ → Nonempty β) : ∃ f' : γ → β, StronglyMeasurable f' ∧ f' ∘ g = f :=
  ⟨Function.extendₓ g f fun x => Classical.choice (hne x),
    hg.strongly_measurable_extend hf (strongly_measurable_const' fun _ _ => rfl),
    funext fun x => extend_applyₓ hg.Injective _ _ _⟩

protected theorem inner {𝕜 : Type _} {E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E] {m : MeasurableSpace α}
    {f g : α → E} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun t => @inner 𝕜 _ _ (f t) (g t) :=
  Continuous.comp_strongly_measurable continuous_inner (hf.prod_mk hg)

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr «expr × »(E, E)]]
theorem measurable_set_eq_fun {m : MeasurableSpace α} {E} [TopologicalSpace E] [MetrizableSpace E] {f g : α → E}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) : MeasurableSet { x | f x = g x } := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr «expr × »(E, E)]]"
  exact (hf.prod_mk hg).Measurable is_closed_diagonal.measurable_set

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr «expr × »(β, β)]]
theorem measurable_set_lt {m : MeasurableSpace α} [TopologicalSpace β] [LinearOrderₓ β] [OrderClosedTopology β]
    [PseudoMetrizableSpace β] {f g : α → β} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    MeasurableSet { a | f a < g a } := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr «expr × »(β, β)]]"
  exact (hf.prod_mk hg).Measurable is_open_lt_prod.measurable_set

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr «expr × »(β, β)]]
theorem measurable_set_le {m : MeasurableSpace α} [TopologicalSpace β] [Preorderₓ β] [OrderClosedTopology β]
    [PseudoMetrizableSpace β] {f g : α → β} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    MeasurableSet { a | f a ≤ g a } := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr «expr × »(β, β)]]"
  exact (hf.prod_mk hg).Measurable is_closed_le_prod.measurable_set

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » s)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » s)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » s)
theorem strongly_measurable_in_set {m : MeasurableSpace α} [TopologicalSpace β] [Zero β] {s : Set α} {f : α → β}
    (hs : MeasurableSet s) (hf : StronglyMeasurable f) (hf_zero : ∀ (x) (_ : x ∉ s), f x = 0) :
    ∃ fs : ℕ → α →ₛ β, (∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) ∧ ∀ (x) (_ : x ∉ s) (n), fs n x = 0 := by
  let g_seq_s : ℕ → @simple_func α m β := fun n => (hf.approx n).restrict s
  have hg_eq : ∀, ∀ x ∈ s, ∀, ∀ n, g_seq_s n x = hf.approx n x := by
    intro x hx n
    rw [simple_func.coe_restrict _ hs, Set.indicator_of_mem hx]
  have hg_zero : ∀ (x) (_ : x ∉ s), ∀ n, g_seq_s n x = 0 := by
    intro x hx n
    rw [simple_func.coe_restrict _ hs, Set.indicator_of_not_mem hx]
  refine' ⟨g_seq_s, fun x => _, hg_zero⟩
  by_cases' hx : x ∈ s
  · simp_rw [hg_eq x hx]
    exact hf.tendsto_approx x
    
  · simp_rw [hg_zero x hx, hf_zero x hx]
    exact tendsto_const_nhds
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » s)
/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` supported
on `s` is `m`-strongly-measurable, then `f` is also `m₂`-strongly-measurable. -/
theorem strongly_measurable_of_measurable_space_le_on {α E} {m m₂ : MeasurableSpace α} [TopologicalSpace E] [Zero E]
    {s : Set α} {f : α → E} (hs_m : measurable_set[m] s)
    (hs : ∀ t, measurable_set[m] (s ∩ t) → measurable_set[m₂] (s ∩ t)) (hf : strongly_measurable[m] f)
    (hf_zero : ∀ (x) (_ : x ∉ s), f x = 0) : strongly_measurable[m₂] f := by
  have hs_m₂ : measurable_set[m₂] s := by
    rw [← Set.inter_univ s]
    refine' hs Set.Univ _
    rwa [Set.inter_univ]
  obtain ⟨g_seq_s, hg_seq_tendsto, hg_seq_zero⟩ := strongly_measurable_in_set hs_m hf hf_zero
  let g_seq_s₂ : ℕ → @simple_func α m₂ E := fun n =>
    { toFun := g_seq_s n,
      measurable_set_fiber' := fun x => by
        rw [← Set.inter_univ (g_seq_s n ⁻¹' {x}), ← Set.union_compl_self s, Set.inter_union_distrib_left,
          Set.inter_comm (g_seq_s n ⁻¹' {x})]
        refine' MeasurableSet.union (hs _ (hs_m.inter _)) _
        · exact @simple_func.measurable_set_fiber _ _ m _ _
          
        by_cases' hx : x = 0
        · suffices g_seq_s n ⁻¹' {x} ∩ sᶜ = sᶜ by
            rw [this]
            exact hs_m₂.compl
          ext1 y
          rw [hx, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
          exact ⟨fun h => h.2, fun h => ⟨hg_seq_zero y h n, h⟩⟩
          
        · suffices g_seq_s n ⁻¹' {x} ∩ sᶜ = ∅ by
            rw [this]
            exact MeasurableSet.empty
          ext1 y
          simp only [← mem_inter_eq, ← mem_preimage, ← mem_singleton_iff, ← mem_compl_eq, ← mem_empty_eq, ← iff_falseₓ,
            ← not_and, ← not_not_mem]
          refine' imp_of_not_imp_not _ _ fun hys => _
          rw [hg_seq_zero y hys n]
          exact Ne.symm hx
          ,
      finite_range' := @simple_func.finite_range _ _ m (g_seq_s n) }
  have hg_eq : ∀ x n, g_seq_s₂ n x = g_seq_s n x := fun x n => rfl
  refine' ⟨g_seq_s₂, fun x => _⟩
  simp_rw [hg_eq]
  exact hg_seq_tendsto x

end StronglyMeasurable

/-! ## Finitely strongly measurable functions -/


theorem fin_strongly_measurable_zero {α β} {m : MeasurableSpace α} {μ : Measure α} [Zero β] [TopologicalSpace β] :
    FinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, by
    simp only [← Pi.zero_apply, ← simple_func.coe_zero, ← support_zero', ← measure_empty, ← WithTop.zero_lt_top, ←
      forall_const],
    fun n => tendsto_const_nhds⟩

namespace FinStronglyMeasurable

variable {m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β}

theorem ae_fin_strongly_measurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ) :
    AeFinStronglyMeasurable f μ :=
  ⟨f, hf, ae_eq_refl f⟩

section sequence

variable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ)

/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`
and `∀ n, μ (support (hf.approx n)) < ∞`. These properties are given by
`fin_strongly_measurable.tendsto_approx` and `fin_strongly_measurable.fin_support_approx`. -/
protected noncomputable def approx : ℕ → α →ₛ β :=
  hf.some

protected theorem fin_support_approx : ∀ n, μ (Support (hf.approx n)) < ∞ :=
  hf.some_spec.1

protected theorem tendsto_approx : ∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.some_spec.2

end sequence

protected theorem strongly_measurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ) :
    StronglyMeasurable f :=
  ⟨hf.approx, hf.tendsto_approx⟩

theorem exists_set_sigma_finite [Zero β] [TopologicalSpace β] [T2Space β] (hf : FinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ (∀, ∀ x ∈ tᶜ, ∀, f x = 0) ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩
  let T := fun n => support (fs n)
  have hT_meas : ∀ n, MeasurableSet (T n) := fun n => simple_func.measurable_set_support (fs n)
  let t := ⋃ n, T n
  refine' ⟨t, MeasurableSet.Union hT_meas, _, _⟩
  · have h_fs_zero : ∀ n, ∀, ∀ x ∈ tᶜ, ∀, fs n x = 0 := by
      intro n x hxt
      rw [Set.mem_compl_iff, Set.mem_Union, not_exists] at hxt
      simpa using hxt n
    refine' fun x hxt => tendsto_nhds_unique (h_approx x) _
    rw [funext fun n => h_fs_zero n x hxt]
    exact tendsto_const_nhds
    
  · refine' ⟨⟨⟨fun n => tᶜ ∪ T n, fun n => trivialₓ, fun n => _, _⟩⟩⟩
    · rw [measure.restrict_apply' (MeasurableSet.Union hT_meas), Set.union_inter_distrib_right, Set.compl_inter_self t,
        Set.empty_union]
      exact (measure_mono (Set.inter_subset_left _ _)).trans_lt (hT_lt_top n)
      
    · rw [← Set.union_Union (tᶜ) T]
      exact Set.compl_union_self _
      
    

/-- A finitely strongly measurable function is measurable. -/
protected theorem measurable [Zero β] [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf : FinStronglyMeasurable f μ) : Measurable f :=
  hf.StronglyMeasurable.Measurable

section Arithmetic

variable [TopologicalSpace β]

protected theorem mul [MonoidWithZeroₓ β] [HasContinuousMul β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f * g) μ := by
  refine' ⟨fun n => hf.approx n * hg.approx n, _, fun x => (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
  intro n
  exact (measure_mono (support_mul_subset_left _ _)).trans_lt (hf.fin_support_approx n)

protected theorem add [AddMonoidₓ β] [HasContinuousAdd β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f + g) μ :=
  ⟨fun n => hf.approx n + hg.approx n, fun n =>
    (measure_mono (Function.support_add _ _)).trans_lt
      ((measure_union_le _ _).trans_lt (Ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

protected theorem neg [AddGroupₓ β] [TopologicalAddGroup β] (hf : FinStronglyMeasurable f μ) :
    FinStronglyMeasurable (-f) μ := by
  refine' ⟨fun n => -hf.approx n, fun n => _, fun x => (hf.tendsto_approx x).neg⟩
  suffices μ (Function.Support fun x => -(hf.approx n) x) < ∞ by
    convert this
  rw [Function.support_neg (hf.approx n)]
  exact hf.fin_support_approx n

protected theorem sub [AddGroupₓ β] [HasContinuousSub β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f - g) μ :=
  ⟨fun n => hf.approx n - hg.approx n, fun n =>
    (measure_mono (Function.support_sub _ _)).trans_lt
      ((measure_union_le _ _).trans_lt (Ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [AddMonoidₓ β] [Monoidₓ 𝕜] [DistribMulAction 𝕜 β]
    [HasContinuousSmul 𝕜 β] (hf : FinStronglyMeasurable f μ) (c : 𝕜) : FinStronglyMeasurable (c • f) μ := by
  refine' ⟨fun n => c • hf.approx n, fun n => _, fun x => (hf.tendsto_approx x).const_smul c⟩
  rw [simple_func.coe_smul]
  refine' (measure_mono (support_smul_subset_right c _)).trans_lt (hf.fin_support_approx n)

end Arithmetic

section Order

variable [TopologicalSpace β] [Zero β]

protected theorem sup [SemilatticeSup β] [HasContinuousSup β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f⊔g) μ := by
  refine'
    ⟨fun n => hf.approx n⊔hg.approx n, fun n => _, fun x => (hf.tendsto_approx x).sup_right_nhds (hg.tendsto_approx x)⟩
  refine' (measure_mono (support_sup _ _)).trans_lt _
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

protected theorem inf [SemilatticeInf β] [HasContinuousInf β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f⊓g) μ := by
  refine'
    ⟨fun n => hf.approx n⊓hg.approx n, fun n => _, fun x => (hf.tendsto_approx x).inf_right_nhds (hg.tendsto_approx x)⟩
  refine' (measure_mono (support_inf _ _)).trans_lt _
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

end Order

end FinStronglyMeasurable

theorem fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite {α β} {f : α → β}
    [TopologicalSpace β] [T2Space β] [Zero β] {m : MeasurableSpace α} {μ : Measure α} :
    FinStronglyMeasurable f μ ↔
      StronglyMeasurable f ∧ ∃ t, MeasurableSet t ∧ (∀, ∀ x ∈ tᶜ, ∀, f x = 0) ∧ SigmaFinite (μ.restrict t) :=
  ⟨fun hf => ⟨hf.StronglyMeasurable, hf.exists_set_sigma_finite⟩, fun hf =>
    hf.1.fin_strongly_measurable_of_set_sigma_finite hf.2.some_spec.1 hf.2.some_spec.2.1 hf.2.some_spec.2.2⟩

theorem ae_fin_strongly_measurable_zero {α β} {m : MeasurableSpace α} (μ : Measure α) [Zero β] [TopologicalSpace β] :
    AeFinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, fin_strongly_measurable_zero, EventuallyEq.rfl⟩

/-! ## Almost everywhere strongly measurable functions -/


theorem ae_strongly_measurable_const {α β} {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] {b : β} :
    AeStronglyMeasurable (fun a : α => b) μ :=
  strongly_measurable_const.AeStronglyMeasurable

@[to_additive]
theorem ae_strongly_measurable_one {α β} {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] [One β] :
    AeStronglyMeasurable (1 : α → β) μ :=
  strongly_measurable_one.AeStronglyMeasurable

@[simp]
theorem Subsingleton.ae_strongly_measurable {m : MeasurableSpace α} [TopologicalSpace β] [Subsingleton β]
    {μ : Measure α} (f : α → β) : AeStronglyMeasurable f μ :=
  (Subsingleton.strongly_measurable f).AeStronglyMeasurable

@[simp]
theorem Subsingleton.ae_strongly_measurable' {m : MeasurableSpace α} [TopologicalSpace β] [Subsingleton α]
    {μ : Measure α} (f : α → β) : AeStronglyMeasurable f μ :=
  (Subsingleton.strongly_measurable' f).AeStronglyMeasurable

@[simp]
theorem ae_strongly_measurable_zero_measure [MeasurableSpace α] [TopologicalSpace β] (f : α → β) :
    AeStronglyMeasurable f (0 : Measure α) := by
  nontriviality α
  inhabit α
  exact ⟨fun x => f default, strongly_measurable_const, rfl⟩

theorem SimpleFunc.ae_strongly_measurable {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] (f : α →ₛ β) :
    AeStronglyMeasurable f μ :=
  f.StronglyMeasurable.AeStronglyMeasurable

namespace AeStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] [TopologicalSpace γ] {f g : α → β}

section Mk

/-- A `strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`strongly_measurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : AeStronglyMeasurable f μ) : α → β :=
  hf.some

theorem strongly_measurable_mk (hf : AeStronglyMeasurable f μ) : StronglyMeasurable (hf.mk f) :=
  hf.some_spec.1

theorem measurable_mk [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] (hf : AeStronglyMeasurable f μ) :
    Measurable (hf.mk f) :=
  hf.strongly_measurable_mk.Measurable

theorem ae_eq_mk (hf : AeStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.some_spec.2

protected theorem ae_measurable {β} [MeasurableSpace β] [TopologicalSpace β] [PseudoMetrizableSpace β] [BorelSpace β]
    {f : α → β} (hf : AeStronglyMeasurable f μ) : AeMeasurable f μ :=
  ⟨hf.mk f, hf.strongly_measurable_mk.Measurable, hf.ae_eq_mk⟩

end Mk

theorem congr (hf : AeStronglyMeasurable f μ) (h : f =ᵐ[μ] g) : AeStronglyMeasurable g μ :=
  ⟨hf.mk f, hf.strongly_measurable_mk, h.symm.trans hf.ae_eq_mk⟩

theorem _root_.ae_strongly_measurable_congr (h : f =ᵐ[μ] g) : AeStronglyMeasurable f μ ↔ AeStronglyMeasurable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

theorem mono_measure {ν : Measure α} (hf : AeStronglyMeasurable f μ) (h : ν ≤ μ) : AeStronglyMeasurable f ν :=
  ⟨hf.mk f, hf.strongly_measurable_mk, Eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩

protected theorem mono' {ν : Measure α} (h : AeStronglyMeasurable f μ) (h' : ν ≪ μ) : AeStronglyMeasurable f ν :=
  ⟨h.mk f, h.strongly_measurable_mk, h' h.ae_eq_mk⟩

theorem mono_set {s t} (h : s ⊆ t) (ht : AeStronglyMeasurable f (μ.restrict t)) :
    AeStronglyMeasurable f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)

protected theorem restrict (hfm : AeStronglyMeasurable f μ) {s} : AeStronglyMeasurable f (μ.restrict s) :=
  hfm.mono_measure Measure.restrict_le_self

theorem ae_mem_imp_eq_mk {s} (h : AeStronglyMeasurable f (μ.restrict s)) : ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk

/-- The composition of a continuous function and an ae strongly measurable function is ae strongly
measurable. -/
theorem _root_.continuous.comp_ae_strongly_measurable {g : β → γ} {f : α → β} (hg : Continuous g)
    (hf : AeStronglyMeasurable f μ) : AeStronglyMeasurable (fun x => g (f x)) μ :=
  ⟨_, hg.comp_strongly_measurable hf.strongly_measurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk g⟩

/-- A continuous function from `α` to `β` is ae strongly measurable when one of the two spaces is
second countable. -/
theorem _root_.continuous.ae_strongly_measurable [TopologicalSpace α] [OpensMeasurableSpace α] [PseudoMetrizableSpace β]
    [SecondCountableTopologyEither α β] (hf : Continuous f) : AeStronglyMeasurable f μ :=
  hf.StronglyMeasurable.AeStronglyMeasurable

protected theorem prod_mk {f : α → β} {g : α → γ} (hf : AeStronglyMeasurable f μ) (hg : AeStronglyMeasurable g μ) :
    AeStronglyMeasurable (fun x => (f x, g x)) μ :=
  ⟨fun x => (hf.mk f x, hg.mk g x), hf.strongly_measurable_mk.prod_mk hg.strongly_measurable_mk,
    hf.ae_eq_mk.prod_mk hg.ae_eq_mk⟩

/-- In a space with second countable topology, measurable implies ae strongly measurable. -/
theorem _root_.measurable.ae_strongly_measurable {m : MeasurableSpace α} {μ : Measure α} [MeasurableSpace β]
    [PseudoMetrizableSpace β] [SecondCountableTopology β] [OpensMeasurableSpace β] (hf : Measurable f) :
    AeStronglyMeasurable f μ :=
  hf.StronglyMeasurable.AeStronglyMeasurable

section Arithmetic

@[to_additive]
protected theorem mul [Mul β] [HasContinuousMul β] (hf : AeStronglyMeasurable f μ) (hg : AeStronglyMeasurable g μ) :
    AeStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.strongly_measurable_mk.mul hg.strongly_measurable_mk, hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[to_additive]
protected theorem mul_const [Mul β] [HasContinuousMul β] (hf : AeStronglyMeasurable f μ) (c : β) :
    AeStronglyMeasurable (fun x => f x * c) μ :=
  hf.mul ae_strongly_measurable_const

@[to_additive]
protected theorem const_mul [Mul β] [HasContinuousMul β] (hf : AeStronglyMeasurable f μ) (c : β) :
    AeStronglyMeasurable (fun x => c * f x) μ :=
  ae_strongly_measurable_const.mul hf

@[to_additive]
protected theorem inv [Groupₓ β] [TopologicalGroup β] (hf : AeStronglyMeasurable f μ) : AeStronglyMeasurable f⁻¹ μ :=
  ⟨(hf.mk f)⁻¹, hf.strongly_measurable_mk.inv, hf.ae_eq_mk.inv⟩

@[to_additive]
protected theorem div [Groupₓ β] [TopologicalGroup β] (hf : AeStronglyMeasurable f μ) (hg : AeStronglyMeasurable g μ) :
    AeStronglyMeasurable (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.strongly_measurable_mk.div hg.strongly_measurable_mk, hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[to_additive]
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [HasSmul 𝕜 β] [HasContinuousSmul 𝕜 β] {f : α → 𝕜} {g : α → β}
    (hf : AeStronglyMeasurable f μ) (hg : AeStronglyMeasurable g μ) : AeStronglyMeasurable (fun x => f x • g x) μ :=
  continuous_smul.comp_ae_strongly_measurable (hf.prod_mk hg)

protected theorem const_smul {𝕜} [HasSmul 𝕜 β] [HasContinuousConstSmul 𝕜 β] (hf : AeStronglyMeasurable f μ) (c : 𝕜) :
    AeStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.strongly_measurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

protected theorem const_smul' {𝕜} [HasSmul 𝕜 β] [HasContinuousConstSmul 𝕜 β] (hf : AeStronglyMeasurable f μ) (c : 𝕜) :
    AeStronglyMeasurable (fun x => c • f x) μ :=
  hf.const_smul c

@[to_additive]
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [HasSmul 𝕜 β] [HasContinuousSmul 𝕜 β] {f : α → 𝕜}
    (hf : AeStronglyMeasurable f μ) (c : β) : AeStronglyMeasurable (fun x => f x • c) μ :=
  continuous_smul.comp_ae_strongly_measurable (hf.prod_mk ae_strongly_measurable_const)

end Arithmetic

section Order

protected theorem sup [SemilatticeSup β] [HasContinuousSup β] (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) : AeStronglyMeasurable (f⊔g) μ :=
  ⟨hf.mk f⊔hg.mk g, hf.strongly_measurable_mk.sup hg.strongly_measurable_mk, hf.ae_eq_mk.sup hg.ae_eq_mk⟩

protected theorem inf [SemilatticeInf β] [HasContinuousInf β] (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) : AeStronglyMeasurable (f⊓g) μ :=
  ⟨hf.mk f⊓hg.mk g, hf.strongly_measurable_mk.inf hg.strongly_measurable_mk, hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoidₓ

variable {M : Type _} [Monoidₓ M] [TopologicalSpace M] [HasContinuousMul M]

@[to_additive]
theorem _root_.list.ae_strongly_measurable_prod' (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, AeStronglyMeasurable f μ) :
    AeStronglyMeasurable l.Prod μ := by
  induction' l with f l ihl
  · exact ae_strongly_measurable_one
    
  rw [List.forall_mem_consₓ] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)

@[to_additive]
theorem _root_.list.ae_strongly_measurable_prod (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, AeStronglyMeasurable f μ) :
    AeStronglyMeasurable (fun x => (l.map fun f : α → M => f x).Prod) μ := by
  simpa only [Pi.list_prod_apply] using l.ae_strongly_measurable_prod' hl

end Monoidₓ

section CommMonoidₓ

variable {M : Type _} [CommMonoidₓ M] [TopologicalSpace M] [HasContinuousMul M]

@[to_additive]
theorem _root_.multiset.ae_strongly_measurable_prod' (l : Multiset (α → M))
    (hl : ∀, ∀ f ∈ l, ∀, AeStronglyMeasurable f μ) : AeStronglyMeasurable l.Prod μ := by
  rcases l with ⟨l⟩
  simpa using
    l.ae_strongly_measurable_prod'
      (by
        simpa using hl)

@[to_additive]
theorem _root_.multiset.ae_strongly_measurable_prod (s : Multiset (α → M))
    (hs : ∀, ∀ f ∈ s, ∀, AeStronglyMeasurable f μ) :
    AeStronglyMeasurable (fun x => (s.map fun f : α → M => f x).Prod) μ := by
  simpa only [Pi.multiset_prod_apply] using s.ae_strongly_measurable_prod' hs

@[to_additive]
theorem _root_.finset.ae_strongly_measurable_prod' {ι : Type _} {f : ι → α → M} (s : Finset ι)
    (hf : ∀, ∀ i ∈ s, ∀, AeStronglyMeasurable (f i) μ) : AeStronglyMeasurable (∏ i in s, f i) μ :=
  (Multiset.ae_strongly_measurable_prod' _) fun g hg =>
    let ⟨i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive]
theorem _root_.finset.ae_strongly_measurable_prod {ι : Type _} {f : ι → α → M} (s : Finset ι)
    (hf : ∀, ∀ i ∈ s, ∀, AeStronglyMeasurable (f i) μ) : AeStronglyMeasurable (fun a => ∏ i in s, f i a) μ := by
  simpa only [Finset.prod_apply] using s.ae_strongly_measurable_prod' hf

end CommMonoidₓ

section SecondCountableAeStronglyMeasurable

variable [MeasurableSpace β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
theorem _root_.ae_measurable.ae_strongly_measurable [PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] (hf : AeMeasurable f μ) : AeStronglyMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk.StronglyMeasurable, hf.ae_eq_mk⟩

theorem _root_.ae_strongly_measurable_id {α : Type _} [TopologicalSpace α] [PseudoMetrizableSpace α]
    {m : MeasurableSpace α} [OpensMeasurableSpace α] [SecondCountableTopology α] {μ : Measure α} :
    AeStronglyMeasurable (id : α → α) μ :=
  ae_measurable_id.AeStronglyMeasurable

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem _root_.ae_strongly_measurable_iff_ae_measurable [PseudoMetrizableSpace β] [BorelSpace β]
    [SecondCountableTopology β] : AeStronglyMeasurable f μ ↔ AeMeasurable f μ :=
  ⟨fun h => h.AeMeasurable, fun h => h.AeStronglyMeasurable⟩

end SecondCountableAeStronglyMeasurable

protected theorem dist {β : Type _} [PseudoMetricSpace β] {f g : α → β} (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) : AeStronglyMeasurable (fun x => dist (f x) (g x)) μ :=
  continuous_dist.comp_ae_strongly_measurable (hf.prod_mk hg)

protected theorem norm {β : Type _} [NormedGroup β] {f : α → β} (hf : AeStronglyMeasurable f μ) :
    AeStronglyMeasurable (fun x => ∥f x∥) μ :=
  continuous_norm.comp_ae_strongly_measurable hf

protected theorem nnnorm {β : Type _} [NormedGroup β] {f : α → β} (hf : AeStronglyMeasurable f μ) :
    AeStronglyMeasurable (fun x => ∥f x∥₊) μ :=
  continuous_nnnorm.comp_ae_strongly_measurable hf

protected theorem ennnorm {β : Type _} [NormedGroup β] {f : α → β} (hf : AeStronglyMeasurable f μ) :
    AeMeasurable (fun a => (∥f a∥₊ : ℝ≥0∞)) μ :=
  (Ennreal.continuous_coe.comp_ae_strongly_measurable hf.nnnorm).AeMeasurable

protected theorem edist {β : Type _} [NormedGroup β] {f g : α → β} (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) : AeMeasurable (fun a => edist (f a) (g a)) μ :=
  (continuous_edist.comp_ae_strongly_measurable (hf.prod_mk hg)).AeMeasurable

protected theorem real_to_nnreal {f : α → ℝ} (hf : AeStronglyMeasurable f μ) :
    AeStronglyMeasurable (fun x => (f x).toNnreal) μ :=
  continuous_real_to_nnreal.comp_ae_strongly_measurable hf

section

variable {𝕜 : Type _} {E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

protected theorem re {f : α → 𝕜} (hf : AeStronglyMeasurable f μ) : AeStronglyMeasurable (fun x => IsROrC.re (f x)) μ :=
  IsROrC.continuous_re.comp_ae_strongly_measurable hf

protected theorem im {f : α → 𝕜} (hf : AeStronglyMeasurable f μ) : AeStronglyMeasurable (fun x => IsROrC.im (f x)) μ :=
  IsROrC.continuous_im.comp_ae_strongly_measurable hf

protected theorem inner {m : MeasurableSpace α} {μ : Measure α} {f g : α → E} (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) : AeStronglyMeasurable (fun x => ⟪f x, g x⟫) μ :=
  continuous_inner.comp_ae_strongly_measurable (hf.prod_mk hg)

end

theorem _root_.ae_strongly_measurable_indicator_iff [Zero β] {s : Set α} (hs : MeasurableSet s) :
    AeStronglyMeasurable (indicatorₓ s f) μ ↔ AeStronglyMeasurable f (μ.restrict s) := by
  constructor
  · intro h
    exact (h.mono_measure measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
    
  · intro h
    refine' ⟨indicator s (h.mk f), h.strongly_measurable_mk.indicator hs, _⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict (sᶜ)] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B
    

protected theorem indicator [Zero β] (hfm : AeStronglyMeasurable f μ) {s : Set α} (hs : MeasurableSet s) :
    AeStronglyMeasurable (s.indicator f) μ :=
  (ae_strongly_measurable_indicator_iff hs).mpr hfm.restrict

theorem _root_.ae_strongly_measurable_of_ae_strongly_measurable_trim {α} {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m0) {f : α → β} (hf : AeStronglyMeasurable f (μ.trim hm)) : AeStronglyMeasurable f μ :=
  ⟨hf.mk f, StronglyMeasurable.mono hf.strongly_measurable_mk hm, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

theorem comp_ae_measurable {γ : Type _} {mγ : MeasurableSpace γ} {mα : MeasurableSpace α} {f : γ → α} {μ : Measure γ}
    (hg : AeStronglyMeasurable g (Measure.map f μ)) (hf : AeMeasurable f μ) : AeStronglyMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.strongly_measurable_mk.comp_measurable hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (hg.mk g))⟩

theorem comp_measurable {γ : Type _} {mγ : MeasurableSpace γ} {mα : MeasurableSpace α} {f : γ → α} {μ : Measure γ}
    (hg : AeStronglyMeasurable g (Measure.map f μ)) (hf : Measurable f) : AeStronglyMeasurable (g ∘ f) μ :=
  hg.comp_ae_measurable hf.AeMeasurable

theorem comp_measurable' {γ : Type _} {mγ : MeasurableSpace γ} {mα : MeasurableSpace α} {f : γ → α} {μ : Measure γ}
    {ν : Measure α} (hg : AeStronglyMeasurable g ν) (hf : Measurable f) (h : μ.map f ≪ ν) :
    AeStronglyMeasurable (g ∘ f) μ :=
  (hg.mono' h).comp_measurable hf

theorem is_separable_ae_range (hf : AeStronglyMeasurable f μ) : ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t := by
  refine' ⟨range (hf.mk f), hf.strongly_measurable_mk.is_separable_range, _⟩
  filter_upwards [hf.ae_eq_mk] with x hx
  simp [← hx]

/-- A function is almost everywhere strongly measurable if and only if it is almost everywhere
measurable, and up to a zero measure set its range is contained in a separable set. -/
theorem _root_.ae_strongly_measurable_iff_ae_measurable_separable [PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β] : AeStronglyMeasurable f μ ↔ AeMeasurable f μ ∧ ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t := by
  refine' ⟨fun H => ⟨H.AeMeasurable, H.is_separable_ae_range⟩, _⟩
  rintro ⟨H, ⟨t, t_sep, ht⟩⟩
  rcases eq_empty_or_nonempty t with (rfl | h₀)
  · simp only [← mem_empty_eq, ← eventually_false_iff_eq_bot, ← ae_eq_bot] at ht
    rw [ht]
    exact ae_strongly_measurable_zero_measure f
    
  · obtain ⟨g, g_meas, gt, fg⟩ : ∃ g : α → β, Measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g :=
      H.exists_ae_eq_range_subset ht h₀
    refine' ⟨g, _, fg⟩
    exact strongly_measurable_iff_measurable_separable.2 ⟨g_meas, t_sep.mono Gt⟩
    

theorem _root_.measurable_embedding.ae_strongly_measurable_map_iff {γ : Type _} {mγ : MeasurableSpace γ}
    {mα : MeasurableSpace α} {f : γ → α} {μ : Measure γ} (hf : MeasurableEmbedding f) {g : α → β} :
    AeStronglyMeasurable g (Measure.map f μ) ↔ AeStronglyMeasurable (g ∘ f) μ := by
  refine' ⟨fun H => H.comp_measurable hf.measurable, _⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_strongly_measurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 HEq⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[["[", expr β, ",", expr γ, "]"]]
theorem _root_.embedding.ae_strongly_measurable_comp_iff [PseudoMetrizableSpace β] [PseudoMetrizableSpace γ] {g : β → γ}
    {f : α → β} (hg : Embedding g) : AeStronglyMeasurable (fun x => g (f x)) μ ↔ AeStronglyMeasurable f μ := by
  let this := pseudo_metrizable_space_pseudo_metric γ
  trace
    "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[\"[\", expr β, \",\", expr γ, \"]\"]]"
  refine'
    ⟨fun H => ae_strongly_measurable_iff_ae_measurable_separable.2 ⟨_, _⟩, fun H =>
      hg.continuous.comp_ae_strongly_measurable H⟩
  · let G : β → range g := cod_restrict g (range g) mem_range_self
    have hG : ClosedEmbedding G :=
      { hg.cod_restrict _ _ with
        closed_range := by
          convert is_closed_univ
          apply eq_univ_of_forall
          rintro ⟨-, ⟨x, rfl⟩⟩
          exact mem_range_self x }
    have : AeMeasurable (G ∘ f) μ := AeMeasurable.subtype_mk H.ae_measurable
    exact hG.measurable_embedding.ae_measurable_comp_iff.1 this
    
  · rcases(ae_strongly_measurable_iff_ae_measurable_separable.1 H).2 with ⟨t, ht, h't⟩
    exact ⟨g ⁻¹' t, hg.is_separable_preimage ht, h't⟩
    

theorem _root_.measure_theory.measure_preserving.ae_strongly_measurable_comp_iff {β : Type _} {f : α → β}
    {mα : MeasurableSpace α} {μa : Measure α} {mβ : MeasurableSpace β} {μb : Measure β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) {g : β → γ} : AeStronglyMeasurable (g ∘ f) μa ↔ AeStronglyMeasurable g μb := by
  rw [← hf.map_eq, h₂.ae_strongly_measurable_map_iff]

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]
/-- An almost everywhere sequential limit of almost everywhere strongly measurable functions is
almost everywhere strongly measurable. -/
theorem _root_.ae_strongly_measurable_of_tendsto_ae {ι : Type _} [PseudoMetrizableSpace β] (u : Filter ι) [NeBot u]
    [IsCountablyGenerated u] {f : ι → α → β} {g : α → β} (hf : ∀ i, AeStronglyMeasurable (f i) μ)
    (lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) : AeStronglyMeasurable g μ := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]"
  refine' ae_strongly_measurable_iff_ae_measurable_separable.2 ⟨_, _⟩
  · exact ae_measurable_of_tendsto_metrizable_ae _ (fun n => (hf n).AeMeasurable) limₓ
    
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : ∀ n : ℕ, ∃ t : Set β, IsSeparable t ∧ f (v n) ⁻¹' t ∈ μ.ae := fun n =>
      (ae_strongly_measurable_iff_ae_measurable_separable.1 (hf (v n))).2
    choose t t_sep ht using this
    refine' ⟨Closure (⋃ i, t i), (is_separable_Union fun i => t_sep i).closure, _⟩
    filter_upwards [ae_all_iff.2 ht, limₓ] with x hx h'x
    apply mem_closure_of_tendsto (h'x.comp hv)
    apply eventually_of_forall fun n => _
    apply mem_Union_of_mem n
    exact hx n
    

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]
/-- If a sequence of almost everywhere strongly measurable functions converges almost everywhere,
one can select a strongly measurable function as the almost everywhere limit. -/
theorem _root_.exists_strongly_measurable_limit_of_tendsto_ae [PseudoMetrizableSpace β] {f : ℕ → α → β}
    (hf : ∀ n, AeStronglyMeasurable (f n) μ) (h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : β, Tendsto (fun n => f n x) atTop (𝓝 l)) :
    ∃ (f_lim : α → β)(hf_lim_meas : StronglyMeasurable f_lim), ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)) :=
  by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]"
  obtain ⟨g, g_meas, hg⟩ : ∃ (g : α → β)(g_meas : Measurable g), ∀ᵐ x ∂μ, tendsto (fun n => f n x) at_top (𝓝 (g x)) :=
    measurable_limit_of_tendsto_metrizable_ae (fun n => (hf n).AeMeasurable) h_ae_tendsto
  have Hg : ae_strongly_measurable g μ := ae_strongly_measurable_of_tendsto_ae _ hf hg
  refine' ⟨Hg.mk g, Hg.strongly_measurable_mk, _⟩
  filter_upwards [hg, Hg.ae_eq_mk] with x hx h'x
  rwa [h'x] at hx

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]
theorem sum_measure [PseudoMetrizableSpace β] {m : MeasurableSpace α} {μ : ι → Measure α}
    (h : ∀ i, AeStronglyMeasurable f (μ i)) : AeStronglyMeasurable f (Measure.sum μ) := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]"
  refine' ae_strongly_measurable_iff_ae_measurable_separable.2 ⟨AeMeasurable.sum_measure fun i => (h i).AeMeasurable, _⟩
  have A : ∀ i : ι, ∃ t : Set β, IsSeparable t ∧ f ⁻¹' t ∈ (μ i).ae := fun i =>
    (ae_strongly_measurable_iff_ae_measurable_separable.1 (h i)).2
  choose t t_sep ht using A
  refine' ⟨⋃ i, t i, is_separable_Union t_sep, _⟩
  simp only [← measure.ae_sum_eq, ← mem_Union, ← eventually_supr]
  intro i
  filter_upwards [ht i] with x hx
  exact ⟨i, hx⟩

@[simp]
theorem _root_.ae_strongly_measurable_sum_measure_iff [PseudoMetrizableSpace β] {m : MeasurableSpace α}
    {μ : ι → Measure α} : AeStronglyMeasurable f (Sum μ) ↔ ∀ i, AeStronglyMeasurable f (μ i) :=
  ⟨fun h i => h.mono_measure (Measure.le_sum _ _), sum_measure⟩

@[simp]
theorem _root_.ae_strongly_measurable_add_measure_iff [PseudoMetrizableSpace β] {ν : Measure α} :
    AeStronglyMeasurable f (μ + ν) ↔ AeStronglyMeasurable f μ ∧ AeStronglyMeasurable f ν := by
  rw [← sum_cond, ae_strongly_measurable_sum_measure_iff, Bool.forall_bool, And.comm]
  rfl

theorem add_measure [PseudoMetrizableSpace β] {ν : Measure α} {f : α → β} (hμ : AeStronglyMeasurable f μ)
    (hν : AeStronglyMeasurable f ν) : AeStronglyMeasurable f (μ + ν) :=
  ae_strongly_measurable_add_measure_iff.2 ⟨hμ, hν⟩

protected theorem Union [PseudoMetrizableSpace β] {s : ι → Set α} (h : ∀ i, AeStronglyMeasurable f (μ.restrict (s i))) :
    AeStronglyMeasurable f (μ.restrict (⋃ i, s i)) :=
  (sum_measure h).mono_measure <| restrict_Union_le

@[simp]
theorem _root_.ae_strongly_measurable_Union_iff [PseudoMetrizableSpace β] {s : ι → Set α} :
    AeStronglyMeasurable f (μ.restrict (⋃ i, s i)) ↔ ∀ i, AeStronglyMeasurable f (μ.restrict (s i)) :=
  ⟨fun h i => h.mono_measure <| restrict_mono (subset_Union _ _) le_rfl, AeStronglyMeasurable.Union⟩

@[simp]
theorem _root_.ae_strongly_measurable_union_iff [PseudoMetrizableSpace β] {s t : Set α} :
    AeStronglyMeasurable f (μ.restrict (s ∪ t)) ↔
      AeStronglyMeasurable f (μ.restrict s) ∧ AeStronglyMeasurable f (μ.restrict t) :=
  by
  simp only [← union_eq_Union, ← ae_strongly_measurable_Union_iff, ← Bool.forall_bool, ← cond, ← And.comm]

theorem smul_measure {R : Type _} [Monoidₓ R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : AeStronglyMeasurable f μ) (c : R) : AeStronglyMeasurable f (c • μ) :=
  ⟨h.mk f, h.strongly_measurable_mk, ae_smul_measure h.ae_eq_mk c⟩

section NormedSpace

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] [CompleteSpace 𝕜]

variable {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

theorem _root_.ae_strongly_measurable_smul_const_iff {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    AeStronglyMeasurable (fun x => f x • c) μ ↔ AeStronglyMeasurable f μ :=
  (closed_embedding_smul_left hc).toEmbedding.ae_strongly_measurable_comp_iff

end NormedSpace

section MulAction

variable {G : Type _} [Groupₓ G] [MulAction G β] [HasContinuousConstSmul G β]

theorem _root_.ae_strongly_measurable_const_smul_iff (c : G) :
    AeStronglyMeasurable (fun x => c • f x) μ ↔ AeStronglyMeasurable f μ :=
  ⟨fun h => by
    simpa only [← inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩

variable {G₀ : Type _} [GroupWithZeroₓ G₀] [MulAction G₀ β] [HasContinuousConstSmul G₀ β]

theorem _root_.ae_strongly_measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AeStronglyMeasurable (fun x => c • f x) μ ↔ AeStronglyMeasurable f μ := by
  refine' ⟨fun h => _, fun h => h.const_smul c⟩
  convert h.const_smul' c⁻¹
  simp [← smul_smul, ← inv_mul_cancel hc]

end MulAction

section ContinuousLinearMapNondiscreteNormedField

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜]

variable {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F]

variable {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G]

theorem _root_.strongly_measurable.apply_continuous_linear_map {m : MeasurableSpace α} {φ : α → F →L[𝕜] E}
    (hφ : StronglyMeasurable φ) (v : F) : StronglyMeasurable fun a => φ a v :=
  (ContinuousLinearMap.apply 𝕜 E v).Continuous.comp_strongly_measurable hφ

theorem apply_continuous_linear_map {φ : α → F →L[𝕜] E} (hφ : AeStronglyMeasurable φ μ) (v : F) :
    AeStronglyMeasurable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 E v).Continuous.comp_ae_strongly_measurable hφ

theorem _root_.continuous_linear_map.ae_strongly_measurable_comp₂ (L : E →L[𝕜] F →L[𝕜] G) {f : α → E} {g : α → F}
    (hf : AeStronglyMeasurable f μ) (hg : AeStronglyMeasurable g μ) : AeStronglyMeasurable (fun x => L (f x) (g x)) μ :=
  L.continuous₂.comp_ae_strongly_measurable <| hf.prod_mk hg

end ContinuousLinearMapNondiscreteNormedField

theorem _root_.ae_strongly_measurable_with_density_iff {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {f : α → ℝ≥0 }
    (hf : Measurable f) {g : α → E} :
    AeStronglyMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔ AeStronglyMeasurable (fun x => (f x : ℝ) • g x) μ :=
  by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurable_set_singleton 0)).compl
    refine' ⟨fun x => (f x : ℝ) • g' x, hf.coe_nnreal_real.strongly_measurable.smul g'meas, _⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x ≠ 0 }
    · rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg'] with a ha h'a
      have : (f a : ℝ≥0∞) ≠ 0 := by
        simpa only [← Ne.def, ← Ennreal.coe_eq_zero] using h'a
      rw [ha this]
      
    · filter_upwards [ae_restrict_mem A.compl] with x hx
      simp only [← not_not, ← mem_set_of_eq, ← mem_compl_eq] at hx
      simp [← hx]
      
    
  · rintro ⟨g', g'meas, hg'⟩
    refine' ⟨fun x => (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.strongly_measurable.smul g'meas, _⟩
    rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg'] with x hx h'x
    rw [← hx, smul_smul, _root_.inv_mul_cancel, one_smul]
    simp only [← Ne.def, ← Ennreal.coe_eq_zero] at h'x
    simpa only [← Nnreal.coe_eq_zero, ← Ne.def] using h'x
    

end AeStronglyMeasurable

/-! ## Almost everywhere finitely strongly measurable functions -/


namespace AeFinStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] {f g : α → β}

section Mk

variable [Zero β]

/-- A `fin_strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`fin_strongly_measurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : AeFinStronglyMeasurable f μ) : α → β :=
  hf.some

theorem fin_strongly_measurable_mk (hf : AeFinStronglyMeasurable f μ) : FinStronglyMeasurable (hf.mk f) μ :=
  hf.some_spec.1

theorem ae_eq_mk (hf : AeFinStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.some_spec.2

protected theorem ae_measurable {β} [Zero β] [MeasurableSpace β] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [BorelSpace β] {f : α → β} (hf : AeFinStronglyMeasurable f μ) : AeMeasurable f μ :=
  ⟨hf.mk f, hf.fin_strongly_measurable_mk.Measurable, hf.ae_eq_mk⟩

end Mk

section Arithmetic

protected theorem mul [MonoidWithZeroₓ β] [HasContinuousMul β] (hf : AeFinStronglyMeasurable f μ)
    (hg : AeFinStronglyMeasurable g μ) : AeFinStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.fin_strongly_measurable_mk.mul hg.fin_strongly_measurable_mk, hf.ae_eq_mk.mul hg.ae_eq_mk⟩

protected theorem add [AddMonoidₓ β] [HasContinuousAdd β] (hf : AeFinStronglyMeasurable f μ)
    (hg : AeFinStronglyMeasurable g μ) : AeFinStronglyMeasurable (f + g) μ :=
  ⟨hf.mk f + hg.mk g, hf.fin_strongly_measurable_mk.add hg.fin_strongly_measurable_mk, hf.ae_eq_mk.add hg.ae_eq_mk⟩

protected theorem neg [AddGroupₓ β] [TopologicalAddGroup β] (hf : AeFinStronglyMeasurable f μ) :
    AeFinStronglyMeasurable (-f) μ :=
  ⟨-hf.mk f, hf.fin_strongly_measurable_mk.neg, hf.ae_eq_mk.neg⟩

protected theorem sub [AddGroupₓ β] [HasContinuousSub β] (hf : AeFinStronglyMeasurable f μ)
    (hg : AeFinStronglyMeasurable g μ) : AeFinStronglyMeasurable (f - g) μ :=
  ⟨hf.mk f - hg.mk g, hf.fin_strongly_measurable_mk.sub hg.fin_strongly_measurable_mk, hf.ae_eq_mk.sub hg.ae_eq_mk⟩

protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [AddMonoidₓ β] [Monoidₓ 𝕜] [DistribMulAction 𝕜 β]
    [HasContinuousSmul 𝕜 β] (hf : AeFinStronglyMeasurable f μ) (c : 𝕜) : AeFinStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.fin_strongly_measurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

end Arithmetic

section Order

variable [Zero β]

protected theorem sup [SemilatticeSup β] [HasContinuousSup β] (hf : AeFinStronglyMeasurable f μ)
    (hg : AeFinStronglyMeasurable g μ) : AeFinStronglyMeasurable (f⊔g) μ :=
  ⟨hf.mk f⊔hg.mk g, hf.fin_strongly_measurable_mk.sup hg.fin_strongly_measurable_mk, hf.ae_eq_mk.sup hg.ae_eq_mk⟩

protected theorem inf [SemilatticeInf β] [HasContinuousInf β] (hf : AeFinStronglyMeasurable f μ)
    (hg : AeFinStronglyMeasurable g μ) : AeFinStronglyMeasurable (f⊓g) μ :=
  ⟨hf.mk f⊓hg.mk g, hf.fin_strongly_measurable_mk.inf hg.fin_strongly_measurable_mk, hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end Order

variable [Zero β] [T2Space β]

theorem exists_set_sigma_finite (hf : AeFinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ f =ᵐ[μ.restrict (tᶜ)] 0 ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨g, hg, hfg⟩
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigma_finite
  refine' ⟨t, ht, _, htμ⟩
  refine' eventually_eq.trans (ae_restrict_of_ae hfg) _
  rw [eventually_eq, ae_restrict_iff' ht.compl]
  exact eventually_of_forall hgt_zero

/-- A measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`. -/
def SigmaFiniteSet (hf : AeFinStronglyMeasurable f μ) : Set α :=
  hf.exists_set_sigma_finite.some

protected theorem measurable_set (hf : AeFinStronglyMeasurable f μ) : MeasurableSet hf.SigmaFiniteSet :=
  hf.exists_set_sigma_finite.some_spec.1

theorem ae_eq_zero_compl (hf : AeFinStronglyMeasurable f μ) : f =ᵐ[μ.restrict (hf.SigmaFiniteSetᶜ)] 0 :=
  hf.exists_set_sigma_finite.some_spec.2.1

instance sigma_finite_restrict (hf : AeFinStronglyMeasurable f μ) : SigmaFinite (μ.restrict hf.SigmaFiniteSet) :=
  hf.exists_set_sigma_finite.some_spec.2.2

end AeFinStronglyMeasurable

section SecondCountableTopology

variable {G : Type _} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [NormedGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] {f : α → G}

/-- In a space with second countable topology and a sigma-finite measure, `fin_strongly_measurable`
  and `measurable` are equivalent. -/
theorem fin_strongly_measurable_iff_measurable {m0 : MeasurableSpace α} (μ : Measure α) [SigmaFinite μ] :
    FinStronglyMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.Measurable, fun h => (Measurable.strongly_measurable h).FinStronglyMeasurable μ⟩

/-- In a space with second countable topology and a sigma-finite measure,
  `ae_fin_strongly_measurable` and `ae_measurable` are equivalent. -/
theorem ae_fin_strongly_measurable_iff_ae_measurable {m0 : MeasurableSpace α} (μ : Measure α) [SigmaFinite μ] :
    AeFinStronglyMeasurable f μ ↔ AeMeasurable f μ := by
  simp_rw [ae_fin_strongly_measurable, AeMeasurable, fin_strongly_measurable_iff_measurable]

end SecondCountableTopology

theorem measurable_uncurry_of_continuous_of_measurable {α β ι : Type _} [TopologicalSpace ι] [MetrizableSpace ι]
    [MeasurableSpace ι] [SecondCountableTopology ι] [OpensMeasurableSpace ι] {mβ : MeasurableSpace β}
    [TopologicalSpace β] [PseudoMetrizableSpace β] [BorelSpace β] {m : MeasurableSpace α} {u : ι → α → β}
    (hu_cont : ∀ x, Continuous fun i => u i x) (h : ∀ i, Measurable (u i)) : Measurable (Function.uncurry u) := by
  obtain ⟨t_sf, ht_sf⟩ : ∃ t : ℕ → simple_func ι ι, ∀ j x, tendsto (fun n => u (t n j) x) at_top (𝓝 <| u j x) := by
    have h_str_meas : strongly_measurable (id : ι → ι) := strongly_measurable_id
    refine' ⟨h_str_meas.approx, fun j x => _⟩
    exact ((hu_cont x).Tendsto j).comp (h_str_meas.tendsto_approx j)
  let U := fun (n : ℕ) (p : ι × α) => u (t_sf n p.fst) p.snd
  have h_tendsto : tendsto U at_top (𝓝 fun p => u p.fst p.snd) := by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine' measurable_of_tendsto_metrizable (fun n => _) h_tendsto
  have : Encodable (t_sf n).range := Fintype.toEncodable ↥(t_sf n).range
  have h_meas : Measurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd := by
    have :
      (fun p : ↥(t_sf n).range × α => u (↑p.fst) p.snd) =
        (fun p : α × (t_sf n).range => u (↑p.snd) p.fst) ∘ Prod.swap :=
      rfl
    rw [this, @measurable_swap_iff α (↥(t_sf n).range) β m]
    exact measurable_from_prod_encodable fun j => h j
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, simple_func.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine' h_meas.comp (Measurable.prod_mk _ measurable_snd)
  exact ((t_sf n).Measurable.comp measurable_fst).subtype_mk

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]
theorem strongly_measurable_uncurry_of_continuous_of_strongly_measurable {α β ι : Type _} [TopologicalSpace ι]
    [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι] [OpensMeasurableSpace ι] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [MeasurableSpace α] {u : ι → α → β} (hu_cont : ∀ x, Continuous fun i => u i x)
    (h : ∀ i, StronglyMeasurable (u i)) : StronglyMeasurable (Function.uncurry u) := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr β]]"
  obtain ⟨t_sf, ht_sf⟩ : ∃ t : ℕ → simple_func ι ι, ∀ j x, tendsto (fun n => u (t n j) x) at_top (𝓝 <| u j x) := by
    have h_str_meas : strongly_measurable (id : ι → ι) := strongly_measurable_id
    refine' ⟨h_str_meas.approx, fun j x => _⟩
    exact ((hu_cont x).Tendsto j).comp (h_str_meas.tendsto_approx j)
  let U := fun (n : ℕ) (p : ι × α) => u (t_sf n p.fst) p.snd
  have h_tendsto : tendsto U at_top (𝓝 fun p => u p.fst p.snd) := by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine' strongly_measurable_of_tendsto _ (fun n => _) h_tendsto
  have : Encodable (t_sf n).range := Fintype.toEncodable ↥(t_sf n).range
  have h_str_meas : strongly_measurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd := by
    refine' strongly_measurable_iff_measurable_separable.2 ⟨_, _⟩
    · have :
        (fun p : ↥(t_sf n).range × α => u (↑p.fst) p.snd) =
          (fun p : α × (t_sf n).range => u (↑p.snd) p.fst) ∘ Prod.swap :=
        rfl
      rw [this, measurable_swap_iff]
      exact measurable_from_prod_encodable fun j => (h j).Measurable
      
    · have : IsSeparable (⋃ i : (t_sf n).range, range (u i)) := is_separable_Union fun i => (h i).is_separable_range
      apply this.mono
      rintro _ ⟨⟨i, x⟩, rfl⟩
      simp only [← mem_Union, ← mem_range]
      exact ⟨i, x, rfl⟩
      
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, simple_func.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine' h_str_meas.comp_measurable (Measurable.prod_mk _ measurable_snd)
  exact ((t_sf n).Measurable.comp measurable_fst).subtype_mk

end MeasureTheory

