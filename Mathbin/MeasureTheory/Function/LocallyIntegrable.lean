/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.MeasureTheory.Integral.IntegrableOn

/-!
# Locally integrable functions

A function is called *locally integrable* (`measure_theory.locally_integrable`) if it is integrable
on every compact subset of its domain.

This file contains properties of locally integrable functions and of integrability results
on compact sets.

## Main statements

* `continuous.locally_integrable`: A continuous function is locally integrable.

-/


open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace

open TopologicalSpace Interval

variable {X Y E : Type _} [MeasurableSpace X] [TopologicalSpace X]

variable [MeasurableSpace Y] [TopologicalSpace Y]

variable [NormedGroup E] {f : X → E} {μ : Measureₓ X}

namespace MeasureTheory

/-- A function `f : X → E` is locally integrable if it is integrable on all compact sets.
  See `measure_theory.locally_integrable_iff` for the justification of this name. -/
def LocallyIntegrable (f : X → E)
    (μ : Measure X := by
      run_tac
        volume_tac) :
    Prop :=
  ∀ ⦃K⦄, IsCompact K → IntegrableOn f K μ

theorem Integrable.locally_integrable (hf : Integrable f μ) : LocallyIntegrable f μ := fun K hK => hf.IntegrableOn

theorem LocallyIntegrable.ae_strongly_measurable [SigmaCompactSpace X] (hf : LocallyIntegrable f μ) :
    AeStronglyMeasurable f μ := by
  rw [← @restrict_univ _ _ μ, ← Union_compact_covering, ae_strongly_measurable_Union_iff]
  exact fun i => (hf <| is_compact_compact_covering X i).AeStronglyMeasurable

theorem locally_integrable_iff [LocallyCompactSpace X] :
    LocallyIntegrable f μ ↔ ∀ x : X, ∃ U ∈ 𝓝 x, IntegrableOn f U μ := by
  refine' ⟨fun hf x => _, fun hf K hK => _⟩
  · obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x
    exact ⟨K, h2K, hf hK⟩
    
  · refine'
      IsCompact.induction_on hK integrable_on_empty (fun s t hst h => h.mono_set hst)
        (fun s t hs ht => integrable_on_union.mpr ⟨hs, ht⟩) fun x hx => _
    obtain ⟨K, hK, h2K⟩ := hf x
    exact ⟨K, nhds_within_le_nhds hK, h2K⟩
    

section Real

variable [OpensMeasurableSpace X] {A K : Set X} {g g' : X → ℝ}

theorem IntegrableOn.mul_continuous_on_of_subset (hg : IntegrableOn g A μ) (hg' : ContinuousOn g' K)
    (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A ⊆ K) : IntegrableOn (fun x => g x * g' x) A μ := by
  rcases IsCompact.exists_bound_of_continuous_on hK hg' with ⟨C, hC⟩
  rw [integrable_on, ← mem_ℒp_one_iff_integrable] at hg⊢
  have : ∀ᵐ x ∂μ.restrict A, ∥g x * g' x∥ ≤ C * ∥g x∥ := by
    filter_upwards [ae_restrict_mem hA] with x hx
    rw [Real.norm_eq_abs, abs_mul, mul_comm, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right (hC x (hAK hx)) (abs_nonneg _)
  exact
    mem_ℒp.of_le_mul hg
      (hg.ae_strongly_measurable.ae_measurable.mul ((hg'.mono hAK).AeMeasurable hA)).AeStronglyMeasurable this

theorem IntegrableOn.mul_continuous_on [T2Space X] (hg : IntegrableOn g K μ) (hg' : ContinuousOn g' K)
    (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg.mul_continuous_on_of_subset hg' hK.MeasurableSet hK (Subset.refl _)

theorem IntegrableOn.continuous_on_mul_of_subset (hg : ContinuousOn g K) (hg' : IntegrableOn g' A μ) (hK : IsCompact K)
    (hA : MeasurableSet A) (hAK : A ⊆ K) : IntegrableOn (fun x => g x * g' x) A μ := by
  simpa [← mul_comm] using hg'.mul_continuous_on_of_subset hg hA hK hAK

theorem IntegrableOn.continuous_on_mul [T2Space X] (hg : ContinuousOn g K) (hg' : IntegrableOn g' K μ)
    (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  IntegrableOn.continuous_on_mul_of_subset hg hg' hK hK.MeasurableSet Subset.rfl

end Real

end MeasureTheory

open MeasureTheory

/-- If a function is integrable at `𝓝[s] x` for each point `x` of a compact set `s`, then it is
integrable on `s`. -/
theorem IsCompact.integrable_on_of_nhds_within {K : Set X} (hK : IsCompact K)
    (hf : ∀, ∀ x ∈ K, ∀, IntegrableAtFilter f (𝓝[K] x) μ) : IntegrableOn f K μ :=
  IsCompact.induction_on hK integrable_on_empty (fun s t hst ht => ht.mono_set hst) (fun s t hs ht => hs.union ht) hf

section borel

variable [OpensMeasurableSpace X] [MetrizableSpace X] [IsLocallyFiniteMeasure μ]

variable {K : Set X} {a b : X}

/-- A function `f` continuous on a compact set `K` is integrable on this set with respect to any
locally finite measure. -/
theorem ContinuousOn.integrable_on_compact (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ := by
  let this := metrizable_space_metric X
  apply hK.integrable_on_of_nhds_within fun x hx => _
  exact hf.integrable_at_nhds_within_of_is_separable hK.measurable_set hK.is_separable hx

/-- A continuous function `f` is locally integrable with respect to any locally finite measure. -/
theorem Continuous.locally_integrable (hf : Continuous f) : LocallyIntegrable f μ := fun s hs =>
  hf.ContinuousOn.integrable_on_compact hs

theorem ContinuousOn.integrable_on_Icc [Preorderₓ X] [CompactIccSpace X] (hf : ContinuousOn f (Icc a b)) :
    IntegrableOn f (Icc a b) μ :=
  hf.integrable_on_compact is_compact_Icc

theorem Continuous.integrable_on_Icc [Preorderₓ X] [CompactIccSpace X] (hf : Continuous f) :
    IntegrableOn f (Icc a b) μ :=
  hf.LocallyIntegrable is_compact_Icc

theorem Continuous.integrable_on_Ioc [Preorderₓ X] [CompactIccSpace X] (hf : Continuous f) :
    IntegrableOn f (Ioc a b) μ :=
  hf.integrable_on_Icc.mono_set Ioc_subset_Icc_self

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem ContinuousOn.integrable_on_interval [LinearOrderₓ X] [CompactIccSpace X]
    (hf : ContinuousOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    IntegrableOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" μ :=
  hf.integrable_on_Icc

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem Continuous.integrable_on_interval [LinearOrderₓ X] [CompactIccSpace X] (hf : Continuous f) :
    IntegrableOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" μ :=
  hf.integrable_on_Icc

theorem Continuous.integrable_on_interval_oc [LinearOrderₓ X] [CompactIccSpace X] (hf : Continuous f) :
    IntegrableOn f (Ι a b) μ :=
  hf.integrable_on_Ioc

/-- A continuous function with compact support is integrable on the whole space. -/
theorem Continuous.integrable_of_has_compact_support (hf : Continuous f) (hcf : HasCompactSupport f) : Integrable f μ :=
  (integrable_on_iff_integable_of_support_subset (subset_tsupport f) measurable_set_closure).mp <|
    hf.LocallyIntegrable hcf

end borel

section Monotone

variable [BorelSpace X] [MetrizableSpace X] [ConditionallyCompleteLinearOrder X] [ConditionallyCompleteLinearOrder E]
  [OrderTopology X] [OrderTopology E] [SecondCountableTopology E] [IsLocallyFiniteMeasure μ] {s : Set X}

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr E]]
theorem MonotoneOn.integrable_on_compact (hs : IsCompact s) (hmono : MonotoneOn f s) : IntegrableOn f s μ := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr E]]"
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact integrable_on_empty
    
  have hbelow : BddBelow (f '' s) :=
    ⟨f (Inf s), fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono (hs.Inf_mem h) hy (cInf_le hs.bdd_below hy)⟩
  have habove : BddAbove (f '' s) :=
    ⟨f (Sup s), fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono hy (hs.Sup_mem h) (le_cSup hs.bdd_above hy)⟩
  have : Metric.Bounded (f '' s) := Metric.bounded_of_bdd_above_of_bdd_below habove hbelow
  rcases bounded_iff_forall_norm_le.mp this with ⟨C, hC⟩
  refine'
    integrable.mono' (continuous_const.locally_integrable hs)
      (ae_measurable_restrict_of_monotone_on hs.measurable_set hmono).AeStronglyMeasurable
      ((ae_restrict_iff' hs.measurable_set).mpr <| (ae_of_all _) fun y hy => hC (f y) (mem_image_of_mem f hy))

theorem AntitoneOn.integrable_on_compact (hs : IsCompact s) (hanti : AntitoneOn f s) : IntegrableOn f s μ :=
  hanti.dual_right.integrable_on_compact hs

theorem Monotone.locally_integrable (hmono : Monotone f) : LocallyIntegrable f μ := fun s hs =>
  (hmono.MonotoneOn _).integrable_on_compact hs

theorem Antitone.locally_integrable (hanti : Antitone f) : LocallyIntegrable f μ :=
  hanti.dual_right.LocallyIntegrable

end Monotone

