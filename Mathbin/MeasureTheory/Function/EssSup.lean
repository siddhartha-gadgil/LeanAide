/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace
import Mathbin.Order.Filter.Ennreal

/-!
# Essential supremum and infimum
We define the essential supremum and infimum of a function `f : α → β` with respect to a measure
`μ` on `α`. The essential supremum is the infimum of the constants `c : β` such that `f x ≤ c`
almost everywhere.

TODO: The essential supremum of functions `α → ℝ≥0∞` is used in particular to define the norm in
the `L∞` space (see measure_theory/lp_space.lean).

There is a different quantity which is sometimes also called essential supremum: the least
upper-bound among measurable functions of a family of measurable functions (in an almost-everywhere
sense). We do not define that quantity here, which is simply the supremum of a map with values in
`α →ₘ[μ] β` (see measure_theory/ae_eq_fun.lean).

## Main definitions

* `ess_sup f μ := μ.ae.limsup f`
* `ess_inf f μ := μ.ae.liminf f`
-/


open MeasureTheory Filter TopologicalSpace

open Ennreal MeasureTheory

variable {α β : Type _} {m : MeasurableSpace α} {μ ν : Measureₓ α}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β]

/-- Essential supremum of `f` with respect to measure `μ`: the smallest `c : β` such that
`f x ≤ c` a.e. -/
def essSup {m : MeasurableSpace α} (f : α → β) (μ : Measureₓ α) :=
  μ.ae.limsup f

/-- Essential infimum of `f` with respect to measure `μ`: the greatest `c : β` such that
`c ≤ f x` a.e. -/
def essInf {m : MeasurableSpace α} (f : α → β) (μ : Measureₓ α) :=
  μ.ae.liminf f

theorem ess_sup_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essSup f μ = essSup g μ :=
  limsup_congr hfg

theorem ess_inf_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essInf f μ = essInf g μ :=
  @ess_sup_congr_ae α βᵒᵈ _ _ _ _ _ hfg

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder β]

theorem ess_sup_eq_Inf {m : MeasurableSpace α} (μ : Measureₓ α) (f : α → β) :
    essSup f μ = inf { a | μ { x | a < f x } = 0 } := by
  dsimp' [← essSup, ← limsup, ← Limsup]
  congr
  ext a
  simp [← eventually_map, ← ae_iff]

end ConditionallyCompleteLinearOrder

section CompleteLattice

variable [CompleteLattice β]

@[simp]
theorem ess_sup_measure_zero {m : MeasurableSpace α} {f : α → β} : essSup f (0 : Measureₓ α) = ⊥ :=
  le_bot_iff.mp
    (Inf_le
      (by
        simp [← Set.mem_set_of_eq, ← eventually_le, ← ae_iff]))

@[simp]
theorem ess_inf_measure_zero {m : MeasurableSpace α} {f : α → β} : essInf f (0 : Measureₓ α) = ⊤ :=
  @ess_sup_measure_zero α βᵒᵈ _ _ _

theorem ess_sup_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : essSup f μ ≤ essSup g μ :=
  limsup_le_limsup hfg

theorem ess_inf_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : essInf f μ ≤ essInf g μ :=
  liminf_le_liminf hfg

theorem ess_sup_const (c : β) (hμ : μ ≠ 0) : essSup (fun x : α => c) μ = c := by
  have hμ_ne_bot : μ.ae.ne_bot := by
    rwa [ne_bot_iff, Ne.def, ae_eq_bot]
  exact limsup_const c

theorem ess_sup_le_of_ae_le {f : α → β} (c : β) (hf : f ≤ᵐ[μ] fun _ => c) : essSup f μ ≤ c := by
  refine' (ess_sup_mono_ae hf).trans _
  by_cases' hμ : μ = 0
  · simp [← hμ]
    
  · rwa [ess_sup_const]
    

theorem ess_inf_const (c : β) (hμ : μ ≠ 0) : essInf (fun x : α => c) μ = c :=
  @ess_sup_const α βᵒᵈ _ _ _ _ hμ

theorem le_ess_inf_of_ae_le {f : α → β} (c : β) (hf : (fun _ => c) ≤ᵐ[μ] f) : c ≤ essInf f μ :=
  @ess_sup_le_of_ae_le α βᵒᵈ _ _ _ _ c hf

theorem ess_sup_const_bot : essSup (fun x : α => (⊥ : β)) μ = (⊥ : β) :=
  limsup_const_bot

theorem ess_inf_const_top : essInf (fun x : α => (⊤ : β)) μ = (⊤ : β) :=
  liminf_const_top

theorem OrderIso.ess_sup_apply {m : MeasurableSpace α} {γ} [CompleteLattice γ] (f : α → β) (μ : Measureₓ α)
    (g : β ≃o γ) : g (essSup f μ) = essSup (fun x => g (f x)) μ := by
  refine' OrderIso.limsup_apply g _ _ _ _
  all_goals
    run_tac
      is_bounded_default

theorem OrderIso.ess_inf_apply {m : MeasurableSpace α} {γ} [CompleteLattice γ] (f : α → β) (μ : Measureₓ α)
    (g : β ≃o γ) : g (essInf f μ) = essInf (fun x => g (f x)) μ :=
  @OrderIso.ess_sup_apply α βᵒᵈ _ _ γᵒᵈ _ _ _ g.dual

theorem ess_sup_mono_measure {f : α → β} (hμν : ν ≪ μ) : essSup f ν ≤ essSup f μ := by
  refine' limsup_le_limsup_of_le (measure.ae_le_iff_absolutely_continuous.mpr hμν) _ _
  all_goals
    run_tac
      is_bounded_default

theorem ess_sup_mono_measure' {α : Type _} {β : Type _} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α}
    [CompleteLattice β] {f : α → β} (hμν : ν ≤ μ) : essSup f ν ≤ essSup f μ :=
  ess_sup_mono_measure (Measure.absolutely_continuous_of_le hμν)

theorem ess_inf_antitone_measure {f : α → β} (hμν : μ ≪ ν) : essInf f ν ≤ essInf f μ := by
  refine' liminf_le_liminf_of_le (measure.ae_le_iff_absolutely_continuous.mpr hμν) _ _
  all_goals
    run_tac
      is_bounded_default

theorem ess_sup_smul_measure {f : α → β} {c : ℝ≥0∞} (hc : c ≠ 0) : essSup f (c • μ) = essSup f μ := by
  simp_rw [essSup]
  suffices h_smul : (c • μ).ae = μ.ae
  · rw [h_smul]
    
  ext1
  simp_rw [mem_ae_iff]
  simp [← hc]

section TopologicalSpace

variable {γ : Type _} {mγ : MeasurableSpace γ} {f : α → γ} {g : γ → β}

include mγ

theorem ess_sup_comp_le_ess_sup_map_measure (hf : AeMeasurable f μ) : essSup (g ∘ f) μ ≤ essSup g (Measure.map f μ) :=
  by
  refine'
    Limsup_le_Limsup_of_le (fun t => _)
      (by
        run_tac
          is_bounded_default)
      (by
        run_tac
          is_bounded_default)
  simp_rw [Filter.mem_map]
  have : g ∘ f ⁻¹' t = f ⁻¹' (g ⁻¹' t) := by
    ext1 x
    simp_rw [Set.mem_preimage]
  rw [this]
  exact fun h => mem_ae_of_mem_ae_map hf h

theorem _root_.measurable_embedding.ess_sup_map_measure (hf : MeasurableEmbedding f) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  refine' le_antisymmₓ _ (ess_sup_comp_le_ess_sup_map_measure hf.measurable.ae_measurable)
  refine'
    Limsup_le_Limsup
      (by
        run_tac
          is_bounded_default)
      (by
        run_tac
          is_bounded_default)
      fun c h_le => _
  rw [eventually_map] at h_le⊢
  exact hf.ae_map_iff.mpr h_le

variable [MeasurableSpace β] [TopologicalSpace β] [SecondCountableTopology β] [OrderClosedTopology β]
  [OpensMeasurableSpace β]

theorem ess_sup_map_measure_of_measurable (hg : Measurable g) (hf : AeMeasurable f μ) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  refine' le_antisymmₓ _ (ess_sup_comp_le_ess_sup_map_measure hf)
  refine'
    Limsup_le_Limsup
      (by
        run_tac
          is_bounded_default)
      (by
        run_tac
          is_bounded_default)
      fun c h_le => _
  rw [eventually_map] at h_le⊢
  rw [ae_map_iff hf (measurable_set_le hg measurable_const)]
  exact h_le

theorem ess_sup_map_measure (hg : AeMeasurable g (Measure.map f μ)) (hf : AeMeasurable f μ) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  rw [ess_sup_congr_ae hg.ae_eq_mk, ess_sup_map_measure_of_measurable hg.measurable_mk hf]
  refine' ess_sup_congr_ae _
  have h_eq := ae_of_ae_map hf hg.ae_eq_mk
  rw [← eventually_eq] at h_eq
  exact h_eq.symm

omit mγ

end TopologicalSpace

end CompleteLattice

section CompleteLinearOrder

variable [CompleteLinearOrder β]

theorem ae_lt_of_ess_sup_lt {f : α → β} {x : β} (hf : essSup f μ < x) : ∀ᵐ y ∂μ, f y < x :=
  Filter.eventually_lt_of_limsup_lt hf

theorem ae_lt_of_lt_ess_inf {f : α → β} {x : β} (hf : x < essInf f μ) : ∀ᵐ y ∂μ, x < f y :=
  @ae_lt_of_ess_sup_lt α βᵒᵈ _ _ _ _ _ hf

theorem ess_sup_indicator_eq_ess_sup_restrict [Zero β] {s : Set α} {f : α → β} (hf : 0 ≤ᵐ[μ.restrict s] f)
    (hs : MeasurableSet s) (hs_not_null : μ s ≠ 0) : essSup (s.indicator f) μ = essSup f (μ.restrict s) := by
  refine'
    le_antisymmₓ _
      (Limsup_le_Limsup_of_le (map_restrict_ae_le_map_indicator_ae hs)
        (by
          run_tac
            is_bounded_default)
        (by
          run_tac
            is_bounded_default))
  refine'
    Limsup_le_Limsup
      (by
        run_tac
          is_bounded_default)
      (by
        run_tac
          is_bounded_default)
      fun c h_restrict_le => _
  rw [eventually_map] at h_restrict_le⊢
  rw [ae_restrict_iff' hs] at h_restrict_le
  have hc : 0 ≤ c := by
    suffices ∃ x, 0 ≤ f x ∧ f x ≤ c by
      obtain ⟨x, hx⟩ := this
      exact hx.1.trans hx.2
    refine' frequently.exists _
    · exact μ.ae
      
    rw [eventually_le, ae_restrict_iff' hs] at hf
    have hs' : ∃ᵐ x ∂μ, x ∈ s := by
      contrapose! hs_not_null
      rw [not_frequently, ae_iff] at hs_not_null
      suffices { a : α | ¬a ∉ s } = s by
        rwa [← this]
      simp
    refine' hs'.mp (hf.mp (h_restrict_le.mono fun x hxs_imp_c hxf_nonneg hxs => _))
    rw [Pi.zero_apply] at hxf_nonneg
    exact ⟨hxf_nonneg hxs, hxs_imp_c hxs⟩
  refine' h_restrict_le.mono fun x hxc => _
  by_cases' hxs : x ∈ s
  · simpa [← hxs] using hxc hxs
    
  · simpa [← hxs] using hc
    

end CompleteLinearOrder

namespace Ennreal

variable {f : α → ℝ≥0∞}

theorem ae_le_ess_sup (f : α → ℝ≥0∞) : ∀ᵐ y ∂μ, f y ≤ essSup f μ :=
  eventually_le_limsup f

@[simp]
theorem ess_sup_eq_zero_iff : essSup f μ = 0 ↔ f =ᵐ[μ] 0 :=
  limsup_eq_zero_iff

theorem ess_sup_const_mul {a : ℝ≥0∞} : essSup (fun x : α => a * f x) μ = a * essSup f μ :=
  limsup_const_mul

theorem ess_sup_add_le (f g : α → ℝ≥0∞) : essSup (f + g) μ ≤ essSup f μ + essSup g μ :=
  limsup_add_le f g

theorem ess_sup_liminf_le {ι} [Encodable ι] [LinearOrderₓ ι] (f : ι → α → ℝ≥0∞) :
    essSup (fun x => atTop.liminf fun n => f n x) μ ≤ atTop.liminf fun n => essSup (fun x => f n x) μ := by
  simp_rw [essSup]
  exact Ennreal.limsup_liminf_le_liminf_limsup fun a b => f b a

end Ennreal

