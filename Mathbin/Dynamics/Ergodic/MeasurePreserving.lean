/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.MeasureTheory.Measure.AeMeasurable

/-!
# Measure preserving maps

We say that `f : α → β` is a measure preserving map w.r.t. measures `μ : measure α` and
`ν : measure β` if `f` is measurable and `map f μ = ν`. In this file we define the predicate
`measure_theory.measure_preserving` and prove its basic properties.

We use the term "measure preserving" because in many applications `α = β` and `μ = ν`.

## References

Partially based on
[this](https://www.isa-afp.org/browser_info/current/AFP/Ergodic_Theory/Measure_Preserving_Transformations.html)
Isabelle formalization.

## Tags

measure preserving map, measure
-/


variable {α β γ δ : Type _} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

namespace MeasureTheory

open Measureₓ Function Set

variable {μa : Measure α} {μb : Measure β} {μc : Measure γ} {μd : Measure δ}

/-- `f` is a measure preserving map w.r.t. measures `μa` and `μb` if `f` is measurable
and `map f μa = μb`. -/
@[protect_proj]
structure MeasurePreserving (f : α → β)
  (μa : Measure α := by
    run_tac
      volume_tac)
  (μb : Measure β := by
    run_tac
      volume_tac) :
  Prop where
  Measurable : Measurable f
  map_eq : map f μa = μb

protected theorem _root_.measurable.measure_preserving {f : α → β} (h : Measurable f) (μa : Measure α) :
    MeasurePreserving f μa (map f μa) :=
  ⟨h, rfl⟩

namespace MeasurePreserving

protected theorem id (μ : Measure α) : MeasurePreserving id μ μ :=
  ⟨measurable_id, map_id⟩

protected theorem ae_measurable {f : α → β} (hf : MeasurePreserving f μa μb) : AeMeasurable f μa :=
  hf.1.AeMeasurable

theorem symm (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving e μa μb) :
    MeasurePreserving e.symm μb μa :=
  ⟨e.symm.Measurable, by
    rw [← h.map_eq, map_map e.symm.measurable e.measurable, e.symm_comp_self, map_id]⟩

theorem restrict_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : MeasurableSet s) :
    MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.Measurable, by
    rw [← hf.map_eq, restrict_map hf.measurable hs]⟩

theorem restrict_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) (s : Set β) :
    MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.Measurable, by
    rw [← hf.map_eq, h₂.restrict_map]⟩

theorem restrict_image_emb {f : α → β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) (s : Set α) :
    MeasurePreserving f (μa.restrict s) (μb.restrict (f '' s)) := by
  simpa only [← preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)

theorem ae_measurable_comp_iff {f : α → β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) {g : β → γ} :
    AeMeasurable (g ∘ f) μa ↔ AeMeasurable g μb := by
  rw [← hf.map_eq, h₂.ae_measurable_map_iff]

protected theorem quasi_measure_preserving {f : α → β} (hf : MeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa μb :=
  ⟨hf.1, hf.2.AbsolutelyContinuous⟩

theorem comp {g : β → γ} {f : α → β} (hg : MeasurePreserving g μb μc) (hf : MeasurePreserving f μa μb) :
    MeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.1.comp hf.1, by
    rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩

protected theorem sigma_finite {f : α → β} (hf : MeasurePreserving f μa μb) [SigmaFinite μb] : SigmaFinite μa :=
  SigmaFinite.of_map μa hf.AeMeasurable
    (by
      rwa [hf.map_eq])

theorem measure_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : MeasurableSet s) :
    μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq, map_apply hf.1 hs]

theorem measure_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb) (hfe : MeasurableEmbedding f) (s : Set β) :
    μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq, hfe.map_apply]

protected theorem iterate {f : α → α} (hf : MeasurePreserving f μa μa) : ∀ n, MeasurePreserving (f^[n]) μa μa
  | 0 => MeasurePreserving.id μa
  | n + 1 => (iterate n).comp hf

variable {μ : Measure α} {f : α → α} {s : Set α}

/-- If `μ univ < n * μ s` and `f` is a map preserving measure `μ`,
then for some `x ∈ s` and `0 < m < n`, `f^[m] x ∈ s`. -/
theorem exists_mem_image_mem_of_volume_lt_mul_volume (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) {n : ℕ}
    (hvol : μ (Univ : Set α) < n * μ s) : ∃ x ∈ s, ∃ m ∈ Ioo 0 n, (f^[m]) x ∈ s := by
  have A : ∀ m, MeasurableSet (f^[m] ⁻¹' s) := fun m => (hf.iterate m).Measurable hs
  have B : ∀ m, μ (f^[m] ⁻¹' s) = μ s := fun m => (hf.iterate m).measure_preimage hs
  have : μ (univ : Set α) < (Finset.range n).Sum fun m => μ (f^[m] ⁻¹' s) := by
    simpa only [← B, ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.card_range]
  rcases exists_nonempty_inter_of_measure_univ_lt_sum_measure μ (fun m hm => A m) this with
    ⟨i, hi, j, hj, hij, x, hxi, hxj⟩
  -- without `tactic.skip` Lean closes the extra goal but it takes a long time; not sure why
  wlog (discharger := tactic.skip) hlt : i < j := hij.lt_or_lt using i j, j i
  · simp only [← Set.mem_preimage, ← Finset.mem_range] at hi hj hxi hxj
    refine' ⟨(f^[i]) x, hxi, j - i, ⟨tsub_pos_of_lt hlt, lt_of_le_of_ltₓ (j.sub_le i) hj⟩, _⟩
    rwa [← iterate_add_apply, tsub_add_cancel_of_le hlt.le]
    
  · exact fun hi hj hij hxi hxj => this hj hi hij.symm hxj hxi
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (m «expr ≠ » 0)
/-- A self-map preserving a finite measure is conservative: if `μ s ≠ 0`, then at least one point
`x ∈ s` comes back to `s` under iterations of `f`. Actually, a.e. point of `s` comes back to `s`
infinitely many times, see `measure_theory.measure_preserving.conservative` and theorems about
`measure_theory.conservative`. -/
theorem exists_mem_image_mem [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) (hs' : μ s ≠ 0) :
    ∃ x ∈ s, ∃ (m : _)(_ : m ≠ 0), (f^[m]) x ∈ s := by
  rcases Ennreal.exists_nat_mul_gt hs' (measure_ne_top μ (univ : Set α)) with ⟨N, hN⟩
  rcases hf.exists_mem_image_mem_of_volume_lt_mul_volume hs hN with ⟨x, hx, m, hm, hmx⟩
  exact ⟨x, hx, m, hm.1.ne', hmx⟩

end MeasurePreserving

end MeasureTheory

