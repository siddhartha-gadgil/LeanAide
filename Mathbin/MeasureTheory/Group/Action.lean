/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.MeasureTheory.Group.MeasurableEquiv
import Mathbin.MeasureTheory.Measure.Regular
import Mathbin.Dynamics.Ergodic.MeasurePreserving
import Mathbin.Dynamics.Minimal

/-!
# Measures invariant under group actions

A measure `μ : measure α` is said to be *invariant* under an action of a group `G` if scalar
multiplication by `c : G` is a measure preserving map for all `c`. In this file we define a
typeclass for measures invariant under action of an (additive or multiplicative) group and prove
some basic properties of such measures.
-/


open Ennreal Nnreal Pointwise TopologicalSpace

open MeasureTheory MeasureTheory.Measure Set Function

namespace MeasureTheory

variable {G M α : Type _}

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`measure_preimage_vadd] []
/-- A measure `μ : measure α` is invariant under an additive action of `M` on `α` if for any
measurable set `s : set α` and `c : M`, the measure of its preimage under `λ x, c +ᵥ x` is equal to
the measure of `s`. -/
class VaddInvariantMeasure (M α : Type _) [HasVadd M α] {_ : MeasurableSpace α} (μ : Measure α) : Prop where
  measure_preimage_vadd : ∀ (c : M) ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c +ᵥ x) ⁻¹' s) = μ s

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`measure_preimage_smul] []
/-- A measure `μ : measure α` is invariant under a multiplicative action of `M` on `α` if for any
measurable set `s : set α` and `c : M`, the measure of its preimage under `λ x, c • x` is equal to
the measure of `s`. -/
@[to_additive]
class SmulInvariantMeasure (M α : Type _) [HasSmul M α] {_ : MeasurableSpace α} (μ : Measure α) : Prop where
  measure_preimage_smul : ∀ (c : M) ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c • x) ⁻¹' s) = μ s

namespace SmulInvariantMeasure

@[to_additive]
instance zero [MeasurableSpace α] [HasSmul M α] : SmulInvariantMeasure M α 0 :=
  ⟨fun _ _ _ => rfl⟩

variable [HasSmul M α] {m : MeasurableSpace α} {μ ν : Measure α}

@[to_additive]
instance add [SmulInvariantMeasure M α μ] [SmulInvariantMeasure M α ν] : SmulInvariantMeasure M α (μ + ν) :=
  ⟨fun c s hs =>
    show _ + _ = _ + _ from congr_arg2ₓ (· + ·) (measure_preimage_smul μ c hs) (measure_preimage_smul ν c hs)⟩

@[to_additive]
instance smul [SmulInvariantMeasure M α μ] (c : ℝ≥0∞) : SmulInvariantMeasure M α (c • μ) :=
  ⟨fun a s hs => show c • _ = c • _ from congr_arg ((· • ·) c) (measure_preimage_smul μ a hs)⟩

@[to_additive]
instance smul_nnreal [SmulInvariantMeasure M α μ] (c : ℝ≥0 ) : SmulInvariantMeasure M α (c • μ) :=
  SmulInvariantMeasure.smul c

end SmulInvariantMeasure

variable (G) {m : MeasurableSpace α} [Groupₓ G] [MulAction G α] [MeasurableSpace G] [HasMeasurableSmul G α] (c : G)
  (μ : Measure α)

/-- Equivalent definitions of a measure invariant under a multiplicative action of a group.

- 0: `smul_invariant_measure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under scalar
     multiplication by `c` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c • s` of `s` under
     scalar multiplication by `c` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, scalar multiplication by `c` maps `μ` to `μ`;

- 6: for any `c : G`, scalar multiplication by `c` is a measure preserving map. -/
@[to_additive]
theorem smul_invariant_measure_tfae :
    Tfae
      [SmulInvariantMeasure G α μ, ∀ (c : G) (s), MeasurableSet s → μ ((· • ·) c ⁻¹' s) = μ s,
        ∀ (c : G) (s), MeasurableSet s → μ (c • s) = μ s, ∀ (c : G) (s), μ ((· • ·) c ⁻¹' s) = μ s,
        ∀ (c : G) (s), μ (c • s) = μ s, ∀ c : G, Measure.map ((· • ·) c) μ = μ,
        ∀ c : G, MeasurePreserving ((· • ·) c) μ μ] :=
  by
  tfae_have 1 ↔ 2
  exact ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 2 → 6
  exact fun H c =>
    ext fun s hs => by
      rw [map_apply (measurable_const_smul c) hs, H _ _ hs]
  tfae_have 6 → 7
  exact fun H c => ⟨measurable_const_smul c, H c⟩
  tfae_have 7 → 4
  exact fun H c => (H c).measure_preimage_emb (measurable_embedding_const_smul c)
  tfae_have 4 → 5
  exact fun H c s => by
    rw [← preimage_smul_inv]
    apply H
  tfae_have 5 → 3
  exact fun H c s hs => H c s
  tfae_have 3 → 2
  · intro H c s hs
    rw [preimage_smul]
    exact H c⁻¹ s hs
    
  tfae_finish

/-- Equivalent definitions of a measure invariant under an additive action of a group.

- 0: `vadd_invariant_measure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under
     vector addition `(+ᵥ) c` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c +ᵥ s` of `s` under
     vector addition `(+ᵥ) c` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, vector addition of `c` maps `μ` to `μ`;

- 6: for any `c : G`, vector addition of `c` is a measure preserving map. -/
add_decl_doc vadd_invariant_measure_tfae

variable {G} [SmulInvariantMeasure G α μ]

@[to_additive]
theorem measure_preserving_smul : MeasurePreserving ((· • ·) c) μ μ :=
  ((smul_invariant_measure_tfae G μ).out 0 6).mp ‹_› c

@[simp, to_additive]
theorem map_smul : map ((· • ·) c) μ = μ :=
  (measure_preserving_smul c μ).map_eq

@[simp, to_additive]
theorem measure_preimage_smul (s : Set α) : μ ((· • ·) c ⁻¹' s) = μ s :=
  ((smul_invariant_measure_tfae G μ).out 0 3).mp ‹_› c s

@[simp, to_additive]
theorem measure_smul_set (s : Set α) : μ (c • s) = μ s :=
  ((smul_invariant_measure_tfae G μ).out 0 4).mp ‹_› c s

variable {μ}

@[to_additive]
theorem NullMeasurableSet.smul {s} (hs : NullMeasurableSet s μ) (c : G) : NullMeasurableSet (c • s) μ := by
  simpa only [preimage_smul_inv] using hs.preimage (measure_preserving_smul _ _).QuasiMeasurePreserving

section IsMinimal

variable (G) [TopologicalSpace α] [HasContinuousConstSmul G α] [MulAction.IsMinimal G α] {K U : Set α}

/-- If measure `μ` is invariant under a group action and is nonzero on a compact set `K`, then it is
positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0` instead of
`μ K ≠ 0`, see `measure_theory.measure_is_open_pos_of_smul_invariant_of_ne_zero`. -/
@[to_additive]
theorem measure_is_open_pos_of_smul_invariant_of_compact_ne_zero (hK : IsCompact K) (hμK : μ K ≠ 0) (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < μ U :=
  let ⟨t, ht⟩ := hK.exists_finite_cover_smul G hU hne
  pos_iff_ne_zero.2 fun hμU =>
    hμK <|
      measure_mono_null ht <|
        (measure_bUnion_null_iff t.countable_to_set).2 fun _ _ => by
          rwa [measure_smul_set]

/-- If measure `μ` is invariant under an additive group action and is nonzero on a compact set `K`,
then it is positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0`
instead of `μ K ≠ 0`, see `measure_theory.measure_is_open_pos_of_vadd_invariant_of_ne_zero`. -/
add_decl_doc measure_is_open_pos_of_vadd_invariant_of_compact_ne_zero

@[to_additive]
theorem is_locally_finite_measure_of_smul_invariant (hU : IsOpen U) (hne : U.Nonempty) (hμU : μ U ≠ ∞) :
    IsLocallyFiniteMeasure μ :=
  ⟨fun x =>
    let ⟨g, hg⟩ := hU.exists_smul_mem G x hne
    ⟨(· • ·) g ⁻¹' U, (hU.Preimage (continuous_id.const_smul _)).mem_nhds hg,
      Ne.lt_top <| by
        rwa [measure_preimage_smul]⟩⟩

variable [Measure.Regular μ]

@[to_additive]
theorem measure_is_open_pos_of_smul_invariant_of_ne_zero (hμ : μ ≠ 0) (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  let ⟨K, hK, hμK⟩ := Regular.exists_compact_not_null.mpr hμ
  measure_is_open_pos_of_smul_invariant_of_compact_ne_zero G hK hμK hU hne

@[to_additive]
theorem measure_pos_iff_nonempty_of_smul_invariant (hμ : μ ≠ 0) (hU : IsOpen U) : 0 < μ U ↔ U.Nonempty :=
  ⟨fun h => nonempty_of_measure_ne_zero h.ne', measure_is_open_pos_of_smul_invariant_of_ne_zero G hμ hU⟩

include G

@[to_additive]
theorem measure_eq_zero_iff_eq_empty_of_smul_invariant (hμ : μ ≠ 0) (hU : IsOpen U) : μ U = 0 ↔ U = ∅ := by
  rw [← not_iff_not, ← Ne.def, ← pos_iff_ne_zero, measure_pos_iff_nonempty_of_smul_invariant G hμ hU, ←
    ne_empty_iff_nonempty]

end IsMinimal

end MeasureTheory

