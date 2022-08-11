/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.MeasureTheory.Measure.OuterMeasure
import Mathbin.Order.Filter.CountableInter
import Mathbin.Data.Set.Accumulate

/-!
# Measure spaces

This file defines measure spaces, the almost-everywhere filter and ae_measurable functions.
See `measure_theory.measure_space` for their properties and for extended documentation.

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

## Implementation notes

Given `μ : measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

See the documentation of `measure_theory.measure_space` for ways to construct measures and proving
that two measure are equal.

A `measure_space` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

This file does not import `measure_theory.measurable_space`, but only `measurable_space_def`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space
-/


noncomputable section

open Classical Set

open Filter hiding map

open Function MeasurableSpace

open Classical TopologicalSpace BigOperators Filter Ennreal Nnreal

variable {α β γ δ ι : Type _}

namespace MeasureTheory

/-- A measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure. -/
structure Measure (α : Type _) [MeasurableSpace α] extends OuterMeasure α where
  m_Union ⦃f : ℕ → Set α⦄ :
    (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) → measure_of (⋃ i, f i) = ∑' i, measure_of (f i)
  trimmed : to_outer_measure.trim = to_outer_measure

/-- Measure projections for a measure space.

For measurable sets this returns the measure assigned by the `measure_of` field in `measure`.
But we can extend this to _all_ sets, but using the outer measure. This gives us monotonicity and
subadditivity for all sets.
-/
instance Measure.hasCoeToFun [MeasurableSpace α] : CoeFun (Measure α) fun _ => Set α → ℝ≥0∞ :=
  ⟨fun m => m.toOuterMeasure⟩

section

variable [MeasurableSpace α] {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

namespace Measureₓ

/-! ### General facts about measures -/


/-- Obtain a measure by giving a countably additive function that sends `∅` to `0`. -/
def ofMeasurable (m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞) (m0 : m ∅ MeasurableSet.empty = 0)
    (mU :
      ∀ ⦃f : ℕ → Set α⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.Union h) = ∑' i, m (f i) (h i)) :
    Measure α :=
  { inducedOuterMeasure m _ m0 with
    m_Union := fun f hf hd =>
      show inducedOuterMeasure m _ m0 (Union f) = ∑' i, inducedOuterMeasure m _ m0 (f i) by
        rw [induced_outer_measure_eq m0 mU, mU hf hd]
        congr
        funext n
        rw [induced_outer_measure_eq m0 mU],
    trimmed :=
      show (inducedOuterMeasure m _ m0).trim = inducedOuterMeasure m _ m0 by
        unfold outer_measure.trim
        congr
        funext s hs
        exact induced_outer_measure_eq m0 mU hs }

theorem of_measurable_apply {m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞} {m0 : m ∅ MeasurableSet.empty = 0}
    {mU :
      ∀ ⦃f : ℕ → Set α⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.Union h) = ∑' i, m (f i) (h i)}
    (s : Set α) (hs : MeasurableSet s) : ofMeasurable m m0 mU s = m s hs :=
  induced_outer_measure_eq m0 mU hs

theorem to_outer_measure_injective : Injective (toOuterMeasure : Measure α → OuterMeasure α) :=
  fun ⟨m₁, u₁, h₁⟩ ⟨m₂, u₂, h₂⟩ h => by
  congr
  exact h

@[ext]
theorem ext (h : ∀ s, MeasurableSet s → μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  to_outer_measure_injective <| by
    rw [← trimmed, outer_measure.trim_congr h, trimmed]

theorem ext_iff : μ₁ = μ₂ ↔ ∀ s, MeasurableSet s → μ₁ s = μ₂ s :=
  ⟨by
    rintro rfl s hs
    rfl, Measure.ext⟩

end Measureₓ

@[simp]
theorem coe_to_outer_measure : ⇑μ.toOuterMeasure = μ :=
  rfl

theorem to_outer_measure_apply (s : Set α) : μ.toOuterMeasure s = μ s :=
  rfl

theorem measure_eq_trim (s : Set α) : μ s = μ.toOuterMeasure.trim s := by
  rw [μ.trimmed] <;> rfl

theorem measure_eq_infi (s : Set α) : μ s = ⨅ (t) (st : s ⊆ t) (ht : MeasurableSet t), μ t := by
  rw [measure_eq_trim, outer_measure.trim_eq_infi] <;> rfl

/-- A variant of `measure_eq_infi` which has a single `infi`. This is useful when applying a
  lemma next that only works for non-empty infima, in which case you can use
  `nonempty_measurable_superset`. -/
theorem measure_eq_infi' (μ : Measure α) (s : Set α) : μ s = ⨅ t : { t // s ⊆ t ∧ MeasurableSet t }, μ t := by
  simp_rw [infi_subtype, infi_and, Subtype.coe_mk, ← measure_eq_infi]

theorem measure_eq_induced_outer_measure : μ s = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.Empty s :=
  measure_eq_trim _

theorem to_outer_measure_eq_induced_outer_measure :
    μ.toOuterMeasure = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.Empty :=
  μ.trimmed.symm

theorem measure_eq_extend (hs : MeasurableSet s) : μ s = extend (fun t (ht : MeasurableSet t) => μ t) s :=
  (extend_eq _ hs).symm

@[simp]
theorem measure_empty : μ ∅ = 0 :=
  μ.Empty

theorem nonempty_of_measure_ne_zero (h : μ s ≠ 0) : s.Nonempty :=
  ne_empty_iff_nonempty.1 fun h' => h <| h'.symm ▸ measure_empty

theorem measure_mono (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ :=
  μ.mono h

theorem measure_mono_null (h : s₁ ⊆ s₂) (h₂ : μ s₂ = 0) : μ s₁ = 0 :=
  nonpos_iff_eq_zero.1 <| h₂ ▸ measure_mono h

theorem measure_mono_top (h : s₁ ⊆ s₂) (h₁ : μ s₁ = ∞) : μ s₂ = ∞ :=
  top_unique <| h₁ ▸ measure_mono h

/-- For every set there exists a measurable superset of the same measure. -/
theorem exists_measurable_superset (μ : Measure α) (s : Set α) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s := by
  simpa only [measure_eq_trim] using μ.to_outer_measure.exists_measurable_superset_eq_trim s

/-- For every set `s` and a countable collection of measures `μ i` there exists a measurable
superset `t ⊇ s` such that each measure `μ i` takes the same value on `s` and `t`. -/
theorem exists_measurable_superset_forall_eq {ι} [Encodable ι] (μ : ι → Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ ∀ i, μ i t = μ i s := by
  simpa only [measure_eq_trim] using
    outer_measure.exists_measurable_superset_forall_eq_trim (fun i => (μ i).toOuterMeasure) s

theorem exists_measurable_superset₂ (μ ν : Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s ∧ ν t = ν s := by
  simpa only [← bool.forall_bool.trans And.comm] using exists_measurable_superset_forall_eq (fun b => cond b μ ν) s

theorem exists_measurable_superset_of_null (h : μ s = 0) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0 :=
  h ▸ exists_measurable_superset μ s

theorem exists_measurable_superset_iff_measure_eq_zero : (∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0) ↔ μ s = 0 :=
  ⟨fun ⟨t, hst, _, ht⟩ => measure_mono_null hst ht, exists_measurable_superset_of_null⟩

theorem measure_Union_le [Encodable β] (s : β → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  μ.toOuterMeasure.Union _

theorem measure_bUnion_le {s : Set β} (hs : s.Countable) (f : β → Set α) : μ (⋃ b ∈ s, f b) ≤ ∑' p : s, μ (f p) := by
  have := hs.to_encodable
  rw [bUnion_eq_Union]
  apply measure_Union_le

theorem measure_bUnion_finset_le (s : Finset β) (f : β → Set α) : μ (⋃ b ∈ s, f b) ≤ ∑ p in s, μ (f p) := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype]
  exact measure_bUnion_le s.countable_to_set f

theorem measure_Union_fintype_le [Fintype β] (f : β → Set α) : μ (⋃ b, f b) ≤ ∑ p, μ (f p) := by
  convert measure_bUnion_finset_le Finset.univ f
  simp

theorem measure_bUnion_lt_top {s : Set β} {f : β → Set α} (hs : s.Finite) (hfin : ∀, ∀ i ∈ s, ∀, μ (f i) ≠ ∞) :
    μ (⋃ i ∈ s, f i) < ∞ := by
  convert (measure_bUnion_finset_le hs.to_finset f).trans_lt _
  · ext
    rw [finite.mem_to_finset]
    
  apply Ennreal.sum_lt_top
  simpa only [← finite.mem_to_finset]

theorem measure_Union_null [Encodable β] {s : β → Set α} : (∀ i, μ (s i) = 0) → μ (⋃ i, s i) = 0 :=
  μ.toOuterMeasure.Union_null

@[simp]
theorem measure_Union_null_iff [Encodable ι] {s : ι → Set α} : μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0 :=
  μ.toOuterMeasure.Union_null_iff

theorem measure_bUnion_null_iff {s : Set ι} (hs : s.Countable) {t : ι → Set α} :
    μ (⋃ i ∈ s, t i) = 0 ↔ ∀, ∀ i ∈ s, ∀, μ (t i) = 0 :=
  μ.toOuterMeasure.bUnion_null_iff hs

theorem measure_sUnion_null_iff {S : Set (Set α)} (hS : S.Countable) : μ (⋃₀S) = 0 ↔ ∀, ∀ s ∈ S, ∀, μ s = 0 :=
  μ.toOuterMeasure.sUnion_null_iff hS

theorem measure_union_le (s₁ s₂ : Set α) : μ (s₁ ∪ s₂) ≤ μ s₁ + μ s₂ :=
  μ.toOuterMeasure.union _ _

theorem measure_union_null : μ s₁ = 0 → μ s₂ = 0 → μ (s₁ ∪ s₂) = 0 :=
  μ.toOuterMeasure.union_null

@[simp]
theorem measure_union_null_iff : μ (s₁ ∪ s₂) = 0 ↔ μ s₁ = 0 ∧ μ s₂ = 0 :=
  ⟨fun h => ⟨measure_mono_null (subset_union_left _ _) h, measure_mono_null (subset_union_right _ _) h⟩, fun h =>
    measure_union_null h.1 h.2⟩

theorem measure_union_lt_top (hs : μ s < ∞) (ht : μ t < ∞) : μ (s ∪ t) < ∞ :=
  (measure_union_le s t).trans_lt (Ennreal.add_lt_top.mpr ⟨hs, ht⟩)

@[simp]
theorem measure_union_lt_top_iff : μ (s ∪ t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞ := by
  refine' ⟨fun h => ⟨_, _⟩, fun h => measure_union_lt_top h.1 h.2⟩
  · exact (measure_mono (Set.subset_union_left s t)).trans_lt h
    
  · exact (measure_mono (Set.subset_union_right s t)).trans_lt h
    

theorem measure_union_ne_top (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) : μ (s ∪ t) ≠ ∞ :=
  (measure_union_lt_top hs.lt_top ht.lt_top).Ne

@[simp]
theorem measure_union_eq_top_iff : μ (s ∪ t) = ∞ ↔ μ s = ∞ ∨ μ t = ∞ :=
  not_iff_not.1 <| by
    simp only [lt_top_iff_ne_top, Ne.def, ← not_or_distrib, ← measure_union_lt_top_iff]

theorem exists_measure_pos_of_not_measure_Union_null [Encodable β] {s : β → Set α} (hs : μ (⋃ n, s n) ≠ 0) :
    ∃ n, 0 < μ (s n) := by
  contrapose! hs
  exact measure_Union_null fun n => nonpos_iff_eq_zero.1 (hs n)

theorem measure_inter_lt_top_of_left_ne_top (hs_finite : μ s ≠ ∞) : μ (s ∩ t) < ∞ :=
  (measure_mono (Set.inter_subset_left s t)).trans_lt hs_finite.lt_top

theorem measure_inter_lt_top_of_right_ne_top (ht_finite : μ t ≠ ∞) : μ (s ∩ t) < ∞ :=
  inter_comm t s ▸ measure_inter_lt_top_of_left_ne_top ht_finite

theorem measure_inter_null_of_null_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S ∩ T) = 0 :=
  measure_mono_null (inter_subset_right S T) h

theorem measure_inter_null_of_null_left {S : Set α} (T : Set α) (h : μ S = 0) : μ (S ∩ T) = 0 :=
  measure_mono_null (inter_subset_left S T) h

/-! ### The almost everywhere filter -/


/-- The “almost everywhere” filter of co-null sets. -/
def Measure.ae {α} {m : MeasurableSpace α} (μ : Measure α) : Filter α where
  Sets := { s | μ (sᶜ) = 0 }
  univ_sets := by
    simp
  inter_sets := fun s t hs ht => by
    simp only [← compl_inter, ← mem_set_of_eq] <;> exact measure_union_null hs ht
  sets_of_superset := fun s t hs hst => measure_mono_null (Set.compl_subset_compl.2 hst) hs

-- mathport name: «expr∀ᵐ ∂ , »
notation3"∀ᵐ "(...)" ∂"μ", "r:(scoped P => Filter.Eventually P Measure.ae μ) => r

-- mathport name: «expr∃ᵐ ∂ , »
notation3"∃ᵐ "(...)" ∂"μ", "r:(scoped P => Filter.Frequently P Measure.ae μ) => r

-- mathport name: «expr =ᵐ[ ] »
notation:50 f " =ᵐ[" μ:50 "] " g:50 => f =ᶠ[Measure.ae μ] g

-- mathport name: «expr ≤ᵐ[ ] »
notation:50 f " ≤ᵐ[" μ:50 "] " g:50 => f ≤ᶠ[Measure.ae μ] g

theorem mem_ae_iff {s : Set α} : s ∈ μ.ae ↔ μ (sᶜ) = 0 :=
  Iff.rfl

theorem ae_iff {p : α → Prop} : (∀ᵐ a ∂μ, p a) ↔ μ { a | ¬p a } = 0 :=
  Iff.rfl

theorem compl_mem_ae_iff {s : Set α} : sᶜ ∈ μ.ae ↔ μ s = 0 := by
  simp only [← mem_ae_iff, ← compl_compl]

theorem frequently_ae_iff {p : α → Prop} : (∃ᵐ a ∂μ, p a) ↔ μ { a | p a } ≠ 0 :=
  not_congr compl_mem_ae_iff

theorem frequently_ae_mem_iff {s : Set α} : (∃ᵐ a ∂μ, a ∈ s) ↔ μ s ≠ 0 :=
  not_congr compl_mem_ae_iff

theorem measure_zero_iff_ae_nmem {s : Set α} : μ s = 0 ↔ ∀ᵐ a ∂μ, a ∉ s :=
  compl_mem_ae_iff.symm

theorem ae_of_all {p : α → Prop} (μ : Measure α) : (∀ a, p a) → ∀ᵐ a ∂μ, p a :=
  eventually_of_forall

--instance ae_is_measurably_generated : is_measurably_generated μ.ae :=
--⟨λ s hs, let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs in
--  ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩
instance : CountableInterFilter μ.ae :=
  ⟨by
    intro S hSc hS
    rw [mem_ae_iff, compl_sInter, sUnion_image]
    exact (measure_bUnion_null_iff hSc).2 hS⟩

theorem ae_imp_iff {p : α → Prop} {q : Prop} : (∀ᵐ x ∂μ, q → p x) ↔ q → ∀ᵐ x ∂μ, p x :=
  Filter.eventually_imp_distrib_left

theorem ae_all_iff [Encodable ι] {p : α → ι → Prop} : (∀ᵐ a ∂μ, ∀ i, p a i) ↔ ∀ i, ∀ᵐ a ∂μ, p a i :=
  eventually_countable_forall

theorem ae_ball_iff {S : Set ι} (hS : S.Countable) {p : ∀ (x : α), ∀ i ∈ S, ∀, Prop} :
    (∀ᵐ x ∂μ, ∀, ∀ i ∈ S, ∀, p x i ‹_›) ↔ ∀, ∀ i ∈ S, ∀, ∀ᵐ x ∂μ, p x i ‹_› :=
  eventually_countable_ball hS

theorem ae_eq_refl (f : α → δ) : f =ᵐ[μ] f :=
  eventually_eq.rfl

theorem ae_eq_symm {f g : α → δ} (h : f =ᵐ[μ] g) : g =ᵐ[μ] f :=
  h.symm

theorem ae_eq_trans {f g h : α → δ} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h :=
  h₁.trans h₂

theorem ae_le_of_ae_lt {f g : α → ℝ≥0∞} (h : ∀ᵐ x ∂μ, f x < g x) : f ≤ᵐ[μ] g := by
  rw [Filter.EventuallyLe, ae_iff]
  rw [ae_iff] at h
  refine' measure_mono_null (fun x hx => _) h
  exact not_ltₓ.2 (le_of_ltₓ (not_leₓ.1 hx))

@[simp]
theorem ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0 :=
  eventually_eq_empty.trans <| by
    simp only [← ae_iff, ← not_not, ← set_of_mem_eq]

@[simp]
theorem ae_eq_univ : s =ᵐ[μ] (Univ : Set α) ↔ μ (sᶜ) = 0 :=
  eventually_eq_univ

theorem ae_le_set : s ≤ᵐ[μ] t ↔ μ (s \ t) = 0 :=
  calc
    s ≤ᵐ[μ] t ↔ ∀ᵐ x ∂μ, x ∈ s → x ∈ t := Iff.rfl
    _ ↔ μ (s \ t) = 0 := by
      simp [← ae_iff] <;> rfl
    

theorem ae_le_set_inter {s' t' : Set α} (h : s ≤ᵐ[μ] t) (h' : s' ≤ᵐ[μ] t') : (s ∩ s' : Set α) ≤ᵐ[μ] (t ∩ t' : Set α) :=
  h.inter h'

@[simp]
theorem union_ae_eq_right : (s ∪ t : Set α) =ᵐ[μ] t ↔ μ (s \ t) = 0 := by
  simp [← eventually_le_antisymm_iff, ← ae_le_set, ← union_diff_right, ← diff_eq_empty.2 (Set.subset_union_right _ _)]

theorem diff_ae_eq_self : (s \ t : Set α) =ᵐ[μ] s ↔ μ (s ∩ t) = 0 := by
  simp [← eventually_le_antisymm_iff, ← ae_le_set, ← diff_diff_right, ← diff_diff, ←
    diff_eq_empty.2 (Set.subset_union_right _ _)]

theorem diff_null_ae_eq_self (ht : μ t = 0) : (s \ t : Set α) =ᵐ[μ] s :=
  diff_ae_eq_self.mpr (measure_mono_null (inter_subset_right _ _) ht)

theorem ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t) = 0 ∧ μ (t \ s) = 0 := by
  simp [← eventually_le_antisymm_iff, ← ae_le_set]

theorem ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') : (s ∩ s' : Set α) =ᵐ[μ] (t ∩ t' : Set α) :=
  h.inter h'

@[to_additive]
theorem _root_.set.mul_indicator_ae_eq_one {M : Type _} [One M] {f : α → M} {s : Set α} (h : s.mulIndicator f =ᵐ[μ] 1) :
    μ (s ∩ Function.MulSupport f) = 0 := by
  simpa [← Filter.EventuallyEq, ← ae_iff] using h

/-- If `s ⊆ t` modulo a set of measure `0`, then `μ s ≤ μ t`. -/
@[mono]
theorem measure_mono_ae (H : s ≤ᵐ[μ] t) : μ s ≤ μ t :=
  calc
    μ s ≤ μ (s ∪ t) := measure_mono <| subset_union_left s t
    _ = μ (t ∪ s \ t) := by
      rw [union_diff_self, Set.union_comm]
    _ ≤ μ t + μ (s \ t) := measure_union_le _ _
    _ = μ t := by
      rw [ae_le_set.1 H, add_zeroₓ]
    

alias measure_mono_ae ← _root_.filter.eventually_le.measure_le

/-- If two sets are equal modulo a set of measure zero, then `μ s = μ t`. -/
theorem measure_congr (H : s =ᵐ[μ] t) : μ s = μ t :=
  le_antisymmₓ H.le.measure_le H.symm.le.measure_le

alias measure_congr ← _root_.filter.eventually_eq.measure_eq

theorem measure_mono_null_ae (H : s ≤ᵐ[μ] t) (ht : μ t = 0) : μ s = 0 :=
  nonpos_iff_eq_zero.1 <| ht ▸ H.measure_le

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊇ » s)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊇ » s)
/-- A measurable set `t ⊇ s` such that `μ t = μ s`. It even satisfies `μ (t ∩ u) = μ (s ∩ u)` for
any measurable set `u` if `μ s ≠ ∞`, see `measure_to_measurable_inter`.
(This property holds without the assumption `μ s ≠ ∞` when the space is sigma-finite,
see `measure_to_measurable_inter_of_sigma_finite`).
If `s` is a null measurable set, then
we also have `t =ᵐ[μ] s`, see `null_measurable_set.to_measurable_ae_eq`.
This notion is sometimes called a "measurable hull" in the literature. -/
irreducible_def ToMeasurable (μ : Measure α) (s : Set α) : Set α :=
  if h : ∃ (t : _)(_ : t ⊇ s), MeasurableSet t ∧ t =ᵐ[μ] s then h.some
  else
    if h' : ∃ (t : _)(_ : t ⊇ s), MeasurableSet t ∧ ∀ u, MeasurableSet u → μ (t ∩ u) = μ (s ∩ u) then h'.some
    else (exists_measurable_superset μ s).some

theorem subset_to_measurable (μ : Measure α) (s : Set α) : s ⊆ ToMeasurable μ s := by
  rw [to_measurable]
  split_ifs with hs h's
  exacts[hs.some_spec.fst, h's.some_spec.fst, (exists_measurable_superset μ s).some_spec.1]

theorem ae_le_to_measurable : s ≤ᵐ[μ] ToMeasurable μ s :=
  (subset_to_measurable _ _).EventuallyLe

@[simp]
theorem measurable_set_to_measurable (μ : Measure α) (s : Set α) : MeasurableSet (ToMeasurable μ s) := by
  rw [to_measurable]
  split_ifs with hs h's
  exacts[hs.some_spec.snd.1, h's.some_spec.snd.1, (exists_measurable_superset μ s).some_spec.2.1]

@[simp]
theorem measure_to_measurable (s : Set α) : μ (ToMeasurable μ s) = μ s := by
  rw [to_measurable]
  split_ifs with hs h's
  · exact measure_congr hs.some_spec.snd.2
    
  · simpa only [← inter_univ] using h's.some_spec.snd.2 univ MeasurableSet.univ
    
  · exact (exists_measurable_superset μ s).some_spec.2.2
    

/-- A measure space is a measurable space equipped with a
  measure, referred to as `volume`. -/
class MeasureSpace (α : Type _) extends MeasurableSpace α where
  volume : Measure α

export MeasureSpace (volume)

/-- `volume` is the canonical  measure on `α`. -/
add_decl_doc volume

section MeasureSpace

-- mathport name: «expr∀ᵐ , »
notation3"∀ᵐ "(...)", "r:(scoped P => Filter.Eventually P MeasureTheory.Measure.ae MeasureTheory.MeasureSpace.volume) =>
  r

-- mathport name: «expr∃ᵐ , »
notation3"∃ᵐ "(...)", "r:(scoped P => Filter.Frequently P MeasureTheory.Measure.ae MeasureTheory.MeasureSpace.volume) =>
  r

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- The tactic `exact volume`, to be used in optional (`auto_param`) arguments. -/
unsafe def volume_tac : tactic Unit :=
  sorry

end MeasureSpace

end

end MeasureTheory

section

open MeasureTheory

/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. We define this property, called `ae_measurable f μ`. It's properties are discussed in
`measure_theory.measure_space`.
-/


variable {m : MeasurableSpace α} [MeasurableSpace β] {f g : α → β} {μ ν : Measureₓ α}

/-- A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. -/
def AeMeasurable {m : MeasurableSpace α} (f : α → β)
    (μ : Measureₓ α := by
      run_tac
        measure_theory.volume_tac) :
    Prop :=
  ∃ g : α → β, Measurable g ∧ f =ᵐ[μ] g

theorem Measurable.ae_measurable (h : Measurable f) : AeMeasurable f μ :=
  ⟨f, h, ae_eq_refl f⟩

namespace AeMeasurable

/-- Given an almost everywhere measurable function `f`, associate to it a measurable function
that coincides with it almost everywhere. `f` is explicit in the definition to make sure that
it shows in pretty-printing. -/
def mk (f : α → β) (h : AeMeasurable f μ) : α → β :=
  Classical.some h

theorem measurable_mk (h : AeMeasurable f μ) : Measurable (h.mk f) :=
  (Classical.some_spec h).1

theorem ae_eq_mk (h : AeMeasurable f μ) : f =ᵐ[μ] h.mk f :=
  (Classical.some_spec h).2

theorem congr (hf : AeMeasurable f μ) (h : f =ᵐ[μ] g) : AeMeasurable g μ :=
  ⟨hf.mk f, hf.measurable_mk, h.symm.trans hf.ae_eq_mk⟩

end AeMeasurable

theorem ae_measurable_congr (h : f =ᵐ[μ] g) : AeMeasurable f μ ↔ AeMeasurable g μ :=
  ⟨fun hf => AeMeasurable.congr hf h, fun hg => AeMeasurable.congr hg h.symm⟩

@[simp]
theorem ae_measurable_const {b : β} : AeMeasurable (fun a : α => b) μ :=
  measurable_const.AeMeasurable

theorem ae_measurable_id : AeMeasurable id μ :=
  measurable_id.AeMeasurable

theorem ae_measurable_id' : AeMeasurable (fun x => x) μ :=
  measurable_id.AeMeasurable

theorem Measurable.comp_ae_measurable [MeasurableSpace δ] {f : α → δ} {g : δ → β} (hg : Measurable g)
    (hf : AeMeasurable f μ) : AeMeasurable (g ∘ f) μ :=
  ⟨g ∘ hf.mk f, hg.comp hf.measurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk _⟩

end

