/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathbin.MeasureTheory.Measure.AeDisjoint

/-!
# Null measurable sets and complete measures

## Main definitions

### Null measurable sets and functions

A set `s : set α` is called *null measurable* (`measure_theory.null_measurable_set`) if it satisfies
any of the following equivalent conditions:

* there exists a measurable set `t` such that `s =ᵐ[μ] t` (this is used as a definition);
* `measure_theory.to_measurable μ s =ᵐ[μ] s`;
* there exists a measurable subset `t ⊆ s` such that `t =ᵐ[μ] s` (in this case the latter equality
  means that `μ (s \ t) = 0`);
* `s` can be represented as a union of a measurable set and a set of measure zero;
* `s` can be represented as a difference of a measurable set and a set of measure zero.

Null measurable sets form a σ-algebra that is registered as a `measurable_space` instance on
`measure_theory.null_measurable_space α μ`. We also say that `f : α → β` is
`measure_theory.null_measurable` if the preimage of a measurable set is a null measurable set.
In other words, `f : α → β` is null measurable if it is measurable as a function
`measure_theory.null_measurable_space α μ → β`.

### Complete measures

We say that a measure `μ` is complete w.r.t. the `measurable_space α` σ-algebra (or the σ-algebra is
complete w.r.t measure `μ`) if every set of measure zero is measurable. In this case all null
measurable sets and functions are measurable.

For each measure `μ`, we define `measure_theory.measure.completion μ` to be the same measure
interpreted as a measure on `measure_theory.null_measurable_space α μ` and prove that this is a
complete measure.

## Implementation notes

We define `measure_theory.null_measurable_set` as `@measurable_set (null_measurable_space α μ) _` so
that theorems about `measurable_set`s like `measurable_set.union` can be applied to
`null_measurable_set`s. However, these lemmas output terms of the same form
`@measurable_set (null_measurable_space α μ) _ _`. While this is definitionally equal to the
expected output `null_measurable_set s μ`, it looks different and may be misleading. So we copy all
standard lemmas about measurable sets to the `measure_theory.null_measurable_set` namespace and fix
the output type.

## Tags

measurable, measure, null measurable, completion
-/


open Filter Set Encodable

variable {ι α β γ : Type _}

namespace MeasureTheory

/-- A type tag for `α` with `measurable_set` given by `null_measurable_set`. -/
@[nolint unused_arguments]
def NullMeasurableSpace (α : Type _) [MeasurableSpace α]
    (μ : Measure α := by
      run_tac
        volume_tac) :
    Type _ :=
  α

section

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

instance [h : Inhabited α] : Inhabited (NullMeasurableSpace α μ) :=
  h

instance [h : Subsingleton α] : Subsingleton (NullMeasurableSpace α μ) :=
  h

instance : MeasurableSpace (NullMeasurableSpace α μ) where
  MeasurableSet' := fun s => ∃ t, MeasurableSet t ∧ s =ᵐ[μ] t
  measurable_set_empty := ⟨∅, MeasurableSet.empty, ae_eq_refl _⟩
  measurable_set_compl := fun s ⟨t, htm, hts⟩ => ⟨tᶜ, htm.compl, hts.compl⟩
  measurable_set_Union := fun s hs => by
    choose t htm hts using hs
    exact ⟨⋃ i, t i, MeasurableSet.Union htm, EventuallyEq.countable_Union hts⟩

/-- A set is called `null_measurable_set` if it can be approximated by a measurable set up to
a set of null measure. -/
def NullMeasurableSet [MeasurableSpace α] (s : Set α)
    (μ : Measure α := by
      run_tac
        volume_tac) :
    Prop :=
  @MeasurableSet (NullMeasurableSpace α μ) _ s

@[simp]
theorem _root_.measurable_set.null_measurable_set (h : MeasurableSet s) : NullMeasurableSet s μ :=
  ⟨s, h, ae_eq_refl _⟩

@[simp]
theorem null_measurable_set_empty : NullMeasurableSet ∅ μ :=
  MeasurableSet.empty

@[simp]
theorem null_measurable_set_univ : NullMeasurableSet Univ μ :=
  MeasurableSet.univ

namespace NullMeasurableSet

theorem of_null (h : μ s = 0) : NullMeasurableSet s μ :=
  ⟨∅, MeasurableSet.empty, ae_eq_empty.2 h⟩

theorem compl (h : NullMeasurableSet s μ) : NullMeasurableSet (sᶜ) μ :=
  h.compl

theorem of_compl (h : NullMeasurableSet (sᶜ) μ) : NullMeasurableSet s μ :=
  h.of_compl

@[simp]
theorem compl_iff : NullMeasurableSet (sᶜ) μ ↔ NullMeasurableSet s μ :=
  MeasurableSet.compl_iff

@[nontriviality]
theorem of_subsingleton [Subsingleton α] : NullMeasurableSet s μ :=
  Subsingleton.measurable_set

protected theorem congr (hs : NullMeasurableSet s μ) (h : s =ᵐ[μ] t) : NullMeasurableSet t μ :=
  let ⟨s', hm, hs'⟩ := hs
  ⟨s', hm, h.symm.trans hs'⟩

protected theorem Union [Encodable ι] {s : ι → Set α} (h : ∀ i, NullMeasurableSet (s i) μ) :
    NullMeasurableSet (⋃ i, s i) μ :=
  MeasurableSet.Union h

protected theorem bUnion_decode₂ [Encodable ι] ⦃f : ι → Set α⦄ (h : ∀ i, NullMeasurableSet (f i) μ) (n : ℕ) :
    NullMeasurableSet (⋃ b ∈ Encodable.decode₂ ι n, f b) μ :=
  MeasurableSet.bUnion_decode₂ h n

protected theorem bUnion {f : ι → Set α} {s : Set ι} (hs : s.Countable) (h : ∀, ∀ b ∈ s, ∀, NullMeasurableSet (f b) μ) :
    NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  MeasurableSet.bUnion hs h

protected theorem sUnion {s : Set (Set α)} (hs : s.Countable) (h : ∀, ∀ t ∈ s, ∀, NullMeasurableSet t μ) :
    NullMeasurableSet (⋃₀s) μ := by
  rw [sUnion_eq_bUnion]
  exact MeasurableSet.bUnion hs h

theorem Union_Prop {p : Prop} {f : p → Set α} (hf : ∀ i, NullMeasurableSet (f i) μ) : NullMeasurableSet (⋃ i, f i) μ :=
  MeasurableSet.Union_Prop hf

theorem Union_fintype [Fintype ι] {f : ι → Set α} (h : ∀ b, NullMeasurableSet (f b) μ) :
    NullMeasurableSet (⋃ b, f b) μ :=
  MeasurableSet.Union_fintype h

protected theorem Inter [Encodable ι] {f : ι → Set α} (h : ∀ i, NullMeasurableSet (f i) μ) :
    NullMeasurableSet (⋂ i, f i) μ :=
  MeasurableSet.Inter h

protected theorem bInter {f : β → Set α} {s : Set β} (hs : s.Countable) (h : ∀, ∀ b ∈ s, ∀, NullMeasurableSet (f b) μ) :
    NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  MeasurableSet.bInter hs h

protected theorem sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀, ∀ t ∈ s, ∀, NullMeasurableSet t μ) :
    NullMeasurableSet (⋂₀ s) μ :=
  MeasurableSet.sInter hs h

theorem Inter_Prop {p : Prop} {f : p → Set α} (hf : ∀ b, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b, f b) μ :=
  MeasurableSet.Inter_Prop hf

theorem Inter_fintype [Fintype ι] {f : ι → Set α} (h : ∀ b, NullMeasurableSet (f b) μ) :
    NullMeasurableSet (⋂ b, f b) μ :=
  MeasurableSet.Inter_fintype h

@[simp]
protected theorem union (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) : NullMeasurableSet (s ∪ t) μ :=
  hs.union ht

protected theorem union_null (hs : NullMeasurableSet s μ) (ht : μ t = 0) : NullMeasurableSet (s ∪ t) μ :=
  hs.union (of_null ht)

@[simp]
protected theorem inter (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) : NullMeasurableSet (s ∩ t) μ :=
  hs.inter ht

@[simp]
protected theorem diff (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) : NullMeasurableSet (s \ t) μ :=
  hs.diff ht

@[simp]
protected theorem disjointed {f : ℕ → Set α} (h : ∀ i, NullMeasurableSet (f i) μ) (n) :
    NullMeasurableSet (disjointed f n) μ :=
  MeasurableSet.disjointed h n

@[simp]
protected theorem const (p : Prop) : NullMeasurableSet { a : α | p } μ :=
  MeasurableSet.const p

instance [MeasurableSingletonClass α] : MeasurableSingletonClass (NullMeasurableSpace α μ) :=
  ⟨fun x => (@measurable_set_singleton α _ _ x).NullMeasurableSet⟩

protected theorem insert [MeasurableSingletonClass (NullMeasurableSpace α μ)] (hs : NullMeasurableSet s μ) (a : α) :
    NullMeasurableSet (insert a s) μ :=
  hs.insert a

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊇ » s)
theorem exists_measurable_superset_ae_eq (h : NullMeasurableSet s μ) :
    ∃ (t : _)(_ : t ⊇ s), MeasurableSet t ∧ t =ᵐ[μ] s := by
  rcases h with ⟨t, htm, hst⟩
  refine' ⟨t ∪ to_measurable μ (s \ t), _, htm.union (measurable_set_to_measurable _ _), _⟩
  · exact diff_subset_iff.1 (subset_to_measurable _ _)
    
  · have : to_measurable μ (s \ t) =ᵐ[μ] (∅ : Set α) := by
      simp [← ae_le_set.1 hst.le]
    simpa only [← union_empty] using hst.symm.union this
    

theorem to_measurable_ae_eq (h : NullMeasurableSet s μ) : ToMeasurable μ s =ᵐ[μ] s := by
  rw [to_measurable, dif_pos]
  exact h.exists_measurable_superset_ae_eq.some_spec.snd.2

theorem compl_to_measurable_compl_ae_eq (h : NullMeasurableSet s μ) : ToMeasurable μ (sᶜ)ᶜ =ᵐ[μ] s := by
  simpa only [← compl_compl] using h.compl.to_measurable_ae_eq.compl

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem exists_measurable_subset_ae_eq (h : NullMeasurableSet s μ) :
    ∃ (t : _)(_ : t ⊆ s), MeasurableSet t ∧ t =ᵐ[μ] s :=
  ⟨ToMeasurable μ (sᶜ)ᶜ, compl_subset_comm.2 <| subset_to_measurable _ _, (measurable_set_to_measurable _ _).compl,
    h.compl_to_measurable_compl_ae_eq⟩

end NullMeasurableSet

/-- If `sᵢ` is a countable family of (null) measurable pairwise `μ`-a.e. disjoint sets, then there
exists a subordinate family `tᵢ ⊆ sᵢ` of measurable pairwise disjoint sets such that
`tᵢ =ᵐ[μ] sᵢ`. -/
theorem exists_subordinate_pairwise_disjoint [Encodable ι] {s : ι → Set α} (h : ∀ i, NullMeasurableSet (s i) μ)
    (hd : Pairwise (AeDisjoint μ on s)) :
    ∃ t : ι → Set α, (∀ i, t i ⊆ s i) ∧ (∀ i, s i =ᵐ[μ] t i) ∧ (∀ i, MeasurableSet (t i)) ∧ Pairwise (Disjoint on t) :=
  by
  choose t ht_sub htm ht_eq using fun i => (h i).exists_measurable_subset_ae_eq
  rcases exists_null_pairwise_disjoint_diff hd with ⟨u, hum, hu₀, hud⟩
  exact
    ⟨fun i => t i \ u i, fun i => (diff_subset _ _).trans (ht_sub _), fun i =>
      (ht_eq _).symm.trans (diff_null_ae_eq_self (hu₀ i)).symm, fun i => (htm i).diff (hum i),
      hud.mono fun i j h => h.mono (diff_subset_diff_left (ht_sub i)) (diff_subset_diff_left (ht_sub j))⟩

theorem measure_Union {m0 : MeasurableSpace α} {μ : Measure α} [Encodable ι] {f : ι → Set α}
    (hn : Pairwise (Disjoint on f)) (h : ∀ i, MeasurableSet (f i)) : μ (⋃ i, f i) = ∑' i, μ (f i) := by
  rw [measure_eq_extend (MeasurableSet.Union h), extend_Union MeasurableSet.empty _ MeasurableSet.Union _ hn h]
  · simp [← measure_eq_extend, ← h]
    
  · exact μ.empty
    
  · exact μ.m_Union
    

theorem measure_Union₀ [Encodable ι] {f : ι → Set α} (hd : Pairwise (AeDisjoint μ on f))
    (h : ∀ i, NullMeasurableSet (f i) μ) : μ (⋃ i, f i) = ∑' i, μ (f i) := by
  rcases exists_subordinate_pairwise_disjoint h hd with ⟨t, ht_sub, ht_eq, htm, htd⟩
  calc μ (⋃ i, f i) = μ (⋃ i, t i) := measure_congr (EventuallyEq.countable_Union ht_eq)_ = ∑' i, μ (t i) :=
      measure_Union htd htm _ = ∑' i, μ (f i) := tsum_congr fun i => measure_congr (ht_eq _).symm

theorem measure_union₀_aux (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) (hd : AeDisjoint μ s t) :
    μ (s ∪ t) = μ s + μ t := by
  rw [union_eq_Union, measure_Union₀, tsum_fintype, Fintype.sum_bool, cond, cond]
  exacts[(pairwise_on_bool ae_disjoint.symmetric).2 hd, fun b => Bool.casesOn b ht hs]

/-- A null measurable set `t` is Carathéodory measurable: for any `s`, we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
theorem measure_inter_add_diff₀ (s : Set α) (ht : NullMeasurableSet t μ) : μ (s ∩ t) + μ (s \ t) = μ s := by
  refine' le_antisymmₓ _ _
  · rcases exists_measurable_superset μ s with ⟨s', hsub, hs'm, hs'⟩
    replace hs'm : null_measurable_set s' μ := hs'm.null_measurable_set
    calc μ (s ∩ t) + μ (s \ t) ≤ μ (s' ∩ t) + μ (s' \ t) :=
        add_le_add (measure_mono <| inter_subset_inter_left _ hsub)
          (measure_mono <| diff_subset_diff_left hsub)_ = μ (s' ∩ t ∪ s' \ t) :=
        (measure_union₀_aux (hs'm.inter ht) (hs'm.diff ht) <|
            (@disjoint_inf_sdiff _ s' t _).AeDisjoint).symm _ = μ s' :=
        congr_arg μ (inter_union_diff _ _)_ = μ s := hs'
    
  · calc μ s = μ (s ∩ t ∪ s \ t) := by
        rw [inter_union_diff]_ ≤ μ (s ∩ t) + μ (s \ t) := measure_union_le _ _
    

theorem measure_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) : μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [← measure_inter_add_diff₀ (s ∪ t) ht, union_inter_cancel_right, union_diff_right, ← measure_inter_add_diff₀ s ht,
    add_commₓ, ← add_assocₓ, add_right_commₓ]

theorem measure_union_add_inter₀' (hs : NullMeasurableSet s μ) (t : Set α) : μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter₀ t hs, add_commₓ]

theorem measure_union₀ (ht : NullMeasurableSet t μ) (hd : AeDisjoint μ s t) : μ (s ∪ t) = μ s + μ t := by
  rw [← measure_union_add_inter₀ s ht, hd.eq, add_zeroₓ]

theorem measure_union₀' (hs : NullMeasurableSet s μ) (hd : AeDisjoint μ s t) : μ (s ∪ t) = μ s + μ t := by
  rw [union_comm, measure_union₀ hs hd.symm, add_commₓ]

section MeasurableSingletonClass

variable [MeasurableSingletonClass (NullMeasurableSpace α μ)]

theorem null_measurable_set_singleton (x : α) : NullMeasurableSet {x} μ :=
  measurable_set_singleton x

@[simp]
theorem null_measurable_set_insert {a : α} {s : Set α} : NullMeasurableSet (insert a s) μ ↔ NullMeasurableSet s μ :=
  measurable_set_insert

theorem null_measurable_set_eq {a : α} : NullMeasurableSet { x | x = a } μ :=
  null_measurable_set_singleton a

protected theorem _root_.set.finite.null_measurable_set (hs : s.Finite) : NullMeasurableSet s μ :=
  Finite.measurable_set hs

protected theorem _root_.finset.null_measurable_set (s : Finset α) : NullMeasurableSet (↑s) μ :=
  Finset.measurable_set s

end MeasurableSingletonClass

theorem _root_.set.finite.null_measurable_set_bUnion {f : ι → Set α} {s : Set ι} (hs : s.Finite)
    (h : ∀, ∀ b ∈ s, ∀, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  Finite.measurable_set_bUnion hs h

theorem _root_.finset.null_measurable_set_bUnion {f : ι → Set α} (s : Finset ι)
    (h : ∀, ∀ b ∈ s, ∀, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  Finset.measurable_set_bUnion s h

theorem _root_.set.finite.null_measurable_set_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : ∀, ∀ t ∈ s, ∀, NullMeasurableSet t μ) : NullMeasurableSet (⋃₀s) μ :=
  Finite.measurable_set_sUnion hs h

theorem _root_.set.finite.null_measurable_set_bInter {f : ι → Set α} {s : Set ι} (hs : s.Finite)
    (h : ∀, ∀ b ∈ s, ∀, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  Finite.measurable_set_bInter hs h

theorem _root_.finset.null_measurable_set_bInter {f : ι → Set α} (s : Finset ι)
    (h : ∀, ∀ b ∈ s, ∀, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  s.finite_to_set.null_measurable_set_bInter h

theorem _root_.set.finite.null_measurable_set_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : ∀, ∀ t ∈ s, ∀, NullMeasurableSet t μ) : NullMeasurableSet (⋂₀ s) μ :=
  NullMeasurableSet.sInter hs.Countable h

theorem null_measurable_set_to_measurable : NullMeasurableSet (ToMeasurable μ s) μ :=
  (measurable_set_to_measurable _ _).NullMeasurableSet

end

section NullMeasurable

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {μ : Measure α}

/-- A function `f : α → β` is null measurable if the preimage of a measurable set is a null
measurable set. -/
def NullMeasurable (f : α → β)
    (μ : Measure α := by
      run_tac
        volume_tac) :
    Prop :=
  ∀ ⦃s : Set β⦄, MeasurableSet s → NullMeasurableSet (f ⁻¹' s) μ

protected theorem _root_.measurable.null_measurable (h : Measurable f) : NullMeasurable f μ := fun s hs =>
  (h hs).NullMeasurableSet

protected theorem NullMeasurable.measurable' (h : NullMeasurable f μ) : @Measurable (NullMeasurableSpace α μ) β _ _ f :=
  h

theorem Measurable.comp_null_measurable {g : β → γ} (hg : Measurable g) (hf : NullMeasurable f μ) :
    NullMeasurable (g ∘ f) μ :=
  hg.comp hf

theorem NullMeasurable.congr {g : α → β} (hf : NullMeasurable f μ) (hg : f =ᵐ[μ] g) : NullMeasurable g μ := fun s hs =>
  (hf hs).congr <|
    eventually_eq_set.2 <|
      hg.mono fun x hx => by
        rw [mem_preimage, mem_preimage, hx]

end NullMeasurable

section IsComplete

/-- A measure is complete if every null set is also measurable.
  A null set is a subset of a measurable set with measure `0`.
  Since every measure is defined as a special case of an outer measure, we can more simply state
  that a set `s` is null if `μ s = 0`. -/
class Measure.IsComplete {_ : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : ∀ s, μ s = 0 → MeasurableSet s

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

theorem Measure.is_complete_iff : μ.IsComplete ↔ ∀ s, μ s = 0 → MeasurableSet s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem Measure.IsComplete.out (h : μ.IsComplete) : ∀ s, μ s = 0 → MeasurableSet s :=
  h.1

theorem measurable_set_of_null [μ.IsComplete] (hs : μ s = 0) : MeasurableSet s :=
  MeasureTheory.Measure.IsComplete.out' s hs

theorem NullMeasurableSet.measurable_of_complete (hs : NullMeasurableSet s μ) [μ.IsComplete] : MeasurableSet s :=
  diff_diff_cancel_left (subset_to_measurable μ s) ▸
    (measurable_set_to_measurable _ _).diff (measurable_set_of_null (ae_le_set.1 hs.to_measurable_ae_eq.le))

theorem NullMeasurable.measurable_of_complete [μ.IsComplete] {m1 : MeasurableSpace β} {f : α → β}
    (hf : NullMeasurable f μ) : Measurable f := fun s hs => (hf hs).measurable_of_complete

theorem _root_.measurable.congr_ae {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} [hμ : μ.IsComplete]
    {f g : α → β} (hf : Measurable f) (hfg : f =ᵐ[μ] g) : Measurable g :=
  (hf.NullMeasurable.congr hfg).measurable_of_complete

namespace Measureₓ

/-- Given a measure we can complete it to a (complete) measure on all null measurable sets. -/
def completion {_ : MeasurableSpace α} (μ : Measure α) : @MeasureTheory.Measure (NullMeasurableSpace α μ) _ where
  toOuterMeasure := μ.toOuterMeasure
  m_Union := fun s hs hd => measure_Union₀ (hd.mono fun i j h => h.AeDisjoint) hs
  trimmed := by
    refine' le_antisymmₓ (fun s => _) (outer_measure.le_trim _)
    rw [outer_measure.trim_eq_infi]
    simp only [← to_outer_measure_apply]
    refine' (infi₂_mono _).trans_eq (measure_eq_infi _).symm
    exact fun t ht => infi_mono' fun h => ⟨h.NullMeasurableSet, le_rfl⟩

instance completion.is_complete {m : MeasurableSpace α} (μ : Measure α) : μ.completion.IsComplete :=
  ⟨fun z hz => NullMeasurableSet.of_null hz⟩

@[simp]
theorem coe_completion {_ : MeasurableSpace α} (μ : Measure α) : ⇑μ.completion = μ :=
  rfl

theorem completion_apply {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : μ.completion s = μ s :=
  rfl

end Measureₓ

end IsComplete

end MeasureTheory

