/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Order.UpperLower

/-!
# Intersecting families

This file defines intersecting families and proves their basic properties.

## Main declarations

* `set.intersecting`: Predicate for a set of elements in a generalized boolean algebra to be an
  intersecting family.
* `set.intersecting.card_le`: An intersecting family can only take up to half the elements, because
  `a` and `aᶜ` cannot simultaneously be in it.
* `set.intersecting.is_max_iff_card_eq`: Any maximal intersecting family takes up half the elements.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/


open Finset

variable {α : Type _}

namespace Set

section SemilatticeInf

variable [SemilatticeInf α] [OrderBot α] {s t : Set α} {a b c : α}

/-- A set family is intersecting if every pair of elements is non-disjoint. -/
def Intersecting (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ¬Disjoint a b

@[mono]
theorem Intersecting.mono (h : t ⊆ s) (hs : s.Intersecting) : t.Intersecting := fun a ha b hb => hs (h ha) (h hb)

theorem Intersecting.not_bot_mem (hs : s.Intersecting) : ⊥ ∉ s := fun h => hs h h disjoint_bot_left

theorem Intersecting.ne_bot (hs : s.Intersecting) (ha : a ∈ s) : a ≠ ⊥ :=
  ne_of_mem_of_not_mem ha hs.not_bot_mem

theorem intersecting_empty : (∅ : Set α).Intersecting := fun _ => False.elim

@[simp]
theorem intersecting_singleton : ({a} : Set α).Intersecting ↔ a ≠ ⊥ := by
  simp [← intersecting]

theorem Intersecting.insert (hs : s.Intersecting) (ha : a ≠ ⊥) (h : ∀, ∀ b ∈ s, ∀, ¬Disjoint a b) :
    (insert a s).Intersecting := by
  rintro b (rfl | hb) c (rfl | hc)
  · rwa [disjoint_self]
    
  · exact h _ hc
    
  · exact fun H => h _ hb H.symm
    
  · exact hs hb hc
    

theorem intersecting_insert : (insert a s).Intersecting ↔ s.Intersecting ∧ a ≠ ⊥ ∧ ∀, ∀ b ∈ s, ∀, ¬Disjoint a b :=
  ⟨fun h =>
    ⟨h.mono <| subset_insert _ _, h.ne_bot <| mem_insert _ _, fun b hb => h (mem_insert _ _) <| mem_insert_of_mem _ hb⟩,
    fun h => h.1.insert h.2.1 h.2.2⟩

theorem intersecting_iff_pairwise_not_disjoint : s.Intersecting ↔ (s.Pairwise fun a b => ¬Disjoint a b) ∧ s ≠ {⊥} := by
  refine' ⟨fun h => ⟨fun a ha b hb _ => h ha hb, _⟩, fun h a ha b hb hab => _⟩
  · rintro rfl
    exact intersecting_singleton.1 h rfl
    
  · have := h.1.Eq ha hb (not_not.2 hab)
    rw [this, disjoint_self] at hab
    rw [hab] at hb
    exact h.2 (eq_singleton_iff_unique_mem.2 ⟨hb, fun c hc => not_ne_iff.1 fun H => h.1 hb hc H.symm disjoint_bot_left⟩)
    

protected theorem Subsingleton.intersecting (hs : s.Subsingleton) : s.Intersecting ↔ s ≠ {⊥} :=
  intersecting_iff_pairwise_not_disjoint.trans <| and_iff_right <| hs.Pairwise _

theorem intersecting_iff_eq_empty_of_subsingleton [Subsingleton α] (s : Set α) : s.Intersecting ↔ s = ∅ := by
  refine'
    subsingleton_of_subsingleton.intersecting.trans
      ⟨not_imp_comm.2 fun h => subsingleton_of_subsingleton.eq_singleton_of_mem _, _⟩
  · obtain ⟨a, ha⟩ := ne_empty_iff_nonempty.1 h
    rwa [Subsingleton.elimₓ ⊥ a]
    
  · rintro rfl
    exact (Set.singleton_nonempty _).ne_empty.symm
    

/-- Maximal intersecting families are upper sets. -/
protected theorem Intersecting.is_upper_set (hs : s.Intersecting) (h : ∀ t : Set α, t.Intersecting → s ⊆ t → s = t) :
    IsUpperSet s := by
  classical
  rintro a b hab ha
  rw [h (insert b s) _ (subset_insert _ _)]
  · exact mem_insert _ _
    
  exact hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc <| hbc.mono_left hab

/-- Maximal intersecting families are upper sets. Finset version. -/
theorem Intersecting.is_upper_set' {s : Finset α} (hs : (s : Set α).Intersecting)
    (h : ∀ t : Finset α, (t : Set α).Intersecting → s ⊆ t → s = t) : IsUpperSet (s : Set α) := by
  classical
  rintro a b hab ha
  rw [h (insert b s) _ (Finset.subset_insert _ _)]
  · exact mem_insert_self _ _
    
  rw [coe_insert]
  exact hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc <| hbc.mono_left hab

end SemilatticeInf

theorem Intersecting.exists_mem_set {𝒜 : Set (Set α)} (h𝒜 : 𝒜.Intersecting) {s t : Set α} (hs : s ∈ 𝒜) (ht : t ∈ 𝒜) :
    ∃ a, a ∈ s ∧ a ∈ t :=
  not_disjoint_iff.1 <| h𝒜 hs ht

theorem Intersecting.exists_mem_finset [DecidableEq α] {𝒜 : Set (Finset α)} (h𝒜 : 𝒜.Intersecting) {s t : Finset α}
    (hs : s ∈ 𝒜) (ht : t ∈ 𝒜) : ∃ a, a ∈ s ∧ a ∈ t :=
  not_disjoint_iff.1 <| disjoint_coe.Not.2 <| h𝒜 hs ht

variable [BooleanAlgebra α]

theorem Intersecting.not_compl_mem {s : Set α} (hs : s.Intersecting) {a : α} (ha : a ∈ s) : aᶜ ∉ s := fun h =>
  hs ha h disjoint_compl_right

theorem Intersecting.not_mem {s : Set α} (hs : s.Intersecting) {a : α} (ha : aᶜ ∈ s) : a ∉ s := fun h =>
  hs ha h disjoint_compl_left

variable [Fintype α] {s : Finset α}

theorem Intersecting.card_le (hs : (s : Set α).Intersecting) : 2 * s.card ≤ Fintype.card α := by
  classical
  refine' (s ∪ s.map ⟨compl, compl_injective⟩).card_le_univ.trans_eq' _
  rw [two_mul, card_union_eq, card_map]
  rintro x hx
  rw [Finset.inf_eq_inter, Finset.mem_inter, mem_map] at hx
  obtain ⟨x, hx', rfl⟩ := hx.2
  exact hs.not_compl_mem hx' hx.1

variable [Nontrivial α]

-- Note, this lemma is false when `α` has exactly one element and boring when `α` is empty.
theorem Intersecting.is_max_iff_card_eq (hs : (s : Set α).Intersecting) :
    (∀ t : Finset α, (t : Set α).Intersecting → s ⊆ t → s = t) ↔ 2 * s.card = Fintype.card α := by
  classical
  refine'
    ⟨fun h => _, fun h t ht hst =>
      eq_of_subset_of_card_le hst <| le_of_mul_le_mul_left (ht.card_le.trans_eq h.symm) two_pos⟩
  suffices s ∪ s.map ⟨compl, compl_injective⟩ = Finset.univ by
    rw [Fintype.card, ← this, two_mul, card_union_eq, card_map]
    rintro x hx
    rw [Finset.inf_eq_inter, Finset.mem_inter, mem_map] at hx
    obtain ⟨x, hx', rfl⟩ := hx.2
    exact hs.not_compl_mem hx' hx.1
  rw [← coe_eq_univ, coe_union, coe_map, Function.Embedding.coe_fn_mk,
    image_eq_preimage_of_inverse compl_compl compl_compl]
  refine' eq_univ_of_forall fun a => _
  simp_rw [mem_union, mem_preimage]
  by_contra' ha
  refine' s.ne_insert_of_not_mem _ ha.1 (h _ _ <| s.subset_insert _)
  rw [coe_insert]
  refine' hs.insert _ fun b hb hab => ha.2 <| (hs.is_upper_set' h) hab.le_compl_left hb
  rintro rfl
  have :=
    h {⊤}
      (by
        rw [coe_singleton]
        exact intersecting_singleton.2 top_ne_bot)
  rw [compl_bot] at ha
  rw [coe_eq_empty.1 ((hs.is_upper_set' h).not_top_mem.1 ha.2)] at this
  exact singleton_ne_empty _ (this <| empty_subset _).symm

theorem Intersecting.exists_card_eq (hs : (s : Set α).Intersecting) :
    ∃ t, s ⊆ t ∧ 2 * t.card = Fintype.card α ∧ (t : Set α).Intersecting := by
  have := hs.card_le
  rw [mul_comm, ← Nat.le_div_iff_mul_le' two_pos] at this
  revert hs
  refine' s.strong_downward_induction_on _ this
  rintro s ih hcard hs
  by_cases' ∀ t : Finset α, (t : Set α).Intersecting → s ⊆ t → s = t
  · exact ⟨s, subset.rfl, hs.is_max_iff_card_eq.1 h, hs⟩
    
  push_neg  at h
  obtain ⟨t, ht, hst⟩ := h
  refine' (ih _ (_root_.ssubset_iff_subset_ne.2 hst) ht).imp fun u => And.imp_left hst.1.trans
  rw [Nat.le_div_iff_mul_le' two_pos, mul_comm]
  exact ht.card_le

end Set

