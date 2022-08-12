/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.Card
import Mathbin.Data.Multiset.Sum

/-!
# Disjoint sum of finsets

This file defines the disjoint sum of two finsets as `finset (α ⊕ β)`. Beware not to confuse with
the `finset.sum` operation which computes the additive sum.

## Main declarations

* `finset.disj_sum`: `s.disj_sum t` is the disjoint sum of `s` and `t`.
-/


open Function Multiset Sum

namespace Finset

variable {α β : Type _} (s : Finset α) (t : Finset β)

/-- Disjoint sum of finsets. -/
def disjSum : Finset (Sum α β) :=
  ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩

@[simp]
theorem val_disj_sum : (s.disjSum t).1 = s.1.disjSum t.1 :=
  rfl

@[simp]
theorem empty_disj_sum : (∅ : Finset α).disjSum t = t.map Embedding.inr :=
  val_inj.1 <| Multiset.zero_disj_sum _

@[simp]
theorem disj_sum_empty : s.disjSum (∅ : Finset β) = s.map Embedding.inl :=
  val_inj.1 <| Multiset.disj_sum_zero _

@[simp]
theorem card_disj_sum : (s.disjSum t).card = s.card + t.card :=
  Multiset.card_disj_sum _ _

variable {s t} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} {a : α} {b : β} {x : Sum α β}

theorem mem_disj_sum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
  Multiset.mem_disj_sum

@[simp]
theorem inl_mem_disj_sum : inl a ∈ s.disjSum t ↔ a ∈ s :=
  inl_mem_disj_sum

@[simp]
theorem inr_mem_disj_sum : inr b ∈ s.disjSum t ↔ b ∈ t :=
  inr_mem_disj_sum

theorem disj_sum_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁.disjSum t₁ ⊆ s₂.disjSum t₂ :=
  val_le_iff.1 <| disj_sum_mono (val_le_iff.2 hs) (val_le_iff.2 ht)

theorem disj_sum_mono_left (t : Finset β) : Monotone fun s : Finset α => s.disjSum t := fun s₁ s₂ hs =>
  disj_sum_mono hs Subset.rfl

theorem disj_sum_mono_right (s : Finset α) : Monotone (s.disjSum : Finset β → Finset (Sum α β)) := fun t₁ t₂ =>
  disj_sum_mono Subset.rfl

theorem disj_sum_ssubset_disj_sum_of_ssubset_of_subset (hs : s₁ ⊂ s₂) (ht : t₁ ⊆ t₂) : s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disj_sum_lt_disj_sum_of_lt_of_le (val_lt_iff.2 hs) (val_le_iff.2 ht)

theorem disj_sum_ssubset_disj_sum_of_subset_of_ssubset (hs : s₁ ⊆ s₂) (ht : t₁ ⊂ t₂) : s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disj_sum_lt_disj_sum_of_le_of_lt (val_le_iff.2 hs) (val_lt_iff.2 ht)

theorem disj_sum_strict_mono_left (t : Finset β) : StrictMono fun s : Finset α => s.disjSum t := fun s₁ s₂ hs =>
  disj_sum_ssubset_disj_sum_of_ssubset_of_subset hs Subset.rfl

theorem disj_sum_strict_mono_right (s : Finset α) : StrictMono (s.disjSum : Finset β → Finset (Sum α β)) := fun s₁ s₂ =>
  disj_sum_ssubset_disj_sum_of_subset_of_ssubset Subset.rfl

end Finset

