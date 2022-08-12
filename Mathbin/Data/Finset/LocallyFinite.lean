/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yaël Dillies
-/
import Mathbin.Order.LocallyFinite

/-!
# Intervals as finsets

This file provides basic results about all the `finset.Ixx`, which are defined in
`order.locally_finite`.

## TODO

This file was originally only about `finset.Ico a b` where `a b : ℕ`. No care has yet been taken to
generalize these lemmas properly and many lemmas about `Icc`, `Ioc`, `Ioo` are missing. In general,
what's to do is taking the lemmas in `data.x.intervals` and abstract away the concrete structure.

Complete the API. See
https://github.com/leanprover-community/mathlib/pull/14448#discussion_r906109235
for some ideas.
-/


open BigOperators

variable {ι α : Type _}

namespace Finset

section Preorderₓ

variable [Preorderₓ α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

@[simp]
theorem nonempty_Icc : (icc a b).Nonempty ↔ a ≤ b := by
  rw [← coe_nonempty, coe_Icc, Set.nonempty_Icc]

@[simp]
theorem nonempty_Ico : (ico a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ico, Set.nonempty_Ico]

@[simp]
theorem nonempty_Ioc : (ioc a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioc, Set.nonempty_Ioc]

@[simp]
theorem nonempty_Ioo [DenselyOrdered α] : (ioo a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioo, Set.nonempty_Ioo]

@[simp]
theorem Icc_eq_empty_iff : icc a b = ∅ ↔ ¬a ≤ b := by
  rw [← coe_eq_empty, coe_Icc, Set.Icc_eq_empty_iff]

@[simp]
theorem Ico_eq_empty_iff : ico a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ico, Set.Ico_eq_empty_iff]

@[simp]
theorem Ioc_eq_empty_iff : ioc a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioc, Set.Ioc_eq_empty_iff]

@[simp]
theorem Ioo_eq_empty_iff [DenselyOrdered α] : ioo a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioo, Set.Ioo_eq_empty_iff]

alias Icc_eq_empty_iff ↔ _ Icc_eq_empty

alias Ico_eq_empty_iff ↔ _ Ico_eq_empty

alias Ioc_eq_empty_iff ↔ _ Ioc_eq_empty

@[simp]
theorem Ioo_eq_empty (h : ¬a < b) : ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]
theorem Icc_eq_empty_of_lt (h : b < a) : icc a b = ∅ :=
  Icc_eq_empty h.not_le

@[simp]
theorem Ico_eq_empty_of_le (h : b ≤ a) : ico a b = ∅ :=
  Ico_eq_empty h.not_lt

@[simp]
theorem Ioc_eq_empty_of_le (h : b ≤ a) : ioc a b = ∅ :=
  Ioc_eq_empty h.not_lt

@[simp]
theorem Ioo_eq_empty_of_le (h : b ≤ a) : ioo a b = ∅ :=
  Ioo_eq_empty h.not_lt

@[simp]
theorem left_mem_Icc : a ∈ icc a b ↔ a ≤ b := by
  simp only [← mem_Icc, ← true_andₓ, ← le_rfl]

@[simp]
theorem left_mem_Ico : a ∈ ico a b ↔ a < b := by
  simp only [← mem_Ico, ← true_andₓ, ← le_reflₓ]

@[simp]
theorem right_mem_Icc : b ∈ icc a b ↔ a ≤ b := by
  simp only [← mem_Icc, ← and_trueₓ, ← le_rfl]

@[simp]
theorem right_mem_Ioc : b ∈ ioc a b ↔ a < b := by
  simp only [← mem_Ioc, ← and_trueₓ, ← le_rfl]

@[simp]
theorem left_not_mem_Ioc : a ∉ ioc a b := fun h => lt_irreflₓ _ (mem_Ioc.1 h).1

@[simp]
theorem left_not_mem_Ioo : a ∉ ioo a b := fun h => lt_irreflₓ _ (mem_Ioo.1 h).1

@[simp]
theorem right_not_mem_Ico : b ∉ ico a b := fun h => lt_irreflₓ _ (mem_Ico.1 h).2

@[simp]
theorem right_not_mem_Ioo : b ∉ ioo a b := fun h => lt_irreflₓ _ (mem_Ioo.1 h).2

theorem Icc_subset_Icc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : icc a₁ b₁ ⊆ icc a₂ b₂ := by
  simpa [coe_subset] using Set.Icc_subset_Icc ha hb

theorem Ico_subset_Ico (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : ico a₁ b₁ ⊆ ico a₂ b₂ := by
  simpa [coe_subset] using Set.Ico_subset_Ico ha hb

theorem Ioc_subset_Ioc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : ioc a₁ b₁ ⊆ ioc a₂ b₂ := by
  simpa [coe_subset] using Set.Ioc_subset_Ioc ha hb

theorem Ioo_subset_Ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : ioo a₁ b₁ ⊆ ioo a₂ b₂ := by
  simpa [coe_subset] using Set.Ioo_subset_Ioo ha hb

theorem Icc_subset_Icc_left (h : a₁ ≤ a₂) : icc a₂ b ⊆ icc a₁ b :=
  Icc_subset_Icc h le_rfl

theorem Ico_subset_Ico_left (h : a₁ ≤ a₂) : ico a₂ b ⊆ ico a₁ b :=
  Ico_subset_Ico h le_rfl

theorem Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : ioc a₂ b ⊆ ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl

theorem Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : ioo a₂ b ⊆ ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl

theorem Icc_subset_Icc_right (h : b₁ ≤ b₂) : icc a b₁ ⊆ icc a b₂ :=
  Icc_subset_Icc le_rfl h

theorem Ico_subset_Ico_right (h : b₁ ≤ b₂) : ico a b₁ ⊆ ico a b₂ :=
  Ico_subset_Ico le_rfl h

theorem Ioc_subset_Ioc_right (h : b₁ ≤ b₂) : ioc a b₁ ⊆ ioc a b₂ :=
  Ioc_subset_Ioc le_rfl h

theorem Ioo_subset_Ioo_right (h : b₁ ≤ b₂) : ioo a b₁ ⊆ ioo a b₂ :=
  Ioo_subset_Ioo le_rfl h

theorem Ico_subset_Ioo_left (h : a₁ < a₂) : ico a₂ b ⊆ ioo a₁ b := by
  rw [← coe_subset, coe_Ico, coe_Ioo]
  exact Set.Ico_subset_Ioo_left h

theorem Ioc_subset_Ioo_right (h : b₁ < b₂) : ioc a b₁ ⊆ ioo a b₂ := by
  rw [← coe_subset, coe_Ioc, coe_Ioo]
  exact Set.Ioc_subset_Ioo_right h

theorem Icc_subset_Ico_right (h : b₁ < b₂) : icc a b₁ ⊆ ico a b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ico]
  exact Set.Icc_subset_Ico_right h

theorem Ioo_subset_Ico_self : ioo a b ⊆ ico a b := by
  rw [← coe_subset, coe_Ioo, coe_Ico]
  exact Set.Ioo_subset_Ico_self

theorem Ioo_subset_Ioc_self : ioo a b ⊆ ioc a b := by
  rw [← coe_subset, coe_Ioo, coe_Ioc]
  exact Set.Ioo_subset_Ioc_self

theorem Ico_subset_Icc_self : ico a b ⊆ icc a b := by
  rw [← coe_subset, coe_Ico, coe_Icc]
  exact Set.Ico_subset_Icc_self

theorem Ioc_subset_Icc_self : ioc a b ⊆ icc a b := by
  rw [← coe_subset, coe_Ioc, coe_Icc]
  exact Set.Ioc_subset_Icc_self

theorem Ioo_subset_Icc_self : ioo a b ⊆ icc a b :=
  Ioo_subset_Ico_self.trans Ico_subset_Icc_self

theorem Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Icc, coe_Icc, Set.Icc_subset_Icc_iff h₁]

theorem Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ioo, Set.Icc_subset_Ioo_iff h₁]

theorem Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ico, Set.Icc_subset_Ico_iff h₁]

theorem Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  (Icc_subset_Ico_iff h₁.dual).trans And.comm

--TODO: `Ico_subset_Ioo_iff`, `Ioc_subset_Ioo_iff`
theorem Icc_ssubset_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : icc a₁ b₁ ⊂ icc a₂ b₂ := by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_left hI ha hb

theorem Icc_ssubset_Icc_right (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) : icc a₁ b₁ ⊂ icc a₂ b₂ := by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_right hI ha hb

variable (a)

@[simp]
theorem Ico_self : ico a a = ∅ :=
  Ico_eq_empty <| lt_irreflₓ _

@[simp]
theorem Ioc_self : ioc a a = ∅ :=
  Ioc_eq_empty <| lt_irreflₓ _

@[simp]
theorem Ioo_self : ioo a a = ∅ :=
  Ioo_eq_empty <| lt_irreflₓ _

variable {a}

/-- A set with upper and lower bounds in a locally finite order is a fintype -/
def _root_.set.fintype_of_mem_bounds {s : Set α} [DecidablePred (· ∈ s)] (ha : a ∈ LowerBounds s)
    (hb : b ∈ UpperBounds s) : Fintype s :=
  (Set.fintypeSubset (Set.Icc a b)) fun x hx => ⟨ha hx, hb hx⟩

theorem _root_.bdd_below.finite_of_bdd_above {s : Set α} (h₀ : BddBelow s) (h₁ : BddAbove s) : s.Finite := by
  let ⟨a, ha⟩ := h₀
  let ⟨b, hb⟩ := h₁
  classical
  exact ⟨Set.fintypeOfMemBounds ha hb⟩

section Filter

theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) : (ico a b).filter (· < c) = ∅ :=
  filter_false_of_mem fun x hx => (hca.trans (mem_Ico.1 hx).1).not_lt

theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) : (ico a b).filter (· < c) = ico a b :=
  filter_true_of_mem fun x hx => (mem_Ico.1 hx).2.trans_le hbc

theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) : (ico a b).filter (· < c) = ico a c := by
  ext x
  rw [mem_filter, mem_Ico, mem_Ico, And.right_comm]
  exact and_iff_left_of_imp fun h => h.2.trans_le hcb

theorem Ico_filter_le_of_le_left {a b c : α} [DecidablePred ((· ≤ ·) c)] (hca : c ≤ a) :
    (ico a b).filter ((· ≤ ·) c) = ico a b :=
  filter_true_of_mem fun x hx => hca.trans (mem_Ico.1 hx).1

theorem Ico_filter_le_of_right_le {a b : α} [DecidablePred ((· ≤ ·) b)] : (ico a b).filter ((· ≤ ·) b) = ∅ :=
  filter_false_of_mem fun x hx => (mem_Ico.1 hx).2.not_le

theorem Ico_filter_le_of_left_le {a b c : α} [DecidablePred ((· ≤ ·) c)] (hac : a ≤ c) :
    (ico a b).filter ((· ≤ ·) c) = ico c b := by
  ext x
  rw [mem_filter, mem_Ico, mem_Ico, and_comm, And.left_comm]
  exact and_iff_right_of_imp fun h => hac.trans h.1

variable (a b) [Fintype α]

theorem filter_lt_lt_eq_Ioo [DecidablePred fun j => a < j ∧ j < b] : (univ.filter fun j => a < j ∧ j < b) = ioo a b :=
  by
  ext
  simp

theorem filter_lt_le_eq_Ioc [DecidablePred fun j => a < j ∧ j ≤ b] : (univ.filter fun j => a < j ∧ j ≤ b) = ioc a b :=
  by
  ext
  simp

theorem filter_le_lt_eq_Ico [DecidablePred fun j => a ≤ j ∧ j < b] : (univ.filter fun j => a ≤ j ∧ j < b) = ico a b :=
  by
  ext
  simp

theorem filter_le_le_eq_Icc [DecidablePred fun j => a ≤ j ∧ j ≤ b] : (univ.filter fun j => a ≤ j ∧ j ≤ b) = icc a b :=
  by
  ext
  simp

end Filter

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

theorem Icc_subset_Ici_self : icc a b ⊆ ici a := by
  simpa [coe_subset] using Set.Icc_subset_Ici_self

theorem Ico_subset_Ici_self : ico a b ⊆ ici a := by
  simpa [coe_subset] using Set.Ico_subset_Ici_self

theorem Ioc_subset_Ioi_self : ioc a b ⊆ ioi a := by
  simpa [coe_subset] using Set.Ioc_subset_Ioi_self

theorem Ioo_subset_Ioi_self : ioo a b ⊆ ioi a := by
  simpa [coe_subset] using Set.Ioo_subset_Ioi_self

theorem Ioc_subset_Ici_self : ioc a b ⊆ ici a :=
  Ioc_subset_Icc_self.trans Icc_subset_Ici_self

theorem Ioo_subset_Ici_self : ioo a b ⊆ ici a :=
  Ioo_subset_Ico_self.trans Ico_subset_Ici_self

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

theorem Icc_subset_Iic_self : icc a b ⊆ iic b := by
  simpa [coe_subset] using Set.Icc_subset_Iic_self

theorem Ioc_subset_Iic_self : ioc a b ⊆ iic b := by
  simpa [coe_subset] using Set.Ioc_subset_Iic_self

theorem Ico_subset_Iio_self : ico a b ⊆ iio b := by
  simpa [coe_subset] using Set.Ico_subset_Iio_self

theorem Ioo_subset_Iio_self : ioo a b ⊆ iio b := by
  simpa [coe_subset] using Set.Ioo_subset_Iio_self

theorem Ico_subset_Iic_self : ico a b ⊆ iic b :=
  Ico_subset_Icc_self.trans Icc_subset_Iic_self

theorem Ioo_subset_Iic_self : ioo a b ⊆ iic b :=
  Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self

end LocallyFiniteOrderBot

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a : α}

theorem Ioi_subset_Ici_self : ioi a ⊆ ici a := by
  simpa [coe_subset] using Set.Ioi_subset_Ici_self

theorem _root_.bdd_below.finite {s : Set α} (hs : BddBelow s) : s.Finite :=
  let ⟨a, ha⟩ := hs
  (ici a).finite_to_set.Subset fun x hx => mem_Ici.2 <| ha hx

variable [Fintype α]

theorem filter_lt_eq_Ioi [DecidablePred ((· < ·) a)] : univ.filter ((· < ·) a) = ioi a := by
  ext
  simp

theorem filter_le_eq_Ici [DecidablePred ((· ≤ ·) a)] : univ.filter ((· ≤ ·) a) = ici a := by
  ext
  simp

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a : α}

theorem Iio_subset_Iic_self : iio a ⊆ iic a := by
  simpa [coe_subset] using Set.Iio_subset_Iic_self

theorem _root_.bdd_above.finite {s : Set α} (hs : BddAbove s) : s.Finite :=
  hs.dual.Finite

variable [Fintype α]

theorem filter_gt_eq_Iio [DecidablePred (· < a)] : univ.filter (· < a) = iio a := by
  ext
  simp

theorem filter_ge_eq_Iic [DecidablePred (· ≤ a)] : univ.filter (· ≤ a) = iic a := by
  ext
  simp

end LocallyFiniteOrderBot

variable [DecidableEq α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

theorem disjoint_Ioi_Iio (a : α) : Disjoint (ioi a) (iio a) :=
  disjoint_left.2 fun b hab hba => (mem_Ioi.1 hab).not_lt <| mem_Iio.1 hba

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [LocallyFiniteOrder α] {a b c : α}

@[simp]
theorem Icc_self (a : α) : icc a a = {a} := by
  rw [← coe_eq_singleton, coe_Icc, Set.Icc_self]

@[simp]
theorem Icc_eq_singleton_iff : icc a b = {c} ↔ a = c ∧ b = c := by
  rw [← coe_eq_singleton, coe_Icc, Set.Icc_eq_singleton_iff]

section DecidableEq

variable [DecidableEq α]

@[simp]
theorem Icc_erase_left (a b : α) : (icc a b).erase a = ioc a b := by
  simp [coe_inj]

@[simp]
theorem Icc_erase_right (a b : α) : (icc a b).erase b = ico a b := by
  simp [coe_inj]

@[simp]
theorem Ico_erase_left (a b : α) : (ico a b).erase a = ioo a b := by
  simp [coe_inj]

@[simp]
theorem Ioc_erase_right (a b : α) : (ioc a b).erase b = ioo a b := by
  simp [coe_inj]

@[simp]
theorem Icc_diff_both (a b : α) : icc a b \ {a, b} = ioo a b := by
  simp [coe_inj]

@[simp]
theorem Ico_insert_right (h : a ≤ b) : insert b (ico a b) = icc a b := by
  rw [← coe_inj, coe_insert, coe_Icc, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ico_union_right h]

@[simp]
theorem Ioc_insert_left (h : a ≤ b) : insert a (ioc a b) = icc a b := by
  rw [← coe_inj, coe_insert, coe_Ioc, coe_Icc, Set.insert_eq, Set.union_comm, Set.Ioc_union_left h]

@[simp]
theorem Ioo_insert_left (h : a < b) : insert a (ioo a b) = ico a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ioo_union_left h]

@[simp]
theorem Ioo_insert_right (h : a < b) : insert b (ioo a b) = ioc a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ioc, Set.insert_eq, Set.union_comm, Set.Ioo_union_right h]

@[simp]
theorem Icc_diff_Ico_self (h : a ≤ b) : icc a b \ ico a b = {b} := by
  simp [coe_inj, ← h]

@[simp]
theorem Icc_diff_Ioc_self (h : a ≤ b) : icc a b \ ioc a b = {a} := by
  simp [coe_inj, ← h]

@[simp]
theorem Icc_diff_Ioo_self (h : a ≤ b) : icc a b \ ioo a b = {a, b} := by
  simp [coe_inj, ← h]

@[simp]
theorem Ico_diff_Ioo_self (h : a < b) : ico a b \ ioo a b = {a} := by
  simp [coe_inj, ← h]

@[simp]
theorem Ioc_diff_Ioo_self (h : a < b) : ioc a b \ ioo a b = {b} := by
  simp [coe_inj, ← h]

@[simp]
theorem Ico_inter_Ico_consecutive (a b c : α) : ico a b ∩ ico b c = ∅ := by
  refine' eq_empty_of_forall_not_mem fun x hx => _
  rw [mem_inter, mem_Ico, mem_Ico] at hx
  exact hx.1.2.not_le hx.2.1

theorem Ico_disjoint_Ico_consecutive (a b c : α) : Disjoint (ico a b) (ico b c) :=
  le_of_eqₓ <| Ico_inter_Ico_consecutive a b c

end DecidableEq

-- Those lemmas are purposefully the other way around
theorem Icc_eq_cons_Ico (h : a ≤ b) : icc a b = (ico a b).cons b right_not_mem_Ico := by
  classical
  rw [cons_eq_insert, Ico_insert_right h]

theorem Icc_eq_cons_Ioc (h : a ≤ b) : icc a b = (ioc a b).cons a left_not_mem_Ioc := by
  classical
  rw [cons_eq_insert, Ioc_insert_left h]

theorem Ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) : ((ico a b).filter fun x => x ≤ a) = {a} :=
  by
  ext x
  rw [mem_filter, mem_Ico, mem_singleton, And.right_comm, ← le_antisymm_iffₓ, eq_comm]
  exact and_iff_left_of_imp fun h => h.le.trans_lt hab

theorem card_Ico_eq_card_Icc_sub_one (a b : α) : (ico a b).card = (icc a b).card - 1 := by
  classical
  by_cases' h : a ≤ b
  · rw [← Ico_insert_right h, card_insert_of_not_mem right_not_mem_Ico]
    exact (Nat.add_sub_cancel _ _).symm
    
  · rw [Ico_eq_empty fun h' => h h'.le, Icc_eq_empty h, card_empty, zero_tsub]
    

theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : (ioc a b).card = (icc a b).card - 1 :=
  @card_Ico_eq_card_Icc_sub_one αᵒᵈ _ _ _ _

theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : (ioo a b).card = (ico a b).card - 1 := by
  classical
  by_cases' h : a ≤ b
  · obtain rfl | h' := h.eq_or_lt
    · rw [Ioo_self, Ico_self, card_empty]
      
    rw [← Ioo_insert_left h', card_insert_of_not_mem left_not_mem_Ioo]
    exact (Nat.add_sub_cancel _ _).symm
    
  · rw [Ioo_eq_empty fun h' => h h'.le, Ico_eq_empty fun h' => h h'.le, card_empty, zero_tsub]
    

theorem card_Ioo_eq_card_Ioc_sub_one (a b : α) : (ioo a b).card = (ioc a b).card - 1 :=
  @card_Ioo_eq_card_Ico_sub_one αᵒᵈ _ _ _ _

theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : (ioo a b).card = (icc a b).card - 2 := by
  rw [card_Ioo_eq_card_Ico_sub_one, card_Ico_eq_card_Icc_sub_one]
  rfl

section OrderTop

variable [OrderTop α]

@[simp]
theorem Ici_erase [DecidableEq α] (a : α) : (ici a).erase a = ioi a :=
  Icc_erase_left _ _

@[simp]
theorem Ioi_insert [DecidableEq α] (a : α) : insert a (ioi a) = ici a :=
  Ioc_insert_left le_top

-- Purposefully written the other way around
theorem Ici_eq_cons_Ioi (a : α) : ici a = (ioi a).cons a left_not_mem_Ioc := by
  classical
  rw [cons_eq_insert, Ioi_insert]

end OrderTop

section OrderBot

variable [OrderBot α]

@[simp]
theorem Iic_erase [DecidableEq α] (b : α) : (iic b).erase b = iio b :=
  Icc_erase_right _ _

@[simp]
theorem Iio_insert [DecidableEq α] (b : α) : insert b (iio b) = iic b :=
  Ico_insert_right bot_le

-- Purposefully written the other way around
theorem Iic_eq_cons_Iio (b : α) : iic b = (iio b).cons b right_not_mem_Ico := by
  classical
  rw [cons_eq_insert, Iio_insert]

end OrderBot

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b : α}

theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) : ico a₁ b₁ ⊆ ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Ico, coe_Ico, Set.Ico_subset_Ico_iff h]

theorem Ico_union_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) : ico a b ∪ ico b c = ico a c := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico_eq_Ico hab hbc]

@[simp]
theorem Ioc_union_Ioc_eq_Ioc {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : ioc a b ∪ ioc b c = ioc a c := by
  rw [← coe_inj, coe_union, coe_Ioc, coe_Ioc, coe_Ioc, Set.Ioc_union_Ioc_eq_Ioc h₁ h₂]

theorem Ico_subset_Ico_union_Ico {a b c : α} : ico a c ⊆ ico a b ∪ ico b c := by
  rw [← coe_subset, coe_union, coe_Ico, coe_Ico, coe_Ico]
  exact Set.Ico_subset_Ico_union_Ico

theorem Ico_union_Ico' {a b c d : α} (hcb : c ≤ b) (had : a ≤ d) : ico a b ∪ ico c d = ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico' hcb had]

theorem Ico_union_Ico {a b c d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    ico a b ∪ ico c d = ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico h₁ h₂]

theorem Ico_inter_Ico {a b c d : α} : ico a b ∩ ico c d = ico (max a c) (min b d) := by
  rw [← coe_inj, coe_inter, coe_Ico, coe_Ico, coe_Ico, ← inf_eq_min, ← sup_eq_max, Set.Ico_inter_Ico]

@[simp]
theorem Ico_filter_lt (a b c : α) : ((ico a b).filter fun x => x < c) = ico a (min b c) := by
  cases le_totalₓ b c
  · rw [Ico_filter_lt_of_right_le h, min_eq_leftₓ h]
    
  · rw [Ico_filter_lt_of_le_right h, min_eq_rightₓ h]
    

@[simp]
theorem Ico_filter_le (a b c : α) : ((ico a b).filter fun x => c ≤ x) = ico (max a c) b := by
  cases le_totalₓ a c
  · rw [Ico_filter_le_of_left_le h, max_eq_rightₓ h]
    
  · rw [Ico_filter_le_of_le_left h, max_eq_leftₓ h]
    

@[simp]
theorem Ico_diff_Ico_left (a b c : α) : ico a b \ ico a c = ico (max a c) b := by
  cases le_totalₓ a c
  · ext x
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, max_eq_rightₓ h, And.right_comm, not_and, not_ltₓ]
    exact and_congr_left' ⟨fun hx => hx.2 hx.1, fun hx => ⟨h.trans hx, fun _ => hx⟩⟩
    
  · rw [Ico_eq_empty_of_le h, sdiff_empty, max_eq_leftₓ h]
    

@[simp]
theorem Ico_diff_Ico_right (a b c : α) : ico a b \ ico c b = ico a (min b c) := by
  cases le_totalₓ b c
  · rw [Ico_eq_empty_of_le h, sdiff_empty, min_eq_leftₓ h]
    
  · ext x
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, min_eq_rightₓ h, and_assoc, not_and', not_leₓ]
    exact and_congr_right' ⟨fun hx => hx.2 hx.1, fun hx => ⟨hx.trans_le h, fun _ => hx⟩⟩
    

end LocallyFiniteOrder

variable [Fintype α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

theorem Ioi_disj_union_Iio (a : α) :
    (ioi a).disjUnion (iio a) (disjoint_left.1 <| disjoint_Ioi_Iio a) = ({a} : Finset α)ᶜ := by
  ext
  simp [← eq_comm]

end LinearOrderₓ

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid α] [HasExistsAddOfLe α] [DecidableEq α] [LocallyFiniteOrder α]

theorem image_add_left_Icc (a b c : α) : (icc a b).Image ((· + ·) c) = icc (c + a) (c + b) := by
  ext x
  rw [mem_image, mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_Icc] at hy
    exact ⟨add_le_add_left hy.1 c, add_le_add_left hy.2 c⟩
    
  · intro hx
    obtain ⟨y, hy⟩ := exists_add_of_le hx.1
    rw [add_assocₓ] at hy
    rw [hy] at hx
    exact ⟨a + y, mem_Icc.2 ⟨le_of_add_le_add_left hx.1, le_of_add_le_add_left hx.2⟩, hy.symm⟩
    

theorem image_add_left_Ico (a b c : α) : (ico a b).Image ((· + ·) c) = ico (c + a) (c + b) := by
  ext x
  rw [mem_image, mem_Ico]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_Ico] at hy
    exact ⟨add_le_add_left hy.1 c, add_lt_add_left hy.2 c⟩
    
  · intro hx
    obtain ⟨y, hy⟩ := exists_add_of_le hx.1
    rw [add_assocₓ] at hy
    rw [hy] at hx
    exact ⟨a + y, mem_Ico.2 ⟨le_of_add_le_add_left hx.1, lt_of_add_lt_add_left hx.2⟩, hy.symm⟩
    

theorem image_add_left_Ioc (a b c : α) : (ioc a b).Image ((· + ·) c) = ioc (c + a) (c + b) := by
  ext x
  rw [mem_image, mem_Ioc]
  refine' ⟨_, fun hx => _⟩
  · rintro ⟨y, hy, rfl⟩
    rw [mem_Ioc] at hy
    exact ⟨add_lt_add_left hy.1 c, add_le_add_left hy.2 c⟩
    
  · obtain ⟨y, hy⟩ := exists_add_of_le hx.1.le
    rw [add_assocₓ] at hy
    rw [hy] at hx
    exact ⟨a + y, mem_Ioc.2 ⟨lt_of_add_lt_add_left hx.1, le_of_add_le_add_left hx.2⟩, hy.symm⟩
    

theorem image_add_left_Ioo (a b c : α) : (ioo a b).Image ((· + ·) c) = ioo (c + a) (c + b) := by
  ext x
  rw [mem_image, mem_Ioo]
  refine' ⟨_, fun hx => _⟩
  · rintro ⟨y, hy, rfl⟩
    rw [mem_Ioo] at hy
    exact ⟨add_lt_add_left hy.1 c, add_lt_add_left hy.2 c⟩
    
  · obtain ⟨y, hy⟩ := exists_add_of_le hx.1.le
    rw [add_assocₓ] at hy
    rw [hy] at hx
    exact ⟨a + y, mem_Ioo.2 ⟨lt_of_add_lt_add_left hx.1, lt_of_add_lt_add_left hx.2⟩, hy.symm⟩
    

theorem image_add_right_Icc (a b c : α) : (icc a b).Image (· + c) = icc (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact image_add_left_Icc a b c

theorem image_add_right_Ico (a b c : α) : (ico a b).Image (· + c) = ico (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact image_add_left_Ico a b c

theorem image_add_right_Ioc (a b c : α) : (ioc a b).Image (· + c) = ioc (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact image_add_left_Ioc a b c

theorem image_add_right_Ioo (a b c : α) : (ioo a b).Image (· + c) = ioo (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact image_add_left_Ioo a b c

end OrderedCancelAddCommMonoid

@[to_additive]
theorem prod_prod_Ioi_mul_eq_prod_prod_off_diag [Fintype ι] [LinearOrderₓ ι] [LocallyFiniteOrderTop ι]
    [LocallyFiniteOrderBot ι] [CommMonoidₓ α] (f : ι → ι → α) :
    (∏ i, ∏ j in ioi i, f j i * f i j) = ∏ i, ∏ j in {i}ᶜ, f j i := by
  simp_rw [← Ioi_disj_union_Iio, prod_disj_union, prod_mul_distrib]
  congr 1
  rw [prod_sigma', prod_sigma']
  refine' prod_bij' (fun i hi => ⟨i.2, i.1⟩) _ _ (fun i hi => ⟨i.2, i.1⟩) _ _ _ <;> simp

end Finset

