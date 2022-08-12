/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.LocallyFinite

/-!
# Intervals as multisets

This file provides basic results about all the `multiset.Ixx`, which are defined in
`order.locally_finite`.
-/


variable {α : Type _}

namespace Multiset

section Preorderₓ

variable [Preorderₓ α] [LocallyFiniteOrder α] {a b c : α}

theorem nodup_Icc : (icc a b).Nodup :=
  Finset.nodup _

theorem nodup_Ico : (ico a b).Nodup :=
  Finset.nodup _

theorem nodup_Ioc : (ioc a b).Nodup :=
  Finset.nodup _

theorem nodup_Ioo : (ioo a b).Nodup :=
  Finset.nodup _

@[simp]
theorem Icc_eq_zero_iff : icc a b = 0 ↔ ¬a ≤ b := by
  rw [Icc, Finset.val_eq_zero, Finset.Icc_eq_empty_iff]

@[simp]
theorem Ico_eq_zero_iff : ico a b = 0 ↔ ¬a < b := by
  rw [Ico, Finset.val_eq_zero, Finset.Ico_eq_empty_iff]

@[simp]
theorem Ioc_eq_zero_iff : ioc a b = 0 ↔ ¬a < b := by
  rw [Ioc, Finset.val_eq_zero, Finset.Ioc_eq_empty_iff]

@[simp]
theorem Ioo_eq_zero_iff [DenselyOrdered α] : ioo a b = 0 ↔ ¬a < b := by
  rw [Ioo, Finset.val_eq_zero, Finset.Ioo_eq_empty_iff]

alias Icc_eq_zero_iff ↔ _ Icc_eq_zero

alias Ico_eq_zero_iff ↔ _ Ico_eq_zero

alias Ioc_eq_zero_iff ↔ _ Ioc_eq_zero

@[simp]
theorem Ioo_eq_zero (h : ¬a < b) : ioo a b = 0 :=
  eq_zero_iff_forall_not_mem.2 fun x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]
theorem Icc_eq_zero_of_lt (h : b < a) : icc a b = 0 :=
  Icc_eq_zero h.not_le

@[simp]
theorem Ico_eq_zero_of_le (h : b ≤ a) : ico a b = 0 :=
  Ico_eq_zero h.not_lt

@[simp]
theorem Ioc_eq_zero_of_le (h : b ≤ a) : ioc a b = 0 :=
  Ioc_eq_zero h.not_lt

@[simp]
theorem Ioo_eq_zero_of_le (h : b ≤ a) : ioo a b = 0 :=
  Ioo_eq_zero h.not_lt

variable (a)

@[simp]
theorem Ico_self : ico a a = 0 := by
  rw [Ico, Finset.Ico_self, Finset.empty_val]

@[simp]
theorem Ioc_self : ioc a a = 0 := by
  rw [Ioc, Finset.Ioc_self, Finset.empty_val]

@[simp]
theorem Ioo_self : ioo a a = 0 := by
  rw [Ioo, Finset.Ioo_self, Finset.empty_val]

variable {a b c}

theorem left_mem_Icc : a ∈ icc a b ↔ a ≤ b :=
  Finset.left_mem_Icc

theorem left_mem_Ico : a ∈ ico a b ↔ a < b :=
  Finset.left_mem_Ico

theorem right_mem_Icc : b ∈ icc a b ↔ a ≤ b :=
  Finset.right_mem_Icc

theorem right_mem_Ioc : b ∈ ioc a b ↔ a < b :=
  Finset.right_mem_Ioc

@[simp]
theorem left_not_mem_Ioc : a ∉ ioc a b :=
  Finset.left_not_mem_Ioc

@[simp]
theorem left_not_mem_Ioo : a ∉ ioo a b :=
  Finset.left_not_mem_Ioo

@[simp]
theorem right_not_mem_Ico : b ∉ ico a b :=
  Finset.right_not_mem_Ico

@[simp]
theorem right_not_mem_Ioo : b ∉ ioo a b :=
  Finset.right_not_mem_Ioo

theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) : ((ico a b).filter fun x => x < c) = ∅ := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_le_left hca]
  rfl

theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) : ((ico a b).filter fun x => x < c) = ico a b :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_right_le hbc]

theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) : ((ico a b).filter fun x => x < c) = ico a c :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_le_right hcb]
  rfl

theorem Ico_filter_le_of_le_left [DecidablePred ((· ≤ ·) c)] (hca : c ≤ a) :
    ((ico a b).filter fun x => c ≤ x) = ico a b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_le_left hca]

theorem Ico_filter_le_of_right_le [DecidablePred ((· ≤ ·) b)] : ((ico a b).filter fun x => b ≤ x) = ∅ := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_right_le]
  rfl

theorem Ico_filter_le_of_left_le [DecidablePred ((· ≤ ·) c)] (hac : a ≤ c) :
    ((ico a b).filter fun x => c ≤ x) = ico c b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_left_le hac]
  rfl

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [LocallyFiniteOrder α] {a b : α}

@[simp]
theorem Icc_self (a : α) : icc a a = {a} := by
  rw [Icc, Finset.Icc_self, Finset.singleton_val]

theorem Ico_cons_right (h : a ≤ b) : b ::ₘ ico a b = icc a b := by
  classical
  rw [Ico, ← Finset.insert_val_of_not_mem right_not_mem_Ico, Finset.Ico_insert_right h]
  rfl

theorem Ioo_cons_left (h : a < b) : a ::ₘ ioo a b = ico a b := by
  classical
  rw [Ioo, ← Finset.insert_val_of_not_mem left_not_mem_Ioo, Finset.Ioo_insert_left h]
  rfl

theorem Ico_disjoint_Ico {a b c d : α} (h : b ≤ c) : (ico a b).Disjoint (ico c d) := fun x hab hbc => by
  rw [mem_Ico] at hab hbc
  exact hab.2.not_le (h.trans hbc.1)

@[simp]
theorem Ico_inter_Ico_of_le [DecidableEq α] {a b c d : α} (h : b ≤ c) : ico a b ∩ ico c d = 0 :=
  Multiset.inter_eq_zero_iff_disjoint.2 <| Ico_disjoint_Ico h

theorem Ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) : ((ico a b).filter fun x => x ≤ a) = {a} :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_left hab]
  rfl

theorem card_Ico_eq_card_Icc_sub_one (a b : α) : (ico a b).card = (icc a b).card - 1 :=
  Finset.card_Ico_eq_card_Icc_sub_one _ _

theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : (ioc a b).card = (icc a b).card - 1 :=
  Finset.card_Ioc_eq_card_Icc_sub_one _ _

theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : (ioo a b).card = (ico a b).card - 1 :=
  Finset.card_Ioo_eq_card_Ico_sub_one _ _

theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : (ioo a b).card = (icc a b).card - 2 :=
  Finset.card_Ioo_eq_card_Icc_sub_two _ _

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α] [LocallyFiniteOrder α] {a b c d : α}

theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) : ico a₁ b₁ ⊆ ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  Finset.Ico_subset_Ico_iff h

theorem Ico_add_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) : ico a b + ico b c = ico a c := by
  rw [add_eq_union_iff_disjoint.2 (Ico_disjoint_Ico le_rfl), Ico, Ico, Ico, ← Finset.union_val,
    Finset.Ico_union_Ico_eq_Ico hab hbc]

theorem Ico_inter_Ico : ico a b ∩ ico c d = ico (max a c) (min b d) := by
  rw [Ico, Ico, Ico, ← Finset.inter_val, Finset.Ico_inter_Ico]

@[simp]
theorem Ico_filter_lt (a b c : α) : ((ico a b).filter fun x => x < c) = ico a (min b c) := by
  rw [Ico, Ico, ← Finset.filter_val, Finset.Ico_filter_lt]

@[simp]
theorem Ico_filter_le (a b c : α) : ((ico a b).filter fun x => c ≤ x) = ico (max a c) b := by
  rw [Ico, Ico, ← Finset.filter_val, Finset.Ico_filter_le]

@[simp]
theorem Ico_sub_Ico_left (a b c : α) : ico a b - ico a c = ico (max a c) b := by
  rw [Ico, Ico, Ico, ← Finset.sdiff_val, Finset.Ico_diff_Ico_left]

@[simp]
theorem Ico_sub_Ico_right (a b c : α) : ico a b - ico c b = ico a (min b c) := by
  rw [Ico, Ico, Ico, ← Finset.sdiff_val, Finset.Ico_diff_Ico_right]

end LinearOrderₓ

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid α] [HasExistsAddOfLe α] [LocallyFiniteOrder α]

theorem map_add_left_Icc (a b c : α) : (icc a b).map ((· + ·) c) = icc (c + a) (c + b) := by
  classical
  rw [Icc, Icc, ← Finset.image_add_left_Icc, Finset.image_val, ((Finset.nodup _).map <| add_right_injective c).dedup]

theorem map_add_left_Ico (a b c : α) : (ico a b).map ((· + ·) c) = ico (c + a) (c + b) := by
  classical
  rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val, ((Finset.nodup _).map <| add_right_injective c).dedup]

theorem map_add_left_Ioc (a b c : α) : (ioc a b).map ((· + ·) c) = ioc (c + a) (c + b) := by
  classical
  rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val, ((Finset.nodup _).map <| add_right_injective c).dedup]

theorem map_add_left_Ioo (a b c : α) : (ioo a b).map ((· + ·) c) = ioo (c + a) (c + b) := by
  classical
  rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val, ((Finset.nodup _).map <| add_right_injective c).dedup]

theorem map_add_right_Icc (a b c : α) : ((icc a b).map fun x => x + c) = icc (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact map_add_left_Icc _ _ _

theorem map_add_right_Ico (a b c : α) : ((ico a b).map fun x => x + c) = ico (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact map_add_left_Ico _ _ _

theorem map_add_right_Ioc (a b c : α) : ((ioc a b).map fun x => x + c) = ioc (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact map_add_left_Ioc _ _ _

theorem map_add_right_Ioo (a b c : α) : ((ioo a b).map fun x => x + c) = ioo (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact map_add_left_Ioo _ _ _

end OrderedCancelAddCommMonoid

end Multiset

