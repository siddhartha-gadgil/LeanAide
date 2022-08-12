/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Int.Basic
import Mathbin.Algebra.CharZero
import Mathbin.Order.LocallyFinite
import Mathbin.Data.Finset.LocallyFinite

/-!
# Finite intervals of integers

This file proves that `ℤ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Int

instance : LocallyFiniteOrder ℤ where
  finsetIcc := fun a b => (Finset.range (b + 1 - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding a
  finsetIco := fun a b => (Finset.range (b - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding a
  finsetIoc := fun a b => (Finset.range (b - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)
  finsetIoo := fun a b => (Finset.range (b - a - 1).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)
  finset_mem_Icc := fun a b x => by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_to_nat, Function.Embedding.trans_apply, Nat.cast_embedding_apply,
      add_left_embedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      rw [lt_sub_iff_add_lt, Int.lt_add_one_iff, add_commₓ] at h
      exact ⟨Int.Le.intro rfl, h⟩
      
    · rintro ⟨ha, hb⟩
      use (x - a).toNat
      rw [← lt_add_one_iff] at hb
      rw [to_nat_sub_of_le ha]
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩
      
  finset_mem_Ico := fun a b x => by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_to_nat, Function.Embedding.trans_apply, Nat.cast_embedding_apply,
      add_left_embedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      exact ⟨Int.Le.intro rfl, lt_sub_iff_add_lt'.mp h⟩
      
    · rintro ⟨ha, hb⟩
      use (x - a).toNat
      rw [to_nat_sub_of_le ha]
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩
      
  finset_mem_Ioc := fun a b x => by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_to_nat, Function.Embedding.trans_apply, Nat.cast_embedding_apply,
      add_left_embedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      rw [← add_one_le_iff, le_sub_iff_add_le', add_commₓ _ (1 : ℤ), ← add_assocₓ] at h
      exact ⟨Int.Le.intro rfl, h⟩
      
    · rintro ⟨ha, hb⟩
      use (x - (a + 1)).toNat
      rw [to_nat_sub_of_le ha, ← add_one_le_iff, sub_add, add_sub_cancel]
      exact ⟨sub_le_sub_right hb _, add_sub_cancel'_right _ _⟩
      
  finset_mem_Ioo := fun a b x => by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_to_nat, Function.Embedding.trans_apply, Nat.cast_embedding_apply,
      add_left_embedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      rw [sub_sub, lt_sub_iff_add_lt'] at h
      exact ⟨Int.Le.intro rfl, h⟩
      
    · rintro ⟨ha, hb⟩
      use (x - (a + 1)).toNat
      rw [to_nat_sub_of_le ha, sub_sub]
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩
      

namespace Int

variable (a b : ℤ)

theorem Icc_eq_finset_map :
    icc a b = (Finset.range (b + 1 - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl

theorem Ico_eq_finset_map :
    ico a b = (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl

theorem Ioc_eq_finset_map :
    ioc a b = (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl

theorem Ioo_eq_finset_map :
    ioo a b = (Finset.range (b - a - 1).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl

@[simp]
theorem card_Icc : (icc a b).card = (b + 1 - a).toNat := by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]

@[simp]
theorem card_Ico : (ico a b).card = (b - a).toNat := by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]

@[simp]
theorem card_Ioc : (ioc a b).card = (b - a).toNat := by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]

@[simp]
theorem card_Ioo : (ioo a b).card = (b - a - 1).toNat := by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]

theorem card_Icc_of_le (h : a ≤ b + 1) : ((icc a b).card : ℤ) = b + 1 - a := by
  rw [card_Icc, to_nat_sub_of_le h]

theorem card_Ico_of_le (h : a ≤ b) : ((ico a b).card : ℤ) = b - a := by
  rw [card_Ico, to_nat_sub_of_le h]

theorem card_Ioc_of_le (h : a ≤ b) : ((ioc a b).card : ℤ) = b - a := by
  rw [card_Ioc, to_nat_sub_of_le h]

theorem card_Ioo_of_lt (h : a < b) : ((ioo a b).card : ℤ) = b - a - 1 := by
  rw [card_Ioo, sub_sub, to_nat_sub_of_le h]

@[simp]
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = (b + 1 - a).toNat := by
  rw [← card_Icc, Fintype.card_of_finset]

@[simp]
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = (b - a).toNat := by
  rw [← card_Ico, Fintype.card_of_finset]

@[simp]
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = (b - a).toNat := by
  rw [← card_Ioc, Fintype.card_of_finset]

@[simp]
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = (b - a - 1).toNat := by
  rw [← card_Ioo, Fintype.card_of_finset]

theorem card_fintype_Icc_of_le (h : a ≤ b + 1) : (Fintype.card (Set.Icc a b) : ℤ) = b + 1 - a := by
  rw [card_fintype_Icc, to_nat_sub_of_le h]

theorem card_fintype_Ico_of_le (h : a ≤ b) : (Fintype.card (Set.Ico a b) : ℤ) = b - a := by
  rw [card_fintype_Ico, to_nat_sub_of_le h]

theorem card_fintype_Ioc_of_le (h : a ≤ b) : (Fintype.card (Set.Ioc a b) : ℤ) = b - a := by
  rw [card_fintype_Ioc, to_nat_sub_of_le h]

theorem card_fintype_Ioo_of_lt (h : a < b) : (Fintype.card (Set.Ioo a b) : ℤ) = b - a - 1 := by
  rw [card_fintype_Ioo, sub_sub, to_nat_sub_of_le h]

theorem image_Ico_mod (n a : ℤ) (h : 0 ≤ a) : (ico n (n + a)).Image (· % a) = ico 0 a := by
  obtain rfl | ha := eq_or_lt_of_le h
  · simp
    
  ext i
  simp only [← mem_image, ← exists_prop, ← mem_range, ← mem_Ico]
  constructor
  · rintro ⟨i, h, rfl⟩
    exact ⟨mod_nonneg i (ne_of_gtₓ ha), mod_lt_of_pos i ha⟩
    
  intro hia
  have hn := Int.mod_add_div n a
  obtain hi | hi := lt_or_leₓ i (n % a)
  · refine' ⟨i + a * (n / a + 1), ⟨_, _⟩, _⟩
    · rw [add_commₓ (n / a), mul_addₓ, mul_oneₓ, ← add_assocₓ]
      refine' hn.symm.le.trans (add_le_add_right _ _)
      simpa only [← zero_addₓ] using add_le_add hia.left (Int.mod_lt_of_pos n ha).le
      
    · refine' lt_of_lt_of_leₓ (add_lt_add_right hi (a * (n / a + 1))) _
      rw [mul_addₓ, mul_oneₓ, ← add_assocₓ, hn]
      
    · rw [Int.add_mul_mod_self_left, Int.mod_eq_of_lt hia.left hia.right]
      
    
  · refine' ⟨i + a * (n / a), ⟨_, _⟩, _⟩
    · exact hn.symm.le.trans (add_le_add_right hi _)
      
    · rw [add_commₓ n a]
      refine' add_lt_add_of_lt_of_le hia.right (le_transₓ _ hn.le)
      simp only [← zero_le, ← le_add_iff_nonneg_left]
      exact Int.mod_nonneg n (ne_of_gtₓ ha)
      
    · rw [Int.add_mul_mod_self_left, Int.mod_eq_of_lt hia.left hia.right]
      
    

end Int

