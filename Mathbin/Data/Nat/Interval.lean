/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.LocallyFinite

/-!
# Finite intervals of naturals

This file proves that `ℕ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

Some lemmas can be generalized using `ordered_group`, `canonically_ordered_monoid` or `succ_order`
and subsequently be moved upstream to `data.finset.locally_finite`.
-/


open Finset Nat

instance : LocallyFiniteOrder ℕ where
  finsetIcc := fun a b => (List.range' a (b + 1 - a)).toFinset
  finsetIco := fun a b => (List.range' a (b - a)).toFinset
  finsetIoc := fun a b => (List.range' (a + 1) (b - a)).toFinset
  finsetIoo := fun a b => (List.range' (a + 1) (b - a - 1)).toFinset
  finset_mem_Icc := fun a b x => by
    rw [List.mem_to_finset, List.mem_range']
    cases le_or_ltₓ a b
    · rw [add_tsub_cancel_of_le (Nat.lt_succ_of_leₓ h).le, Nat.lt_succ_iffₓ]
      
    · rw [tsub_eq_zero_iff_le.2 (succ_le_of_lt h), add_zeroₓ]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2)
      
  finset_mem_Ico := fun a b x => by
    rw [List.mem_to_finset, List.mem_range']
    cases le_or_ltₓ a b
    · rw [add_tsub_cancel_of_le h]
      
    · rw [tsub_eq_zero_iff_le.2 h.le, add_zeroₓ]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2.le)
      
  finset_mem_Ioc := fun a b x => by
    rw [List.mem_to_finset, List.mem_range']
    cases le_or_ltₓ a b
    · rw [← succ_sub_succ, add_tsub_cancel_of_le (succ_le_succ h), Nat.lt_succ_iffₓ, Nat.succ_le_iff]
      
    · rw [tsub_eq_zero_iff_le.2 h.le, add_zeroₓ]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.le.trans hx.2)
      
  finset_mem_Ioo := fun a b x => by
    rw [List.mem_to_finset, List.mem_range', ← tsub_add_eq_tsub_tsub]
    cases le_or_ltₓ (a + 1) b
    · rw [add_tsub_cancel_of_le h, Nat.succ_le_iff]
      
    · rw [tsub_eq_zero_iff_le.2 h.le, add_zeroₓ]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2)
      

variable (a b c : ℕ)

namespace Nat

theorem Icc_eq_range' : icc a b = (List.range' a (b + 1 - a)).toFinset :=
  rfl

theorem Ico_eq_range' : ico a b = (List.range' a (b - a)).toFinset :=
  rfl

theorem Ioc_eq_range' : ioc a b = (List.range' (a + 1) (b - a)).toFinset :=
  rfl

theorem Ioo_eq_range' : ioo a b = (List.range' (a + 1) (b - a - 1)).toFinset :=
  rfl

theorem Iio_eq_range : Iio = range := by
  ext b x
  rw [mem_Iio, mem_range]

@[simp]
theorem Ico_zero_eq_range : ico 0 = range := by
  rw [← bot_eq_zero, ← Iio_eq_Ico, Iio_eq_range]

theorem _root_.finset.range_eq_Ico : range = ico 0 :=
  Ico_zero_eq_range.symm

@[simp]
theorem card_Icc : (icc a b).card = b + 1 - a := by
  rw [Icc_eq_range', List.card_to_finset, (List.nodup_range' _ _).dedup, List.length_range']

@[simp]
theorem card_Ico : (ico a b).card = b - a := by
  rw [Ico_eq_range', List.card_to_finset, (List.nodup_range' _ _).dedup, List.length_range']

@[simp]
theorem card_Ioc : (ioc a b).card = b - a := by
  rw [Ioc_eq_range', List.card_to_finset, (List.nodup_range' _ _).dedup, List.length_range']

@[simp]
theorem card_Ioo : (ioo a b).card = b - a - 1 := by
  rw [Ioo_eq_range', List.card_to_finset, (List.nodup_range' _ _).dedup, List.length_range']

@[simp]
theorem card_Iic : (iic b).card = b + 1 := by
  rw [Iic_eq_Icc, card_Icc, bot_eq_zero, tsub_zero]

@[simp]
theorem card_Iio : (iio b).card = b := by
  rw [Iio_eq_Ico, card_Ico, bot_eq_zero, tsub_zero]

@[simp]
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [Fintype.card_of_finset, card_Icc]

@[simp]
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = b - a := by
  rw [Fintype.card_of_finset, card_Ico]

@[simp]
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [Fintype.card_of_finset, card_Ioc]

@[simp]
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [Fintype.card_of_finset, card_Ioo]

@[simp]
theorem card_fintype_Iic : Fintype.card (Set.Iic b) = b + 1 := by
  rw [Fintype.card_of_finset, card_Iic]

@[simp]
theorem card_fintype_Iio : Fintype.card (Set.Iio b) = b := by
  rw [Fintype.card_of_finset, card_Iio]

-- TODO@Yaël: Generalize all the following lemmas to `succ_order`
theorem Icc_succ_left : icc a.succ b = ioc a b := by
  ext x
  rw [mem_Icc, mem_Ioc, succ_le_iff]

theorem Ico_succ_right : ico a b.succ = icc a b := by
  ext x
  rw [mem_Ico, mem_Icc, lt_succ_iff]

theorem Ico_succ_left : ico a.succ b = ioo a b := by
  ext x
  rw [mem_Ico, mem_Ioo, succ_le_iff]

theorem Icc_pred_right {b : ℕ} (h : 0 < b) : icc a (b - 1) = ico a b := by
  ext x
  rw [mem_Icc, mem_Ico, lt_iff_le_pred h]

theorem Ico_succ_succ : ico a.succ b.succ = ioc a b := by
  ext x
  rw [mem_Ico, mem_Ioc, succ_le_iff, lt_succ_iff]

@[simp]
theorem Ico_succ_singleton : ico a (a + 1) = {a} := by
  rw [Ico_succ_right, Icc_self]

@[simp]
theorem Ico_pred_singleton {a : ℕ} (h : 0 < a) : ico (a - 1) a = {a - 1} := by
  rw [← Icc_pred_right _ h, Icc_self]

@[simp]
theorem Ioc_succ_singleton : ioc b (b + 1) = {b + 1} := by
  rw [← Nat.Icc_succ_left, Icc_self]

variable {a b c}

theorem Ico_succ_right_eq_insert_Ico (h : a ≤ b) : ico a (b + 1) = insert b (ico a b) := by
  rw [Ico_succ_right, ← Ico_insert_right h]

theorem Ico_insert_succ_left (h : a < b) : insert a (ico a.succ b) = ico a b := by
  rw [Ico_succ_left, ← Ioo_insert_left h]

theorem image_sub_const_Ico (h : c ≤ a) : ((ico a b).Image fun x => x - c) = ico (a - c) (b - c) := by
  ext x
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Ico] at hx⊢
    exact ⟨tsub_le_tsub_right hx.1 _, tsub_lt_tsub_right_of_le (h.trans hx.1) hx.2⟩
    
  · rintro h
    refine' ⟨x + c, _, add_tsub_cancel_right _ _⟩
    rw [mem_Ico] at h⊢
    exact ⟨tsub_le_iff_right.1 h.1, lt_tsub_iff_right.1 h.2⟩
    

theorem Ico_image_const_sub_eq_Ico (hac : a ≤ c) : ((ico a b).Image fun x => c - x) = ico (c + 1 - b) (c + 1 - a) := by
  ext x
  rw [mem_image, mem_Ico]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Ico] at hx
    refine' ⟨_, ((tsub_le_tsub_iff_left hac).2 hx.1).trans_lt ((tsub_lt_tsub_iff_right hac).2 (Nat.lt_succ_selfₓ _))⟩
    cases lt_or_leₓ c b
    · rw [tsub_eq_zero_iff_le.mpr (succ_le_of_lt h)]
      exact zero_le _
      
    · rw [← succ_sub_succ c]
      exact (tsub_le_tsub_iff_left (succ_le_succ <| hx.2.le.trans h)).2 hx.2
      
    
  · rintro ⟨hb, ha⟩
    rw [lt_tsub_iff_left, lt_succ_iff] at ha
    have hx : x ≤ c := (Nat.le_add_leftₓ _ _).trans ha
    refine' ⟨c - x, _, tsub_tsub_cancel_of_le hx⟩
    · rw [mem_Ico]
      exact ⟨le_tsub_of_add_le_right ha, (tsub_lt_iff_left hx).2 <| succ_le_iff.1 <| tsub_le_iff_right.1 hb⟩
      
    

theorem Ico_succ_left_eq_erase_Ico : ico a.succ b = erase (ico a b) a := by
  ext x
  rw [Ico_succ_left, mem_erase, mem_Ico, mem_Ioo, ← and_assoc, ne_comm, and_comm (a ≠ x), lt_iff_le_and_ne]

theorem mod_inj_on_Ico (n a : ℕ) : Set.InjOn (· % a) (Finset.ico n (n + a)) := by
  induction' n with n ih
  · simp only [← zero_addₓ, ← nat_zero_eq_zero, ← Ico_zero_eq_range]
    rintro k hk l hl (hkl : k % a = l % a)
    simp only [← Finset.mem_range, ← Finset.mem_coe] at hk hl
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl
    
  rw [Ico_succ_left_eq_erase_Ico, succ_add, Ico_succ_right_eq_insert_Ico le_self_add]
  rintro k hk l hl (hkl : k % a = l % a)
  have ha : 0 < a := by
    by_contra ha
    simp only [← not_ltₓ, ← nonpos_iff_eq_zero] at ha
    simpa [← ha] using hk
  simp only [← Finset.mem_coe, ← Finset.mem_insert, ← Finset.mem_erase] at hk hl
  rcases hk with ⟨hkn, rfl | hk⟩ <;> rcases hl with ⟨hln, rfl | hl⟩
  · rfl
    
  · rw [add_mod_right] at hkl
    refine' (hln <| ih hl _ hkl.symm).elim
    simp only [← lt_add_iff_pos_right, ← Set.left_mem_Ico, ← Finset.coe_Ico, ← ha]
    
  · rw [add_mod_right] at hkl
    suffices k = n by
      contradiction
    refine' ih hk _ hkl
    simp only [← lt_add_iff_pos_right, ← Set.left_mem_Ico, ← Finset.coe_Ico, ← ha]
    
  · refine' ih _ _ hkl <;> simp only [← Finset.mem_coe, ← hk, ← hl]
    

/-- Note that while this lemma cannot be easily generalized to a type class, it holds for ℤ as
well. See `int.image_Ico_mod` for the ℤ version. -/
theorem image_Ico_mod (n a : ℕ) : (ico n (n + a)).Image (· % a) = range a := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [range_zero, add_zeroₓ, Ico_self, image_empty]
    
  ext i
  simp only [← mem_image, ← exists_prop, ← mem_range, ← mem_Ico]
  constructor
  · rintro ⟨i, h, rfl⟩
    exact mod_lt i ha.bot_lt
    
  intro hia
  have hn := Nat.mod_add_divₓ n a
  obtain hi | hi := lt_or_leₓ i (n % a)
  · refine' ⟨i + a * (n / a + 1), ⟨_, _⟩, _⟩
    · rw [add_commₓ (n / a), mul_addₓ, mul_oneₓ, ← add_assocₓ]
      refine' hn.symm.le.trans (add_le_add_right _ _)
      simpa only [← zero_addₓ] using add_le_add (zero_le i) (Nat.mod_ltₓ n ha.bot_lt).le
      
    · refine' lt_of_lt_of_leₓ (add_lt_add_right hi (a * (n / a + 1))) _
      rw [mul_addₓ, mul_oneₓ, ← add_assocₓ, hn]
      
    · rw [Nat.add_mul_mod_self_leftₓ, Nat.mod_eq_of_ltₓ hia]
      
    
  · refine' ⟨i + a * (n / a), ⟨_, _⟩, _⟩
    · exact hn.symm.le.trans (add_le_add_right hi _)
      
    · rw [add_commₓ n a]
      refine' add_lt_add_of_lt_of_le hia (le_transₓ _ hn.le)
      simp only [← zero_le, ← le_add_iff_nonneg_left]
      
    · rw [Nat.add_mul_mod_self_leftₓ, Nat.mod_eq_of_ltₓ hia]
      
    

section Multiset

open Multiset

theorem multiset_Ico_map_mod (n a : ℕ) : (Multiset.ico n (n + a)).map (· % a) = range a := by
  convert congr_arg Finset.val (image_Ico_mod n a)
  refine' ((nodup_map_iff_inj_on (Finset.ico _ _).Nodup).2 <| _).dedup.symm
  exact mod_inj_on_Ico _ _

end Multiset

end Nat

namespace Finset

theorem range_image_pred_top_sub (n : ℕ) : ((Finset.range n).Image fun j => n - 1 - j) = Finset.range n := by
  cases n
  · rw [range_zero, image_empty]
    
  · rw [Finset.range_eq_Ico, Nat.Ico_image_const_sub_eq_Ico (zero_le _)]
    simp_rw [succ_sub_succ, tsub_zero, tsub_self]
    

theorem range_add_eq_union : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  rw [Finset.range_eq_Ico, map_eq_image]
  convert (Ico_union_Ico_eq_Ico a.zero_le le_self_add).symm
  exact image_add_left_Ico _ _ _

end Finset

