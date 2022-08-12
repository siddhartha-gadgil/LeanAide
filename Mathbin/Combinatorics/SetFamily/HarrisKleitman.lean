/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Order.UpperLower

/-!
# Harris-Kleitman inequality

This file proves the Harris-Kleitman inequality. This relates `𝒜.card * ℬ.card` and
`2 ^ card α * (𝒜 ∩ ℬ).card` where `𝒜` and `ℬ` are upward- or downcard-closed finite families of
finsets. This can be interpreted as saying that any two lower sets (resp. any two upper sets)
correlate in the uniform measure.

## Main declarations

* `finset.non_member_subfamily`: `𝒜.non_member_subfamily a` is the subfamily of sets not containing
  `a`.
* `finset.member_subfamily`: `𝒜.member_subfamily a` is the image of the subfamily of sets
  containing `a` under removing `a`.
* `is_lower_set.le_card_inter_finset`: One form of the Harris-Kleitman inequality.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/


open BigOperators

variable {α : Type _} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s : Finset α} {a : α}

namespace Finset

/-- ELements of `𝒜` that do not contain `a`. -/
def nonMemberSubfamily (𝒜 : Finset (Finset α)) (a : α) : Finset (Finset α) :=
  𝒜.filter fun s => a ∉ s

/-- Image of the elements of `𝒜` which contain `a` under removing `a`. Finsets that do not contain
`a` such that `insert a s ∈ 𝒜`. -/
def memberSubfamily (𝒜 : Finset (Finset α)) (a : α) : Finset (Finset α) :=
  (𝒜.filter fun s => a ∈ s).Image fun s => erase s a

@[simp]
theorem mem_non_member_subfamily : s ∈ 𝒜.nonMemberSubfamily a ↔ s ∈ 𝒜 ∧ a ∉ s :=
  mem_filter

@[simp]
theorem mem_member_subfamily : s ∈ 𝒜.memberSubfamily a ↔ insert a s ∈ 𝒜 ∧ a ∉ s := by
  simp_rw [member_subfamily, mem_image, mem_filter]
  refine' ⟨_, fun h => ⟨insert a s, ⟨h.1, mem_insert_self _ _⟩, erase_insert h.2⟩⟩
  rintro ⟨s, hs, rfl⟩
  rw [insert_erase hs.2]
  exact ⟨hs.1, not_mem_erase _ _⟩

theorem non_member_subfamily_inter (𝒜 ℬ : Finset (Finset α)) (a : α) :
    (𝒜 ∩ ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a ∩ ℬ.nonMemberSubfamily a :=
  filter_inter_distrib _ _ _

theorem member_subfamily_inter (𝒜 ℬ : Finset (Finset α)) (a : α) :
    (𝒜 ∩ ℬ).memberSubfamily a = 𝒜.memberSubfamily a ∩ ℬ.memberSubfamily a := by
  unfold member_subfamily
  rw [filter_inter_distrib, image_inter_of_inj_on _ _ ((erase_inj_on' _).mono _)]
  rw [← coe_union, ← filter_union, coe_filter]
  exact Set.inter_subset_right _ _

theorem card_member_subfamily_add_card_non_member_subfamily (𝒜 : Finset (Finset α)) (a : α) :
    (𝒜.memberSubfamily a).card + (𝒜.nonMemberSubfamily a).card = 𝒜.card := by
  rw [member_subfamily, non_member_subfamily, card_image_of_inj_on, filter_card_add_filter_neg_card_eq_card]
  exact (erase_inj_on' _).mono fun s hs => (mem_filter.1 hs).2

end Finset

open Finset

theorem IsLowerSet.non_member_subfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    IsLowerSet (𝒜.nonMemberSubfamily a : Set (Finset α)) := fun s t hts => by
  simp_rw [mem_coe, mem_non_member_subfamily]
  exact And.imp (h hts) (mt <| @hts _)

theorem IsLowerSet.member_subfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    IsLowerSet (𝒜.memberSubfamily a : Set (Finset α)) := by
  rintro s t hts
  simp_rw [mem_coe, mem_member_subfamily]
  exact And.imp (h <| insert_subset_insert _ hts) (mt <| @hts _)

theorem IsLowerSet.member_subfamily_subset_non_member_subfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    𝒜.memberSubfamily a ⊆ 𝒜.nonMemberSubfamily a := fun s => by
  rw [mem_member_subfamily, mem_non_member_subfamily]
  exact And.imp_left (h <| subset_insert _ _)

/-- **Harris-Kleitman inequality**: Any two lower sets of finsets correlate. -/
theorem IsLowerSet.le_card_inter_finset' (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α)))
    (h𝒜s : ∀, ∀ t ∈ 𝒜, ∀, t ⊆ s) (hℬs : ∀, ∀ t ∈ ℬ, ∀, t ⊆ s) : 𝒜.card * ℬ.card ≤ 2 ^ s.card * (𝒜 ∩ ℬ).card := by
  induction' s using Finset.induction with a s hs ih generalizing 𝒜 ℬ
  · simp_rw [subset_empty, ← subset_singleton_iff', subset_singleton_iff] at h𝒜s hℬs
    obtain rfl | rfl := h𝒜s
    · simp only [← card_empty, ← empty_inter, ← mul_zero, ← zero_mul]
      
    obtain rfl | rfl := hℬs
    · simp only [← card_empty, ← inter_empty, ← mul_zero, ← zero_mul]
      
    · simp only [← card_empty, ← pow_zeroₓ, ← inter_singleton_of_mem, ← mem_singleton, ← card_singleton]
      
    
  rw [card_insert_of_not_mem hs, ← card_member_subfamily_add_card_non_member_subfamily 𝒜 a, ←
    card_member_subfamily_add_card_non_member_subfamily ℬ a, add_mulₓ, mul_addₓ, mul_addₓ, add_commₓ (_ * _),
    add_add_add_commₓ]
  refine'
    (add_le_add_right
          (mul_add_mul_le_mul_add_mul (card_le_of_subset h𝒜.member_subfamily_subset_non_member_subfamily) <|
            card_le_of_subset hℬ.member_subfamily_subset_non_member_subfamily)
          _).trans
      _
  rw [← two_mul, pow_succₓ, mul_assoc]
  have h₀ : ∀ 𝒞 : Finset (Finset α), (∀, ∀ t ∈ 𝒞, ∀, t ⊆ insert a s) → ∀, ∀ t ∈ 𝒞.nonMemberSubfamily a, ∀, t ⊆ s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_non_member_subfamily] at ht
    exact (subset_insert_iff_of_not_mem ht.2).1 (h𝒞 _ ht.1)
  have h₁ : ∀ 𝒞 : Finset (Finset α), (∀, ∀ t ∈ 𝒞, ∀, t ⊆ insert a s) → ∀, ∀ t ∈ 𝒞.memberSubfamily a, ∀, t ⊆ s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_member_subfamily] at ht
    exact (subset_insert_iff_of_not_mem ht.2).1 ((subset_insert _ _).trans <| h𝒞 _ ht.1)
  refine' mul_le_mul_left' _ _
  refine'
    (add_le_add (ih h𝒜.member_subfamily hℬ.member_subfamily (h₁ _ h𝒜s) <| h₁ _ hℬs) <|
          ih h𝒜.non_member_subfamily hℬ.non_member_subfamily (h₀ _ h𝒜s) <| h₀ _ hℬs).trans_eq
      _
  rw [← mul_addₓ, ← member_subfamily_inter, ← non_member_subfamily_inter,
    card_member_subfamily_add_card_non_member_subfamily]

variable [Fintype α]

/-- **Harris-Kleitman inequality**: Any two lower sets of finsets correlate. -/
theorem IsLowerSet.le_card_inter_finset (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    𝒜.card * ℬ.card ≤ 2 ^ Fintype.card α * (𝒜 ∩ ℬ).card :=
  (h𝒜.le_card_inter_finset' hℬ fun _ _ => subset_univ _) fun _ _ => subset_univ _

/-- **Harris-Kleitman inequality**: Upper sets and lower sets of finsets anticorrelate. -/
theorem IsUpperSet.card_inter_le_finset (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    2 ^ Fintype.card α * (𝒜 ∩ ℬ).card ≤ 𝒜.card * ℬ.card := by
  rw [← is_lower_set_compl, ← coe_compl] at h𝒜
  have := h𝒜.le_card_inter_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, tsub_le_iff_tsub_le, ← mul_tsub, ←
    card_sdiff (inter_subset_right _ _), sdiff_inter_self_right, sdiff_compl, _root_.inf_comm] at this

/-- **Harris-Kleitman inequality**: Lower sets and upper sets of finsets anticorrelate. -/
theorem IsLowerSet.card_inter_le_finset (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    2 ^ Fintype.card α * (𝒜 ∩ ℬ).card ≤ 𝒜.card * ℬ.card := by
  rw [inter_comm, mul_comm 𝒜.card]
  exact hℬ.card_inter_le_finset h𝒜

/-- **Harris-Kleitman inequality**: Any two upper sets of finsets correlate. -/
theorem IsUpperSet.le_card_inter_finset (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    𝒜.card * ℬ.card ≤ 2 ^ Fintype.card α * (𝒜 ∩ ℬ).card := by
  rw [← is_lower_set_compl, ← coe_compl] at h𝒜
  have := h𝒜.card_inter_le_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, le_tsub_iff_le_tsub, ← mul_tsub, ←
    card_sdiff (inter_subset_right _ _), sdiff_inter_self_right, sdiff_compl, _root_.inf_comm] at this
  · exact mul_le_mul_left' (card_le_of_subset <| inter_subset_right _ _) _
    
  · rw [← Fintype.card_finset]
    exact mul_le_mul_right' (card_le_univ _) _
    

