/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Finset.Sym

/-!
# Stars and bars

In this file, we prove the case `n = 2` of stars and bars.

## Informal statement

If we have `n` objects to put in `k` boxes, we can do so in exactly `(n + k - 1).choose n` ways.

## Formal statement

We can identify the `k` boxes with the elements of a fintype `α` of card `k`. Then placing `n`
elements in those boxes corresponds to choosing how many of each element of `α` appear in a multiset
of card `n`. `sym α n` being the subtype of `multiset α` of multisets of card `n`, writing stars
and bars using types gives
```lean
-- TODO: this lemma is not yet proven
lemma stars_and_bars {α : Type*} [fintype α] (n : ℕ) :
  card (sym α n) = (card α + n - 1).choose (card α) := sorry
```

## TODO

Prove the general case of stars and bars.

## Tags

stars and bars
-/


open Finset Fintype

namespace Sym2

variable {α : Type _} [DecidableEq α]

/-- The `diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.card`. -/
theorem card_image_diag (s : Finset α) : (s.diag.Image Quotientₓ.mk).card = s.card := by
  rw [card_image_of_inj_on, diag_card]
  rintro ⟨x₀, x₁⟩ hx _ _ h
  cases Quotientₓ.eq.1 h
  · rfl
    
  · simp only [← mem_coe, ← mem_diag] at hx
    rw [hx.2]
    

theorem two_mul_card_image_off_diag (s : Finset α) : 2 * (s.offDiag.Image Quotientₓ.mk).card = s.offDiag.card := by
  rw
    [card_eq_sum_card_fiberwise
      (fun x => mem_image_of_mem _ : ∀, ∀ x ∈ s.off_diag, ∀, Quotientₓ.mk x ∈ s.off_diag.image Quotientₓ.mk),
    sum_const_nat (Quotientₓ.ind _), mul_comm]
  rintro ⟨x, y⟩ hxy
  simp_rw [mem_image, exists_prop, mem_off_diag, Quotientₓ.eq] at hxy
  obtain ⟨a, ⟨ha₁, ha₂, ha⟩, h⟩ := hxy
  obtain ⟨hx, hy, hxy⟩ : x ∈ s ∧ y ∈ s ∧ x ≠ y := by
    cases h <;> have := ha.symm <;> exact ⟨‹_›, ‹_›, ‹_›⟩
  have hxy' : y ≠ x := hxy.symm
  have : (s.off_diag.filter fun z => ⟦z⟧ = ⟦(x, y)⟧) = ({(x, y), (y, x)} : Finset _) := by
    ext ⟨x₁, y₁⟩
    rw [mem_filter, mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.inj_iff, Prod.mk.inj_iff, and_iff_right_iff_imp]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rw [mem_off_diag] <;> exact ⟨‹_›, ‹_›, ‹_›⟩
  -- hxy' is used here
  rw [this, card_insert_of_not_mem, card_singleton]
  simp only [← not_and, ← Prod.mk.inj_iff, ← mem_singleton]
  exact fun _ => hxy'

/-- The `off_diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.off_diag.card / 2`.
This is because every element `⟦(x, y)⟧` of `sym2 α` not on the diagonal comes from exactly two
pairs: `(x, y)` and `(y, x)`. -/
theorem card_image_off_diag (s : Finset α) : (s.offDiag.Image Quotientₓ.mk).card = s.card.choose 2 := by
  rw [Nat.choose_two_right, mul_tsub, mul_oneₓ, ← off_diag_card,
    Nat.div_eq_of_eq_mul_rightₓ zero_lt_two (two_mul_card_image_off_diag s).symm]

theorem card_subtype_diag [Fintype α] : card { a : Sym2 α // a.IsDiag } = card α := by
  convert card_image_diag (univ : Finset α)
  rw [Fintype.card_of_subtype, ← filter_image_quotient_mk_is_diag]
  rintro x
  rw [mem_filter, univ_product_univ, mem_image]
  obtain ⟨a, ha⟩ := Quotientₓ.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩

theorem card_subtype_not_diag [Fintype α] : card { a : Sym2 α // ¬a.IsDiag } = (card α).choose 2 := by
  convert card_image_off_diag (univ : Finset α)
  rw [Fintype.card_of_subtype, ← filter_image_quotient_mk_not_is_diag]
  rintro x
  rw [mem_filter, univ_product_univ, mem_image]
  obtain ⟨a, ha⟩ := Quotientₓ.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩

/-- Finset **stars and bars** for the case `n = 2`. -/
theorem _root_.finset.card_sym2 (s : Finset α) : s.Sym2.card = s.card * (s.card + 1) / 2 := by
  rw [← image_diag_union_image_off_diag, card_union_eq, Sym2.card_image_diag, Sym2.card_image_off_diag,
    Nat.choose_two_right, add_commₓ, ← Nat.triangle_succ, Nat.succ_sub_one, mul_comm]
  rintro m he
  rw [inf_eq_inter, mem_inter, mem_image, mem_image] at he
  obtain ⟨⟨a, ha, rfl⟩, b, hb, hab⟩ := he
  refine' not_is_diag_mk_of_mem_off_diag hb _
  rw [hab]
  exact is_diag_mk_of_mem_diag ha

/-- Type **stars and bars** for the case `n = 2`. -/
protected theorem card [Fintype α] : card (Sym2 α) = card α * (card α + 1) / 2 :=
  Finset.card_sym2 _

end Sym2

