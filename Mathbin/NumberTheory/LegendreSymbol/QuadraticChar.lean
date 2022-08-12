/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathbin.NumberTheory.LegendreSymbol.ZmodChar
import Mathbin.FieldTheory.Finite.Basic

/-!
# Quadratic characters of finite fields

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/


namespace Charₓ

/-!
### Definition of the quadratic character

We define the quadratic character of a finite field `F` with values in ℤ.
-/


section Define

/-- Define the quadratic character with values in ℤ on a monoid with zero `α`.
It takes the value zero at zero; for non-zero argument `a : α`, it is `1`
if `a` is a square, otherwise it is `-1`.

This only deserves the name "character" when it is multiplicative,
e.g., when `α` is a finite field. See `quadratic_char_mul`.

We will later define `quadratic_char` to be a multiplicative character
of type `mul_char F ℤ`, when the domain is a finite field `F`.
-/
def quadraticCharFun (α : Type _) [MonoidWithZeroₓ α] [DecidableEq α] [DecidablePred (IsSquare : α → Prop)] (a : α) :
    ℤ :=
  if a = 0 then 0 else if IsSquare a then 1 else -1

end Define

/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/


section QuadraticChar

open MulChar

variable {F : Type _} [Field F] [Fintype F] [DecidableEq F]

/-- Some basic API lemmas -/
theorem quadratic_char_eq_zero_iff' {a : F} : quadraticCharFun F a = 0 ↔ a = 0 := by
  simp only [← quadratic_char_fun]
  by_cases' ha : a = 0
  · simp only [← ha, ← eq_self_iff_true, ← if_true]
    
  · simp only [← ha, ← if_false, ← iff_falseₓ]
    split_ifs <;> simp only [← neg_eq_zero, ← one_ne_zero, ← not_false_iff]
    

@[simp]
theorem quadratic_char_zero : quadraticCharFun F 0 = 0 := by
  simp only [← quadratic_char_fun, ← eq_self_iff_true, ← if_true, ← id.def]

@[simp]
theorem quadratic_char_one : quadraticCharFun F 1 = 1 := by
  simp only [← quadratic_char_fun, ← one_ne_zero, ← is_square_one, ← if_true, ← if_false, ← id.def]

/-- If `ring_char F = 2`, then `quadratic_char_fun F` takes the value `1` on nonzero elements. -/
theorem quadratic_char_eq_one_of_char_two' (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) : quadraticCharFun F a = 1 := by
  simp only [← quadratic_char_fun, ← ha, ← if_false, ← ite_eq_left_iff]
  intro h
  exfalso
  exact h (FiniteField.is_square_of_char_two hF a)

/-- If `ring_char F` is odd, then `quadratic_char_fun F a` can be computed in
terms of `a ^ (fintype.card F / 2)`. -/
theorem quadratic_char_eq_pow_of_char_ne_two' (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticCharFun F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 := by
  simp only [← quadratic_char_fun, ← ha, ← if_false]
  simp_rw [FiniteField.is_square_iff hF ha]

/-- The quadratic character is multiplicative. -/
theorem quadratic_char_mul (a b : F) : quadraticCharFun F (a * b) = quadraticCharFun F a * quadraticCharFun F b := by
  by_cases' ha : a = 0
  · rw [ha, zero_mul, quadratic_char_zero, zero_mul]
    
  -- now `a ≠ 0`
  by_cases' hb : b = 0
  · rw [hb, mul_zero, quadratic_char_zero, mul_zero]
    
  -- now `a ≠ 0` and `b ≠ 0`
  have hab := mul_ne_zero ha hb
  by_cases' hF : ringChar F = 2
  · -- case `ring_char F = 2`
    rw [quadratic_char_eq_one_of_char_two' hF ha, quadratic_char_eq_one_of_char_two' hF hb,
      quadratic_char_eq_one_of_char_two' hF hab, mul_oneₓ]
    
  · -- case of odd characteristic
    rw [quadratic_char_eq_pow_of_char_ne_two' hF ha, quadratic_char_eq_pow_of_char_ne_two' hF hb,
      quadratic_char_eq_pow_of_char_ne_two' hF hab, mul_powₓ]
    cases' FiniteField.pow_dichotomy hF hb with hb' hb'
    · simp only [← hb', ← mul_oneₓ, ← eq_self_iff_true, ← if_true]
      
    · have h := Ringₓ.neg_one_ne_one_of_char_ne_two hF
      -- `-1 ≠ 1`
      simp only [← hb', ← h, ← mul_neg, ← mul_oneₓ, ← if_false, ← ite_mul, ← neg_mul]
      cases' FiniteField.pow_dichotomy hF ha with ha' ha' <;>
        simp only [← ha', ← h, ← neg_negₓ, ← eq_self_iff_true, ← if_true, ← if_false]
      
    

variable (F)

/-- The quadratic character as a multiplicative character. -/
@[simps]
def quadraticChar : MulChar F ℤ where
  toFun := quadraticCharFun F
  map_one' := quadratic_char_one
  map_mul' := quadratic_char_mul
  map_nonunit' := fun a ha => by
    rw [of_not_not (mt Ne.is_unit ha)]
    exact quadratic_char_zero

variable {F}

/-- The value of the quadratic character on `a` is zero iff `a = 0`. -/
theorem quadratic_char_eq_zero_iff {a : F} : quadraticChar F a = 0 ↔ a = 0 :=
  quadratic_char_eq_zero_iff'

/-- For nonzero `a : F`, `quadratic_char F a = 1 ↔ is_square a`. -/
theorem quadratic_char_one_iff_is_square {a : F} (ha : a ≠ 0) : quadraticChar F a = 1 ↔ IsSquare a := by
  simp only [← quadratic_char_apply, ← quadratic_char_fun, ← ha, ←
    (by
      decide : (-1 : ℤ) ≠ 1),
    ← if_false, ← ite_eq_left_iff, ← imp_false, ← not_not]

/-- The quadratic character takes the value `1` on nonzero squares. -/
theorem quadratic_char_sq_one' {a : F} (ha : a ≠ 0) : quadraticChar F (a ^ 2) = 1 := by
  simp only [← quadratic_char_fun, ← ha, ← pow_eq_zero_iff, ← Nat.succ_pos', ← is_square_sq, ← if_true, ← if_false, ←
    quadratic_char_apply]

/-- The square of the quadratic character on nonzero arguments is `1`. -/
theorem quadratic_char_sq_one {a : F} (ha : a ≠ 0) : quadraticChar F a ^ 2 = 1 := by
  rwa [pow_two, ← map_mul, ← pow_two, quadratic_char_sq_one']

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
theorem quadratic_char_dichotomy {a : F} (ha : a ≠ 0) : quadraticChar F a = 1 ∨ quadraticChar F a = -1 :=
  sq_eq_one_iff.1 <| quadratic_char_sq_one ha

/-- A variant -/
theorem quadratic_char_eq_neg_one_iff_not_one {a : F} (ha : a ≠ 0) : quadraticChar F a = -1 ↔ ¬quadraticChar F a = 1 :=
  by
  refine' ⟨fun h => _, fun h₂ => (or_iff_right h₂).mp (quadratic_char_dichotomy ha)⟩
  rw [h]
  norm_num

/-- For `a : F`, `quadratic_char F a = -1 ↔ ¬ is_square a`. -/
theorem quadratic_char_neg_one_iff_not_is_square {a : F} : quadraticChar F a = -1 ↔ ¬IsSquare a := by
  by_cases' ha : a = 0
  · simp only [← ha, ← is_square_zero, ← MulChar.map_zero, ← zero_eq_neg, ← one_ne_zero, ← not_true]
    
  · rw [quadratic_char_eq_neg_one_iff_not_one ha, quadratic_char_one_iff_is_square ha]
    

/-- If `F` has odd characteristic, then `quadratic_char F` takes the value `-1`. -/
theorem quadratic_char_exists_neg_one (hF : ringChar F ≠ 2) : ∃ a, quadraticChar F a = -1 :=
  (FiniteField.exists_nonsquare hF).imp fun b h₁ => quadratic_char_neg_one_iff_not_is_square.mpr h₁

/-- If `ring_char F = 2`, then `quadratic_char F` takes the value `1` on nonzero elements. -/
theorem quadratic_char_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) : quadraticChar F a = 1 :=
  quadratic_char_eq_one_of_char_two' hF ha

/-- If `ring_char F` is odd, then `quadratic_char F a` can be computed in
terms of `a ^ (fintype.card F / 2)`. -/
theorem quadratic_char_eq_pow_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticChar F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 :=
  quadratic_char_eq_pow_of_char_ne_two' hF ha

variable (F)

/-- The quadratic character is quadratic as a multiplicative character. -/
theorem quadratic_char_is_quadratic : (quadraticChar F).IsQuadratic := by
  intro a
  by_cases' ha : a = 0
  · left
    rw [ha]
    exact quadratic_char_zero
    
  · right
    exact quadratic_char_dichotomy ha
    

variable {F}

/-- The quadratic character is nontrivial as a multiplicative character
when the domain has odd characteristic. -/
theorem quadratic_char_is_nontrivial (hF : ringChar F ≠ 2) : (quadraticChar F).IsNontrivial := by
  rcases quadratic_char_exists_neg_one hF with ⟨a, ha⟩
  have hu : IsUnit a := by
    by_contra hf
    rw [map_nonunit _ hf] at ha
    norm_num  at ha
  refine' ⟨hu.unit, (_ : quadratic_char F a ≠ 1)⟩
  rw [ha]
  norm_num

/-- The number of solutions to `x^2 = a` is determined by the quadratic character. -/
theorem quadratic_char_card_sqrts (hF : ringChar F ≠ 2) (a : F) :
    ↑{ x : F | x ^ 2 = a }.toFinset.card = quadraticChar F a + 1 := by
  -- we consider the cases `a = 0`, `a` is a nonzero square and `a` is a nonsquare in turn
  by_cases' h₀ : a = 0
  · simp only [← h₀, ← pow_eq_zero_iff, ← Nat.succ_pos', ← Int.coe_nat_succ, ← Int.coe_nat_zero, ← MulChar.map_zero, ←
      Set.set_of_eq_eq_singleton, ← Set.to_finset_card, ← Set.card_singleton]
    
  · set s := { x : F | x ^ 2 = a }.toFinset with hs
    by_cases' h : IsSquare a
    · rw [(quadratic_char_one_iff_is_square h₀).mpr h]
      rcases h with ⟨b, h⟩
      rw [h, mul_self_eq_zero] at h₀
      have h₁ : s = [b, -b].toFinset := by
        ext x
        simp only [← Finset.mem_filter, ← Finset.mem_univ, ← true_andₓ, ← List.to_finset_cons, ← List.to_finset_nil, ←
          insert_emptyc_eq, ← Finset.mem_insert, ← Finset.mem_singleton]
        rw [← pow_two] at h
        simp only [← hs, ← Set.mem_to_finset, ← Set.mem_set_of_eq, ← h]
        constructor
        · exact eq_or_eq_neg_of_sq_eq_sq _ _
          
        · rintro (h₂ | h₂) <;> rw [h₂]
          simp only [← neg_sq]
          
      norm_cast
      rw [h₁, List.to_finset_cons, List.to_finset_cons, List.to_finset_nil]
      exact Finset.card_doubleton (Ne.symm (mt (Ringₓ.eq_self_iff_eq_zero_of_char_ne_two hF).mp h₀))
      
    · rw [quadratic_char_neg_one_iff_not_is_square.mpr h]
      simp only [← Int.coe_nat_eq_zero, ← Finset.card_eq_zero, ← Set.to_finset_card, ← Fintype.card_of_finset, ←
        Set.mem_set_of_eq, ← add_left_negₓ]
      ext x
      simp only [← iff_falseₓ, ← Finset.mem_filter, ← Finset.mem_univ, ← true_andₓ, ← Finset.not_mem_empty]
      rw [is_square_iff_exists_sq] at h
      exact fun h' => h ⟨_, h'.symm⟩
      
    

open BigOperators

/-- The sum over the values of the quadratic character is zero when the characteristic is odd. -/
theorem quadratic_char_sum_zero (hF : ringChar F ≠ 2) : (∑ a : F, quadraticChar F a) = 0 :=
  IsNontrivial.sum_eq_zero (quadratic_char_is_nontrivial hF)

end QuadraticChar

end Charₓ

/-!
### Special values of the quadratic character

We express `quadratic_char F (-1)` in terms of `χ₄`.
-/


section SpecialValues

namespace Charₓ

open Zmod

variable {F : Type _} [Field F] [Fintype F]

/-- The value of the quadratic character at `-1` -/
theorem quadratic_char_neg_one [DecidableEq F] (hF : ringChar F ≠ 2) : quadraticChar F (-1) = χ₄ (Fintype.card F) := by
  have h := quadratic_char_eq_pow_of_char_ne_two hF (neg_ne_zero.mpr one_ne_zero)
  rw [h, χ₄_eq_neg_one_pow (FiniteField.odd_card_of_char_ne_two hF)]
  set n := Fintype.card F / 2
  cases' Nat.even_or_odd n with h₂ h₂
  · simp only [← Even.neg_one_pow h₂, ← eq_self_iff_true, ← if_true]
    
  · simp only [← Odd.neg_one_pow h₂, ← ite_eq_right_iff]
    exact fun hf => False.ndrec (1 = -1) (Ringₓ.neg_one_ne_one_of_char_ne_two hF hf)
    

/-- The interpretation in terms of whether `-1` is a square in `F` -/
theorem is_square_neg_one_iff : IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3 := by
  classical
  -- suggested by the linter (instead of `[decidable_eq F]`)
  by_cases' hF : ringChar F = 2
  · simp only [← FiniteField.is_square_of_char_two hF, ← Ne.def, ← true_iffₓ]
    exact fun hf => one_ne_zero ((Nat.odd_of_mod_four_eq_three hf).symm.trans (FiniteField.even_card_of_char_two hF))
    
  · have h₁ : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h₂ := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadratic_char_one_iff_is_square h₁, quadratic_char_neg_one hF, χ₄_nat_eq_if_mod_four, h₂]
    simp only [← Nat.one_ne_zero, ← if_false, ← ite_eq_left_iff, ← Ne.def]
    norm_num
    constructor
    · intro h h'
      have t := (of_not_not h).symm.trans h'
      norm_num  at t
      
    exact fun h h' => h' ((or_iff_left h).mp (nat.odd_mod_four_iff.mp h₂))
    

end Charₓ

end SpecialValues

