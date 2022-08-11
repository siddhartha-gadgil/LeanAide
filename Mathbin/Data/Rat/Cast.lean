/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Rat.Order
import Mathbin.Data.Int.CharZero
import Mathbin.Algebra.Field.Opposite

/-!
# Casts for Rational Numbers

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/


open BigOperators

variable {F ι α β : Type _}

namespace Rat

open Rat

section WithDivRing

variable [DivisionRing α]

/-- Construct the canonical injection from `ℚ` into an arbitrary
  division ring. If the field has positive characteristic `p`,
  we define `1 / p = 1 / 0 = 0` for consistency with our
  division by zero convention. -/
-- see Note [coercion into rings]
instance (priority := 900) castCoe : CoeTₓ ℚ α :=
  ⟨fun r => r.1 / r.2⟩

theorem cast_def (r : ℚ) : (r : α) = r.num / r.denom :=
  rfl

@[simp]
theorem cast_of_int (n : ℤ) : (ofInt n : α) = n :=
  show (n / (1 : ℕ) : α) = n by
    rw [Nat.cast_oneₓ, div_one]

@[simp, norm_cast]
theorem cast_coe_int (n : ℤ) : ((n : ℚ) : α) = n := by
  rw [coe_int_eq_of_int, cast_of_int]

@[simp, norm_cast]
theorem cast_coe_nat (n : ℕ) : ((n : ℚ) : α) = n := by
  rw [← Int.cast_coe_nat, cast_coe_int, Int.cast_coe_nat]

@[simp, norm_cast]
theorem cast_zero : ((0 : ℚ) : α) = 0 :=
  (cast_of_int _).trans Int.cast_zeroₓ

@[simp, norm_cast]
theorem cast_one : ((1 : ℚ) : α) = 1 :=
  (cast_of_int _).trans Int.cast_oneₓ

theorem cast_commute (r : ℚ) (a : α) : Commute (↑r) a :=
  (r.1.cast_commute a).div_left (r.2.cast_commute a)

theorem cast_comm (r : ℚ) (a : α) : (r : α) * a = a * r :=
  (cast_commute r a).Eq

theorem commute_cast (a : α) (r : ℚ) : Commute a r :=
  (r.cast_commute a).symm

@[norm_cast]
theorem cast_mk_of_ne_zero (a b : ℤ) (b0 : (b : α) ≠ 0) : (a /. b : α) = a / b := by
  have b0' : b ≠ 0 := by
    refine' mt _ b0
    simp (config := { contextual := true })
  cases' e : a /. b with n d h c
  have d0 : (d : α) ≠ 0 := by
    intro d0
    have dd := denom_dvd a b
    cases'
      show (d : ℤ) ∣ b by
        rwa [e] at dd with
      k ke
    have : (b : α) = (d : α) * (k : α) := by
      rw [ke, Int.cast_mul, Int.cast_coe_nat]
    rw [d0, zero_mul] at this
    contradiction
  rw [num_denom'] at e
  have := congr_arg (coe : ℤ → α) ((mk_eq b0' <| ne_of_gtₓ <| Int.coe_nat_pos.2 h).1 e)
  rw [Int.cast_mul, Int.cast_mul, Int.cast_coe_nat] at this
  symm
  change (a / b : α) = n / d
  rw [div_eq_mul_inv, eq_div_iff_mul_eq d0, mul_assoc, (d.commute_cast _).Eq, ← mul_assoc, this, mul_assoc,
    mul_inv_cancel b0, mul_oneₓ]

@[norm_cast]
theorem cast_add_of_ne_zero : ∀ {m n : ℚ}, (m.denom : α) ≠ 0 → (n.denom : α) ≠ 0 → ((m + n : ℚ) : α) = m + n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => fun (d₁0 : (d₁ : α) ≠ 0) (d₂0 : (d₂ : α) ≠ 0) => by
    have d₁0' : (d₁ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by
        rw [e] at d₁0 <;> exact d₁0 Nat.cast_zeroₓ
    have d₂0' : (d₂ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by
        rw [e] at d₂0 <;> exact d₂0 Nat.cast_zeroₓ
    rw [num_denom', num_denom', add_def d₁0' d₂0']
    suffices (n₁ * (d₂ * (d₂⁻¹ * d₁⁻¹)) + n₂ * (d₁ * d₂⁻¹) * d₁⁻¹ : α) = n₁ * d₁⁻¹ + n₂ * d₂⁻¹ by
      rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero]
      · simpa [← division_def, ← left_distrib, ← right_distrib, ← mul_inv_rev, ← d₁0, ← d₂0, ← mul_assoc]
        
      all_goals
        simp [← d₁0, ← d₂0]
    rw [← mul_assoc (d₂ : α), mul_inv_cancel d₂0, one_mulₓ, (Nat.cast_commute _ _).Eq]
    simp [← d₁0, ← mul_assoc]

@[simp, norm_cast]
theorem cast_neg : ∀ n, ((-n : ℚ) : α) = -n
  | ⟨n, d, h, c⟩ =>
    show (↑(-n) / d : α) = -(n / d) by
      rw [div_eq_mul_inv, div_eq_mul_inv, Int.cast_neg, neg_mul_eq_neg_mulₓ]

@[norm_cast]
theorem cast_sub_of_ne_zero {m n : ℚ} (m0 : (m.denom : α) ≠ 0) (n0 : (n.denom : α) ≠ 0) : ((m - n : ℚ) : α) = m - n :=
  by
  have : ((-n).denom : α) ≠ 0 := by
    cases n <;> exact n0
  simp [← sub_eq_add_neg, ← cast_add_of_ne_zero m0 this]

@[norm_cast]
theorem cast_mul_of_ne_zero : ∀ {m n : ℚ}, (m.denom : α) ≠ 0 → (n.denom : α) ≠ 0 → ((m * n : ℚ) : α) = m * n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => fun (d₁0 : (d₁ : α) ≠ 0) (d₂0 : (d₂ : α) ≠ 0) => by
    have d₁0' : (d₁ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by
        rw [e] at d₁0 <;> exact d₁0 Nat.cast_zeroₓ
    have d₂0' : (d₂ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by
        rw [e] at d₂0 <;> exact d₂0 Nat.cast_zeroₓ
    rw [num_denom', num_denom', mul_def d₁0' d₂0']
    suffices (n₁ * (n₂ * d₂⁻¹ * d₁⁻¹) : α) = n₁ * (d₁⁻¹ * (n₂ * d₂⁻¹)) by
      rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero]
      · simpa [← division_def, ← mul_inv_rev, ← d₁0, ← d₂0, ← mul_assoc]
        
      all_goals
        simp [← d₁0, ← d₂0]
    rw [(d₁.commute_cast (_ : α)).inv_right₀.Eq]

@[simp]
theorem cast_inv_nat (n : ℕ) : ((n⁻¹ : ℚ) : α) = n⁻¹ := by
  cases n
  · simp
    
  simp_rw [coe_nat_eq_mk, inv_def, mk, mk_nat, dif_neg n.succ_ne_zero, mk_pnat]
  simp [← cast_def]

@[simp]
theorem cast_inv_int (n : ℤ) : ((n⁻¹ : ℚ) : α) = n⁻¹ := by
  cases n
  · simp [← cast_inv_nat]
    
  · simp only [← Int.cast_neg_succ_of_nat, Nat.cast_succₓ, ← cast_neg, ← inv_neg, ← cast_inv_nat]
    

@[norm_cast]
theorem cast_inv_of_ne_zero : ∀ {n : ℚ}, (n.num : α) ≠ 0 → (n.denom : α) ≠ 0 → ((n⁻¹ : ℚ) : α) = n⁻¹
  | ⟨n, d, h, c⟩ => fun (n0 : (n : α) ≠ 0) (d0 : (d : α) ≠ 0) => by
    have n0' : (n : ℤ) ≠ 0 := fun e => by
      rw [e] at n0 <;> exact n0 Int.cast_zeroₓ
    have d0' : (d : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by
        rw [e] at d0 <;> exact d0 Nat.cast_zeroₓ
    rw [num_denom', inv_def]
    rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, inv_div] <;> simp [← n0, ← d0]

@[norm_cast]
theorem cast_div_of_ne_zero {m n : ℚ} (md : (m.denom : α) ≠ 0) (nn : (n.num : α) ≠ 0) (nd : (n.denom : α) ≠ 0) :
    ((m / n : ℚ) : α) = m / n := by
  have : (n⁻¹.denom : ℤ) ∣ n.num := by
    conv in n⁻¹.denom => rw [← @num_denom n, inv_def] <;> apply denom_dvd
  have : (n⁻¹.denom : α) = 0 → (n.num : α) = 0 := fun h => by
    let ⟨k, e⟩ := this
    have := congr_arg (coe : ℤ → α) e <;> rwa [Int.cast_mul, Int.cast_coe_nat, h, zero_mul] at this
  rw [division_def, cast_mul_of_ne_zero md (mt this nn), cast_inv_of_ne_zero nn nd, division_def]

@[simp, norm_cast]
theorem cast_inj [CharZero α] : ∀ {m n : ℚ}, (m : α) = n ↔ m = n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => by
    refine' ⟨fun h => _, congr_arg _⟩
    have d₁0 : d₁ ≠ 0 := ne_of_gtₓ h₁
    have d₂0 : d₂ ≠ 0 := ne_of_gtₓ h₂
    have d₁a : (d₁ : α) ≠ 0 := Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) ≠ 0 := Nat.cast_ne_zero.2 d₂0
    rw [num_denom', num_denom'] at h⊢
    rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero] at h <;> simp [← d₁0, ← d₂0] at h⊢
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂ : α)).inv_left₀.Eq, ← mul_assoc, ←
      division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm, ← Int.cast_coe_nat d₁, ← Int.cast_mul, ←
      Int.cast_coe_nat d₂, ← Int.cast_mul, Int.cast_inj, ←
      mk_eq (Int.coe_nat_ne_zero.2 d₁0) (Int.coe_nat_ne_zero.2 d₂0)] at h

theorem cast_injective [CharZero α] : Function.Injective (coe : ℚ → α)
  | m, n => cast_inj.1

@[simp]
theorem cast_eq_zero [CharZero α] {n : ℚ} : (n : α) = 0 ↔ n = 0 := by
  rw [← cast_zero, cast_inj]

theorem cast_ne_zero [CharZero α] {n : ℚ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero

@[simp, norm_cast]
theorem cast_add [CharZero α] (m n) : ((m + n : ℚ) : α) = m + n :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gtₓ m.Pos) (Nat.cast_ne_zero.2 <| ne_of_gtₓ n.Pos)

@[simp, norm_cast]
theorem cast_sub [CharZero α] (m n) : ((m - n : ℚ) : α) = m - n :=
  cast_sub_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gtₓ m.Pos) (Nat.cast_ne_zero.2 <| ne_of_gtₓ n.Pos)

@[simp, norm_cast]
theorem cast_mul [CharZero α] (m n) : ((m * n : ℚ) : α) = m * n :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gtₓ m.Pos) (Nat.cast_ne_zero.2 <| ne_of_gtₓ n.Pos)

@[simp, norm_cast]
theorem cast_bit0 [CharZero α] (n : ℚ) : ((bit0 n : ℚ) : α) = bit0 n :=
  cast_add _ _

@[simp, norm_cast]
theorem cast_bit1 [CharZero α] (n : ℚ) : ((bit1 n : ℚ) : α) = bit1 n := by
  rw [bit1, cast_add, cast_one, cast_bit0] <;> rfl

variable (α) [CharZero α]

/-- Coercion `ℚ → α` as a `ring_hom`. -/
def castHom : ℚ →+* α :=
  ⟨coe, cast_one, cast_mul, cast_zero, cast_add⟩

variable {α}

@[simp]
theorem coe_cast_hom : ⇑(castHom α) = coe :=
  rfl

@[simp, norm_cast]
theorem cast_inv (n) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
  (castHom α).map_inv _

@[simp, norm_cast]
theorem cast_div (m n) : ((m / n : ℚ) : α) = m / n :=
  (castHom α).map_div _ _

@[norm_cast]
theorem cast_mk (a b : ℤ) : (a /. b : α) = a / b := by
  simp only [← mk_eq_div, ← cast_div, ← cast_coe_int]

@[simp, norm_cast]
theorem cast_pow (q) (k : ℕ) : ((q ^ k : ℚ) : α) = q ^ k :=
  (castHom α).map_pow q k

@[simp, norm_cast]
theorem cast_list_sum (s : List ℚ) : (↑s.Sum : α) = (s.map coe).Sum :=
  map_list_sum (Rat.castHom α) _

@[simp, norm_cast]
theorem cast_multiset_sum (s : Multiset ℚ) : (↑s.Sum : α) = (s.map coe).Sum :=
  map_multiset_sum (Rat.castHom α) _

@[simp, norm_cast]
theorem cast_sum (s : Finset ι) (f : ι → ℚ) : (↑(∑ i in s, f i) : α) = ∑ i in s, f i :=
  map_sum (Rat.castHom α) _ _

@[simp, norm_cast]
theorem cast_list_prod (s : List ℚ) : (↑s.Prod : α) = (s.map coe).Prod :=
  map_list_prod (Rat.castHom α) _

end WithDivRing

section Field

variable [Field α] [CharZero α]

@[simp, norm_cast]
theorem cast_multiset_prod (s : Multiset ℚ) : (↑s.Prod : α) = (s.map coe).Prod :=
  map_multiset_prod (Rat.castHom α) _

@[simp, norm_cast]
theorem cast_prod (s : Finset ι) (f : ι → ℚ) : (↑(∏ i in s, f i) : α) = ∏ i in s, f i :=
  map_prod (Rat.castHom α) _ _

end Field

@[simp, norm_cast]
theorem cast_nonneg [LinearOrderedField α] : ∀ {n : ℚ}, 0 ≤ (n : α) ↔ 0 ≤ n
  | ⟨n, d, h, c⟩ => by
    rw [num_denom', cast_mk, mk_eq_div, div_nonneg_iff, div_nonneg_iff]
    norm_cast

@[simp, norm_cast]
theorem cast_le [LinearOrderedField α] {m n : ℚ} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]

@[simp, norm_cast]
theorem cast_lt [LinearOrderedField α] {m n : ℚ} : (m : α) < n ↔ m < n := by
  simpa [-cast_le] using not_congr (@cast_le α _ n m)

@[simp]
theorem cast_nonpos [LinearOrderedField α] {n : ℚ} : (n : α) ≤ 0 ↔ n ≤ 0 := by
  rw [← cast_zero, cast_le]

@[simp]
theorem cast_pos [LinearOrderedField α] {n : ℚ} : (0 : α) < n ↔ 0 < n := by
  rw [← cast_zero, cast_lt]

@[simp]
theorem cast_lt_zero [LinearOrderedField α] {n : ℚ} : (n : α) < 0 ↔ n < 0 := by
  rw [← cast_zero, cast_lt]

@[simp, norm_cast]
theorem cast_id : ∀ n : ℚ, ↑n = n
  | ⟨n, d, h, c⟩ => by
    rw [num_denom', cast_mk, mk_eq_div]

@[simp]
theorem cast_hom_rat : castHom ℚ = RingHom.id ℚ :=
  RingHom.ext cast_id

@[simp, norm_cast]
theorem cast_min [LinearOrderedField α] {a b : ℚ} : (↑(min a b) : α) = min a b := by
  by_cases' a ≤ b <;> simp [← h, ← min_def]

@[simp, norm_cast]
theorem cast_max [LinearOrderedField α] {a b : ℚ} : (↑(max a b) : α) = max a b := by
  by_cases' b ≤ a <;> simp [← h, ← max_def]

@[simp, norm_cast]
theorem cast_abs [LinearOrderedField α] {q : ℚ} : ((abs q : ℚ) : α) = abs q := by
  simp [← abs_eq_max_neg]

end Rat

open Rat RingHom

theorem RingHom.eq_rat_cast {k} [DivisionRing k] (f : ℚ →+* k) (r : ℚ) : f r = r :=
  calc
    f r = f (r.1 / r.2) := by
      rw [← Int.cast_coe_nat, ← mk_eq_div, num_denom]
    _ = f r.1 / f r.2 := f.map_div _ _
    _ = r.1 / r.2 := by
      rw [map_nat_cast, map_int_cast]
    

-- This seems to be true for a `[char_p k]` too because `k'` must have the same characteristic
-- but the proof would be much longer
@[simp]
theorem map_rat_cast [DivisionRing α] [DivisionRing β] [CharZero α] [RingHomClass F α β] (f : F) (q : ℚ) : f q = q :=
  ((f : α →+* β).comp <| castHom α).eq_rat_cast q

theorem RingHom.ext_rat {R : Type _} [Semiringₓ R] (f g : ℚ →+* R) : f = g := by
  ext r
  refine' Rat.numDenomCasesOn' r _
  intro a b b0
  let φ : ℤ →+* R := f.comp (Int.castRingHom ℚ)
  let ψ : ℤ →+* R := g.comp (Int.castRingHom ℚ)
  rw [Rat.mk_eq_div, Int.cast_coe_nat]
  have b0' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 b0
  have : ∀ n : ℤ, f n = g n := fun n =>
    show φ n = ψ n by
      rw [φ.ext_int ψ]
  calc f (a * b⁻¹) = f a * f b⁻¹ * (g (b : ℤ) * g b⁻¹) := by
      rw [Int.cast_coe_nat, ← g.map_mul, mul_inv_cancel b0', g.map_one, mul_oneₓ,
        f.map_mul]_ = g a * f b⁻¹ * (f (b : ℤ) * g b⁻¹) :=
      by
      rw [this a, ← this b]_ = g (a * b⁻¹) := by
      rw [Int.cast_coe_nat, mul_assoc, ← mul_assoc (f b⁻¹), ← f.map_mul, inv_mul_cancel b0', f.map_one, one_mulₓ,
        g.map_mul]

instance Rat.subsingleton_ring_hom {R : Type _} [Semiringₓ R] : Subsingleton (ℚ →+* R) :=
  ⟨RingHom.ext_rat⟩

namespace MonoidWithZeroHom

variable {M : Type _} [GroupWithZeroₓ M]

/-- If `f` and `g` agree on the integers then they are equal `φ`.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
theorem ext_rat {f g : ℚ →*₀ M}
    (same_on_int : f.comp (Int.castRingHom ℚ).toMonoidWithZeroHom = g.comp (Int.castRingHom ℚ).toMonoidWithZeroHom) :
    f = g := by
  have same_on_int' : ∀ k : ℤ, f k = g k := congr_fun same_on_int
  ext x
  rw [← @Rat.num_denom x, Rat.mk_eq_div, f.map_div, g.map_div, same_on_int' x.num, same_on_int' x.denom]

/-- Positive integer values of a morphism `φ` and its value on `-1` completely determine `φ`. -/
theorem ext_rat_on_pnat {f g : ℚ →*₀ M} (same_on_neg_one : f (-1) = g (-1))
    (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_rat <|
    ext_int'
      (by
        simpa)
      ‹_›

end MonoidWithZeroHom

namespace MulOpposite

variable [DivisionRing α]

@[simp, norm_cast]
theorem op_rat_cast (r : ℚ) : op (r : α) = (↑r : αᵐᵒᵖ) := by
  rw [cast_def, div_eq_mul_inv, op_mul, op_inv, op_nat_cast, op_int_cast, (Commute.cast_int_right _ r.num).Eq, cast_def,
    div_eq_mul_inv]

@[simp, norm_cast]
theorem unop_rat_cast (r : ℚ) : unop (r : αᵐᵒᵖ) = r := by
  rw [cast_def, div_eq_mul_inv, unop_mul, unop_inv, unop_nat_cast, unop_int_cast, (Commute.cast_int_right _ r.num).Eq,
    cast_def, div_eq_mul_inv]

end MulOpposite

