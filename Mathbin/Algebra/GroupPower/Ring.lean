/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.Hom.Ring

/-!
# Power operations on monoids with zero, semirings, and rings

This file provides additional lemmas about the natural power operator on rings and semirings.
Further lemmas about ordered semirings and rings can be found in `algebra.group_power.lemmas`.

-/


variable {R S M : Type _}

section MonoidWithZeroₓ

variable [MonoidWithZeroₓ M]

theorem zero_pow : ∀ {n : ℕ}, 0 < n → (0 : M) ^ n = 0
  | n + 1, _ => by
    rw [pow_succₓ, zero_mul]

@[simp]
theorem zero_pow' : ∀ n : ℕ, n ≠ 0 → (0 : M) ^ n = 0
  | 0, h => absurd rfl h
  | k + 1, h => by
    rw [pow_succₓ]
    exact zero_mul _

theorem zero_pow_eq (n : ℕ) : (0 : M) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, pow_zeroₓ]
    
  · rw [zero_pow (Nat.pos_of_ne_zeroₓ h)]
    

theorem pow_eq_zero_of_le {x : M} {n m : ℕ} (hn : n ≤ m) (hx : x ^ n = 0) : x ^ m = 0 := by
  rw [← tsub_add_cancel_of_le hn, pow_addₓ, hx, mul_zero]

theorem pow_eq_zero [NoZeroDivisors M] {x : M} {n : ℕ} (H : x ^ n = 0) : x = 0 := by
  induction' n with n ih
  · rw [pow_zeroₓ] at H
    rw [← mul_oneₓ x, H, mul_zero]
    
  · rw [pow_succₓ] at H
    exact Or.cases_on (mul_eq_zero.1 H) id ih
    

@[simp]
theorem pow_eq_zero_iff [NoZeroDivisors M] {a : M} {n : ℕ} (hn : 0 < n) : a ^ n = 0 ↔ a = 0 := by
  refine' ⟨pow_eq_zero, _⟩
  rintro rfl
  exact zero_pow hn

theorem pow_eq_zero_iff' [NoZeroDivisors M] [Nontrivial M] {a : M} {n : ℕ} : a ^ n = 0 ↔ a = 0 ∧ n ≠ 0 := by
  cases (zero_le n).eq_or_gt <;> simp [*, ← ne_of_gtₓ]

theorem pow_ne_zero_iff [NoZeroDivisors M] {a : M} {n : ℕ} (hn : 0 < n) : a ^ n ≠ 0 ↔ a ≠ 0 :=
  (pow_eq_zero_iff hn).Not

theorem ne_zero_pow {a : M} {n : ℕ} (hn : n ≠ 0) : a ^ n ≠ 0 → a ≠ 0 := by
  contrapose!
  rintro rfl
  exact zero_pow' n hn

@[field_simps]
theorem pow_ne_zero [NoZeroDivisors M] {a : M} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
  mt pow_eq_zero h

theorem sq_eq_zero_iff [NoZeroDivisors M] {a : M} : a ^ 2 = 0 ↔ a = 0 :=
  pow_eq_zero_iff two_pos

@[simp]
theorem zero_pow_eq_zero [Nontrivial M] {n : ℕ} : (0 : M) ^ n = 0 ↔ 0 < n := by
  constructor <;> intro h
  · rw [pos_iff_ne_zero]
    rintro rfl
    simpa using h
    
  · exact zero_pow' n h.ne.symm
    

theorem Ringₓ.inverse_pow (r : M) : ∀ n : ℕ, Ring.inverse r ^ n = Ring.inverse (r ^ n)
  | 0 => by
    rw [pow_zeroₓ, pow_zeroₓ, Ring.inverse_one]
  | n + 1 => by
    rw [pow_succₓ, pow_succ'ₓ, Ring.mul_inverse_rev' ((Commute.refl r).pow_left n), Ringₓ.inverse_pow]

end MonoidWithZeroₓ

section CommMonoidWithZero

variable [CommMonoidWithZero M] {n : ℕ} (hn : 0 < n)

include M hn

/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `monoid_with_zero_hom` -/
def powMonoidWithZeroHom : M →*₀ M :=
  { powMonoidHom n with map_zero' := zero_pow hn }

@[simp]
theorem coe_pow_monoid_with_zero_hom : (powMonoidWithZeroHom hn : M → M) = (· ^ n) :=
  rfl

@[simp]
theorem pow_monoid_with_zero_hom_apply (a : M) : powMonoidWithZeroHom hn a = a ^ n :=
  rfl

end CommMonoidWithZero

theorem pow_dvd_pow_iff [CancelCommMonoidWithZero R] {x : R} {n m : ℕ} (h0 : x ≠ 0) (h1 : ¬IsUnit x) :
    x ^ n ∣ x ^ m ↔ n ≤ m := by
  constructor
  · intro h
    rw [← not_ltₓ]
    intro hmn
    apply h1
    have : x ^ m * x ∣ x ^ m * 1 := by
      rw [← pow_succ'ₓ, mul_oneₓ]
      exact (pow_dvd_pow _ (Nat.succ_le_of_ltₓ hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← is_unit_iff_dvd_one] at this
    apply pow_ne_zero m h0
    
  · apply pow_dvd_pow
    

section Semiringₓ

variable [Semiringₓ R] [Semiringₓ S]

protected theorem RingHom.map_pow (f : R →+* S) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n :=
  map_pow f a

theorem min_pow_dvd_add {n m : ℕ} {a b c : R} (ha : c ^ n ∣ a) (hb : c ^ m ∣ b) : c ^ min n m ∣ a + b := by
  replace ha := (pow_dvd_pow c (min_le_leftₓ n m)).trans ha
  replace hb := (pow_dvd_pow c (min_le_rightₓ n m)).trans hb
  exact dvd_add ha hb

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R]

theorem add_sq (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp only [← sq, ← add_mul_self_eq]

theorem add_sq' (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [add_sq, add_assocₓ, add_commₓ _ (b ^ 2), add_assocₓ]

alias add_sq ← add_pow_two

end CommSemiringₓ

section HasDistribNeg

variable [Monoidₓ R] [HasDistribNeg R]

variable (R)

theorem neg_one_pow_eq_or : ∀ n : ℕ, (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1
  | 0 => Or.inl (pow_zeroₓ _)
  | n + 1 =>
    (neg_one_pow_eq_or n).swap.imp
      (fun h => by
        rw [pow_succₓ, h, neg_one_mul, neg_negₓ])
      fun h => by
      rw [pow_succₓ, h, mul_oneₓ]

variable {R}

theorem neg_pow (a : R) (n : ℕ) : -a ^ n = -1 ^ n * a ^ n :=
  neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n

@[simp]
theorem neg_pow_bit0 (a : R) (n : ℕ) : -a ^ bit0 n = a ^ bit0 n := by
  rw [pow_bit0', neg_mul_neg, pow_bit0']

@[simp]
theorem neg_pow_bit1 (a : R) (n : ℕ) : -a ^ bit1 n = -(a ^ bit1 n) := by
  simp only [← bit1, ← pow_succₓ, ← neg_pow_bit0, ← neg_mul_eq_neg_mulₓ]

@[simp]
theorem neg_sq (a : R) : -a ^ 2 = a ^ 2 := by
  simp [← sq]

@[simp]
theorem neg_one_sq : (-1 : R) ^ 2 = 1 := by
  rw [neg_sq, one_pow]

alias neg_sq ← neg_pow_two

alias neg_one_sq ← neg_one_pow_two

end HasDistribNeg

section Ringₓ

variable [Ringₓ R] {a b : R}

protected theorem Commute.sq_sub_sq (h : Commute a b) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, h.mul_self_sub_mul_self_eq]

@[simp]
theorem neg_one_pow_mul_eq_zero_iff {n : ℕ} {r : R} : -1 ^ n * r = 0 ↔ r = 0 := by
  rcases neg_one_pow_eq_or R n with ⟨⟩ <;> simp [← h]

@[simp]
theorem mul_neg_one_pow_eq_zero_iff {n : ℕ} {r : R} : r * -1 ^ n = 0 ↔ r = 0 := by
  rcases neg_one_pow_eq_or R n with ⟨⟩ <;> simp [← h]

variable [NoZeroDivisors R]

protected theorem Commute.sq_eq_sq_iff_eq_or_eq_neg (h : Commute a b) : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_comm]

@[simp]
theorem sq_eq_one_iff : a ^ 2 = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg, one_pow]

theorem sq_ne_one_iff : a ^ 2 ≠ 1 ↔ a ≠ 1 ∧ a ≠ -1 :=
  sq_eq_one_iff.Not.trans not_or_distrib

end Ringₓ

section CommRingₓ

variable [CommRingₓ R]

theorem sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
  (Commute.all a b).sq_sub_sq

alias sq_sub_sq ← pow_two_sub_pow_two

theorem sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  rw [sub_eq_add_neg, add_sq, neg_sq, mul_neg, ← sub_eq_add_neg]

alias sub_sq ← sub_pow_two

theorem sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
  rw [sub_eq_add_neg, add_sq', neg_sq, mul_neg, ← sub_eq_add_neg]

variable [NoZeroDivisors R] {a b : R}

theorem sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
  (Commute.all a b).sq_eq_sq_iff_eq_or_eq_neg

theorem eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b ^ 2 → a = b ∨ a = -b :=
  sq_eq_sq_iff_eq_or_eq_neg.1

-- Copies of the above comm_ring lemmas for `units R`.
namespace Units

protected theorem sq_eq_sq_iff_eq_or_eq_neg {a b : Rˣ} : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  simp_rw [ext_iff, coe_pow, sq_eq_sq_iff_eq_or_eq_neg, Units.coe_neg]

protected theorem eq_or_eq_neg_of_sq_eq_sq (a b : Rˣ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b :=
  Units.sq_eq_sq_iff_eq_or_eq_neg.1 h

end Units

end CommRingₓ

