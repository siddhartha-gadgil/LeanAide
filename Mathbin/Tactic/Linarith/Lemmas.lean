/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathbin.Algebra.Order.Ring
import Mathbin.Data.Int.Basic
import Mathbin.Tactic.NormNum

/-!
# Lemmas for `linarith`

This file contains auxiliary lemmas that `linarith` uses to construct proofs.
If you find yourself looking for a theorem here, you might be in the wrong place.
-/


namespace Linarith

theorem Int.coe_nat_bit0 (n : ℕ) : (↑(bit0 n : ℕ) : ℤ) = bit0 (↑n : ℤ) := by
  simp [← bit0]

theorem Int.coe_nat_bit1 (n : ℕ) : (↑(bit1 n : ℕ) : ℤ) = bit1 (↑n : ℤ) := by
  simp [← bit1, ← bit0]

theorem Int.coe_nat_bit0_mul (n : ℕ) (x : ℕ) : (↑(bit0 n * x) : ℤ) = (↑(bit0 n) : ℤ) * (↑x : ℤ) := by
  simp

theorem Int.coe_nat_bit1_mul (n : ℕ) (x : ℕ) : (↑(bit1 n * x) : ℤ) = (↑(bit1 n) : ℤ) * (↑x : ℤ) := by
  simp

theorem Int.coe_nat_one_mul (x : ℕ) : (↑(1 * x) : ℤ) = 1 * (↑x : ℤ) := by
  simp

theorem Int.coe_nat_zero_mul (x : ℕ) : (↑(0 * x) : ℤ) = 0 * (↑x : ℤ) := by
  simp

theorem Int.coe_nat_mul_bit0 (n : ℕ) (x : ℕ) : (↑(x * bit0 n) : ℤ) = (↑x : ℤ) * (↑(bit0 n) : ℤ) := by
  simp

theorem Int.coe_nat_mul_bit1 (n : ℕ) (x : ℕ) : (↑(x * bit1 n) : ℤ) = (↑x : ℤ) * (↑(bit1 n) : ℤ) := by
  simp

theorem Int.coe_nat_mul_one (x : ℕ) : (↑(x * 1) : ℤ) = (↑x : ℤ) * 1 := by
  simp

theorem Int.coe_nat_mul_zero (x : ℕ) : (↑(x * 0) : ℤ) = (↑x : ℤ) * 0 := by
  simp

theorem nat_eq_subst {n1 n2 : ℕ} {z1 z2 : ℤ} (hn : n1 = n2) (h1 : ↑n1 = z1) (h2 : ↑n2 = z2) : z1 = z2 := by
  simpa [← Eq.symm h1, ← Eq.symm h2, ← Int.coe_nat_eq_coe_nat_iff]

theorem nat_le_subst {n1 n2 : ℕ} {z1 z2 : ℤ} (hn : n1 ≤ n2) (h1 : ↑n1 = z1) (h2 : ↑n2 = z2) : z1 ≤ z2 := by
  simpa [← Eq.symm h1, ← Eq.symm h2, ← Int.coe_nat_le]

theorem nat_lt_subst {n1 n2 : ℕ} {z1 z2 : ℤ} (hn : n1 < n2) (h1 : ↑n1 = z1) (h2 : ↑n2 = z2) : z1 < z2 := by
  simpa [← Eq.symm h1, ← Eq.symm h2, ← Int.coe_nat_lt]

theorem eq_of_eq_of_eq {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : b = 0) : a + b = 0 := by
  simp [*]

theorem le_of_eq_of_le {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : b ≤ 0) : a + b ≤ 0 := by
  simp [*]

theorem lt_of_eq_of_lt {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : b < 0) : a + b < 0 := by
  simp [*]

theorem le_of_le_of_eq {α} [OrderedSemiring α] {a b : α} (ha : a ≤ 0) (hb : b = 0) : a + b ≤ 0 := by
  simp [*]

theorem lt_of_lt_of_eq {α} [OrderedSemiring α] {a b : α} (ha : a < 0) (hb : b = 0) : a + b < 0 := by
  simp [*]

theorem mul_neg {α} [OrderedRing α] {a b : α} (ha : a < 0) (hb : 0 < b) : b * a < 0 :=
  have : -b * a > 0 := mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha
  neg_of_neg_pos
    (by
      simpa)

theorem mul_nonpos {α} [OrderedRing α] {a b : α} (ha : a ≤ 0) (hb : 0 < b) : b * a ≤ 0 := by
  have : -b * a ≥ 0 := mul_nonneg_of_nonpos_of_nonpos (le_of_ltₓ (neg_neg_of_pos hb)) ha
  simpa

-- used alongside `mul_neg` and `mul_nonpos`, so has the same argument pattern for uniformity
@[nolint unused_arguments]
theorem mul_eq {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : 0 < b) : b * a = 0 := by
  simp [*]

theorem eq_of_not_lt_of_not_gt {α} [LinearOrderₓ α] (a b : α) (h1 : ¬a < b) (h2 : ¬b < a) : a = b :=
  le_antisymmₓ (le_of_not_gtₓ h2) (le_of_not_gtₓ h1)

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
theorem mul_zero_eq {α} {R : α → α → Prop} [Semiringₓ α] {a b : α} (_ : R a 0) (h : b = 0) : a * b = 0 := by
  simp [← h]

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
theorem zero_mul_eq {α} {R : α → α → Prop} [Semiringₓ α] {a b : α} (h : a = 0) (_ : R b 0) : a * b = 0 := by
  simp [← h]

end Linarith

