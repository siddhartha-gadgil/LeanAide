/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.GroupPower.Lemmas

/-!
# Powers of elements of groups with an adjoined zero element

In this file we define integer power functions for groups with an adjoined zero element.
This generalises the integer power function on a division ring.
-/


section GroupWithZeroₓ

variable {G₀ : Type _} [GroupWithZeroₓ G₀] {a : G₀} {m n : ℕ}

section NatPow

theorem pow_sub₀ (a : G₀) {m n : ℕ} (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  have h1 : m - n + n = m := tsub_add_cancel_of_le h
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by
    rw [← pow_addₓ, h1]
  simpa only [← div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2

theorem pow_sub_of_lt (a : G₀) {m n : ℕ} (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (tsub_pos_of_lt h), zero_pow (n.zero_le.trans_lt h), zero_mul]
    
  · exact pow_sub₀ _ ha h.le
    

theorem pow_inv_comm₀ (a : G₀) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left₀.pow_pow m n

theorem inv_pow_sub₀ (ha : a ≠ 0) (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub₀ _ (inv_ne_zero ha) h, inv_pow, inv_pow, inv_invₓ]

theorem inv_pow_sub_of_lt (a : G₀) (h : n < m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub_of_lt a⁻¹ h, inv_pow, inv_pow, inv_invₓ]

end NatPow

end GroupWithZeroₓ

section Zpow

open Int

variable {G₀ : Type _} [GroupWithZeroₓ G₀]

attribute [local ematch] le_of_ltₓ

theorem zero_zpow : ∀ z : ℤ, z ≠ 0 → (0 : G₀) ^ z = 0
  | (n : ℕ), h => by
    rw [zpow_coe_nat, zero_pow']
    simpa using h
  | -[1+ n], h => by
    simp

theorem zero_zpow_eq (n : ℤ) : (0 : G₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, zpow_zero]
    
  · rw [zero_zpow _ h]
    

theorem zpow_add_one₀ {a : G₀} (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by
    simp only [Int.coe_nat_succ, ← zpow_coe_nat, ← pow_succ'ₓ]
  | -[1+ 0] => by
    erw [zpow_zero, zpow_neg_succ_of_nat, pow_oneₓ, inv_mul_cancel ha]
  | -[1+ n + 1] => by
    rw [Int.neg_succ_of_nat_eq, zpow_neg, neg_add, neg_add_cancel_right, zpow_neg, ← Int.coe_nat_succ, zpow_coe_nat,
      zpow_coe_nat, pow_succₓ _ (n + 1), mul_inv_rev, mul_assoc, inv_mul_cancel ha, mul_oneₓ]

theorem zpow_sub_one₀ {a : G₀} (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := by
      rw [mul_assoc, mul_inv_cancel ha, mul_oneₓ]
    _ = a ^ n * a⁻¹ := by
      rw [← zpow_add_one₀ ha, sub_add_cancel]
    

theorem zpow_add₀ {a : G₀} (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n using Int.induction_on with n ihn n ihn
  case hz =>
    simp
  · simp only [add_assocₓ, ← zpow_add_one₀ ha, ← ihn, ← mul_assoc]
    
  · rw [zpow_sub_one₀ ha, ← mul_assoc, ← ihn, ← zpow_sub_one₀ ha, add_sub_assoc]
    

theorem zpow_add' {a : G₀} {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) : a ^ (m + n) = a ^ m * a ^ n := by
  by_cases' hm : m = 0
  · simp [← hm]
    
  by_cases' hn : n = 0
  · simp [← hn]
    
  by_cases' ha : a = 0
  · subst a
    simp only [← false_orₓ, ← eq_self_iff_true, ← not_true, ← Ne.def, ← hm, ← hn, ← false_andₓ, ← or_falseₓ] at h
    rw [zero_zpow _ h, zero_zpow _ hm, zero_mul]
    
  · exact zpow_add₀ ha m n
    

theorem zpow_one_add₀ {a : G₀} (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i := by
  rw [zpow_add₀ h, zpow_one]

theorem SemiconjBy.zpow_right₀ {a x y : G₀} (h : SemiconjBy a x y) : ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ) => by
    simp [← h.pow_right n]
  | -[1+ n] => by
    simp [← (h.pow_right (n + 1)).inv_right₀]

theorem Commute.zpow_right₀ {a b : G₀} (h : Commute a b) : ∀ m : ℤ, Commute a (b ^ m) :=
  h.zpow_right₀

theorem Commute.zpow_left₀ {a b : G₀} (h : Commute a b) (m : ℤ) : Commute (a ^ m) b :=
  (h.symm.zpow_right₀ m).symm

theorem Commute.zpow_zpow₀ {a b : G₀} (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left₀ m).zpow_right₀ n

theorem Commute.zpow_self₀ (a : G₀) (n : ℤ) : Commute (a ^ n) a :=
  (Commute.refl a).zpow_left₀ n

theorem Commute.self_zpow₀ (a : G₀) (n : ℤ) : Commute a (a ^ n) :=
  (Commute.refl a).zpow_right₀ n

theorem Commute.zpow_zpow_self₀ (a : G₀) (m n : ℤ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).zpow_zpow₀ m n

theorem zpow_bit1₀ (a : G₀) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [← zpow_bit0, bit1, zpow_add', zpow_one]
  right
  left
  apply bit1_ne_zero

theorem zpow_ne_zero_of_ne_zero {a : G₀} (ha : a ≠ 0) : ∀ z : ℤ, a ^ z ≠ 0
  | (n : ℕ) => by
    rw [zpow_coe_nat]
    exact pow_ne_zero _ ha
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat]
    exact inv_ne_zero (pow_ne_zero _ ha)

theorem zpow_sub₀ {a : G₀} (ha : a ≠ 0) (z1 z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 := by
  rw [sub_eq_add_neg, zpow_add₀ ha, zpow_neg, div_eq_mul_inv]

theorem zpow_bit1' (a : G₀) (n : ℤ) : a ^ bit1 n = (a * a) ^ n * a := by
  rw [zpow_bit1₀, (Commute.refl a).mul_zpow]

theorem zpow_eq_zero {x : G₀} {n : ℤ} (h : x ^ n = 0) : x = 0 :=
  Classical.by_contradiction fun hx => zpow_ne_zero_of_ne_zero hx n h

theorem zpow_eq_zero_iff {a : G₀} {n : ℤ} (hn : 0 < n) : a ^ n = 0 ↔ a = 0 := by
  refine' ⟨zpow_eq_zero, _⟩
  rintro rfl
  exact zero_zpow _ hn.ne'

theorem zpow_ne_zero {x : G₀} (n : ℤ) : x ≠ 0 → x ^ n ≠ 0 :=
  mt zpow_eq_zero

theorem zpow_neg_mul_zpow_self (n : ℤ) {x : G₀} (h : x ≠ 0) : x ^ -n * x ^ n = 1 := by
  rw [zpow_neg]
  exact inv_mul_cancel (zpow_ne_zero n h)

end Zpow

section

variable {G₀ : Type _} [CommGroupWithZero G₀]

theorem div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b := by
  by_cases' ha : a = 0
  · simp [← ha]
    
  rw [sq, mul_assoc, mul_div_cancel_left _ ha]

end

/-- If a monoid homomorphism `f` between two `group_with_zero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
theorem MonoidWithZeroHom.map_zpow {G₀ G₀' : Type _} [GroupWithZeroₓ G₀] [GroupWithZeroₓ G₀'] (f : G₀ →*₀ G₀')
    (x : G₀) : ∀ n : ℤ, f (x ^ n) = f x ^ n
  | (n : ℕ) => by
    rw [zpow_coe_nat, zpow_coe_nat]
    exact f.to_monoid_hom.map_pow x n
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat]
    exact (f.map_inv _).trans <| congr_arg _ <| f.to_monoid_hom.map_pow x _

