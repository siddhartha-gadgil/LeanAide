/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathbin.Algebra.GroupWithZero.Power
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Algebra.BigOperators.Intervals
import Mathbin.Tactic.Abel
import Mathbin.Data.Nat.Parity

/-!
# Partial sums of geometric series

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof. We also provide some bounds on the
"geometric" sum of `a/b^i` where `a b : ℕ`.

## Main statements

* `geom_sum_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-x^m}{x-1}$ in a division ring.
* `geom_sum₂_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-y^{n-m}x^m}{x-y}$ in a field.

Several variants are recorded, generalising in particular to the case of a noncommutative ring in
which `x` and `y` commute. Even versions not using division or subtraction, valid in each semiring,
are recorded.
-/


universe u

variable {α : Type u}

open Finset MulOpposite

open BigOperators

section Semiringₓ

variable [Semiringₓ α]

theorem geom_sum_succ {x : α} {n : ℕ} : (∑ i in range (n + 1), x ^ i) = (x * ∑ i in range n, x ^ i) + 1 := by
  simp only [← mul_sum, pow_succₓ, ← sum_range_succ', ← pow_zeroₓ]

theorem geom_sum_succ' {x : α} {n : ℕ} : (∑ i in range (n + 1), x ^ i) = x ^ n + ∑ i in range n, x ^ i :=
  (sum_range_succ _ _).trans (add_commₓ _ _)

theorem geom_sum_zero (x : α) : (∑ i in range 0, x ^ i) = 0 :=
  rfl

theorem geom_sum_one (x : α) : (∑ i in range 1, x ^ i) = 1 := by
  simp [← geom_sum_succ']

@[simp]
theorem geom_sum_two {x : α} : (∑ i in range 2, x ^ i) = x + 1 := by
  simp [← geom_sum_succ']

@[simp]
theorem zero_geom_sum : ∀ {n}, (∑ i in range n, (0 : α) ^ i) = if n = 0 then 0 else 1
  | 0 => by
    simp
  | 1 => by
    simp
  | n + 2 => by
    rw [geom_sum_succ']
    simp [← zero_geom_sum]

theorem one_geom_sum (n : ℕ) : (∑ i in range n, (1 : α) ^ i) = n := by
  simp

@[simp]
theorem op_geom_sum (x : α) (n : ℕ) : op (∑ i in range n, x ^ i) = ∑ i in range n, op x ^ i := by
  simp

@[simp]
theorem op_geom_sum₂ (x y : α) (n : ℕ) :
    op (∑ i in range n, x ^ i * y ^ (n - 1 - i)) = ∑ i in range n, op y ^ i * op x ^ (n - 1 - i) := by
  simp only [← op_sum, ← op_mul, ← op_pow]
  rw [← sum_range_reflect]
  refine' sum_congr rfl fun j j_in => _
  rw [mem_range, Nat.lt_iff_add_one_le] at j_in
  congr
  apply tsub_tsub_cancel_of_le
  exact le_tsub_of_add_le_right j_in

theorem geom_sum₂_with_one (x : α) (n : ℕ) : (∑ i in range n, x ^ i * 1 ^ (n - 1 - i)) = ∑ i in range n, x ^ i :=
  sum_congr rfl fun i _ => by
    rw [one_pow, mul_oneₓ]

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
protected theorem Commute.geom_sum₂_mul_add {x y : α} (h : Commute x y) (n : ℕ) :
    (∑ i in range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n := by
  let f := fun m i : ℕ => (x + y) ^ i * y ^ (m - 1 - i)
  change (∑ i in range n, (f n) i) * x + y ^ n = (x + y) ^ n
  induction' n with n ih
  · rw [range_zero, sum_empty, zero_mul, zero_addₓ, pow_zeroₓ, pow_zeroₓ]
    
  · have f_last : f (n + 1) n = (x + y) ^ n := by
      dsimp' [← f]
      rw [← tsub_add_eq_tsub_tsub, Nat.add_comm, tsub_self, pow_zeroₓ, mul_oneₓ]
    have f_succ : ∀ i, i ∈ range n → f (n + 1) i = y * f n i := fun i hi => by
      dsimp' [← f]
      have : Commute y ((x + y) ^ i) := (h.symm.add_right (Commute.refl y)).pow_right i
      rw [← mul_assoc, this.eq, mul_assoc, ← pow_succₓ y (n - 1 - i)]
      congr 2
      rw [add_tsub_cancel_right, ← tsub_add_eq_tsub_tsub, add_commₓ 1 i]
      have : i + 1 + (n - (i + 1)) = n := add_tsub_cancel_of_le (mem_range.mp hi)
      rw [add_commₓ (i + 1)] at this
      rw [← this, add_tsub_cancel_right, add_commₓ i 1, ← add_assocₓ, add_tsub_cancel_right]
    rw [pow_succₓ (x + y), add_mulₓ, sum_range_succ_comm, add_mulₓ, f_last, add_assocₓ]
    rw [(((Commute.refl x).add_right h).pow_right n).Eq]
    congr 1
    rw [sum_congr rfl f_succ, ← mul_sum, pow_succₓ y, mul_assoc, ← mul_addₓ y, ih]
    

end Semiringₓ

@[simp]
theorem neg_one_geom_sum [Ringₓ α] {n : ℕ} : (∑ i in range n, (-1 : α) ^ i) = if Even n then 0 else 1 := by
  induction' n with k hk
  · simp
    
  · simp only [← geom_sum_succ', ← Nat.even_add_one, ← hk]
    split_ifs
    · rw [h.neg_one_pow, add_zeroₓ]
      
    · rw [(Nat.odd_iff_not_even.2 h).neg_one_pow, neg_add_selfₓ]
      
    

theorem geom_sum₂_self {α : Type _} [CommRingₓ α] (x : α) (n : ℕ) :
    (∑ i in range n, x ^ i * x ^ (n - 1 - i)) = n * x ^ (n - 1) :=
  calc
    (∑ i in Finset.range n, x ^ i * x ^ (n - 1 - i)) = ∑ i in Finset.range n, x ^ (i + (n - 1 - i)) := by
      simp_rw [← pow_addₓ]
    _ = ∑ i in Finset.range n, x ^ (n - 1) :=
      Finset.sum_congr rfl fun i hi =>
        congr_arg _ <| add_tsub_cancel_of_le <| Nat.le_pred_of_ltₓ <| Finset.mem_range.1 hi
    _ = (Finset.range n).card • x ^ (n - 1) := Finset.sum_const _
    _ = n * x ^ (n - 1) := by
      rw [Finset.card_range, nsmul_eq_mul]
    

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
theorem geom_sum₂_mul_add [CommSemiringₓ α] (x y : α) (n : ℕ) :
    (∑ i in range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n :=
  (Commute.all x y).geom_sum₂_mul_add n

theorem geom_sum_mul_add [Semiringₓ α] (x : α) (n : ℕ) : (∑ i in range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n := by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this

protected theorem Commute.geom_sum₂_mul [Ringₓ α] {x y : α} (h : Commute x y) (n : ℕ) :
    (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  rw [sub_add_cancel] at this
  rw [← this, add_sub_cancel]

theorem Commute.mul_neg_geom_sum₂ [Ringₓ α] {x y : α} (h : Commute x y) (n : ℕ) :
    ((y - x) * ∑ i in range n, x ^ i * y ^ (n - 1 - i)) = y ^ n - x ^ n := by
  apply op_injective
  simp only [← op_mul, ← op_sub, ← op_geom_sum₂, ← op_pow]
  exact (Commute.op h.symm).geom_sum₂_mul n

theorem Commute.mul_geom_sum₂ [Ringₓ α] {x y : α} (h : Commute x y) (n : ℕ) :
    ((x - y) * ∑ i in range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n := by
  rw [← neg_sub (y ^ n), ← h.mul_neg_geom_sum₂, ← neg_mul, neg_sub]

theorem geom_sum₂_mul [CommRingₓ α] (x y : α) (n : ℕ) :
    (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n :=
  (Commute.all x y).geom_sum₂_mul n

theorem geom_sum_mul [Ringₓ α] (x : α) (n : ℕ) : (∑ i in range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  have := (Commute.one_right x).geom_sum₂_mul n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this

theorem mul_geom_sum [Ringₓ α] (x : α) (n : ℕ) : ((x - 1) * ∑ i in range n, x ^ i) = x ^ n - 1 :=
  op_injective <| by
    simpa using geom_sum_mul (op x) n

theorem geom_sum_mul_neg [Ringₓ α] (x : α) (n : ℕ) : (∑ i in range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  have := congr_arg Neg.neg (geom_sum_mul x n)
  rw [neg_sub, ← mul_neg, neg_sub] at this
  exact this

theorem mul_neg_geom_sum [Ringₓ α] (x : α) (n : ℕ) : ((1 - x) * ∑ i in range n, x ^ i) = 1 - x ^ n :=
  op_injective <| by
    simpa using geom_sum_mul_neg (op x) n

protected theorem Commute.geom_sum₂ [DivisionRing α] {x y : α} (h' : Commute x y) (h : x ≠ y) (n : ℕ) :
    (∑ i in range n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ n) / (x - y) := by
  have : x - y ≠ 0 := by
    simp_all [-sub_eq_add_neg, ← sub_eq_iff_eq_add]
  rw [← h'.geom_sum₂_mul, mul_div_cancel _ this]

theorem geom₂_sum [Field α] {x y : α} (h : x ≠ y) (n : ℕ) :
    (∑ i in range n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ n) / (x - y) :=
  (Commute.all x y).geom_sum₂ h n

theorem geom_sum_eq [DivisionRing α] {x : α} (h : x ≠ 1) (n : ℕ) : (∑ i in range n, x ^ i) = (x ^ n - 1) / (x - 1) := by
  have : x - 1 ≠ 0 := by
    simp_all [-sub_eq_add_neg, ← sub_eq_iff_eq_add]
  rw [← geom_sum_mul, mul_div_cancel _ this]

protected theorem Commute.mul_geom_sum₂_Ico [Ringₓ α] {x y : α} (h : Commute x y) {m n : ℕ} (hmn : m ≤ n) :
    ((x - y) * ∑ i in Finset.ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) := by
  rw [sum_Ico_eq_sub _ hmn]
  have : (∑ k in range m, x ^ k * y ^ (n - 1 - k)) = ∑ k in range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)) := by
    refine' sum_congr rfl fun j j_in => _
    rw [← pow_addₓ]
    congr
    rw [mem_range, Nat.lt_iff_add_one_le, add_commₓ] at j_in
    have h' : n - m + (m - (1 + j)) = n - (1 + j) := tsub_add_tsub_cancel hmn j_in
    rw [← tsub_add_eq_tsub_tsub m, h', ← tsub_add_eq_tsub_tsub]
  rw [this]
  simp_rw [pow_mul_commₓ y (n - m) _]
  simp_rw [← mul_assoc]
  rw [← sum_mul, mul_sub, h.mul_geom_sum₂, ← mul_assoc, h.mul_geom_sum₂, sub_mul, ← pow_addₓ, add_tsub_cancel_of_le hmn,
    sub_sub_sub_cancel_right (x ^ n) (x ^ m * y ^ (n - m)) (y ^ n)]

protected theorem Commute.geom_sum₂_succ_eq {α : Type u} [Ringₓ α] {x y : α} (h : Commute x y) {n : ℕ} :
    (∑ i in range (n + 1), x ^ i * y ^ (n - i)) = x ^ n + y * ∑ i in range n, x ^ i * y ^ (n - 1 - i) := by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zeroₓ, mul_oneₓ, add_right_injₓ, ← mul_assoc,
    (h.symm.pow_right _).Eq, mul_assoc, ← pow_succₓ]
  refine' sum_congr rfl fun i hi => _
  suffices n - 1 - i + 1 = n - i by
    rw [this]
  cases n
  · exact absurd (list.mem_range.mp hi) i.not_lt_zero
    
  · rw [tsub_add_eq_add_tsub (Nat.le_pred_of_ltₓ (list.mem_range.mp hi)),
      tsub_add_cancel_of_le (nat.succ_le_iff.mpr n.succ_pos)]
    

theorem geom_sum₂_succ_eq {α : Type u} [CommRingₓ α] (x y : α) {n : ℕ} :
    (∑ i in range (n + 1), x ^ i * y ^ (n - i)) = x ^ n + y * ∑ i in range n, x ^ i * y ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_succ_eq

theorem mul_geom_sum₂_Ico [CommRingₓ α] (x y : α) {m n : ℕ} (hmn : m ≤ n) :
    ((x - y) * ∑ i in Finset.ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
  (Commute.all x y).mul_geom_sum₂_Ico hmn

protected theorem Commute.geom_sum₂_Ico_mul [Ringₓ α] {x y : α} (h : Commute x y) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.ico m n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ (n - m) * x ^ m := by
  apply op_injective
  simp only [← op_sub, ← op_mul, ← op_pow, ← op_sum]
  have : (∑ k in Ico m n, op y ^ (n - 1 - k) * op x ^ k) = ∑ k in Ico m n, op x ^ k * op y ^ (n - 1 - k) := by
    refine' sum_congr rfl fun k k_in => _
    apply Commute.pow_pow (Commute.op h.symm)
  rw [this]
  exact (Commute.op h).mul_geom_sum₂_Ico hmn

theorem geom_sum_Ico_mul [Ringₓ α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.ico m n, x ^ i) * (x - 1) = x ^ n - x ^ m := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul, geom_sum_mul, sub_sub_sub_cancel_right]

theorem geom_sum_Ico_mul_neg [Ringₓ α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.ico m n, x ^ i) * (1 - x) = x ^ m - x ^ n := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul_neg, geom_sum_mul_neg, sub_sub_sub_cancel_left]

protected theorem Commute.geom_sum₂_Ico [DivisionRing α] {x y : α} (h : Commute x y) (hxy : x ≠ y) {m n : ℕ}
    (hmn : m ≤ n) : (∑ i in Finset.ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) := by
  have : x - y ≠ 0 := by
    simp_all [-sub_eq_add_neg, ← sub_eq_iff_eq_add]
  rw [← h.geom_sum₂_Ico_mul hmn, mul_div_cancel _ this]

theorem geom_sum₂_Ico [Field α] {x y : α} (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) :=
  (Commute.all x y).geom_sum₂_Ico hxy hmn

theorem geom_sum_Ico [DivisionRing α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.ico m n, x ^ i) = (x ^ n - x ^ m) / (x - 1) := by
  simp only [← sum_Ico_eq_sub _ hmn, ← geom_sum_eq hx, ← div_sub_div_same, ← sub_sub_sub_cancel_right]

theorem geom_sum_Ico' [DivisionRing α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.ico m n, x ^ i) = (x ^ m - x ^ n) / (1 - x) := by
  simp only [← geom_sum_Ico hx hmn]
  convert neg_div_neg_eq (x ^ m - x ^ n) (1 - x) <;> abel

theorem geom_sum_Ico_le_of_lt_one [LinearOrderedField α] {x : α} (hx : 0 ≤ x) (h'x : x < 1) {m n : ℕ} :
    (∑ i in ico m n, x ^ i) ≤ x ^ m / (1 - x) := by
  rcases le_or_ltₓ m n with (hmn | hmn)
  · rw [geom_sum_Ico' h'x.ne hmn]
    apply div_le_div (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    simpa using pow_nonneg hx _
    
  · rw [Ico_eq_empty, sum_empty]
    · apply div_nonneg (pow_nonneg hx _)
      simpa using h'x.le
      
    · simpa using hmn.le
      
    

theorem geom_sum_inv [DivisionRing α] {x : α} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
    (∑ i in range n, x⁻¹ ^ i) = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) := by
  have h₁ : x⁻¹ ≠ 1 := by
    rwa [inv_eq_one_div, Ne.def, div_eq_iff_mul_eq hx0, one_mulₓ]
  have h₂ : x⁻¹ - 1 ≠ 0 := mt sub_eq_zero.1 h₁
  have h₃ : x - 1 ≠ 0 := mt sub_eq_zero.1 hx1
  have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
    Nat.recOn n
      (by
        simp )
      fun n h => by
      rw [pow_succₓ, mul_inv_rev, ← mul_assoc, h, mul_assoc, mul_inv_cancel hx0, mul_assoc, inv_mul_cancel hx0]
  rw [geom_sum_eq h₁, div_eq_iff_mul_eq h₂, ← mul_right_inj' h₃, ← mul_assoc, ← mul_assoc, mul_inv_cancel h₃]
  simp [← mul_addₓ, ← add_mulₓ, ← mul_inv_cancel hx0, ← mul_assoc, ← h₄, ← sub_eq_add_neg, ← add_commₓ, ←
    add_left_commₓ]

variable {β : Type _}

theorem RingHom.map_geom_sum [Semiringₓ α] [Semiringₓ β] (x : α) (n : ℕ) (f : α →+* β) :
    f (∑ i in range n, x ^ i) = ∑ i in range n, f x ^ i := by
  simp [← f.map_sum]

theorem RingHom.map_geom_sum₂ [Semiringₓ α] [Semiringₓ β] (x y : α) (n : ℕ) (f : α →+* β) :
    f (∑ i in range n, x ^ i * y ^ (n - 1 - i)) = ∑ i in range n, f x ^ i * f y ^ (n - 1 - i) := by
  simp [← f.map_sum]

/-! ### Geometric sum with `ℕ`-division -/


theorem Nat.pred_mul_geom_sum_le (a b n : ℕ) : ((b - 1) * ∑ i in range n.succ, a / b ^ i) ≤ a * b - a / b ^ n :=
  calc
    ((b - 1) * ∑ i in range n.succ, a / b ^ i) =
        (∑ i in range n, a / b ^ (i + 1) * b) + a * b - ((∑ i in range n, a / b ^ i) + a / b ^ n) :=
      by
      rw [tsub_mul, mul_comm, sum_mul, one_mulₓ, sum_range_succ', sum_range_succ, pow_zeroₓ, Nat.div_oneₓ]
    _ ≤ (∑ i in range n, a / b ^ i) + a * b - ((∑ i in range n, a / b ^ i) + a / b ^ n) := by
      refine' tsub_le_tsub_right (add_le_add_right (sum_le_sum fun i _ => _) _) _
      rw [pow_succ'ₓ, ← Nat.div_div_eq_div_mulₓ]
      exact Nat.div_mul_le_selfₓ _ _
    _ = a * b - a / b ^ n := add_tsub_add_eq_tsub_left _ _ _
    

theorem Nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) : (∑ i in range n, a / b ^ i) ≤ a * b / (b - 1) := by
  refine' (Nat.le_div_iff_mul_leₓ <| tsub_pos_of_lt hb).2 _
  cases n
  · rw [sum_range_zero, zero_mul]
    exact Nat.zero_leₓ _
    
  rw [mul_comm]
  exact (Nat.pred_mul_geom_sum_le a b n).trans tsub_le_self

theorem Nat.geom_sum_Ico_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) : (∑ i in ico 1 n, a / b ^ i) ≤ a / (b - 1) := by
  cases n
  · rw [Ico_eq_empty_of_le (zero_le_one' ℕ), sum_empty]
    exact Nat.zero_leₓ _
    
  rw [← add_le_add_iff_left a]
  calc (a + ∑ i : ℕ in Ico 1 n.succ, a / b ^ i) = a / b ^ 0 + ∑ i : ℕ in Ico 1 n.succ, a / b ^ i := by
      rw [pow_zeroₓ, Nat.div_oneₓ]_ = ∑ i in range n.succ, a / b ^ i := by
      rw [range_eq_Ico, ← Nat.Ico_insert_succ_left (Nat.succ_posₓ _), sum_insert]
      exact fun h => zero_lt_one.not_le (mem_Ico.1 h).1_ ≤ a * b / (b - 1) :=
      Nat.geom_sum_le hb a _ _ = (a * 1 + a * (b - 1)) / (b - 1) := by
      rw [← mul_addₓ, add_tsub_cancel_of_le (one_le_two.trans hb)]_ = a + a / (b - 1) := by
      rw [mul_oneₓ, Nat.add_mul_div_rightₓ _ _ (tsub_pos_of_lt hb), add_commₓ]

section Order

variable {n : ℕ} {x : α}

theorem geom_sum_pos [OrderedSemiring α] (hx : 0 < x) (hn : n ≠ 0) : 0 < ∑ i in range n, x ^ i :=
  (sum_pos fun k hk => pow_pos hx _) <| nonempty_range_iff.2 hn

theorem geom_sum_pos_and_lt_one [OrderedRing α] (hx : x < 0) (hx' : 0 < x + 1) (hn : 1 < n) :
    (0 < ∑ i in range n, x ^ i) ∧ (∑ i in range n, x ^ i) < 1 := by
  refine' Nat.le_induction _ _ n (show 2 ≤ n from hn)
  · rw [geom_sum_two]
    exact ⟨hx', (add_lt_iff_neg_right _).2 hx⟩
    
  clear hn n
  intro n hn ihn
  rw [geom_sum_succ, add_lt_iff_neg_right, ← neg_lt_iff_pos_add', neg_mul_eq_neg_mulₓ]
  exact
    ⟨mul_lt_one_of_nonneg_of_lt_one_left (neg_nonneg.2 hx.le) (neg_lt_iff_pos_add'.2 hx') ihn.2.le,
      mul_neg_of_neg_of_pos hx ihn.1⟩

theorem geom_sum_alternating_of_lt_neg_one [OrderedRing α] (hx : x + 1 < 0) (hn : 1 < n) :
    if Even n then (∑ i in range n, x ^ i) < 0 else 1 < ∑ i in range n, x ^ i := by
  have hx0 : x < 0 := ((le_add_iff_nonneg_right _).2 zero_le_one).trans_lt hx
  refine' Nat.le_induction _ _ n (show 2 ≤ n from hn)
  · simp only [← geom_sum_two, ← hx, ← true_orₓ, ← even_bit0, ← if_true_left_eq_or]
    
  clear hn n
  intro n hn ihn
  simp only [← Nat.even_add_one, ← geom_sum_succ]
  by_cases' hn' : Even n
  · rw [if_pos hn'] at ihn
    rw [if_neg, lt_add_iff_pos_left]
    exact mul_pos_of_neg_of_neg hx0 ihn
    exact not_not_intro hn'
    
  · rw [if_neg hn'] at ihn
    rw [if_pos]
    swap
    · exact hn'
      
    have := add_lt_add_right (mul_lt_mul_of_neg_left ihn hx0) 1
    rw [mul_oneₓ] at this
    exact this.trans hx
    

theorem Odd.geom_sum_pos [LinearOrderedRing α] (h : Odd n) : 0 < ∑ i in range n, x ^ i := by
  rcases n with (_ | _ | k)
  · exact
      ((show ¬Odd 0 by
            decide)
          h).elim
    
  · simp only [← geom_sum_one, ← zero_lt_one]
    
  rw [Nat.odd_iff_not_even] at h
  rcases lt_trichotomyₓ (x + 1) 0 with (hx | hx | hx)
  · have := geom_sum_alternating_of_lt_neg_one hx k.one_lt_succ_succ
    simp only [← h, ← if_false] at this
    exact zero_lt_one.trans this
    
  · simp only [← eq_neg_of_add_eq_zero_left hx, ← h, ← neg_one_geom_sum, ← if_false, ← zero_lt_one]
    
  rcases lt_trichotomyₓ x 0 with (hx' | rfl | hx')
  · exact (geom_sum_pos_and_lt_one hx' hx k.one_lt_succ_succ).1
    
  · simp only [← zero_geom_sum, ← Nat.succ_ne_zero, ← if_false, ← zero_lt_one]
    
  · exact
      geom_sum_pos hx'
        (by
          simp only [← Nat.succ_ne_zero, ← Ne.def, ← not_false_iff])
    

theorem geom_sum_pos_iff [LinearOrderedRing α] (hn : 1 < n) : (0 < ∑ i in range n, x ^ i) ↔ Odd n ∨ 0 < x + 1 := by
  refine' ⟨fun h => _, _⟩
  · suffices ¬0 < x + 1 → Odd n by
      tauto
    intro hx
    rw [not_ltₓ] at hx
    contrapose! h
    rw [← Nat.even_iff_not_odd] at h
    rcases hx.eq_or_lt with (hx | hx)
    · rw [← neg_negₓ (1 : α), add_neg_eq_iff_eq_add, zero_addₓ] at hx
      simp only [← hx, ← neg_one_geom_sum, ← h, ← if_true]
      
    apply le_of_ltₓ
    simpa [← h] using geom_sum_alternating_of_lt_neg_one hx hn
    
  · rintro (hn | hx')
    · exact hn.geom_sum_pos
      
    rcases lt_trichotomyₓ x 0 with (hx | rfl | hx)
    · exact (geom_sum_pos_and_lt_one hx hx' hn).1
      
    · simp only [← (zero_lt_one.trans hn).ne', ← zero_geom_sum, ← if_false, ← zero_lt_one]
      
    · exact geom_sum_pos hx (zero_lt_one.trans hn).ne'
      
    

theorem geom_sum_eq_zero_iff_neg_one [LinearOrderedRing α] (hn : 1 < n) :
    (∑ i in range n, x ^ i) = 0 ↔ x = -1 ∧ Even n := by
  refine'
    ⟨fun h => _, fun ⟨h, hn⟩ => by
      simp only [← h, ← hn, ← neg_one_geom_sum, ← if_true]⟩
  contrapose! h
  rcases eq_or_ne x (-1) with (rfl | h)
  · simp only [← h rfl, ← neg_one_geom_sum, ← if_false, ← Ne.def, ← not_false_iff, ← one_ne_zero]
    
  rw [Ne.def, eq_neg_iff_add_eq_zero, ← Ne.def] at h
  rcases h.lt_or_lt with (h | h)
  · have := geom_sum_alternating_of_lt_neg_one h hn
    split_ifs  at this
    · exact this.ne
      
    · exact (zero_lt_one.trans this).ne'
      
    
  apply ne_of_gtₓ
  rcases lt_trichotomyₓ x 0 with (h' | rfl | h')
  · exact (geom_sum_pos_and_lt_one h' h hn).1
    
  · simp only [← (pos_of_gt hn).ne', ← zero_geom_sum, ← if_false, ← zero_lt_one]
    
  · exact geom_sum_pos h' (pos_of_gt hn).ne'
    

theorem geom_sum_neg_iff [LinearOrderedRing α] (hn : 1 < n) : (∑ i in range n, x ^ i) < 0 ↔ Even n ∧ x + 1 < 0 := by
  rw [← not_iff_not, not_ltₓ, le_iff_lt_or_eqₓ, eq_comm,
    or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn), Nat.odd_iff_not_even, ← add_eq_zero_iff_eq_neg,
    not_and, not_ltₓ, le_iff_lt_or_eqₓ, eq_comm, ← imp_iff_not_or, or_comm, and_comm, Decidable.and_or_imp, or_comm]

end Order

