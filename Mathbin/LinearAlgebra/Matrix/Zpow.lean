/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Integer powers of square matrices

In this file, we define integer power of matrices, relying on
the nonsingular inverse definition for negative powers.

## Implementation details

The main definition is a direct recursive call on the integer inductive type,
as provided by the `div_inv_monoid.zpow` default implementation.
The lemma names are taken from `algebra.group_with_zero.power`.

## Tags

matrix inverse, matrix powers
-/


open Matrix

namespace Matrix

variable {n' : Type _} [DecidableEq n'] [Fintype n'] {R : Type _} [CommRingₓ R]

-- mathport name: «exprM»
local notation "M" => Matrix n' n' R

noncomputable instance : DivInvMonoidₓ M :=
  { show Monoidₓ M by
      infer_instance,
    show Inv M by
      infer_instance with }

section NatPow

@[simp]
theorem inv_pow' (A : M) (n : ℕ) : A⁻¹ ^ n = (A ^ n)⁻¹ := by
  induction' n with n ih
  · simp
    
  · rw [pow_succₓ A, mul_eq_mul, mul_inv_rev, ← ih, ← mul_eq_mul, ← pow_succ'ₓ]
    

theorem pow_sub' (A : M) {m n : ℕ} (ha : IsUnit A.det) (h : n ≤ m) : A ^ (m - n) = A ^ m ⬝ (A ^ n)⁻¹ := by
  rw [← tsub_add_cancel_of_le h, pow_addₓ, mul_eq_mul, Matrix.mul_assoc, mul_nonsing_inv, tsub_add_cancel_of_le h,
    Matrix.mul_one]
  simpa using ha.pow n

theorem pow_inv_comm' (A : M) (m n : ℕ) : A⁻¹ ^ m ⬝ A ^ n = A ^ n ⬝ A⁻¹ ^ m := by
  induction' n with n IH generalizing m
  · simp
    
  cases m
  · simp
    
  rcases nonsing_inv_cancel_or_zero A with (⟨h, h'⟩ | h)
  · calc A⁻¹ ^ (m + 1) ⬝ A ^ (n + 1) = A⁻¹ ^ m ⬝ (A⁻¹ ⬝ A) ⬝ A ^ n := by
        simp only [← pow_succ'ₓ A⁻¹, ← pow_succₓ A, ← mul_eq_mul, ← Matrix.mul_assoc]_ = A ^ n ⬝ A⁻¹ ^ m := by
        simp only [← h, ← Matrix.mul_one, ← Matrix.one_mul, ← IH m]_ = A ^ n ⬝ (A ⬝ A⁻¹) ⬝ A⁻¹ ^ m := by
        simp only [← h', ← Matrix.mul_one, ← Matrix.one_mul]_ = A ^ (n + 1) ⬝ A⁻¹ ^ (m + 1) := by
        simp only [← pow_succ'ₓ A, ← pow_succₓ A⁻¹, ← mul_eq_mul, ← Matrix.mul_assoc]
    
  · simp [← h]
    

end NatPow

section Zpow

open Int

@[simp]
theorem one_zpow : ∀ n : ℤ, (1 : M) ^ n = 1
  | (n : ℕ) => by
    rw [zpow_coe_nat, one_pow]
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, one_pow, inv_one]

theorem zero_zpow : ∀ z : ℤ, z ≠ 0 → (0 : M) ^ z = 0
  | (n : ℕ), h => by
    rw [zpow_coe_nat, zero_pow]
    refine' lt_of_le_of_neₓ n.zero_le (Ne.symm _)
    simpa using h
  | -[1+ n], h => by
    simp [← zero_pow n.zero_lt_succ]

theorem zero_zpow_eq (n : ℤ) : (0 : M) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, zpow_zero]
    
  · rw [zero_zpow _ h]
    

theorem inv_zpow (A : M) : ∀ n : ℤ, A⁻¹ ^ n = (A ^ n)⁻¹
  | (n : ℕ) => by
    rw [zpow_coe_nat, zpow_coe_nat, inv_pow']
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, inv_pow']

@[simp]
theorem zpow_neg_one (A : M) : A ^ (-1 : ℤ) = A⁻¹ := by
  convert DivInvMonoidₓ.zpow_neg' 0 A
  simp only [← zpow_one, ← Int.coe_nat_zero, ← Int.coe_nat_succ, ← zpow_eq_pow, ← zero_addₓ]

theorem zpow_coe_nat (A : M) (n : ℕ) : A ^ (n : ℤ) = A ^ n :=
  zpow_coe_nat _ _

@[simp]
theorem zpow_neg_coe_nat (A : M) (n : ℕ) : A ^ (-n : ℤ) = (A ^ n)⁻¹ := by
  cases n
  · simp
    
  · exact DivInvMonoidₓ.zpow_neg' _ _
    

theorem _root_.is_unit.det_zpow {A : M} (h : IsUnit A.det) (n : ℤ) : IsUnit (A ^ n).det := by
  cases n
  · simpa using h.pow n
    
  · simpa using h.pow n.succ
    

theorem is_unit_det_zpow_iff {A : M} {z : ℤ} : IsUnit (A ^ z).det ↔ IsUnit A.det ∨ z = 0 := by
  induction' z using Int.induction_on with z IH z IH
  · simp
    
  · rw [← Int.coe_nat_succ, zpow_coe_nat, det_pow, is_unit_pos_pow_iff z.zero_lt_succ, ← Int.coe_nat_zero,
      Int.coe_nat_eq_coe_nat_iff]
    simp
    
  · rw [← neg_add', ← Int.coe_nat_succ, zpow_neg_coe_nat, is_unit_nonsing_inv_det_iff, det_pow,
      is_unit_pos_pow_iff z.zero_lt_succ, neg_eq_zero, ← Int.coe_nat_zero, Int.coe_nat_eq_coe_nat_iff]
    simp
    

theorem zpow_neg {A : M} (h : IsUnit A.det) : ∀ n : ℤ, A ^ -n = (A ^ n)⁻¹
  | (n : ℕ) => zpow_neg_coe_nat _ _
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, neg_neg_of_nat_succ, of_nat_eq_coe, zpow_coe_nat, nonsing_inv_nonsing_inv]
    rw [det_pow]
    exact h.pow _

theorem inv_zpow' {A : M} (h : IsUnit A.det) (n : ℤ) : A⁻¹ ^ n = A ^ -n := by
  rw [zpow_neg h, inv_zpow]

theorem zpow_add_one {A : M} (h : IsUnit A.det) : ∀ n : ℤ, A ^ (n + 1) = A ^ n * A
  | (n : ℕ) => by
    simp only [Nat.cast_succₓ, ← pow_succ'ₓ, ← zpow_coe_nat]
  | -((n : ℕ) + 1) =>
    calc
      A ^ (-(n + 1) + 1 : ℤ) = (A ^ n)⁻¹ := by
        rw [neg_add, neg_add_cancel_right, zpow_neg h, zpow_coe_nat]
      _ = (A ⬝ A ^ n)⁻¹ ⬝ A := by
        rw [mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.mul_one]
      _ = A ^ -(n + 1 : ℤ) * A := by
        rw [zpow_neg h, ← Int.coe_nat_succ, zpow_coe_nat, pow_succₓ, mul_eq_mul, mul_eq_mul]
      

theorem zpow_sub_one {A : M} (h : IsUnit A.det) (n : ℤ) : A ^ (n - 1) = A ^ n * A⁻¹ :=
  calc
    A ^ (n - 1) = A ^ (n - 1) * A * A⁻¹ := by
      rw [mul_assoc, mul_eq_mul A, mul_nonsing_inv _ h, mul_oneₓ]
    _ = A ^ n * A⁻¹ := by
      rw [← zpow_add_one h, sub_add_cancel]
    

theorem zpow_add {A : M} (ha : IsUnit A.det) (m n : ℤ) : A ^ (m + n) = A ^ m * A ^ n := by
  induction' n using Int.induction_on with n ihn n ihn
  case hz =>
    simp
  · simp only [add_assocₓ, ← zpow_add_one ha, ← ihn, ← mul_assoc]
    
  · rw [zpow_sub_one ha, ← mul_assoc, ← ihn, ← zpow_sub_one ha, add_sub_assoc]
    

theorem zpow_add_of_nonpos {A : M} {m n : ℤ} (hm : m ≤ 0) (hn : n ≤ 0) : A ^ (m + n) = A ^ m * A ^ n := by
  rcases nonsing_inv_cancel_or_zero A with (⟨h, h'⟩ | h)
  · exact zpow_add (is_unit_det_of_left_inverse h) m n
    
  · obtain ⟨k, rfl⟩ := exists_eq_neg_of_nat hm
    obtain ⟨l, rfl⟩ := exists_eq_neg_of_nat hn
    simp_rw [← neg_add, ← Int.coe_nat_add, zpow_neg_coe_nat, ← inv_pow', h, pow_addₓ]
    

theorem zpow_add_of_nonneg {A : M} {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) : A ^ (m + n) = A ^ m * A ^ n := by
  obtain ⟨k, rfl⟩ := eq_coe_of_zero_le hm
  obtain ⟨l, rfl⟩ := eq_coe_of_zero_le hn
  rw [← Int.coe_nat_add, zpow_coe_nat, zpow_coe_nat, zpow_coe_nat, pow_addₓ]

theorem zpow_one_add {A : M} (h : IsUnit A.det) (i : ℤ) : A ^ (1 + i) = A * A ^ i := by
  rw [zpow_add h, zpow_one]

theorem SemiconjBy.zpow_right {A X Y : M} (hx : IsUnit X.det) (hy : IsUnit Y.det) (h : SemiconjBy A X Y) :
    ∀ m : ℤ, SemiconjBy A (X ^ m) (Y ^ m)
  | (n : ℕ) => by
    simp [← h.pow_right n]
  | -[1+ n] => by
    have hx' : IsUnit (X ^ n.succ).det := by
      rw [det_pow]
      exact hx.pow n.succ
    have hy' : IsUnit (Y ^ n.succ).det := by
      rw [det_pow]
      exact hy.pow n.succ
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, nonsing_inv_apply _ hx', nonsing_inv_apply _ hy', SemiconjBy]
    refine' (is_regular_of_is_left_regular_det hy'.is_regular.left).left _
    rw [← mul_assoc, ← (h.pow_right n.succ).Eq, mul_assoc, mul_eq_mul (X ^ _), mul_smul, mul_adjugate, mul_eq_mul,
      mul_eq_mul, mul_eq_mul, ← Matrix.mul_assoc, mul_smul (Y ^ _) (↑hy'.unit⁻¹ : R), mul_adjugate, smul_smul,
      smul_smul, hx'.coe_inv_mul, hy'.coe_inv_mul, one_smul, Matrix.mul_one, Matrix.one_mul]

theorem Commute.zpow_right {A B : M} (h : Commute A B) (m : ℤ) : Commute A (B ^ m) := by
  rcases nonsing_inv_cancel_or_zero B with (⟨hB, hB'⟩ | hB)
  · refine' SemiconjBy.zpow_right _ _ h _ <;> exact is_unit_det_of_left_inverse hB
    
  · cases m
    · simpa using h.pow_right _
      
    · simp [inv_pow', ← hB]
      
    

theorem Commute.zpow_left {A B : M} (h : Commute A B) (m : ℤ) : Commute (A ^ m) B :=
  (Commute.zpow_right h.symm m).symm

theorem Commute.zpow_zpow {A B : M} (h : Commute A B) (m n : ℤ) : Commute (A ^ m) (B ^ n) :=
  Commute.zpow_right (Commute.zpow_left h _) _

theorem Commute.zpow_self (A : M) (n : ℤ) : Commute (A ^ n) A :=
  Commute.zpow_left (Commute.refl A) _

theorem Commute.self_zpow (A : M) (n : ℤ) : Commute A (A ^ n) :=
  Commute.zpow_right (Commute.refl A) _

theorem Commute.zpow_zpow_self (A : M) (m n : ℤ) : Commute (A ^ m) (A ^ n) :=
  Commute.zpow_zpow (Commute.refl A) _ _

theorem zpow_bit0 (A : M) (n : ℤ) : A ^ bit0 n = A ^ n * A ^ n := by
  cases' le_totalₓ 0 n with nonneg nonpos
  · exact zpow_add_of_nonneg nonneg nonneg
    
  · exact zpow_add_of_nonpos nonpos nonpos
    

theorem zpow_add_one_of_ne_neg_one {A : M} : ∀ n : ℤ, n ≠ -1 → A ^ (n + 1) = A ^ n * A
  | (n : ℕ), _ => by
    simp only [← pow_succ'ₓ, Nat.cast_succₓ, ← zpow_coe_nat]
  | -1, h => absurd rfl h
  | -((n : ℕ) + 2), _ => by
    rcases nonsing_inv_cancel_or_zero A with (⟨h, h'⟩ | h)
    · apply zpow_add_one (is_unit_det_of_left_inverse h)
      
    · show A ^ -((n + 1 : ℕ) : ℤ) = A ^ -((n + 2 : ℕ) : ℤ) * A
      simp_rw [zpow_neg_coe_nat, ← inv_pow', h, zero_pow Nat.succ_pos', zero_mul]
      

theorem zpow_bit1 (A : M) (n : ℤ) : A ^ bit1 n = A ^ n * A ^ n * A := by
  rw [bit1, zpow_add_one_of_ne_neg_one, zpow_bit0]
  intro h
  simpa using congr_arg bodd h

theorem zpow_mul (A : M) (h : IsUnit A.det) : ∀ m n : ℤ, A ^ (m * n) = (A ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by
    rw [zpow_coe_nat, zpow_coe_nat, ← pow_mulₓ, ← zpow_coe_nat, Int.coe_nat_mul]
  | (m : ℕ), -[1+ n] => by
    rw [zpow_coe_nat, zpow_neg_succ_of_nat, ← pow_mulₓ, coe_nat_mul_neg_succ, ← Int.coe_nat_mul, zpow_neg_coe_nat]
  | -[1+ m], (n : ℕ) => by
    rw [zpow_coe_nat, zpow_neg_succ_of_nat, ← inv_pow', ← pow_mulₓ, neg_succ_mul_coe_nat, ← Int.coe_nat_mul,
      zpow_neg_coe_nat, inv_pow']
  | -[1+ m], -[1+ n] => by
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, neg_succ_mul_neg_succ, ← Int.coe_nat_mul, zpow_coe_nat, inv_pow', ←
      pow_mulₓ, nonsing_inv_nonsing_inv]
    rw [det_pow]
    exact h.pow _

theorem zpow_mul' (A : M) (h : IsUnit A.det) (m n : ℤ) : A ^ (m * n) = (A ^ n) ^ m := by
  rw [mul_comm, zpow_mul _ h]

@[simp, norm_cast]
theorem coe_units_zpow (u : Mˣ) : ∀ n : ℤ, ((u ^ n : Mˣ) : M) = u ^ n
  | (n : ℕ) => by
    rw [_root_.zpow_coe_nat, zpow_coe_nat, Units.coe_pow]
  | -[1+ k] => by
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, ← inv_pow, u⁻¹.coe_pow, ← inv_pow', coe_units_inv]

theorem zpow_ne_zero_of_is_unit_det [Nonempty n'] [Nontrivial R] {A : M} (ha : IsUnit A.det) (z : ℤ) : A ^ z ≠ 0 := by
  have := ha.det_zpow z
  contrapose! this
  rw [this, det_zero ‹_›]
  exact not_is_unit_zero

theorem zpow_sub {A : M} (ha : IsUnit A.det) (z1 z2 : ℤ) : A ^ (z1 - z2) = A ^ z1 / A ^ z2 := by
  rw [sub_eq_add_neg, zpow_add ha, zpow_neg ha, div_eq_mul_inv]

theorem Commute.mul_zpow {A B : M} (h : Commute A B) : ∀ i : ℤ, (A * B) ^ i = A ^ i * B ^ i
  | (n : ℕ) => by
    simp [← h.mul_pow n, -mul_eq_mul]
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, mul_eq_mul _⁻¹, ← mul_inv_rev, ← mul_eq_mul,
      h.mul_pow n.succ, (h.pow_pow _ _).Eq]

theorem zpow_bit0' (A : M) (n : ℤ) : A ^ bit0 n = (A * A) ^ n :=
  (zpow_bit0 A n).trans (Commute.mul_zpow (Commute.refl A) n).symm

theorem zpow_bit1' (A : M) (n : ℤ) : A ^ bit1 n = (A * A) ^ n * A := by
  rw [zpow_bit1, Commute.mul_zpow (Commute.refl A)]

theorem zpow_neg_mul_zpow_self (n : ℤ) {A : M} (h : IsUnit A.det) : A ^ -n * A ^ n = 1 := by
  rw [zpow_neg h, mul_eq_mul, nonsing_inv_mul _ (h.det_zpow _)]

theorem one_div_pow {A : M} (n : ℕ) : (1 / A) ^ n = 1 / A ^ n := by
  simp only [← one_div, ← inv_pow']

theorem one_div_zpow {A : M} (n : ℤ) : (1 / A) ^ n = 1 / A ^ n := by
  simp only [← one_div, ← inv_zpow]

@[simp]
theorem transpose_zpow (A : M) : ∀ n : ℤ, (A ^ n)ᵀ = Aᵀ ^ n
  | (n : ℕ) => by
    rw [zpow_coe_nat, zpow_coe_nat, transpose_pow]
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, transpose_nonsing_inv, transpose_pow]

@[simp]
theorem conj_transpose_zpow [StarRing R] (A : M) : ∀ n : ℤ, (A ^ n)ᴴ = Aᴴ ^ n
  | (n : ℕ) => by
    rw [zpow_coe_nat, zpow_coe_nat, conj_transpose_pow]
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, conj_transpose_nonsing_inv, conj_transpose_pow]

end Zpow

end Matrix

