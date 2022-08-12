/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathbin.Data.Nat.Cast.Defs

/-!
# Cast of integers

This file defines the *canonical* homomorphism from the integers into an
additive group with a one (typically a `ring`).  In additive groups with a one
element, there exists a unique such homomorphism and we store it in the
`int_cast : ℤ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `int.cast`: Canonical homomorphism `ℤ → R`.
* `add_group_with_one`: Type class for `int.cast`.
-/


universe u

attribute [simp] Int.of_nat_eq_coe

/-- Default value for `add_group_with_one.int_cast`. -/
protected def Int.castDef {R : Type u} [HasNatCast R] [Neg R] : ℤ → R
  | (n : ℕ) => n
  | -[1+ n] => -(n + 1 : ℕ)

/-- Type class for the canonical homomorphism `ℤ → R`.
-/
class HasIntCast (R : Type u) where
  intCast : ℤ → R

/-- An `add_group_with_one` is an `add_group` with a `1`.
It also contains data for the unique homomorphisms `ℕ → R` and `ℤ → R`.
-/
@[protect_proj]
class AddGroupWithOneₓ (R : Type u) extends HasIntCast R, AddGroupₓ R, AddMonoidWithOneₓ R where
  intCast := Int.castDef
  int_cast_of_nat : ∀ n : ℕ, int_cast n = (n : R) := by
    run_tac
      control_laws_tac
  int_cast_neg_succ_of_nat : ∀ n : ℕ, int_cast (-(n + 1 : ℕ)) = -((n + 1 : ℕ) : R) := by
    run_tac
      control_laws_tac

/-- An `add_comm_group_with_one` is an `add_group_with_one` satisfying `a + b = b + a`. -/
@[protect_proj]
class AddCommGroupWithOne (R : Type u) extends AddCommGroupₓ R, AddGroupWithOneₓ R

/-- Canonical homomorphism from the integers to any ring(-like) structure `R` -/
protected def Int.castₓ {R : Type u} [HasIntCast R] (i : ℤ) : R :=
  HasIntCast.intCast i

namespace Nat

variable {R : Type u} [AddGroupWithOneₓ R]

@[simp, norm_cast]
theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
  eq_sub_of_add_eq <| by
    rw [← cast_add, Nat.sub_add_cancelₓ h]

@[simp, norm_cast]
theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1
  | 0, h => by
    cases h
  | n + 1, h => by
    rw [cast_succ, add_sub_cancel] <;> rfl

end Nat

open Nat

namespace Int

variable {R : Type u} [AddGroupWithOneₓ R]

-- see Note [coercion into rings]
instance (priority := 900) castCoe {R} [HasIntCast R] : CoeTₓ ℤ R :=
  ⟨Int.castₓ⟩

theorem cast_of_nat (n : ℕ) : (ofNat n : R) = n :=
  AddGroupWithOneₓ.int_cast_of_nat n

@[simp]
theorem cast_neg_succ_of_nat (n : ℕ) : (-[1+ n] : R) = -(n + 1 : ℕ) :=
  AddGroupWithOneₓ.int_cast_neg_succ_of_nat n

@[simp, norm_cast]
theorem cast_zeroₓ : ((0 : ℤ) : R) = 0 :=
  (cast_of_nat 0).trans Nat.cast_zeroₓ

@[simp, norm_cast]
theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : R) = n :=
  cast_of_nat _

@[simp, norm_cast]
theorem cast_oneₓ : ((1 : ℤ) : R) = 1 :=
  show (((1 : ℕ) : ℤ) : R) = 1 by
    simp

@[simp, norm_cast]
theorem cast_neg : ∀ n, ((-n : ℤ) : R) = -n
  | (0 : ℕ) => by
    erw [cast_zero, neg_zero]
  | (n + 1 : ℕ) => by
    erw [cast_of_nat, cast_neg_succ_of_nat] <;> rfl
  | -[1+ n] => by
    erw [cast_of_nat, cast_neg_succ_of_nat, neg_negₓ]

@[simp]
theorem cast_sub_nat_nat (m n) : ((Int.subNatNat m n : ℤ) : R) = m - n := by
  unfold sub_nat_nat
  cases e : n - m
  · simp only [← sub_nat_nat, ← cast_of_nat]
    simp [← e, ← Nat.le_of_sub_eq_zeroₓ e]
    
  · rw [sub_nat_nat, cast_neg_succ_of_nat, Nat.add_one, ← e,
      Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succₓ e, neg_sub]
    

theorem neg_of_nat_eq (n : ℕ) : negOfNat n = -(n : ℤ) := by
  cases n <;> rfl

@[simp]
theorem cast_neg_of_nat (n : ℕ) : ((negOfNat n : ℤ) : R) = -n := by
  simp [← neg_of_nat_eq]

@[simp, norm_cast]
theorem cast_add : ∀ m n, ((m + n : ℤ) : R) = m + n
  | (m : ℕ), (n : ℕ) => by
    simp [Int.coe_nat_add]
  | (m : ℕ), -[1+ n] => by
    erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_add_neg]
  | -[1+ m], (n : ℕ) => by
    erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_iff_eq_add, add_assocₓ, eq_neg_add_iff_add_eq, ←
      Nat.cast_addₓ, ← Nat.cast_addₓ, Nat.add_comm]
  | -[1+ m], -[1+ n] =>
    show (-[1+ m + n + 1] : R) = _ by
      rw [cast_neg_succ_of_nat, cast_neg_succ_of_nat, cast_neg_succ_of_nat, ← neg_add_rev, ← Nat.cast_addₓ,
        Nat.add_right_comm m n 1, Nat.add_assoc, Nat.add_comm]

@[simp, norm_cast]
theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n := by
  simp [← Int.sub_eq_add_neg, ← sub_eq_add_neg]

@[simp, norm_cast]
theorem coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n :=
  rfl

@[simp, norm_cast]
theorem coe_nat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n :=
  rfl

@[simp, norm_cast]
theorem cast_bit0 (n : ℤ) : ((bit0 n : ℤ) : R) = bit0 n :=
  cast_add _ _

@[simp, norm_cast]
theorem cast_bit1 (n : ℤ) : ((bit1 n : ℤ) : R) = bit1 n := by
  rw [bit1, cast_add, cast_one, cast_bit0] <;> rfl

theorem cast_two : ((2 : ℤ) : R) = 2 := by
  simp

theorem cast_three : ((3 : ℤ) : R) = 3 := by
  simp

theorem cast_four : ((4 : ℤ) : R) = 4 := by
  simp

end Int

