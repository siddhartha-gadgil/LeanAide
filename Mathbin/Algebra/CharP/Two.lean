/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.CharP.Basic

/-!
# Lemmas about rings of characteristic two

This file contains results about `char_p R 2`, in the `char_two` namespace.

The lemmas in this file with a `_sq` suffix are just special cases of the `_pow_char` lemmas
elsewhere, with a shorter name for ease of discovery, and no need for a `[fact (prime 2)]` argument.
-/


variable {R ι : Type _}

namespace CharTwo

section Semiringₓ

variable [Semiringₓ R] [CharP R 2]

theorem two_eq_zero : (2 : R) = 0 := by
  rw [← Nat.cast_two, CharP.cast_eq_zero]

@[simp]
theorem add_self_eq_zero (x : R) : x + x = 0 := by
  rw [← two_smul R x, two_eq_zero, zero_smul]

@[simp]
theorem bit0_eq_zero : (bit0 : R → R) = 0 := by
  funext
  exact add_self_eq_zero _

theorem bit0_apply_eq_zero (x : R) : (bit0 x : R) = 0 := by
  simp

@[simp]
theorem bit1_eq_one : (bit1 : R → R) = 1 := by
  funext
  simp [← bit1]

theorem bit1_apply_eq_one (x : R) : (bit1 x : R) = 1 := by
  simp

end Semiringₓ

section Ringₓ

variable [Ringₓ R] [CharP R 2]

@[simp]
theorem neg_eq (x : R) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul R x, two_eq_zero, zero_smul]

theorem neg_eq' : Neg.neg = (id : R → R) :=
  funext neg_eq

@[simp]
theorem sub_eq_add (x y : R) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq]

theorem sub_eq_add' : Sub.sub = ((· + ·) : R → R → R) :=
  funext fun x => funext fun y => sub_eq_add x y

end Ringₓ

section CommSemiringₓ

variable [CommSemiringₓ R] [CharP R 2]

theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  add_pow_char _ _ _

theorem add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y := by
  rw [← pow_two, ← pow_two, ← pow_two, add_sq]

open BigOperators

theorem list_sum_sq (l : List R) : l.Sum ^ 2 = (l.map (· ^ 2)).Sum :=
  list_sum_pow_char _ _

theorem list_sum_mul_self (l : List R) : l.Sum * l.Sum = (List.map (fun x => x * x) l).Sum := by
  simp_rw [← pow_two, list_sum_sq]

theorem multiset_sum_sq (l : Multiset R) : l.Sum ^ 2 = (l.map (· ^ 2)).Sum :=
  multiset_sum_pow_char _ _

theorem multiset_sum_mul_self (l : Multiset R) : l.Sum * l.Sum = (Multiset.map (fun x => x * x) l).Sum := by
  simp_rw [← pow_two, multiset_sum_sq]

theorem sum_sq (s : Finset ι) (f : ι → R) : (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^ 2 :=
  sum_pow_char _ _ _

theorem sum_mul_self (s : Finset ι) (f : ι → R) : ((∑ i in s, f i) * ∑ i in s, f i) = ∑ i in s, f i * f i := by
  simp_rw [← pow_two, sum_sq]

end CommSemiringₓ

end CharTwo

section ringChar

variable [Ringₓ R]

theorem neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ ringChar R = 2 := by
  refine' ⟨fun h => _, fun h => @CharTwo.neg_eq _ (ringChar.of_eq h) 1⟩
  rw [eq_comm, ← sub_eq_zero, sub_neg_eq_add, ← Nat.cast_oneₓ, ← Nat.cast_addₓ] at h
  exact ((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h)).resolve_left CharP.ring_char_ne_one

@[simp]
theorem order_of_neg_one [Nontrivial R] : orderOf (-1 : R) = if ringChar R = 2 then 1 else 2 := by
  split_ifs
  · rw [neg_one_eq_one_iff.2 h, order_of_one]
    
  apply order_of_eq_prime
  · simp
    
  simpa [← neg_one_eq_one_iff] using h

end ringChar

