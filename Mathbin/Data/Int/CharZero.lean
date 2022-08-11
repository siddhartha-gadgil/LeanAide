/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Algebra.CharZero
import Mathbin.Data.Int.CastField

/-!
# Injectivity of `int.cast` into characteristic zero rings and fields.

-/


variable {α : Type _}

open Nat

namespace Int

@[simp]
theorem cast_eq_zero [AddGroupWithOneₓ α] [CharZero α] {n : ℤ} : (n : α) = 0 ↔ n = 0 :=
  ⟨fun h => by
    cases n
    · rw [Int.cast_of_nat] at h
      exact congr_arg coe (Nat.cast_eq_zero.1 h)
      
    · rw [cast_neg_succ_of_nat, neg_eq_zero, Nat.cast_eq_zero] at h
      contradiction
      ,
    fun h => by
    rw [h, cast_zero]⟩

@[simp, norm_cast]
theorem cast_inj [AddGroupWithOneₓ α] [CharZero α] {m n : ℤ} : (m : α) = n ↔ m = n := by
  rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]

theorem cast_injective [AddGroupWithOneₓ α] [CharZero α] : Function.Injective (coe : ℤ → α)
  | m, n => cast_inj.1

theorem cast_ne_zero [AddGroupWithOneₓ α] [CharZero α] {n : ℤ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero

@[simp, norm_cast]
theorem cast_div_char_zero {k : Type _} [Field k] [CharZero k] {m n : ℤ} (n_dvd : n ∣ m) : ((m / n : ℤ) : k) = m / n :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [← Int.div_zero]
    
  · exact cast_div n_dvd (cast_ne_zero.mpr hn)
    

end Int

theorem RingHom.injective_int {α : Type _} [NonAssocRing α] (f : ℤ →+* α) [CharZero α] : Function.Injective f :=
  Subsingleton.elimₓ (Int.castRingHom _) f ▸ Int.cast_injective

