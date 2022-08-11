/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Nat.CastField
import Mathbin.Data.Fintype.Basic

/-!
# Characteristic zero (additional theorems)

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main statements

* Characteristic zero implies that the additive monoid is infinite.
-/


namespace Nat

variable {R : Type _} [AddMonoidWithOneₓ R] [CharZero R]

/-- `nat.cast` as an embedding into monoids of characteristic `0`. -/
@[simps]
def castEmbedding : ℕ ↪ R :=
  ⟨coe, cast_injective⟩

@[simp]
theorem cast_pow_eq_one {R : Type _} [Semiringₓ R] [CharZero R] (q : ℕ) (n : ℕ) (hn : n ≠ 0) :
    (q : R) ^ n = 1 ↔ q = 1 := by
  rw [← cast_pow, cast_eq_one]
  exact pow_eq_one_iff hn

@[simp, norm_cast]
theorem cast_div_char_zero {k : Type _} [Field k] [CharZero k] {m n : ℕ} (n_dvd : n ∣ m) : ((m / n : ℕ) : k) = m / n :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    
  · exact cast_div n_dvd (cast_ne_zero.2 hn)
    

end Nat

section

variable (M : Type _) [AddMonoidWithOneₓ M] [CharZero M]

-- see Note [lower instance priority]
instance (priority := 100) CharZero.infinite : Infinite M :=
  Infinite.of_injective coe Nat.cast_injective

variable {M}

@[field_simps]
theorem two_ne_zero' : (2 : M) ≠ 0 := by
  have : ((2 : ℕ) : M) ≠ 0 :=
    Nat.cast_ne_zero.2
      (by
        decide)
  rwa [Nat.cast_two] at this

end

section

variable {R : Type _} [NonAssocSemiringₓ R] [NoZeroDivisors R] [CharZero R]

@[simp]
theorem add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 := by
  simp only [← (two_mul a).symm, ← mul_eq_zero, ← two_ne_zero', ← false_orₓ]

@[simp]
theorem bit0_eq_zero {a : R} : bit0 a = 0 ↔ a = 0 :=
  add_self_eq_zero

@[simp]
theorem zero_eq_bit0 {a : R} : 0 = bit0 a ↔ a = 0 := by
  rw [eq_comm]
  exact bit0_eq_zero

end

section

variable {R : Type _} [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

theorem neg_eq_self_iff {a : R} : -a = a ↔ a = 0 :=
  neg_eq_iff_add_eq_zero.trans add_self_eq_zero

theorem eq_neg_self_iff {a : R} : a = -a ↔ a = 0 :=
  eq_neg_iff_add_eq_zero.trans add_self_eq_zero

theorem nat_mul_inj {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b := by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h
  exact_mod_cast h

theorem nat_mul_inj' {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n ≠ 0) : a = b := by
  simpa [← w] using nat_mul_inj h

theorem bit0_injective : Function.Injective (bit0 : R → R) := fun a b h => by
  dsimp' [← bit0]  at h
  simp only [← (two_mul a).symm, ← (two_mul b).symm] at h
  refine' nat_mul_inj' _ two_ne_zero
  exact_mod_cast h

theorem bit1_injective : Function.Injective (bit1 : R → R) := fun a b h => by
  simp only [← bit1, ← add_left_injₓ] at h
  exact bit0_injective h

@[simp]
theorem bit0_eq_bit0 {a b : R} : bit0 a = bit0 b ↔ a = b :=
  bit0_injective.eq_iff

@[simp]
theorem bit1_eq_bit1 {a b : R} : bit1 a = bit1 b ↔ a = b :=
  bit1_injective.eq_iff

@[simp]
theorem bit1_eq_one {a : R} : bit1 a = 1 ↔ a = 0 := by
  rw
    [show (1 : R) = bit1 0 by
      simp ,
    bit1_eq_bit1]

@[simp]
theorem one_eq_bit1 {a : R} : 1 = bit1 a ↔ a = 0 := by
  rw [eq_comm]
  exact bit1_eq_one

end

section

variable {R : Type _} [DivisionRing R] [CharZero R]

@[simp]
theorem half_add_self (a : R) : (a + a) / 2 = a := by
  rw [← mul_two, mul_div_cancel a two_ne_zero']

@[simp]
theorem add_halves' (a : R) : a / 2 + a / 2 = a := by
  rw [← add_div, half_add_self]

theorem sub_half (a : R) : a - a / 2 = a / 2 := by
  rw [sub_eq_iff_eq_add, add_halves']

theorem half_sub (a : R) : a / 2 - a = -(a / 2) := by
  rw [← neg_sub, sub_half]

end

namespace WithTop

instance {R : Type _} [AddMonoidWithOneₓ R] [CharZero R] :
    CharZero (WithTop R) where cast_injective := fun m n h => by
    rwa [← coe_nat, ← coe_nat n, coe_eq_coe, Nat.cast_inj] at h

end WithTop

section RingHom

variable {R S : Type _} [NonAssocSemiringₓ R] [NonAssocSemiringₓ S]

theorem RingHom.char_zero (ϕ : R →+* S) [hS : CharZero S] : CharZero R :=
  ⟨fun a b h =>
    CharZero.cast_injective
      (by
        rw [← map_nat_cast ϕ, ← map_nat_cast ϕ, h])⟩

theorem RingHom.char_zero_iff {ϕ : R →+* S} (hϕ : Function.Injective ϕ) : CharZero R ↔ CharZero S :=
  ⟨fun hR =>
    ⟨by
      intro a b h <;> rwa [← @Nat.cast_inj R, ← hϕ.eq_iff, map_nat_cast ϕ, map_nat_cast ϕ]⟩,
    fun hS => ϕ.char_zero⟩

theorem RingHom.injective_nat (f : ℕ →+* R) [CharZero R] : Function.Injective f :=
  Subsingleton.elimₓ (Nat.castRingHom _) f ▸ Nat.cast_injective

end RingHom

