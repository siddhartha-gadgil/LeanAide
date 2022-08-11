/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.Data.Nat.Factorization.PrimePow
import Mathbin.RingTheory.Ideal.LocalRing

/-!
# Characteristics of local rings

## Main result

- `char_p_zero_or_prime_power`: In a commutative local ring the characteristics is either
  zero or a prime power.

-/


/-- In a local ring the characteristics is either zero or a prime power. -/
theorem char_p_zero_or_prime_power (R : Type _) [CommRingₓ R] [LocalRing R] (q : ℕ) [char_R_q : CharP R q] :
    q = 0 ∨ IsPrimePow q := by
  -- Assume `q := char(R)` is not zero.
  apply or_iff_not_imp_left.2
  intro q_pos
  let K := LocalRing.ResidueField R
  have RM_char := ringChar.char_p K
  let r := ringChar K
  let n := q.factorization r
  -- `r := char(R/m)` is either prime or zero:
  cases' CharP.char_is_prime_or_zero K r with r_prime r_zero
  · let a := q / r ^ n
    -- If `r` is prime, we can write it as `r = a * q^n` ...
    have q_eq_a_mul_rn : q = r ^ n * a := by
      rw [Nat.mul_div_cancel'ₓ (Nat.pow_factorization_dvd q r)]
    have r_ne_dvd_a := Nat.not_dvd_div_pow_factorization r_prime q_pos
    have rn_dvd_q : r ^ n ∣ q := ⟨a, q_eq_a_mul_rn⟩
    rw [mul_comm] at q_eq_a_mul_rn
    have a_dvd_q : a ∣ q := ⟨r ^ n, q_eq_a_mul_rn⟩
    -- ... where `a` is a unit.
    have a_unit : IsUnit (a : R) := by
      by_contra g
      rw [← mem_nonunits_iff] at g
      rw [← LocalRing.mem_maximal_ideal] at g
      have a_cast_zero := Ideal.Quotient.eq_zero_iff_mem.2 g
      rw [map_nat_cast] at a_cast_zero
      have r_dvd_a := (ringChar.spec K a).1 a_cast_zero
      exact absurd r_dvd_a r_ne_dvd_a
    -- Let `b` be the inverse of `a`.
    cases' a_unit.exists_left_inv with a_inv h_inv_mul_a
    have rn_cast_zero : ↑(r ^ n) = (0 : R) := by
      rw [Nat.cast_powₓ, ← @mul_oneₓ R _ (r ^ n), mul_comm, ← Classical.some_spec a_unit.exists_left_inv, mul_assoc, ←
        Nat.cast_powₓ, ← Nat.cast_mulₓ, ← q_eq_a_mul_rn, CharP.cast_eq_zero R q]
      simp
    have q_eq_rn := Nat.dvd_antisymm ((CharP.cast_eq_zero_iff R q (r ^ n)).mp rn_cast_zero) rn_dvd_q
    have n_pos : n ≠ 0 := by
      by_contra n_zero
      simp [← n_zero] at q_eq_rn
      exact absurd q_eq_rn (CharP.char_ne_one R q)
    -- Definition of prime power: `∃ r n, prime r ∧ 0 < n ∧ r ^ n = q`.
    exact ⟨r, ⟨n, ⟨nat.prime_iff.mp r_prime, ⟨pos_iff_ne_zero.mpr n_pos, q_eq_rn.symm⟩⟩⟩⟩
    
  · have K_char_p_0 := ringChar.of_eq r_zero
    have K_char_zero : CharZero K := CharP.char_p_to_char_zero K
    have R_char_zero := RingHom.char_zero (LocalRing.residue R)
    -- Finally, `r = 0` would lead to a contradiction:
    have q_zero := CharP.eq R char_R_q (CharP.of_char_zero R)
    exact absurd q_zero q_pos
    

