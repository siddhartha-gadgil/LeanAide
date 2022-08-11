/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.Algebra.CharZero
import Mathbin.Data.Nat.Prime

/-!
# Exponential characteristic

This file defines the exponential characteristic and establishes a few basic results relating
it to the (ordinary characteristic).
The definition is stated for a semiring, but the actual results are for nontrivial rings
(as far as exponential characteristic one is concerned), respectively a ring without zero-divisors
(for prime characteristic).

## Main results
- `exp_char`: the definition of exponential characteristic
- `exp_char_is_prime_or_one`: the exponential characteristic is a prime or one
- `char_eq_exp_char_iff`: the characteristic equals the exponential characteristic iff the
  characteristic is prime

## Tags
exponential characteristic, characteristic
-/


universe u

variable (R : Type u)

section Semiringₓ

variable [Semiringₓ R]

/-- The definition of the exponential characteristic of a semiring. -/
class inductive ExpChar (R : Type u) [Semiringₓ R] : ℕ → Prop
  | zero [CharZero R] : ExpChar 1
  | Prime {q : ℕ} (hprime : q.Prime) [hchar : CharP R q] : ExpChar q

/-- The exponential characteristic is one if the characteristic is zero. -/
theorem exp_char_one_of_char_zero (q : ℕ) [hp : CharP R 0] [hq : ExpChar R q] : q = 1 := by
  cases' hq with q hq_one hq_prime
  · rfl
    
  · exact False.elim (lt_irreflₓ _ ((hp.eq R hq_hchar).symm ▸ hq_prime : (0 : ℕ).Prime).Pos)
    

/-- The characteristic equals the exponential characteristic iff the former is prime. -/
theorem char_eq_exp_char_iff (p q : ℕ) [hp : CharP R p] [hq : ExpChar R q] : p = q ↔ p.Prime := by
  cases' hq with q hq_one hq_prime
  · apply iff_of_false
    · rintro rfl
      exact one_ne_zero (hp.eq R (CharP.of_char_zero R))
      
    · intro pprime
      rw [(CharP.eq R hp inferInstance : p = 0)] at pprime
      exact Nat.not_prime_zero pprime
      
    
  · exact ⟨fun hpq => hpq.symm ▸ hq_prime, fun _ => CharP.eq R hp hq_hchar⟩
    

section Nontrivial

variable [Nontrivial R]

/-- The exponential characteristic is one if the characteristic is zero. -/
theorem char_zero_of_exp_char_one (p : ℕ) [hp : CharP R p] [hq : ExpChar R 1] : p = 0 := by
  cases hq
  · exact CharP.eq R hp inferInstance
    
  · exact False.elim (CharP.char_ne_one R 1 rfl)
    

/-- The characteristic is zero if the exponential characteristic is one. -/
-- see Note [lower instance priority]
instance (priority := 100) char_zero_of_exp_char_one' [hq : ExpChar R 1] : CharZero R := by
  cases hq
  · assumption
    
  · exact False.elim (CharP.char_ne_one R 1 rfl)
    

/-- The exponential characteristic is one iff the characteristic is zero. -/
theorem exp_char_one_iff_char_zero (p q : ℕ) [CharP R p] [ExpChar R q] : q = 1 ↔ p = 0 := by
  constructor
  · rintro rfl
    exact char_zero_of_exp_char_one R p
    
  · rintro rfl
    exact exp_char_one_of_char_zero R q
    

section NoZeroDivisors

variable [NoZeroDivisors R]

/-- A helper lemma: the characteristic is prime if it is non-zero. -/
theorem char_prime_of_ne_zero {p : ℕ} [hp : CharP R p] (p_ne_zero : p ≠ 0) : Nat.Prime p := by
  cases' CharP.char_is_prime_or_zero R p with h h
  · exact h
    
  · contradiction
    

/-- The exponential characteristic is a prime number or one. -/
theorem exp_char_is_prime_or_one (q : ℕ) [hq : ExpChar R q] : Nat.Prime q ∨ q = 1 :=
  or_iff_not_imp_right.mpr fun h => by
    cases' CharP.exists R with p hp
    have p_ne_zero : p ≠ 0 := by
      intro p_zero
      have : CharP R 0 := by
        rwa [← p_zero]
      have : q = 1 := exp_char_one_of_char_zero R q
      contradiction
    have p_eq_q : p = q := (char_eq_exp_char_iff R p q).mpr (char_prime_of_ne_zero R p_ne_zero)
    cases' CharP.char_is_prime_or_zero R p with pprime
    · rwa [p_eq_q] at pprime
      
    · contradiction
      

end NoZeroDivisors

end Nontrivial

end Semiringₓ

