/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
import Mathbin.Data.Nat.Prime
import Mathbin.Data.Pnat.Basic

/-!
# Primality and GCD on pnat

This file extends the theory of `ℕ+` with `gcd`, `lcm` and `prime` functions, analogous to those on
`nat`.
-/


namespace Nat.Primes

instance coePnat : Coe Nat.Primes ℕ+ :=
  ⟨fun p => ⟨(p : ℕ), p.property.Pos⟩⟩

theorem coe_pnat_nat (p : Nat.Primes) : ((p : ℕ+) : ℕ) = p :=
  rfl

theorem coe_pnat_inj (p q : Nat.Primes) : (p : ℕ+) = (q : ℕ+) → p = q := fun h => by
  replace h : ((p : ℕ+) : ℕ) = ((q : ℕ+) : ℕ) := congr_arg Subtype.val h
  rw [coePnatNat, coePnatNat] at h
  exact Subtype.eq h

end Nat.Primes

namespace Pnat

open _Root_.Nat

/-- The greatest common divisor (gcd) of two positive natural numbers,
  viewed as positive natural number. -/
def gcd (n m : ℕ+) : ℕ+ :=
  ⟨Nat.gcdₓ (n : ℕ) (m : ℕ), Nat.gcd_pos_of_pos_leftₓ (m : ℕ) n.Pos⟩

/-- The least common multiple (lcm) of two positive natural numbers,
  viewed as positive natural number. -/
def lcm (n m : ℕ+) : ℕ+ :=
  ⟨Nat.lcmₓ (n : ℕ) (m : ℕ), by
    let h := mul_pos n.pos m.pos
    rw [← gcd_mul_lcm (n : ℕ) (m : ℕ), mul_comm] at h
    exact pos_of_dvd_of_pos (Dvd.intro (Nat.gcdₓ (n : ℕ) (m : ℕ)) rfl) h⟩

@[simp]
theorem gcd_coe (n m : ℕ+) : (gcd n m : ℕ) = Nat.gcdₓ n m :=
  rfl

@[simp]
theorem lcm_coe (n m : ℕ+) : (lcm n m : ℕ) = Nat.lcmₓ n m :=
  rfl

theorem gcd_dvd_left (n m : ℕ+) : gcd n m ∣ n :=
  dvd_iff.2 (Nat.gcd_dvd_leftₓ (n : ℕ) (m : ℕ))

theorem gcd_dvd_right (n m : ℕ+) : gcd n m ∣ m :=
  dvd_iff.2 (Nat.gcd_dvd_rightₓ (n : ℕ) (m : ℕ))

theorem dvd_gcd {m n k : ℕ+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd m n :=
  dvd_iff.2 (@Nat.dvd_gcdₓ (m : ℕ) (n : ℕ) (k : ℕ) (dvd_iff.1 hm) (dvd_iff.1 hn))

theorem dvd_lcm_left (n m : ℕ+) : n ∣ lcm n m :=
  dvd_iff.2 (Nat.dvd_lcm_leftₓ (n : ℕ) (m : ℕ))

theorem dvd_lcm_right (n m : ℕ+) : m ∣ lcm n m :=
  dvd_iff.2 (Nat.dvd_lcm_rightₓ (n : ℕ) (m : ℕ))

theorem lcm_dvd {m n k : ℕ+} (hm : m ∣ k) (hn : n ∣ k) : lcm m n ∣ k :=
  dvd_iff.2 (@Nat.lcm_dvdₓ (m : ℕ) (n : ℕ) (k : ℕ) (dvd_iff.1 hm) (dvd_iff.1 hn))

theorem gcd_mul_lcm (n m : ℕ+) : gcd n m * lcm n m = n * m :=
  Subtype.eq (Nat.gcd_mul_lcmₓ (n : ℕ) (m : ℕ))

theorem eq_one_of_lt_two {n : ℕ+} : n < 2 → n = 1 := by
  intro h
  apply le_antisymmₓ
  swap
  apply Pnat.one_le
  change n < 1 + 1 at h
  rw [Pnat.lt_add_one_iff] at h
  apply h

section Prime

/-! ### Prime numbers -/


/-- Primality predicate for `ℕ+`, defined in terms of `nat.prime`. -/
def Prime (p : ℕ+) : Prop :=
  (p : ℕ).Prime

theorem Prime.one_lt {p : ℕ+} : p.Prime → 1 < p :=
  Nat.Prime.one_lt

theorem prime_two : (2 : ℕ+).Prime :=
  Nat.prime_two

theorem dvd_prime {p m : ℕ+} (pp : p.Prime) : m ∣ p ↔ m = 1 ∨ m = p := by
  rw [Pnat.dvd_iff]
  rw [Nat.dvd_prime pp]
  simp

theorem Prime.ne_one {p : ℕ+} : p.Prime → p ≠ 1 := by
  intro pp
  intro contra
  apply Nat.Prime.ne_one pp
  rw [Pnat.coe_eq_one_iff]
  apply contra

@[simp]
theorem not_prime_one : ¬(1 : ℕ+).Prime :=
  Nat.not_prime_one

theorem Prime.not_dvd_one {p : ℕ+} : p.Prime → ¬p ∣ 1 := fun pp : p.Prime => by
  rw [dvd_iff]
  apply Nat.Prime.not_dvd_one pp

theorem exists_prime_and_dvd {n : ℕ+} (hn : n ≠ 1) : ∃ p : ℕ+, p.Prime ∧ p ∣ n := by
  obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (mt coe_eq_one_iff.mp hn)
  exists (⟨p, Nat.Prime.pos hp.left⟩ : ℕ+)
  rw [dvd_iff]
  apply hp

end Prime

section Coprime

/-! ### Coprime numbers and gcd -/


/-- Two pnats are coprime if their gcd is 1. -/
def Coprime (m n : ℕ+) : Prop :=
  m.gcd n = 1

@[simp]
theorem coprime_coe {m n : ℕ+} : Nat.Coprime ↑m ↑n ↔ m.Coprime n := by
  unfold coprime
  unfold Nat.Coprime
  rw [← coe_inj]
  simp

theorem Coprime.mul {k m n : ℕ+} : m.Coprime k → n.Coprime k → (m * n).Coprime k := by
  repeat'
    rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul

theorem Coprime.mul_right {k m n : ℕ+} : k.Coprime m → k.Coprime n → k.Coprime (m * n) := by
  repeat'
    rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul_right

theorem gcd_comm {m n : ℕ+} : m.gcd n = n.gcd m := by
  apply Eq
  simp only [← gcd_coe]
  apply Nat.gcd_commₓ

theorem gcd_eq_left_iff_dvd {m n : ℕ+} : m ∣ n ↔ m.gcd n = m := by
  rw [dvd_iff]
  rw [Nat.gcd_eq_left_iff_dvdₓ]
  rw [← coe_inj]
  simp

theorem gcd_eq_right_iff_dvd {m n : ℕ+} : m ∣ n ↔ n.gcd m = m := by
  rw [gcd_comm]
  apply gcd_eq_left_iff_dvd

theorem Coprime.gcd_mul_left_cancel (m : ℕ+) {n k : ℕ+} : k.Coprime n → (k * m).gcd n = m.gcd n := by
  intro h
  apply Eq
  simp only [← gcd_coe, ← mul_coe]
  apply Nat.Coprime.gcd_mul_left_cancel
  simpa

theorem Coprime.gcd_mul_right_cancel (m : ℕ+) {n k : ℕ+} : k.Coprime n → (m * k).gcd n = m.gcd n := by
  rw [mul_comm]
  apply coprime.gcd_mul_left_cancel

theorem Coprime.gcd_mul_left_cancel_right (m : ℕ+) {n k : ℕ+} : k.Coprime m → m.gcd (k * n) = m.gcd n := by
  intro h
  iterate 2 
    rw [gcd_comm]
    symm
  apply coprime.gcd_mul_left_cancel _ h

theorem Coprime.gcd_mul_right_cancel_right (m : ℕ+) {n k : ℕ+} : k.Coprime m → m.gcd (n * k) = m.gcd n := by
  rw [mul_comm]
  apply coprime.gcd_mul_left_cancel_right

@[simp]
theorem one_gcd {n : ℕ+} : gcd 1 n = 1 := by
  rw [← gcd_eq_left_iff_dvd]
  apply one_dvd

@[simp]
theorem gcd_one {n : ℕ+} : gcd n 1 = 1 := by
  rw [gcd_comm]
  apply one_gcd

@[symm]
theorem Coprime.symm {m n : ℕ+} : m.Coprime n → n.Coprime m := by
  unfold coprime
  rw [gcd_comm]
  simp

@[simp]
theorem one_coprime {n : ℕ+} : (1 : ℕ+).Coprime n :=
  one_gcd

@[simp]
theorem coprime_one {n : ℕ+} : n.Coprime 1 :=
  Coprime.symm one_coprime

theorem Coprime.coprime_dvd_left {m k n : ℕ+} : m ∣ k → k.Coprime n → m.Coprime n := by
  rw [dvd_iff]
  repeat'
    rw [← coprime_coe]
  apply Nat.Coprime.coprime_dvd_left

theorem Coprime.factor_eq_gcd_left {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n) : a = (a * b).gcd m :=
  by
  rw [gcd_eq_left_iff_dvd] at am
  conv_lhs => rw [← am]
  symm
  apply coprime.gcd_mul_right_cancel a
  apply coprime.coprime_dvd_left bn cop.symm

theorem Coprime.factor_eq_gcd_right {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n) : a = (b * a).gcd m :=
  by
  rw [mul_comm]
  apply coprime.factor_eq_gcd_left cop am bn

theorem Coprime.factor_eq_gcd_left_right {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n) :
    a = m.gcd (a * b) := by
  rw [gcd_comm]
  apply coprime.factor_eq_gcd_left cop am bn

theorem Coprime.factor_eq_gcd_right_right {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n) :
    a = m.gcd (b * a) := by
  rw [gcd_comm]
  apply coprime.factor_eq_gcd_right cop am bn

theorem Coprime.gcd_mul (k : ℕ+) {m n : ℕ+} (h : m.Coprime n) : k.gcd (m * n) = k.gcd m * k.gcd n := by
  rw [← coprime_coe] at h
  apply Eq
  simp only [← gcd_coe, ← mul_coe]
  apply Nat.Coprime.gcd_mul k h

theorem gcd_eq_left {m n : ℕ+} : m ∣ n → m.gcd n = m := by
  rw [dvd_iff]
  intro h
  apply Eq
  simp only [← gcd_coe]
  apply Nat.gcd_eq_leftₓ h

theorem Coprime.pow {m n : ℕ+} (k l : ℕ) (h : m.Coprime n) : (m ^ k).Coprime (n ^ l) := by
  rw [← coprime_coe] at *
  simp only [← pow_coe]
  apply Nat.Coprime.pow
  apply h

end Coprime

end Pnat

