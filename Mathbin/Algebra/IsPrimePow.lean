/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.Algebra.Associated
import Mathbin.NumberTheory.Divisors

/-!
# Prime powers

This file deals with prime powers: numbers which are positive integer powers of a single prime.
-/


variable {R : Type _} [CommMonoidWithZero R] (n p : R) (k : ℕ)

/-- `n` is a prime power if there is a prime `p` and a positive natural `k` such that `n` can be
written as `p^k`. -/
def IsPrimePow : Prop :=
  ∃ (p : R)(k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n

theorem is_prime_pow_def : IsPrimePow n ↔ ∃ (p : R)(k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n :=
  Iff.rfl

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a prime `p` and a
natural `k` such that `n` can be written as `p^(k+1)`. -/
theorem is_prime_pow_iff_pow_succ : IsPrimePow n ↔ ∃ (p : R)(k : ℕ), Prime p ∧ p ^ (k + 1) = n :=
  (is_prime_pow_def _).trans
    ⟨fun ⟨p, k, hp, hk, hn⟩ =>
      ⟨_, _, hp, by
        rwa [Nat.sub_add_cancelₓ hk]⟩,
      fun ⟨p, k, hp, hn⟩ => ⟨_, _, hp, Nat.succ_pos', hn⟩⟩

theorem not_is_prime_pow_zero [NoZeroDivisors R] : ¬IsPrimePow (0 : R) := by
  simp only [← is_prime_pow_def, ← not_exists, ← not_and', ← and_imp]
  intro x n hn hx
  rw [pow_eq_zero hx]
  simp

theorem not_is_prime_pow_one : ¬IsPrimePow (1 : R) := by
  simp only [← is_prime_pow_def, ← not_exists, ← not_and', ← and_imp]
  intro x n hn hx ht
  exact ht.not_unit (is_unit_of_pow_eq_one x n hx hn)

theorem Prime.is_prime_pow {p : R} (hp : Prime p) : IsPrimePow p :=
  ⟨p, 1, hp, zero_lt_one, by
    simp ⟩

theorem IsPrimePow.pow {n : R} (hn : IsPrimePow n) {k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) :=
  let ⟨p, k', hp, hk', hn⟩ := hn
  ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by
    rw [pow_mul', hn]⟩

theorem IsPrimePow.ne_zero [NoZeroDivisors R] {n : R} (h : IsPrimePow n) : n ≠ 0 := fun t =>
  Eq.ndrec not_is_prime_pow_zero t.symm h

theorem IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n ≠ 1 := fun t => Eq.ndrec not_is_prime_pow_one t.symm h

section UniqueUnits

theorem eq_of_prime_pow_eq {R : Type _} [CancelCommMonoidWithZero R] [Unique Rˣ] {p₁ p₂ : R} {k₁ k₂ : ℕ}
    (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₁) (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂ := by
  rw [← associated_iff_eq] at h⊢
  apply h.of_pow_associated_of_prime hp₁ hp₂ hk₁

theorem eq_of_prime_pow_eq' {R : Type _} [CancelCommMonoidWithZero R] [Unique Rˣ] {p₁ p₂ : R} {k₁ k₂ : ℕ}
    (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₂) (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂ := by
  rw [← associated_iff_eq] at h⊢
  apply h.of_pow_associated_of_prime' hp₁ hp₂ hk₁

end UniqueUnits

section Nat

theorem is_prime_pow_nat_iff (n : ℕ) : IsPrimePow n ↔ ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p ^ k = n := by
  simp only [← is_prime_pow_def, ← Nat.prime_iff]

theorem Nat.Prime.is_prime_pow {p : ℕ} (hp : p.Prime) : IsPrimePow p :=
  (Nat.prime_iff.mp hp).IsPrimePow

theorem is_prime_pow_nat_iff_bounded (n : ℕ) :
    IsPrimePow n ↔ ∃ p : ℕ, p ≤ n ∧ ∃ k : ℕ, k ≤ n ∧ p.Prime ∧ 0 < k ∧ p ^ k = n := by
  rw [is_prime_pow_nat_iff]
  refine' Iff.symm ⟨fun ⟨p, _, k, _, hp, hk, hn⟩ => ⟨p, k, hp, hk, hn⟩, _⟩
  rintro ⟨p, k, hp, hk, rfl⟩
  refine' ⟨p, _, k, (Nat.lt_pow_self hp.one_lt _).le, hp, hk, rfl⟩
  simpa using Nat.pow_le_pow_of_le_rightₓ hp.pos hk

instance {n : ℕ} : Decidable (IsPrimePow n) :=
  decidableOfIff' _ (is_prime_pow_nat_iff_bounded n)

theorem IsPrimePow.dvd {n m : ℕ} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m ≠ 1) : IsPrimePow m := by
  rw [is_prime_pow_nat_iff] at hn⊢
  rcases hn with ⟨p, k, hp, hk, rfl⟩
  obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow hp).1 hm
  refine' ⟨p, i, hp, _, rfl⟩
  apply Nat.pos_of_ne_zeroₓ
  rintro rfl
  simpa using hm₁

theorem Nat.disjoint_divisors_filter_prime_pow {a b : ℕ} (hab : a.Coprime b) :
    Disjoint (a.divisors.filter IsPrimePow) (b.divisors.filter IsPrimePow) := by
  simp only [← Finset.disjoint_left, ← Finset.mem_filter, ← and_imp, ← Nat.mem_divisors, ← not_and]
  rintro n han ha hn hbn hb -
  exact hn.ne_one (Nat.eq_one_of_dvd_coprimes hab han hbn)

theorem IsPrimePow.two_le : ∀ {n : ℕ}, IsPrimePow n → 2 ≤ n
  | 0, h => (not_is_prime_pow_zero h).elim
  | 1, h => (not_is_prime_pow_one h).elim
  | n + 2, _ => le_add_self

theorem IsPrimePow.pos {n : ℕ} (hn : IsPrimePow n) : 0 < n :=
  pos_of_gt hn.two_le

theorem IsPrimePow.one_lt {n : ℕ} (h : IsPrimePow n) : 1 < n :=
  h.two_le

end Nat

