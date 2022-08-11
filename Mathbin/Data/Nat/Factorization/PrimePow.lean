/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.Algebra.IsPrimePow
import Mathbin.Data.Nat.Factorization.Basic

/-!
# Prime powers and factorizations

This file deals with factorizations of prime powers.
-/


variable {R : Type _} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem IsPrimePow.min_fac_pow_factorization_eq {n : ℕ} (hn : IsPrimePow n) : n.minFac ^ n.factorization n.minFac = n :=
  by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  rw [← Nat.prime_iff] at hp
  rw [hp.pow_min_fac hk.ne', hp.factorization_pow, Finsupp.single_eq_same]

theorem is_prime_pow_of_min_fac_pow_factorization_eq {n : ℕ} (h : n.minFac ^ n.factorization n.minFac = n)
    (hn : n ≠ 1) : IsPrimePow n := by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simpa using h
    
  refine' ⟨_, _, Nat.prime_iff.1 (Nat.min_fac_prime hn), _, h⟩
  rw [pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.factor_iff_mem_factorization,
    Nat.mem_factors_iff_dvd hn' (Nat.min_fac_prime hn)]
  apply Nat.min_fac_dvd

theorem is_prime_pow_iff_min_fac_pow_factorization_eq {n : ℕ} (hn : n ≠ 1) :
    IsPrimePow n ↔ n.minFac ^ n.factorization n.minFac = n :=
  ⟨fun h => h.min_fac_pow_factorization_eq, fun h => is_prime_pow_of_min_fac_pow_factorization_eq h hn⟩

theorem is_prime_pow_iff_factorization_eq_single {n : ℕ} :
    IsPrimePow n ↔ ∃ p k : ℕ, 0 < k ∧ n.factorization = Finsupp.single p k := by
  rw [is_prime_pow_nat_iff]
  refine' exists₂_congrₓ fun p k => _
  constructor
  · rintro ⟨hp, hk, hn⟩
    exact
      ⟨hk, by
        rw [← hn, Nat.Prime.factorization_pow hp]⟩
    
  · rintro ⟨hk, hn⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      simpa only [← Finsupp.single_eq_zero, ← eq_comm, ← Nat.factorization_zero, ← hk.ne'] using hn
    rw [Nat.eq_pow_of_factorization_eq_single hn0 hn]
    exact
      ⟨Nat.prime_of_mem_factorization
          (by
            simp [← hn, ← hk.ne'] : p ∈ n.factorization.support),
        hk, rfl⟩
    

theorem is_prime_pow_iff_card_support_factorization_eq_one {n : ℕ} : IsPrimePow n ↔ n.factorization.support.card = 1 :=
  by
  simp_rw [is_prime_pow_iff_factorization_eq_single, Finsupp.card_support_eq_one', exists_prop, pos_iff_ne_zero]

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a unique prime
dividing it. -/
theorem is_prime_pow_iff_unique_prime_dvd {n : ℕ} : IsPrimePow n ↔ ∃! p : ℕ, p.Prime ∧ p ∣ n := by
  rw [is_prime_pow_nat_iff]
  constructor
  · rintro ⟨p, k, hp, hk, rfl⟩
    refine' ⟨p, ⟨hp, dvd_pow_self _ hk.ne'⟩, _⟩
    rintro q ⟨hq, hq'⟩
    exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hq')
    
  rintro ⟨p, ⟨hp, hn⟩, hq⟩
  -- Take care of the n = 0 case
  rcases eq_or_ne n 0 with (rfl | hn₀)
  · obtain ⟨q, hq', hq''⟩ := Nat.exists_infinite_primes (p + 1)
    cases
      hq q
        ⟨hq'', by
          simp ⟩
    simpa using hq'
    
  -- So assume 0 < n
  refine' ⟨p, n.factorization p, hp, hp.factorization_pos_of_dvd hn₀ hn, _⟩
  simp only [← and_imp] at hq
  apply Nat.dvd_antisymm (Nat.pow_factorization_dvd _ _)
  -- We need to show n ∣ p ^ n.factorization p
  apply Nat.dvd_of_factors_subperm hn₀
  rw [hp.factors_pow, List.subperm_ext_iff]
  intro q hq'
  rw [Nat.mem_factors hn₀] at hq'
  cases hq _ hq'.1 hq'.2
  simp

theorem is_prime_pow_pow_iff {n k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) ↔ IsPrimePow n := by
  simp only [← is_prime_pow_iff_unique_prime_dvd]
  apply exists_unique_congr
  simp only [← And.congr_right_iff]
  intro p hp
  exact ⟨hp.dvd_of_dvd_pow, fun t => t.trans (dvd_pow_self _ hk)⟩

theorem Nat.Coprime.is_prime_pow_dvd_mul {n a b : ℕ} (hab : Nat.Coprime a b) (hn : IsPrimePow n) :
    n ∣ a * b ↔ n ∣ a ∨ n ∣ b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [← Nat.coprime_zero_leftₓ] at hab
    simp [← hab, ← Finset.filter_singleton, ← not_is_prime_pow_one]
    
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp only [← Nat.coprime_zero_rightₓ] at hab
    simp [← hab, ← Finset.filter_singleton, ← not_is_prime_pow_one]
    
  refine' ⟨_, fun h => Or.elim h (fun i => i.trans (dvd_mul_right _ _)) fun i => i.trans (dvd_mul_left _ _)⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := (is_prime_pow_nat_iff _).1 hn
  simp only [← hp.pow_dvd_iff_le_factorization (mul_ne_zero ha hb), ← Nat.factorization_mul ha hb, ←
    hp.pow_dvd_iff_le_factorization ha, ← hp.pow_dvd_iff_le_factorization hb, ← Pi.add_apply, ← Finsupp.coe_add]
  have : a.factorization p = 0 ∨ b.factorization p = 0 := by
    rw [← Finsupp.not_mem_support_iff, ← Finsupp.not_mem_support_iff, ← not_and_distrib, ← Finset.mem_inter]
    exact fun t => Nat.factorization_disjoint_of_coprime hab t
  cases this <;> simp [← this, ← imp_or_distrib]

theorem Nat.mul_divisors_filter_prime_pow {a b : ℕ} (hab : a.Coprime b) :
    (a * b).divisors.filter IsPrimePow = (a.divisors ∪ b.divisors).filter IsPrimePow := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [← Nat.coprime_zero_leftₓ] at hab
    simp [← hab, ← Finset.filter_singleton, ← not_is_prime_pow_one]
    
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp only [← Nat.coprime_zero_rightₓ] at hab
    simp [← hab, ← Finset.filter_singleton, ← not_is_prime_pow_one]
    
  ext n
  simp only [← ha, ← hb, ← Finset.mem_union, ← Finset.mem_filter, ← Nat.mul_eq_zero, ← and_trueₓ, ← Ne.def, ←
    And.congr_left_iff, ← not_false_iff, ← Nat.mem_divisors, ← or_selfₓ]
  apply hab.is_prime_pow_dvd_mul

