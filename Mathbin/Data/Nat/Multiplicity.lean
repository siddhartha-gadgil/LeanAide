/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Algebra.BigOperators.Intervals
import Mathbin.Algebra.GeomSum
import Mathbin.Data.Nat.Bitwise
import Mathbin.Data.Nat.Log
import Mathbin.Data.Nat.Parity
import Mathbin.RingTheory.Int.Basic

/-!
# Natural number multiplicity

This file contains lemmas about the multiplicity function (the maximum prime power dividing a
number) when applied to naturals, in particular calculating it for factorials and binomial
coefficients.

## Multiplicity calculations

* `nat.multiplicity_factorial`: Legendre's Theorem. The multiplicity of `p` in `n!` is
  `n/p + ... + n/p^b` for any `b` such that `n/p^(b + 1) = 0`.
* `nat.multiplicity_factorial_mul`: The multiplicity of `p` in `(p * n)!` is `n` more than that of
  `n!`.
* `nat.multiplicity_choose`: The multiplicity of `p` in `n.choose k` is the number of carries when
  `k` and`n - k` are added in base `p`.

## Other declarations

* `nat.multiplicity_eq_card_pow_dvd`: The multiplicity of `m` in `n` is the number of positive
  natural numbers `i` such that `m ^ i` divides `n`.
* `nat.multiplicity_two_factorial_lt`: The multiplicity of `2` in `n!` is strictly less than `n`.
* `nat.prime.multiplicity_something`: Specialization of `multiplicity.something` to a prime in the
  naturals. Avoids having to provide `p ≠ 1` and other trivialities, along with translating between
  `prime` and `nat.prime`.

## Tags

Legendre, p-adic
-/


open Finset Nat multiplicity

open BigOperators Nat

namespace Nat

/-- The multiplicity of `m` in `n` is the number of positive natural numbers `i` such that `m ^ i`
divides `n`. This set is expressed by filtering `Ico 1 b` where `b` is any bound greater than
`log m n`. -/
theorem multiplicity_eq_card_pow_dvd {m n b : ℕ} (hm : m ≠ 1) (hn : 0 < n) (hb : log m n < b) :
    multiplicity m n = ↑((Finset.ico 1 b).filter fun i => m ^ i ∣ n).card :=
  calc
    multiplicity m n = ↑(ico 1 <| (multiplicity m n).get (finite_nat_iff.2 ⟨hm, hn⟩) + 1).card := by
      simp
    _ = ↑((Finset.ico 1 b).filter fun i => m ^ i ∣ n).card :=
      congr_arg coe <|
        congr_arg card <|
          Finset.ext fun i => by
            rw [mem_filter, mem_Ico, mem_Ico, lt_succ_iff, ← @PartEnat.coe_le_coe i, PartEnat.coe_get, ←
              pow_dvd_iff_le_multiplicity, And.right_comm]
            refine' (and_iff_left_of_imp fun h => _).symm
            cases m
            · rw [zero_pow, zero_dvd_iff] at h
              exact (hn.ne' h.2).elim
              · exact h.1
                
              
            exact
              ((pow_le_iff_le_log (succ_lt_succ <| Nat.pos_of_ne_zeroₓ <| succ_ne_succ.1 hm) hn).1 <|
                    le_of_dvd hn h.2).trans_lt
                hb
    

namespace Prime

theorem multiplicity_one {p : ℕ} (hp : p.Prime) : multiplicity p 1 = 0 :=
  multiplicity.one_right (prime_iff.mp hp).not_unit

theorem multiplicity_mul {p m n : ℕ} (hp : p.Prime) : multiplicity p (m * n) = multiplicity p m + multiplicity p n :=
  multiplicity.mul <| prime_iff.mp hp

theorem multiplicity_pow {p m n : ℕ} (hp : p.Prime) : multiplicity p (m ^ n) = n • multiplicity p m :=
  multiplicity.pow <| prime_iff.mp hp

theorem multiplicity_self {p : ℕ} (hp : p.Prime) : multiplicity p p = 1 :=
  multiplicity_self (prime_iff.mp hp).not_unit hp.ne_zero

theorem multiplicity_pow_self {p n : ℕ} (hp : p.Prime) : multiplicity p (p ^ n) = n :=
  multiplicity_pow_self hp.ne_zero (prime_iff.mp hp).not_unit n

/-- **Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
theorem multiplicity_factorial {p : ℕ} (hp : p.Prime) :
    ∀ {n b : ℕ}, log p n < b → multiplicity p n ! = (∑ i in ico 1 b, n / p ^ i : ℕ)
  | 0, b, hb => by
    simp [← Ico, ← hp.multiplicity_one]
  | n + 1, b, hb =>
    calc
      multiplicity p (n + 1)! = multiplicity p n ! + multiplicity p (n + 1) := by
        rw [factorial_succ, hp.multiplicity_mul, add_commₓ]
      _ = (∑ i in ico 1 b, n / p ^ i : ℕ) + ((Finset.ico 1 b).filter fun i => p ^ i ∣ n + 1).card := by
        rw [multiplicity_factorial ((log_mono_right <| le_succ _).trans_lt hb), ←
          multiplicity_eq_card_pow_dvd hp.ne_one (succ_pos _) hb]
      _ = (∑ i in ico 1 b, n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0 : ℕ) := by
        rw [sum_add_distrib, sum_boole]
        simp
      _ = (∑ i in ico 1 b, (n + 1) / p ^ i : ℕ) :=
        congr_arg coe <| (Finset.sum_congr rfl) fun _ _ => (succ_div _ _).symm
      

/-- The multiplicity of `p` in `(p * (n + 1))!` is one more than the sum
  of the multiplicities of `p` in `(p * n)!` and `n + 1`. -/
theorem multiplicity_factorial_mul_succ {n p : ℕ} (hp : p.Prime) :
    multiplicity p (p * (n + 1))! = multiplicity p (p * n)! + multiplicity p (n + 1) + 1 := by
  have hp' := prime_iff.mp hp
  have h0 : 2 ≤ p := hp.two_le
  have h1 : 1 ≤ p * n + 1 := Nat.le_add_leftₓ _ _
  have h2 : p * n + 1 ≤ p * (n + 1)
  linarith
  have h3 : p * n + 1 ≤ p * (n + 1) + 1
  linarith
  have hm : multiplicity p (p * n)! ≠ ⊤ := by
    rw [Ne.def, eq_top_iff_not_finite, not_not, finite_nat_iff]
    exact ⟨hp.ne_one, factorial_pos _⟩
  revert hm
  have h4 : ∀, ∀ m ∈ Ico (p * n + 1) (p * (n + 1)), ∀, multiplicity p m = 0 := by
    intro m hm
    apply multiplicity_eq_zero_of_not_dvd
    rw [← not_dvd_iff_between_consec_multiples _ (pos_iff_ne_zero.mpr hp.ne_zero)]
    rw [mem_Ico] at hm
    exact ⟨n, lt_of_succ_le hm.1, hm.2⟩
  simp_rw [← prod_Ico_id_eq_factorial, multiplicity.Finset.prod hp', ← sum_Ico_consecutive _ h1 h3, add_assocₓ]
  intro h
  rw [PartEnat.add_left_cancel_iff h, sum_Ico_succ_top h2, multiplicity.mul hp', hp.multiplicity_self, sum_congr rfl h4,
    sum_const_zero, zero_addₓ, add_commₓ (1 : PartEnat)]

/-- The multiplicity of `p` in `(p * n)!` is `n` more than that of `n!`. -/
theorem multiplicity_factorial_mul {n p : ℕ} (hp : p.Prime) : multiplicity p (p * n)! = multiplicity p n ! + n := by
  induction' n with n ih
  · simp
    
  · simp only [← succ_eq_add_one, ← multiplicity.mul, ← hp, ← prime_iff.mp hp, ← ih, ← multiplicity_factorial_mul_succ,
      add_assocₓ, ← Nat.cast_oneₓ, ← Nat.cast_addₓ, ← factorial_succ]
    congr 1
    rw [add_commₓ, add_assocₓ]
    

/-- A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound greater than `log p n` -/
theorem pow_dvd_factorial_iff {p : ℕ} {n r b : ℕ} (hp : p.Prime) (hbn : log p n < b) :
    p ^ r ∣ n ! ↔ r ≤ ∑ i in ico 1 b, n / p ^ i := by
  rw [← PartEnat.coe_le_coe, ← hp.multiplicity_factorial hbn, ← pow_dvd_iff_le_multiplicity]

theorem multiplicity_factorial_le_div_pred {p : ℕ} (hp : p.Prime) (n : ℕ) : multiplicity p n ! ≤ (n / (p - 1) : ℕ) := by
  rw [hp.multiplicity_factorial (lt_succ_self _), PartEnat.coe_le_coe]
  exact Nat.geom_sum_Ico_le hp.two_le _ _

theorem multiplicity_choose_aux {p n b k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    (∑ i in Finset.ico 1 b, n / p ^ i) =
      ((∑ i in Finset.ico 1 b, k / p ^ i) + ∑ i in Finset.ico 1 b, (n - k) / p ^ i) +
        ((Finset.ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card :=
  calc
    (∑ i in Finset.ico 1 b, n / p ^ i) = ∑ i in Finset.ico 1 b, (k + (n - k)) / p ^ i := by
      simp only [← add_tsub_cancel_of_le hkn]
    _ = ∑ i in Finset.ico 1 b, k / p ^ i + (n - k) / p ^ i + if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0 := by
      simp only [← Nat.add_div (pow_pos hp.pos _)]
    _ = _ := by
      simp [← sum_add_distrib, ← sum_boole]
    

/-- The multiplicity of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p n`. -/
theorem multiplicity_choose {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : log p n < b) :
    multiplicity p (choose n k) = ((ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card :=
  have h₁ :
    multiplicity p (choose n k) + multiplicity p (k ! * (n - k)!) =
      ((Finset.ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card + multiplicity p (k ! * (n - k)!) :=
    by
    rw [← hp.multiplicity_mul, ← mul_assoc, choose_mul_factorial_mul_factorial hkn, hp.multiplicity_factorial hnb,
      hp.multiplicity_mul, hp.multiplicity_factorial ((log_mono_right hkn).trans_lt hnb),
      hp.multiplicity_factorial (lt_of_le_of_ltₓ (log_mono_right tsub_le_self) hnb), multiplicity_choose_aux hp hkn]
    simp [← add_commₓ]
  (PartEnat.add_right_cancel_iff
        (PartEnat.ne_top_iff_dom.2 <|
          finite_nat_iff.2 ⟨ne_of_gtₓ hp.one_lt, mul_pos (factorial_pos k) (factorial_pos (n - k))⟩)).1
    h₁

/-- A lower bound on the multiplicity of `p` in `choose n k`. -/
theorem multiplicity_le_multiplicity_choose_add {p : ℕ} (hp : p.Prime) :
    ∀ n k : ℕ, multiplicity p n ≤ multiplicity p (choose n k) + multiplicity p k
  | _, 0 => by
    simp
  | 0, _ + 1 => by
    simp
  | n + 1, k + 1 => by
    rw [← hp.multiplicity_mul]
    refine' multiplicity_le_multiplicity_of_dvd_right _
    rw [← succ_mul_choose_eq]
    exact dvd_mul_right _ _

theorem multiplicity_choose_prime_pow {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : 0 < k) :
    multiplicity p (choose (p ^ n) k) + multiplicity p k = n :=
  le_antisymmₓ
    (by
      have hdisj :
        Disjoint ((ico 1 n.succ).filter fun i => p ^ i ≤ k % p ^ i + (p ^ n - k) % p ^ i)
          ((ico 1 n.succ).filter fun i => p ^ i ∣ k) :=
        by
        simp (config := { contextual := true })[← disjoint_right, *, ← dvd_iff_mod_eq_zero, ←
          Nat.mod_ltₓ _ (pow_pos hp.pos _)]
      rw [multiplicity_choose hp hkn (lt_succ_self _),
        multiplicity_eq_card_pow_dvd (ne_of_gtₓ hp.one_lt) hk0 (lt_succ_of_le (log_mono_right hkn)), ← Nat.cast_addₓ,
        PartEnat.coe_le_coe, log_pow hp.one_lt, ← card_disjoint_union hdisj, filter_union_right]
      have filter_le_Ico := (Ico 1 n.succ).card_filter_le _
      rwa [card_Ico 1 n.succ] at filter_le_Ico)
    (by
      rw [← hp.multiplicity_pow_self] <;> exact multiplicity_le_multiplicity_choose_add hp _ _)

end Prime

theorem multiplicity_two_factorial_lt : ∀ {n : ℕ} (h : n ≠ 0), multiplicity 2 n ! < n := by
  have h2 := prime_iff.mp prime_two
  refine' binary_rec _ _
  · contradiction
    
  · intro b n ih h
    by_cases' hn : n = 0
    · subst hn
      simp at h
      simp [← h, ← one_right h2.not_unit, ← PartEnat.zero_lt_one]
      
    have : multiplicity 2 (2 * n)! < (2 * n : ℕ) := by
      rw [prime_two.multiplicity_factorial_mul]
      refine' (PartEnat.add_lt_add_right (ih hn) (PartEnat.coe_ne_top _)).trans_le _
      rw [two_mul]
      norm_cast
    cases b
    · simpa [← bit0_eq_two_mul n]
      
    · suffices multiplicity 2 (2 * n + 1) + multiplicity 2 (2 * n)! < ↑(2 * n) + 1 by
        simpa [← succ_eq_add_one, ← multiplicity.mul, ← h2, ← prime_two, ← Nat.bit1_eq_succ_bit0, ← bit0_eq_two_mul n]
      rw [multiplicity_eq_zero_of_not_dvd (two_not_dvd_two_mul_add_one n), zero_addₓ]
      refine' this.trans _
      exact_mod_cast lt_succ_self _
      
    

end Nat

