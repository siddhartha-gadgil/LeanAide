/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Nat.Prime

/-!
# Divisor finsets

This file defines sets of divisors of a natural number. This is particularly useful as background
for defining Dirichlet convolution.

## Main Definitions
Let `n : ℕ`. All of the following definitions are in the `nat` namespace:
 * `divisors n` is the `finset` of natural numbers that divide `n`.
 * `proper_divisors n` is the `finset` of natural numbers that divide `n`, other than `n`.
 * `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
 * `perfect n` is true when `n` is positive and the sum of `proper_divisors n` is `n`.

## Implementation details
 * `divisors 0`, `proper_divisors 0`, and `divisors_antidiagonal 0` are defined to be `∅`.

## Tags
divisors, perfect numbers

-/


open Classical

open BigOperators

open Finset

namespace Nat

variable (n : ℕ)

/-- `divisors n` is the `finset` of divisors of `n`. As a special case, `divisors 0 = ∅`. -/
def divisors : Finset ℕ :=
  Finset.filter (fun x : ℕ => x ∣ n) (Finset.ico 1 (n + 1))

/-- `proper_divisors n` is the `finset` of divisors of `n`, other than `n`.
  As a special case, `proper_divisors 0 = ∅`. -/
def properDivisors : Finset ℕ :=
  Finset.filter (fun x : ℕ => x ∣ n) (Finset.ico 1 n)

/-- `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
  As a special case, `divisors_antidiagonal 0 = ∅`. -/
def divisorsAntidiagonal : Finset (ℕ × ℕ) :=
  ((Finset.ico 1 (n + 1)).product (Finset.ico 1 (n + 1))).filter fun x => x.fst * x.snd = n

variable {n}

@[simp]
theorem filter_dvd_eq_divisors (h : n ≠ 0) : (Finset.range n.succ).filter (· ∣ n) = n.divisors := by
  ext
  simp only [← divisors, ← mem_filter, ← mem_range, ← mem_Ico, ← And.congr_left_iff, ← iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)

@[simp]
theorem filter_dvd_eq_proper_divisors (h : n ≠ 0) : (Finset.range n).filter (· ∣ n) = n.properDivisors := by
  ext
  simp only [← proper_divisors, ← mem_filter, ← mem_range, ← mem_Ico, ← And.congr_left_iff, ← iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)

theorem properDivisors.not_self_mem : ¬n ∈ properDivisors n := by
  simp [← proper_divisors]

@[simp]
theorem mem_proper_divisors {m : ℕ} : n ∈ properDivisors m ↔ n ∣ m ∧ n < m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp [← proper_divisors]
    
  simp only [← and_comm, filter_dvd_eq_proper_divisors hm, ← mem_filter, ← mem_range]

theorem divisors_eq_proper_divisors_insert_self_of_pos (h : 0 < n) :
    divisors n = HasInsert.insert n (properDivisors n) := by
  rw [divisors, proper_divisors, Ico_succ_right_eq_insert_Ico h, Finset.filter_insert, if_pos (dvd_refl n)]

@[simp]
theorem mem_divisors {m : ℕ} : n ∈ divisors m ↔ n ∣ m ∧ m ≠ 0 := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp [← divisors]
    
  simp only [← hm, ← Ne.def, ← not_false_iff, ← and_trueₓ, filter_dvd_eq_divisors hm, ← mem_filter, ← mem_range, ←
    and_iff_right_iff_imp, ← lt_succ_iff]
  exact le_of_dvd hm.bot_lt

theorem mem_divisors_self (n : ℕ) (h : n ≠ 0) : n ∈ n.divisors :=
  mem_divisors.2 ⟨dvd_rfl, h⟩

theorem dvd_of_mem_divisors {m : ℕ} (h : n ∈ divisors m) : n ∣ m := by
  cases m
  · apply dvd_zero
    
  · simp [← mem_divisors.1 h]
    

@[simp]
theorem mem_divisors_antidiagonal {x : ℕ × ℕ} : x ∈ divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n ≠ 0 := by
  simp only [← divisors_antidiagonal, ← Finset.mem_Ico, ← Ne.def, ← Finset.mem_filter, ← Finset.mem_product]
  rw [and_comm]
  apply and_congr_right
  rintro rfl
  constructor <;> intro h
  · contrapose! h
    simp [← h]
    
  · rw [Nat.lt_add_one_iff, Nat.lt_add_one_iff]
    rw [mul_eq_zero, Decidable.not_or_iff_and_not] at h
    simp only [← succ_le_of_lt (Nat.pos_of_ne_zeroₓ h.1), ← succ_le_of_lt (Nat.pos_of_ne_zeroₓ h.2), ← true_andₓ]
    exact ⟨le_mul_of_pos_right (Nat.pos_of_ne_zeroₓ h.2), le_mul_of_pos_left (Nat.pos_of_ne_zeroₓ h.1)⟩
    

variable {n}

theorem divisor_le {m : ℕ} : n ∈ divisors m → n ≤ m := by
  cases m
  · simp
    
  simp only [← mem_divisors, ← m.succ_ne_zero, ← and_trueₓ, ← Ne.def, ← not_false_iff]
  exact Nat.le_of_dvdₓ (Nat.succ_posₓ m)

theorem divisors_subset_of_dvd {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) : divisors m ⊆ divisors n :=
  Finset.subset_iff.2 fun x hx => Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans h, hzero⟩

theorem divisors_subset_proper_divisors {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) (hdiff : m ≠ n) :
    divisors m ⊆ properDivisors n := by
  apply Finset.subset_iff.2
  intro x hx
  exact
    Nat.mem_proper_divisors.2
      ⟨(Nat.mem_divisors.1 hx).1.trans h,
        lt_of_le_of_ltₓ (divisor_le hx) (lt_of_le_of_neₓ (divisor_le (Nat.mem_divisors.2 ⟨h, hzero⟩)) hdiff)⟩

@[simp]
theorem divisors_zero : divisors 0 = ∅ := by
  ext
  simp

@[simp]
theorem proper_divisors_zero : properDivisors 0 = ∅ := by
  ext
  simp

theorem proper_divisors_subset_divisors : properDivisors n ⊆ divisors n := by
  cases n
  · simp
    
  rw [divisors_eq_proper_divisors_insert_self_of_pos (Nat.succ_posₓ _)]
  apply subset_insert

@[simp]
theorem divisors_one : divisors 1 = {1} := by
  ext
  simp

@[simp]
theorem proper_divisors_one : properDivisors 1 = ∅ := by
  ext
  simp only [← Finset.not_mem_empty, ← Nat.dvd_one, ← not_and, ← not_ltₓ, ← mem_proper_divisors, ← iff_falseₓ]
  apply ge_of_eq

theorem pos_of_mem_divisors {m : ℕ} (h : m ∈ n.divisors) : 0 < m := by
  cases m
  · rw [mem_divisors, zero_dvd_iff] at h
    cases h.2 h.1
    
  apply Nat.succ_posₓ

theorem pos_of_mem_proper_divisors {m : ℕ} (h : m ∈ n.properDivisors) : 0 < m :=
  pos_of_mem_divisors (proper_divisors_subset_divisors h)

theorem one_mem_proper_divisors_iff_one_lt : 1 ∈ n.properDivisors ↔ 1 < n := by
  rw [mem_proper_divisors, and_iff_right (one_dvd _)]

@[simp]
theorem divisors_antidiagonal_zero : divisorsAntidiagonal 0 = ∅ := by
  ext
  simp

@[simp]
theorem divisors_antidiagonal_one : divisorsAntidiagonal 1 = {(1, 1)} := by
  ext
  simp [← Nat.mul_eq_one_iff, ← Prod.ext_iff]

theorem swap_mem_divisors_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) : x.swap ∈ divisorsAntidiagonal n :=
  by
  rw [mem_divisors_antidiagonal, mul_comm] at h
  simp [← h.1, ← h.2]

theorem fst_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) : x.fst ∈ divisors n := by
  rw [mem_divisors_antidiagonal] at h
  simp [← Dvd.intro _ h.1, ← h.2]

theorem snd_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) : x.snd ∈ divisors n := by
  rw [mem_divisors_antidiagonal] at h
  simp [← Dvd.intro_left _ h.1, ← h.2]

@[simp]
theorem map_swap_divisors_antidiagonal :
    (divisorsAntidiagonal n).map ⟨Prod.swap, Prod.swap_right_inverse.Injective⟩ = divisorsAntidiagonal n := by
  ext
  simp only [← exists_prop, ← mem_divisors_antidiagonal, ← Finset.mem_map, ← Function.Embedding.coe_fn_mk, ← Ne.def, ←
    Prod.swap_prod_mk, ← Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨⟨rfl, h⟩, rfl⟩⟩
    simp [← mul_comm, ← h]
    
  · rintro ⟨rfl, h⟩
    use a.snd, a.fst
    rw [mul_comm]
    simp [← h]
    

theorem sum_divisors_eq_sum_proper_divisors_add_self : (∑ i in divisors n, i) = (∑ i in properDivisors n, i) + n := by
  cases n
  · simp
    
  · rw [divisors_eq_proper_divisors_insert_self_of_pos (Nat.succ_posₓ _),
      Finset.sum_insert proper_divisors.not_self_mem, add_commₓ]
    

/-- `n : ℕ` is perfect if and only the sum of the proper divisors of `n` is `n` and `n`
  is positive. -/
def Perfect (n : ℕ) : Prop :=
  (∑ i in properDivisors n, i) = n ∧ 0 < n

theorem perfect_iff_sum_proper_divisors (h : 0 < n) : Perfect n ↔ (∑ i in properDivisors n, i) = n :=
  and_iff_left h

theorem perfect_iff_sum_divisors_eq_two_mul (h : 0 < n) : Perfect n ↔ (∑ i in divisors n, i) = 2 * n := by
  rw [perfect_iff_sum_proper_divisors h, sum_divisors_eq_sum_proper_divisors_add_self, two_mul]
  constructor <;> intro h
  · rw [h]
    
  · apply add_right_cancelₓ h
    

theorem mem_divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) {x : ℕ} :
    x ∈ divisors (p ^ k) ↔ ∃ (j : ℕ)(H : j ≤ k), x = p ^ j := by
  rw [mem_divisors, Nat.dvd_prime_pow pp, and_iff_left (ne_of_gtₓ (pow_pos pp.pos k))]

theorem Prime.divisors {p : ℕ} (pp : p.Prime) : divisors p = {1, p} := by
  ext
  rw [mem_divisors, dvd_prime pp, and_iff_left pp.ne_zero, Finset.mem_insert, Finset.mem_singleton]

theorem Prime.proper_divisors {p : ℕ} (pp : p.Prime) : properDivisors p = {1} := by
  rw [← erase_insert proper_divisors.not_self_mem, ← divisors_eq_proper_divisors_insert_self_of_pos pp.pos, pp.divisors,
    pair_comm, erase_insert fun con => pp.ne_one (mem_singleton.1 con)]

theorem divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) :
    divisors (p ^ k) = (Finset.range (k + 1)).map ⟨pow p, pow_right_injective pp.two_le⟩ := by
  ext
  simp [← mem_divisors_prime_pow, ← pp, ← Nat.lt_succ_iffₓ, ← @eq_comm _ a]

theorem eq_proper_divisors_of_subset_of_sum_eq_sum {s : Finset ℕ} (hsub : s ⊆ n.properDivisors) :
    ((∑ x in s, x) = ∑ x in n.properDivisors, x) → s = n.properDivisors := by
  cases n
  · rw [proper_divisors_zero, subset_empty] at hsub
    simp [← hsub]
    
  classical
  rw [← sum_sdiff hsub]
  intro h
  apply subset.antisymm hsub
  rw [← sdiff_eq_empty_iff_subset]
  contrapose h
  rw [← Ne.def, ← nonempty_iff_ne_empty] at h
  apply ne_of_ltₓ
  rw [← zero_addₓ (∑ x in s, x), ← add_assocₓ, add_zeroₓ]
  apply add_lt_add_right
  have hlt := sum_lt_sum_of_nonempty h fun x hx => pos_of_mem_proper_divisors (sdiff_subset _ _ hx)
  simp only [← sum_const_zero] at hlt
  apply hlt

theorem sum_proper_divisors_dvd (h : (∑ x in n.properDivisors, x) ∣ n) :
    (∑ x in n.properDivisors, x) = 1 ∨ (∑ x in n.properDivisors, x) = n := by
  cases n
  · simp
    
  cases n
  · contrapose! h
    simp
    
  rw [or_iff_not_imp_right]
  intro ne_n
  have hlt : (∑ x in n.succ.succ.proper_divisors, x) < n.succ.succ :=
    lt_of_le_of_neₓ (Nat.le_of_dvdₓ (Nat.succ_posₓ _) h) ne_n
  symm
  rw [← mem_singleton,
    eq_proper_divisors_of_subset_of_sum_eq_sum (singleton_subset_iff.2 (mem_proper_divisors.2 ⟨h, hlt⟩)) sum_singleton,
    mem_proper_divisors]
  refine' ⟨one_dvd _, Nat.succ_lt_succₓ (Nat.succ_posₓ _)⟩

@[simp, to_additive]
theorem Prime.prod_proper_divisors {α : Type _} [CommMonoidₓ α] {p : ℕ} {f : ℕ → α} (h : p.Prime) :
    (∏ x in p.properDivisors, f x) = f 1 := by
  simp [← h.proper_divisors]

@[simp, to_additive]
theorem Prime.prod_divisors {α : Type _} [CommMonoidₓ α] {p : ℕ} {f : ℕ → α} (h : p.Prime) :
    (∏ x in p.divisors, f x) = f p * f 1 := by
  rw [divisors_eq_proper_divisors_insert_self_of_pos h.pos, prod_insert proper_divisors.not_self_mem,
    h.prod_proper_divisors]

theorem proper_divisors_eq_singleton_one_iff_prime : n.properDivisors = {1} ↔ n.Prime :=
  ⟨fun h => by
    have h1 := mem_singleton.2 rfl
    rw [← h, mem_proper_divisors] at h1
    refine' nat.prime_def_lt''.mpr ⟨h1.2, fun m hdvd => _⟩
    rw [← mem_singleton, ← h, mem_proper_divisors]
    have hle := Nat.le_of_dvdₓ (lt_transₓ (Nat.succ_posₓ _) h1.2) hdvd
    exact Or.imp_left (fun hlt => ⟨hdvd, hlt⟩) hle.lt_or_eq, Prime.proper_divisors⟩

theorem sum_proper_divisors_eq_one_iff_prime : (∑ x in n.properDivisors, x) = 1 ↔ n.Prime := by
  cases n
  · simp [← Nat.not_prime_zero]
    
  cases n
  · simp [← Nat.not_prime_one]
    
  rw [← proper_divisors_eq_singleton_one_iff_prime]
  refine' ⟨fun h => _, fun h => h.symm ▸ sum_singleton⟩
  rw [@eq_comm (Finset ℕ) _ _]
  apply
    eq_proper_divisors_of_subset_of_sum_eq_sum
      (singleton_subset_iff.2 (one_mem_proper_divisors_iff_one_lt.2 (succ_lt_succ (Nat.succ_posₓ _))))
      (Eq.trans sum_singleton h.symm)

theorem mem_proper_divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) {x : ℕ} :
    x ∈ properDivisors (p ^ k) ↔ ∃ (j : ℕ)(H : j < k), x = p ^ j := by
  rw [mem_proper_divisors, Nat.dvd_prime_pow pp, ← exists_and_distrib_right]
  simp only [← exists_prop, ← and_assoc]
  apply exists_congr
  intro a
  constructor <;> intro h
  · rcases h with ⟨h_left, rfl, h_right⟩
    rwa [pow_lt_pow_iff pp.one_lt] at h_right
    simpa
    
  · rcases h with ⟨h_left, rfl⟩
    rwa [pow_lt_pow_iff pp.one_lt]
    simp [← h_left, ← le_of_ltₓ]
    

theorem proper_divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) :
    properDivisors (p ^ k) = (Finset.range k).map ⟨pow p, pow_right_injective pp.two_le⟩ := by
  ext
  simp [← mem_proper_divisors_prime_pow, ← pp, ← Nat.lt_succ_iffₓ, ← @eq_comm _ a]

@[simp, to_additive]
theorem prod_proper_divisors_prime_pow {α : Type _} [CommMonoidₓ α] {k p : ℕ} {f : ℕ → α} (h : p.Prime) :
    (∏ x in (p ^ k).properDivisors, f x) = ∏ x in range k, f (p ^ x) := by
  simp [← h, ← proper_divisors_prime_pow]

@[simp, to_additive sum_divisors_prime_pow]
theorem prod_divisors_prime_pow {α : Type _} [CommMonoidₓ α] {k p : ℕ} {f : ℕ → α} (h : p.Prime) :
    (∏ x in (p ^ k).divisors, f x) = ∏ x in range (k + 1), f (p ^ x) := by
  simp [← h, ← divisors_prime_pow]

@[to_additive]
theorem prod_divisors_antidiagonal {M : Type _} [CommMonoidₓ M] (f : ℕ → ℕ → M) {n : ℕ} :
    (∏ i in n.divisorsAntidiagonal, f i.1 i.2) = ∏ i in n.divisors, f i (n / i) := by
  refine' prod_bij (fun i _ => i.1) _ _ _ _
  · intro i
    apply fst_mem_divisors_of_mem_antidiagonal
    
  · rintro ⟨i, j⟩ hij
    simp only [← mem_divisors_antidiagonal, ← Ne.def] at hij
    rw [← hij.1, Nat.mul_div_cancel_leftₓ]
    apply Nat.pos_of_ne_zeroₓ
    rintro rfl
    simp only [← zero_mul] at hij
    apply hij.2 hij.1.symm
    
  · simp only [← and_imp, ← Prod.forall, ← mem_divisors_antidiagonal, ← Ne.def]
    rintro i₁ j₁ ⟨i₂, j₂⟩ h - (rfl : i₂ * j₂ = _) h₁ (rfl : _ = i₂)
    simp only [← Nat.mul_eq_zero, ← not_or_distrib, Ne.def] at h₁
    rw [mul_right_inj' h₁.1] at h
    simp [← h]
    
  simp only [← and_imp, ← exists_prop, ← mem_divisors_antidiagonal, ← exists_and_distrib_right, ← Ne.def, ←
    exists_eq_right', ← mem_divisors, ← Prod.exists]
  rintro _ ⟨k, rfl⟩ hn
  exact ⟨⟨k, rfl⟩, hn⟩

@[to_additive]
theorem prod_divisors_antidiagonal' {M : Type _} [CommMonoidₓ M] (f : ℕ → ℕ → M) {n : ℕ} :
    (∏ i in n.divisorsAntidiagonal, f i.1 i.2) = ∏ i in n.divisors, f (n / i) i := by
  rw [← map_swap_divisors_antidiagonal, Finset.prod_map]
  exact prod_divisors_antidiagonal fun i j => f j i

/-- The factors of `n` are the prime divisors -/
theorem prime_divisors_eq_to_filter_divisors_prime (n : ℕ) : n.factors.toFinset = (divisors n).filter Prime := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
    
  · ext q
    simpa [← hn, ← hn.ne', ← mem_factors] using and_comm (Prime q) (q ∣ n)
    

@[simp]
theorem image_div_divisors_eq_divisors (n : ℕ) : image (fun x : ℕ => n / x) n.divisors = n.divisors := by
  by_cases' hn : n = 0
  · simp [← hn]
    
  ext
  constructor
  · rw [mem_image]
    rintro ⟨x, hx1, hx2⟩
    rw [mem_divisors] at *
    refine' ⟨_, hn⟩
    rw [← hx2]
    exact div_dvd_of_dvd hx1.1
    
  · rw [mem_divisors, mem_image]
    rintro ⟨h1, -⟩
    exact ⟨n / a, mem_divisors.mpr ⟨div_dvd_of_dvd h1, hn⟩, Nat.div_div_self h1 (pos_iff_ne_zero.mpr hn)⟩
    

@[simp, to_additive sum_div_divisors]
theorem prod_div_divisors {α : Type _} [CommMonoidₓ α] (n : ℕ) (f : ℕ → α) :
    (∏ d in n.divisors, f (n / d)) = n.divisors.Prod f := by
  by_cases' hn : n = 0
  · simp [← hn]
    
  rw [← prod_image]
  · exact
      prod_congr (image_div_divisors_eq_divisors n)
        (by
          simp )
    
  · intro x hx y hy h
    rw [mem_divisors] at hx hy
    exact (div_eq_iff_eq_of_dvd_dvd hn hx.1 hy.1).mp h
    

end Nat

