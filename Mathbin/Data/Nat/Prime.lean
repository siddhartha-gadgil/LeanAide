/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathbin.Data.List.Prime
import Mathbin.Data.List.Sort
import Mathbin.Data.Nat.Gcd
import Mathbin.Data.Nat.SqrtNormNum
import Mathbin.Data.Set.Finite
import Mathbin.Tactic.Wlog
import Mathbin.Algebra.Parity

/-!
# Prime numbers

This file deals with prime numbers: natural numbers `p ≥ 2` whose only divisors are `p` and `1`.

## Important declarations

- `nat.prime`: the predicate that expresses that a natural number `p` is prime
- `nat.primes`: the subtype of natural numbers that are prime
- `nat.min_fac n`: the minimal prime factor of a natural number `n ≠ 1`
- `nat.exists_infinite_primes`: Euclid's theorem that there exist infinitely many prime numbers.
  This also appears as `nat.not_bdd_above_set_of_prime` and `nat.infinite_set_of_prime`.
- `nat.factors n`: the prime factorization of `n`
- `nat.factors_unique`: uniqueness of the prime factorisation
- `nat.prime_iff`: `nat.prime` coincides with the general definition of `prime`
- `nat.irreducible_iff_prime`: a non-unit natural number is only divisible by `1` iff it is prime

-/


open Bool Subtype

open Nat

namespace Nat

/-- `prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`. -/
@[pp_nodot]
def Prime (p : ℕ) :=
  Irreducible p

theorem _root_.irreducible_iff_nat_prime (a : ℕ) : Irreducible a ↔ Nat.Prime a :=
  Iff.rfl

theorem not_prime_zero : ¬Prime 0
  | h => h.ne_zero rfl

theorem not_prime_one : ¬Prime 1
  | h => h.ne_one rfl

theorem Prime.ne_zero {n : ℕ} (h : Prime n) : n ≠ 0 :=
  Irreducible.ne_zero h

theorem Prime.pos {p : ℕ} (pp : Prime p) : 0 < p :=
  Nat.pos_of_ne_zeroₓ pp.ne_zero

theorem Prime.two_le : ∀ {p : ℕ}, Prime p → 2 ≤ p
  | 0, h => (not_prime_zero h).elim
  | 1, h => (not_prime_one h).elim
  | n + 2, _ => le_add_self

theorem Prime.one_lt {p : ℕ} : Prime p → 1 < p :=
  prime.two_le

instance Prime.one_lt' (p : ℕ) [hp : Fact p.Prime] : Fact (1 < p) :=
  ⟨hp.1.one_lt⟩

theorem Prime.ne_one {p : ℕ} (hp : p.Prime) : p ≠ 1 :=
  hp.one_lt.ne'

theorem Prime.eq_one_or_self_of_dvd {p : ℕ} (pp : p.Prime) (m : ℕ) (hm : m ∣ p) : m = 1 ∨ m = p := by
  obtain ⟨n, hn⟩ := hm
  have := pp.is_unit_or_is_unit hn
  rw [Nat.is_unit_iff, Nat.is_unit_iff] at this
  apply Or.imp_rightₓ _ this
  rintro rfl
  rw [hn, mul_oneₓ]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (m «expr ∣ » p)
theorem prime_def_lt'' {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ (m) (_ : m ∣ p), m = 1 ∨ m = p := by
  refine' ⟨fun h => ⟨h.two_le, h.eq_one_or_self_of_dvd⟩, fun h => _⟩
  have h1 := one_lt_two.trans_le h.1
  refine' ⟨mt nat.is_unit_iff.mp h1.ne', fun a b hab => _⟩
  simp only [← Nat.is_unit_iff]
  apply Or.imp_rightₓ _ (h.2 a _)
  · rintro rfl
    rw [← Nat.mul_right_inj (pos_of_gt h1), ← hab, mul_oneₓ]
    
  · rw [hab]
    exact dvd_mul_right _ _
    

theorem prime_def_lt {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀, ∀ m < p, ∀, m ∣ p → m = 1 :=
  prime_def_lt''.trans <|
    and_congr_right fun p2 =>
      forall_congrₓ fun m =>
        ⟨fun h l d => (h d).resolve_right (ne_of_ltₓ l), fun h d =>
          (le_of_dvdₓ (le_of_succ_leₓ p2) d).lt_or_eq_dec.imp_left fun l => h l d⟩

theorem prime_def_lt' {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m < p → ¬m ∣ p :=
  prime_def_lt.trans <|
    and_congr_right fun p2 =>
      forall_congrₓ fun m =>
        ⟨fun h m2 l d =>
          not_lt_of_geₓ m2
            ((h l d).symm ▸ by
              decide),
          fun h l d => by
          rcases m with (_ | _ | m)
          · rw [eq_zero_of_zero_dvd d] at p2
            revert p2
            exact by
              decide
            
          · rfl
            
          · exact
              (h
                    (by
                      decide)
                    l).elim
                d
            ⟩

theorem prime_def_le_sqrt {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m ≤ sqrt p → ¬m ∣ p :=
  prime_def_lt'.trans <|
    and_congr_right fun p2 =>
      ⟨fun a m m2 l => a m m2 <| lt_of_le_of_ltₓ l <| sqrt_lt_self p2, fun a =>
        have : ∀ {m k}, m ≤ k → 1 < m → p ≠ m * k := fun m k mk m1 e =>
          a m m1 (le_sqrt.2 (e.symm ▸ Nat.mul_le_mul_leftₓ m mk)) ⟨k, e⟩
        fun m m2 l ⟨k, e⟩ => by
        cases' le_totalₓ m k with mk km
        · exact this mk m2 e
          
        · rw [mul_comm] at e
          refine' this km (lt_of_mul_lt_mul_right _ (zero_le m)) e
          rwa [one_mulₓ, ← e]
          ⟩

theorem prime_of_coprime (n : ℕ) (h1 : 1 < n) (h : ∀, ∀ m < n, ∀, m ≠ 0 → n.Coprime m) : Prime n := by
  refine' prime_def_lt.mpr ⟨h1, fun m mlt mdvd => _⟩
  have hm : m ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at mdvd
    exact mlt.ne' mdvd
  exact (h m mlt hm).symm.eq_one_of_dvd mdvd

section

/-- This instance is slower than the instance `decidable_prime` defined below,
  but has the advantage that it works in the kernel for small values.

  If you need to prove that a particular number is prime, in any case
  you should not use `dec_trivial`, but rather `by norm_num`, which is
  much faster.
  -/
@[local instance]
def decidablePrime1 (p : ℕ) : Decidable (Prime p) :=
  decidableOfIff' _ prime_def_lt'

theorem prime_two : Prime 2 := by
  decide

end

theorem Prime.pred_pos {p : ℕ} (pp : Prime p) : 0 < pred p :=
  lt_pred_iff.2 pp.one_lt

theorem succ_pred_prime {p : ℕ} (pp : Prime p) : succ (pred p) = p :=
  succ_pred_eq_of_posₓ pp.Pos

theorem dvd_prime {p m : ℕ} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
  ⟨fun d => pp.eq_one_or_self_of_dvd m d, fun h => h.elim (fun e => e.symm ▸ one_dvd _) fun e => e.symm ▸ dvd_rfl⟩

theorem dvd_prime_two_le {p m : ℕ} (pp : Prime p) (H : 2 ≤ m) : m ∣ p ↔ m = p :=
  (dvd_prime pp).trans <| or_iff_right_of_imp <| Not.elim <| ne_of_gtₓ H

theorem prime_dvd_prime_iff_eq {p q : ℕ} (pp : p.Prime) (qp : q.Prime) : p ∣ q ↔ p = q :=
  dvd_prime_two_le qp (Prime.two_le pp)

theorem Prime.not_dvd_one {p : ℕ} (pp : Prime p) : ¬p ∣ 1 :=
  pp.not_dvd_one

theorem not_prime_mul {a b : ℕ} (a1 : 1 < a) (b1 : 1 < b) : ¬Prime (a * b) := fun h =>
  ne_of_ltₓ (Nat.mul_lt_mul_of_pos_leftₓ b1 (lt_of_succ_ltₓ a1)) <| by
    simpa using (dvd_prime_two_le h a1).1 (dvd_mul_right _ _)

theorem not_prime_mul' {a b n : ℕ} (h : a * b = n) (h₁ : 1 < a) (h₂ : 1 < b) : ¬Prime n := by
  rw [← h]
  exact not_prime_mul h₁ h₂

theorem prime_mul_iff {a b : ℕ} : Nat.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime ∧ a = 1 := by
  simp only [← iff_selfₓ, ← irreducible_mul_iff, irreducible_iff_nat_prime, ← Nat.is_unit_iff]

theorem Prime.dvd_iff_eq {p a : ℕ} (hp : p.Prime) (a1 : a ≠ 1) : a ∣ p ↔ p = a := by
  refine'
    ⟨_, by
      rintro rfl
      rfl⟩
  -- rintro ⟨j, rfl⟩ does not work, due to `nat.prime` depending on the class `irreducible`
  rintro ⟨j, hj⟩
  rw [hj] at hp⊢
  rcases prime_mul_iff.mp hp with (⟨h, rfl⟩ | ⟨h, rfl⟩)
  · exact mul_oneₓ _
    
  · exact (a1 rfl).elim
    

section MinFac

theorem min_fac_lemma (n k : ℕ) (h : ¬n < k * k) : sqrt n - k < sqrt n + 2 - k :=
  (tsub_lt_tsub_iff_right <| le_sqrt.2 <| le_of_not_gtₓ h).2 <|
    Nat.lt_add_of_pos_rightₓ
      (by
        decide)

/-- If `n < k * k`, then `min_fac_aux n k = n`, if `k | n`, then `min_fac_aux n k = k`.
  Otherwise, `min_fac_aux n k = min_fac_aux n (k+2)` using well-founded recursion.
  If `n` is odd and `1 < n`, then then `min_fac_aux n 3` is the smallest prime factor of `n`. -/
def minFacAux (n : ℕ) : ℕ → ℕ
  | k =>
    if h : n < k * k then n
    else
      if k ∣ n then k
      else
        have := min_fac_lemma n k h
        min_fac_aux (k + 2)

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def minFac : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => if 2 ∣ n then 2 else minFacAux (n + 2) 3

@[simp]
theorem min_fac_zero : minFac 0 = 2 :=
  rfl

@[simp]
theorem min_fac_one : minFac 1 = 1 :=
  rfl

theorem min_fac_eq : ∀ n, minFac n = if 2 ∣ n then 2 else minFacAux n 3
  | 0 => by
    simp
  | 1 => by
    simp [←
        show 2 ≠ 1 by
          decide] <;>
      rw [min_fac_aux] <;> rfl
  | n + 2 => by
    have : 2 ∣ n + 2 ↔ 2 ∣ n :=
      (Nat.dvd_add_iff_left
          (by
            rfl)).symm
    simp [← min_fac, ← this] <;> congr

private def min_fac_prop (n k : ℕ) :=
  2 ≤ k ∧ k ∣ n ∧ ∀ m, 2 ≤ m → m ∣ n → k ≤ m

theorem min_fac_aux_has_prop {n : ℕ} (n2 : 2 ≤ n) :
    ∀ k i, k = 2 * i + 3 → (∀ m, 2 ≤ m → m ∣ n → k ≤ m) → MinFacProp n (minFacAux n k)
  | k => fun i e a => by
    rw [min_fac_aux]
    by_cases' h : n < k * k <;> simp [← h]
    · have pp : Prime n :=
        prime_def_le_sqrt.2 ⟨n2, fun m m2 l d => not_lt_of_geₓ l <| lt_of_lt_of_leₓ (sqrt_lt.2 h) (a m m2 d)⟩
      exact ⟨n2, dvd_rfl, fun m m2 d => le_of_eqₓ ((dvd_prime_two_le pp m2).1 d).symm⟩
      
    have k2 : 2 ≤ k := by
      subst e
      exact by
        decide
    by_cases' dk : k ∣ n <;> simp [← dk]
    · exact ⟨k2, dk, a⟩
      
    · refine'
        have := min_fac_lemma n k h
        min_fac_aux_has_prop (k + 2) (i + 1)
          (by
            simp [← e, ← left_distrib])
          fun m m2 d => _
      cases' Nat.eq_or_lt_of_leₓ (a m m2 d) with me ml
      · subst me
        contradiction
        
      apply (Nat.eq_or_lt_of_leₓ ml).resolve_left
      intro me
      rw [← me, e] at d
      change 2 * (i + 2) ∣ n at d
      have := a _ le_rfl (dvd_of_mul_right_dvd d)
      rw [e] at this
      exact
        absurd this
          (by
            decide)
      

theorem min_fac_has_prop {n : ℕ} (n1 : n ≠ 1) : MinFacProp n (minFac n) := by
  by_cases' n0 : n = 0
  · simp [← n0, ← min_fac_prop, ← Ge]
    
  have n2 : 2 ≤ n := by
    revert n0 n1
    rcases n with (_ | _ | _) <;>
      exact by
        decide
  simp [← min_fac_eq]
  by_cases' d2 : 2 ∣ n <;> simp [← d2]
  · exact ⟨le_rfl, d2, fun k k2 d => k2⟩
    
  · refine' min_fac_aux_has_prop n2 3 0 rfl fun m m2 d => (Nat.eq_or_lt_of_leₓ m2).resolve_left (mt _ d2)
    exact fun e => e.symm ▸ d
    

theorem min_fac_dvd (n : ℕ) : minFac n ∣ n :=
  if n1 : n = 1 then by
    simp [← n1]
  else (min_fac_has_prop n1).2.1

theorem min_fac_prime {n : ℕ} (n1 : n ≠ 1) : Prime (minFac n) :=
  let ⟨f2, fd, a⟩ := min_fac_has_prop n1
  prime_def_lt'.2 ⟨f2, fun m m2 l d => not_le_of_gtₓ l (a m m2 (d.trans fd))⟩

theorem min_fac_le_of_dvd {n : ℕ} : ∀ {m : ℕ}, 2 ≤ m → m ∣ n → minFac n ≤ m := by
  by_cases' n1 : n = 1 <;>
    [exact fun m m2 d =>
      n1.symm ▸
        le_transₓ
          (by
            decide)
          m2,
    exact (min_fac_has_prop n1).2.2]

theorem min_fac_pos (n : ℕ) : 0 < minFac n := by
  by_cases' n1 : n = 1 <;>
    [exact
      n1.symm ▸ by
        decide,
    exact (min_fac_prime n1).Pos]

theorem min_fac_le {n : ℕ} (H : 0 < n) : minFac n ≤ n :=
  le_of_dvdₓ H (min_fac_dvd n)

theorem le_min_fac {m n : ℕ} : n = 1 ∨ m ≤ minFac n ↔ ∀ p, Prime p → p ∣ n → m ≤ p :=
  ⟨fun h p pp d =>
    h.elim
      (by
        rintro rfl <;> cases pp.not_dvd_one d)
      fun h => le_transₓ h <| min_fac_le_of_dvd pp.two_le d,
    fun H => or_iff_not_imp_left.2 fun n1 => H _ (min_fac_prime n1) (min_fac_dvd _)⟩

theorem le_min_fac' {m n : ℕ} : n = 1 ∨ m ≤ minFac n ↔ ∀ p, 2 ≤ p → p ∣ n → m ≤ p :=
  ⟨fun h p (pp : 1 < p) d =>
    h.elim
      (by
        rintro rfl <;>
          cases
            not_le_of_lt pp
              (le_of_dvd
                (by
                  decide)
                d))
      fun h => le_transₓ h <| min_fac_le_of_dvd pp d,
    fun H => le_min_fac.2 fun p pp d => H p pp.two_le d⟩

theorem prime_def_min_fac {p : ℕ} : Prime p ↔ 2 ≤ p ∧ minFac p = p :=
  ⟨fun pp =>
    ⟨pp.two_le,
      let ⟨f2, fd, a⟩ := min_fac_has_prop <| ne_of_gtₓ pp.one_lt
      ((dvd_prime pp).1 fd).resolve_left (ne_of_gtₓ f2)⟩,
    fun ⟨p2, e⟩ => e ▸ min_fac_prime (ne_of_gtₓ p2)⟩

@[simp]
theorem Prime.min_fac_eq {p : ℕ} (hp : Prime p) : minFac p = p :=
  (prime_def_min_fac.1 hp).2

/-- This instance is faster in the virtual machine than `decidable_prime_1`,
but slower in the kernel.

If you need to prove that a particular number is prime, in any case
you should not use `dec_trivial`, but rather `by norm_num`, which is
much faster.
-/
instance decidablePrime (p : ℕ) : Decidable (Prime p) :=
  decidableOfIff' _ prime_def_min_fac

theorem not_prime_iff_min_fac_lt {n : ℕ} (n2 : 2 ≤ n) : ¬Prime n ↔ minFac n < n :=
  (not_congr <| prime_def_min_fac.trans <| and_iff_right n2).trans <|
    (lt_iff_le_and_ne.trans <| and_iff_right <| min_fac_le <| le_of_succ_leₓ n2).symm

theorem min_fac_le_div {n : ℕ} (pos : 0 < n) (np : ¬Prime n) : minFac n ≤ n / minFac n :=
  match min_fac_dvd n with
  | ⟨0, h0⟩ =>
    absurd Pos <| by
      rw [h0, mul_zero] <;>
        exact by
          decide
  | ⟨1, h1⟩ => by
    rw [mul_oneₓ] at h1
    rw [prime_def_min_fac, not_and_distrib, ← h1, eq_self_iff_true, not_true, or_falseₓ, not_leₓ] at np
    rw [le_antisymmₓ (le_of_lt_succ np) (succ_le_of_lt Pos), min_fac_one, Nat.div_oneₓ]
  | ⟨x + 2, hx⟩ => by
    conv_rhs => congr rw [hx]
    rw [Nat.mul_div_cancel_leftₓ _ (min_fac_pos _)]
    exact
      min_fac_le_of_dvd
        (by
          decide)
        ⟨min_fac n, by
          rwa [mul_comm]⟩

/-- The square of the smallest prime factor of a composite number `n` is at most `n`.
-/
theorem min_fac_sq_le_self {n : ℕ} (w : 0 < n) (h : ¬Prime n) : minFac n ^ 2 ≤ n :=
  have t : minFac n ≤ n / minFac n := min_fac_le_div w h
  calc
    minFac n ^ 2 = minFac n * minFac n := sq (minFac n)
    _ ≤ n / minFac n * minFac n := Nat.mul_le_mul_rightₓ (minFac n) t
    _ ≤ n := div_mul_le_selfₓ n (minFac n)
    

@[simp]
theorem min_fac_eq_one_iff {n : ℕ} : minFac n = 1 ↔ n = 1 := by
  constructor
  · intro h
    by_contra hn
    have := min_fac_prime hn
    rw [h] at this
    exact not_prime_one this
    
  · rintro rfl
    rfl
    

@[simp]
theorem min_fac_eq_two_iff (n : ℕ) : minFac n = 2 ↔ 2 ∣ n := by
  constructor
  · intro h
    convert min_fac_dvd _
    rw [h]
    
  · intro h
    have ub := min_fac_le_of_dvd (le_reflₓ 2) h
    have lb := min_fac_pos n
    apply ub.eq_or_lt.resolve_right fun h' => _
    have := le_antisymmₓ (Nat.succ_le_of_ltₓ lb) (lt_succ_iff.mp h')
    rw [eq_comm, Nat.min_fac_eq_one_iff] at this
    subst this
    exact not_lt_of_le (le_of_dvd zero_lt_one h) one_lt_two
    

end MinFac

theorem exists_dvd_of_not_prime {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
  ⟨minFac n, min_fac_dvd _, ne_of_gtₓ (min_fac_prime (ne_of_gtₓ n2)).one_lt,
    ne_of_ltₓ <| (not_prime_iff_min_fac_lt n2).1 np⟩

theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) : ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
  ⟨minFac n, min_fac_dvd _, (min_fac_prime (ne_of_gtₓ n2)).two_le, (not_prime_iff_min_fac_lt n2).1 np⟩

theorem exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, Prime p ∧ p ∣ n :=
  ⟨minFac n, min_fac_prime hn, min_fac_dvd _⟩

/-- Euclid's theorem on the **infinitude of primes**.
Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Prime p :=
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := ne_of_gtₓ <| succ_lt_succ <| factorial_pos _
  have pp : Prime p := min_fac_prime f1
  have np : n ≤ p :=
    le_of_not_geₓ fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (min_fac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (min_fac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩

/-- A version of `nat.exists_infinite_primes` using the `bdd_above` predicate. -/
theorem not_bdd_above_set_of_prime : ¬BddAbove { p | Prime p } := by
  rw [not_bdd_above_iff]
  intro n
  obtain ⟨p, hi, hp⟩ := exists_infinite_primes n.succ
  exact ⟨p, hp, hi⟩

/-- A version of `nat.exists_infinite_primes` using the `set.infinite` predicate. -/
theorem infinite_set_of_prime : { p | Prime p }.Infinite :=
  Set.infinite_of_not_bdd_above not_bdd_above_set_of_prime

theorem Prime.eq_two_or_odd {p : ℕ} (hp : Prime p) : p = 2 ∨ p % 2 = 1 :=
  p.mod_two_eq_zero_or_one.imp_left fun h =>
    ((hp.eq_one_or_self_of_dvd 2 (dvd_of_mod_eq_zeroₓ h)).resolve_left
        (by
          decide)).symm

theorem Prime.eq_two_or_odd' {p : ℕ} (hp : Prime p) : p = 2 ∨ Odd p :=
  Or.imp_rightₓ (fun h => ⟨p / 2, (div_add_modₓ p 2).symm.trans (congr_arg _ h)⟩) hp.eq_two_or_odd

theorem Prime.even_iff {p : ℕ} (hp : Prime p) : Even p ↔ p = 2 := by
  rw [even_iff_two_dvd, prime_dvd_prime_iff_eq prime_two hp, eq_comm]

/-- A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`. -/
theorem Prime.mod_two_eq_one_iff_ne_two {p : ℕ} [Fact p.Prime] : p % 2 = 1 ↔ p ≠ 2 := by
  refine' ⟨fun h hf => _, (Nat.Prime.eq_two_or_odd <| Fact.out p.prime).resolve_left⟩
  rw [hf] at h
  simpa using h

theorem coprime_of_dvd {m n : ℕ} (H : ∀ k, Prime k → k ∣ m → ¬k ∣ n) : Coprime m n := by
  rw [coprime_iff_gcd_eq_one]
  by_contra g2
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2
  apply H p hp <;> apply dvd_trans hpdvd
  · exact gcd_dvd_left _ _
    
  · exact gcd_dvd_right _ _
    

theorem coprime_of_dvd' {m n : ℕ} (H : ∀ k, Prime k → k ∣ m → k ∣ n → k ∣ 1) : Coprime m n :=
  coprime_of_dvd fun k kp km kn => not_le_of_gtₓ kp.one_lt <| le_of_dvdₓ zero_lt_one <| H k kp km kn

theorem factors_lemma {k} : (k + 2) / minFac (k + 2) < k + 2 :=
  div_lt_selfₓ
    (by
      decide)
    (min_fac_prime
        (by
          decide)).one_lt

/-- `factors n` is the prime factorization of `n`, listed in increasing order. -/
def factors : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | n@(k + 2) =>
    let m := minFac n
    have : n / m < n := factors_lemma
    m :: factors (n / m)

@[simp]
theorem factors_zero : factors 0 = [] := by
  rw [factors]

@[simp]
theorem factors_one : factors 1 = [] := by
  rw [factors]

theorem prime_of_mem_factors : ∀ {n p}, p ∈ factors n → Prime p
  | 0 => by
    simp
  | 1 => by
    simp
  | n@(k + 2) => fun p h =>
    let m := minFac n
    have : n / m < n := factors_lemma
    have h₁ : p = m ∨ p ∈ factors (n / m) :=
      (List.mem_cons_iff _ _ _).1
        (by
          rwa [factors] at h)
    Or.cases_on h₁
      (fun h₂ =>
        h₂.symm ▸
          min_fac_prime
            (by
              decide))
      prime_of_mem_factors

theorem pos_of_mem_factors {n p : ℕ} (h : p ∈ factors n) : 0 < p :=
  Prime.pos (prime_of_mem_factors h)

theorem prod_factors : ∀ {n}, n ≠ 0 → List.prod (factors n) = n
  | 0 => by
    simp
  | 1 => by
    simp
  | n@(k + 2) => fun h =>
    let m := minFac n
    have : n / m < n := factors_lemma
    show (factors n).Prod = n by
      have h₁ : n / m ≠ 0 := fun h => by
        have : n = 0 * m := (Nat.div_eq_iff_eq_mul_left (min_fac_pos _) (min_fac_dvd _)).1 h
        rw [zero_mul] at this <;>
          exact
            (show k + 2 ≠ 0 by
                decide)
              this
      rw [factors, List.prod_cons, prod_factors h₁, Nat.mul_div_cancel'ₓ (min_fac_dvd _)]

theorem factors_prime {p : ℕ} (hp : Nat.Prime p) : p.factors = [p] := by
  have : p = p - 2 + 2 := (tsub_eq_iff_eq_add_of_le hp.two_le).mp rfl
  rw [this, Nat.factors]
  simp only [← Eq.symm this]
  have : Nat.minFac p = p := (nat.prime_def_min_fac.mp hp).2
  constructor
  · exact this
    
  · simp only [← this, ← Nat.factors, ← Nat.div_selfₓ (Nat.Prime.pos hp)]
    

theorem factors_chain : ∀ {n a}, (∀ p, Prime p → p ∣ n → a ≤ p) → List.Chain (· ≤ ·) a (factors n)
  | 0 => fun a h => by
    simp
  | 1 => fun a h => by
    simp
  | n@(k + 2) => fun a h => by
    let m := minFac n
    have : n / m < n := factors_lemma
    rw [factors]
    refine'
      List.Chain.cons
        ((le_min_fac.2 h).resolve_left
          (by
            decide))
        (factors_chain _)
    exact fun p pp d => min_fac_le_of_dvd pp.two_le (d.trans <| div_dvd_of_dvd <| min_fac_dvd _)

theorem factors_chain_2 (n) : List.Chain (· ≤ ·) 2 (factors n) :=
  factors_chain fun p pp _ => pp.two_le

theorem factors_chain' (n) : List.Chain' (· ≤ ·) (factors n) :=
  @List.Chain'.tail _ _ (_ :: _) (factors_chain_2 _)

theorem factors_sorted (n : ℕ) : List.Sorted (· ≤ ·) (factors n) :=
  (List.chain'_iff_pairwise (@le_transₓ _ _)).1 (factors_chain' _)

/-- `factors` can be constructed inductively by extracting `min_fac`, for sufficiently large `n`. -/
theorem factors_add_two (n : ℕ) : factors (n + 2) = minFac (n + 2) :: factors ((n + 2) / minFac (n + 2)) := by
  rw [factors]

@[simp]
theorem factors_eq_nil (n : ℕ) : n.factors = [] ↔ n = 0 ∨ n = 1 := by
  constructor <;> intro h
  · rcases n with (_ | _ | n)
    · exact Or.inl rfl
      
    · exact Or.inr rfl
      
    · rw [factors] at h
      injection h
      
    
  · rcases h with (rfl | rfl)
    · exact factors_zero
      
    · exact factors_one
      
    

theorem eq_of_perm_factors {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a.factors ~ b.factors) : a = b := by
  simpa [← prod_factors ha, ← prod_factors hb] using List.Perm.prod_eq h

theorem Prime.coprime_iff_not_dvd {p n : ℕ} (pp : Prime p) : Coprime p n ↔ ¬p ∣ n :=
  ⟨fun co d =>
    pp.not_dvd_one <|
      co.dvd_of_dvd_mul_left
        (by
          simp [← d]),
    fun nd => coprime_of_dvd fun m m2 mp => ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩

theorem Prime.dvd_iff_not_coprime {p n : ℕ} (pp : Prime p) : p ∣ n ↔ ¬Coprime p n :=
  iff_not_comm.2 pp.coprime_iff_not_dvd

theorem Prime.not_coprime_iff_dvd {m n : ℕ} : ¬Coprime m n ↔ ∃ p, Prime p ∧ p ∣ m ∧ p ∣ n := by
  apply Iff.intro
  · intro h
    exact
      ⟨min_fac (gcd m n), min_fac_prime h, (min_fac_dvd (gcd m n)).trans (gcd_dvd_left m n),
        (min_fac_dvd (gcd m n)).trans (gcd_dvd_right m n)⟩
    
  · intro h
    cases' h with p hp
    apply Nat.not_coprime_of_dvd_of_dvdₓ (prime.one_lt hp.1) hp.2.1 hp.2.2
    

theorem Prime.dvd_mul {p m n : ℕ} (pp : Prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
  ⟨fun H => or_iff_not_imp_left.2 fun h => (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
    Or.ndrec (fun h : p ∣ m => h.mul_right _) fun h : p ∣ n => h.mul_left _⟩

theorem Prime.not_dvd_mul {p m n : ℕ} (pp : Prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n) : ¬p ∣ m * n :=
  mt pp.dvd_mul.1 <| by
    simp [← Hm, ← Hn]

theorem prime_iff {p : ℕ} : p.Prime ↔ Prime p :=
  ⟨fun h => ⟨h.ne_zero, h.not_unit, fun a b => h.dvd_mul.mp⟩, Prime.irreducible⟩

theorem irreducible_iff_prime {p : ℕ} : Irreducible p ↔ Prime p := by
  rw [← prime_iff, Prime]

theorem Prime.dvd_of_dvd_pow {p m n : ℕ} (pp : Prime p) (h : p ∣ m ^ n) : p ∣ m := by
  induction' n with n IH
  · exact pp.not_dvd_one.elim h
    
  · rw [pow_succₓ] at h
    exact (pp.dvd_mul.1 h).elim id IH
    

theorem Prime.pow_not_prime {x n : ℕ} (hn : 2 ≤ n) : ¬(x ^ n).Prime := fun hp =>
  (hp.eq_one_or_self_of_dvd x <| dvd_trans ⟨x, sq _⟩ (pow_dvd_pow _ hn)).elim
    (fun hx1 => hp.ne_one <| hx1.symm ▸ one_pow _) fun hxn =>
    lt_irreflₓ x <|
      calc
        x = x ^ 1 := (pow_oneₓ _).symm
        _ < x ^ n := Nat.pow_right_strict_mono (hxn.symm ▸ hp.two_le) hn
        _ = x := hxn.symm
        

theorem Prime.pow_not_prime' {x : ℕ} : ∀ {n : ℕ}, n ≠ 1 → ¬(x ^ n).Prime
  | 0 => fun _ => not_prime_one
  | 1 => fun h => (h rfl).elim
  | n + 2 => fun _ => Prime.pow_not_prime le_add_self

theorem Prime.eq_one_of_pow {x n : ℕ} (h : (x ^ n).Prime) : n = 1 :=
  not_imp_not.mp Prime.pow_not_prime' h

theorem Prime.pow_eq_iff {p a k : ℕ} (hp : p.Prime) : a ^ k = p ↔ a = p ∧ k = 1 := by
  refine'
    ⟨fun h => _, fun h => by
      rw [h.1, h.2, pow_oneₓ]⟩
  rw [← h] at hp
  rw [← h, hp.eq_one_of_pow, eq_self_iff_true, and_trueₓ, pow_oneₓ]

theorem pow_min_fac {n k : ℕ} (hk : k ≠ 0) : (n ^ k).minFac = n.minFac := by
  rcases eq_or_ne n 1 with (rfl | hn)
  · simp
    
  have hnk : n ^ k ≠ 1 := fun hk' => hn ((pow_eq_one_iff hk).1 hk')
  apply (min_fac_le_of_dvd (min_fac_prime hn).two_le ((min_fac_dvd n).pow hk)).antisymm
  apply min_fac_le_of_dvd (min_fac_prime hnk).two_le ((min_fac_prime hnk).dvd_of_dvd_pow (min_fac_dvd _))

theorem Prime.pow_min_fac {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : (p ^ k).minFac = p := by
  rw [pow_min_fac hk, hp.min_fac_eq]

theorem Prime.mul_eq_prime_sq_iff {x y p : ℕ} (hp : p.Prime) (hx : x ≠ 1) (hy : y ≠ 1) :
    x * y = p ^ 2 ↔ x = p ∧ y = p :=
  ⟨fun h => by
    have pdvdxy : p ∣ x * y := by
      rw [h] <;> simp [← sq]
    wlog := hp.dvd_mul.1 pdvdxy using x y
    cases' case with a ha
    have hap : a ∣ p :=
      ⟨y, by
        rwa [ha, sq, mul_assoc, Nat.mul_right_inj hp.pos, eq_comm] at h⟩
    exact
      ((Nat.dvd_prime hp).1 hap).elim
        (fun _ => by
          clear_aux_decl <;> simp_all (config := { contextual := true })[← sq, ← Nat.mul_right_inj hp.pos])
        fun _ => by
        clear_aux_decl <;>
          simp_all (config := { contextual := true })[← sq, ← mul_comm, ← mul_assoc, ← Nat.mul_right_inj hp.pos, ←
            Nat.mul_right_eq_self_iff hp.pos],
    fun ⟨h₁, h₂⟩ => h₁.symm ▸ h₂.symm ▸ (sq _).symm⟩

theorem Prime.dvd_factorial : ∀ {n p : ℕ} (hp : Prime p), p ∣ n ! ↔ p ≤ n
  | 0, p, hp => iff_of_false hp.not_dvd_one (not_le_of_lt hp.Pos)
  | n + 1, p, hp => by
    rw [factorial_succ, hp.dvd_mul, prime.dvd_factorial hp]
    exact
      ⟨fun h => h.elim (le_of_dvd (succ_pos _)) le_succ_of_le, fun h =>
        (_root_.lt_or_eq_of_le h).elim (Or.inr ∘ le_of_lt_succ) fun h =>
          Or.inl <| by
            rw [h]⟩

theorem Prime.coprime_pow_of_not_dvd {p m a : ℕ} (pp : Prime p) (h : ¬p ∣ a) : Coprime a (p ^ m) :=
  (pp.coprime_iff_not_dvd.2 h).symm.pow_right _

theorem coprime_primes {p q : ℕ} (pp : Prime p) (pq : Prime q) : Coprime p q ↔ p ≠ q :=
  pp.coprime_iff_not_dvd.trans <| not_congr <| dvd_prime_two_le pq pp.two_le

theorem coprime_pow_primes {p q : ℕ} (n m : ℕ) (pp : Prime p) (pq : Prime q) (h : p ≠ q) : Coprime (p ^ n) (q ^ m) :=
  ((coprime_primes pp pq).2 h).pow _ _

theorem coprime_or_dvd_of_prime {p} (pp : Prime p) (i : ℕ) : Coprime p i ∨ p ∣ i := by
  rw [pp.dvd_iff_not_coprime] <;> apply em

theorem coprime_of_lt_prime {n p} (n_pos : 0 < n) (hlt : n < p) (pp : Prime p) : Coprime p n :=
  (coprime_or_dvd_of_prime pp n).resolve_right fun h => lt_le_antisymmₓ hlt (le_of_dvdₓ n_pos h)

theorem eq_or_coprime_of_le_prime {n p} (n_pos : 0 < n) (hle : n ≤ p) (pp : Prime p) : p = n ∨ Coprime p n :=
  hle.eq_or_lt.imp Eq.symm fun h => coprime_of_lt_prime n_pos h pp

theorem dvd_prime_pow {p : ℕ} (pp : Prime p) {m i : ℕ} : i ∣ p ^ m ↔ ∃ k ≤ m, i = p ^ k := by
  simp_rw [dvd_prime_pow (prime_iff.mp pp) m, associated_eq_eq]

theorem Prime.dvd_mul_of_dvd_ne {p1 p2 n : ℕ} (h_neq : p1 ≠ p2) (pp1 : Prime p1) (pp2 : Prime p2) (h1 : p1 ∣ n)
    (h2 : p2 ∣ n) : p1 * p2 ∣ n :=
  Coprime.mul_dvd_of_dvd_of_dvd ((coprime_primes pp1 pp2).mpr h_neq) h1 h2

/-- If `p` is prime,
and `a` doesn't divide `p^k`, but `a` does divide `p^(k+1)`
then `a = p^(k+1)`.
-/
theorem eq_prime_pow_of_dvd_least_prime_pow {a p k : ℕ} (pp : Prime p) (h₁ : ¬a ∣ p ^ k) (h₂ : a ∣ p ^ (k + 1)) :
    a = p ^ (k + 1) := by
  obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂
  congr
  exact le_antisymmₓ h (not_leₓ.1 ((not_congr (pow_dvd_pow_iff_le_right (prime.one_lt pp))).1 h₁))

theorem ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n
  | 0 => by
    simpa using Exists.intro 2 Nat.prime_two
  | 1 => by
    simp [← Nat.not_prime_one]
  | n + 2 => by
    let a := n + 2
    let ha : a ≠ 1 := Nat.succ_succ_ne_one n
    simp only [← true_iffₓ, ← Ne.def, ← not_false_iff, ← ha]
    exact ⟨a.min_fac, Nat.min_fac_prime ha, a.min_fac_dvd⟩

theorem eq_one_iff_not_exists_prime_dvd {n : ℕ} : n = 1 ↔ ∀ p : ℕ, p.Prime → ¬p ∣ n := by
  simpa using not_iff_not.mpr ne_one_iff_exists_prime_dvd

section

open List

theorem mem_factors_iff_dvd {n p : ℕ} (hn : n ≠ 0) (hp : Prime p) : p ∈ factors n ↔ p ∣ n :=
  ⟨fun h => prod_factors hn ▸ List.dvd_prod h, fun h =>
    mem_list_primes_of_dvd_prod (prime_iff.mp hp) (fun p h => prime_iff.mp (prime_of_mem_factors h))
      ((prod_factors hn).symm ▸ h)⟩

theorem dvd_of_mem_factors {n p : ℕ} (h : p ∈ n.factors) : p ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact dvd_zero p
    
  · rwa [← mem_factors_iff_dvd hn.ne' (prime_of_mem_factors h)]
    

theorem mem_factors {n p} (hn : n ≠ 0) : p ∈ factors n ↔ Prime p ∧ p ∣ n :=
  ⟨fun h => ⟨prime_of_mem_factors h, dvd_of_mem_factors h⟩, fun ⟨hprime, hdvd⟩ =>
    (mem_factors_iff_dvd hn hprime).mpr hdvd⟩

theorem le_of_mem_factors {n p : ℕ} (h : p ∈ n.factors) : p ≤ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · rw [factors_zero] at h
    cases h
    
  · exact le_of_dvd hn (dvd_of_mem_factors h)
    

/-- **Fundamental theorem of arithmetic**-/
theorem factors_unique {n : ℕ} {l : List ℕ} (h₁ : Prod l = n) (h₂ : ∀, ∀ p ∈ l, ∀, Prime p) : l ~ factors n := by
  refine' perm_of_prod_eq_prod _ _ _
  · rw [h₁]
    refine' (prod_factors _).symm
    rintro rfl
    rw [prod_eq_zero_iff] at h₁
    exact Prime.ne_zero (h₂ 0 h₁) rfl
    
  · simp_rw [← prime_iff]
    exact h₂
    
  · simp_rw [← prime_iff]
    exact fun p => prime_of_mem_factors
    

theorem Prime.factors_pow {p : ℕ} (hp : p.Prime) (n : ℕ) : (p ^ n).factors = List.repeat p n := by
  symm
  rw [← List.repeat_perm]
  apply Nat.factors_unique (List.prod_repeat p n)
  intro q hq
  rwa [eq_of_mem_repeat hq]

theorem eq_prime_pow_of_unique_prime_dvd {n p : ℕ} (hpos : n ≠ 0) (h : ∀ {d}, Nat.Prime d → d ∣ n → d = p) :
    n = p ^ n.factors.length := by
  set k := n.factors.length
  rw [← prod_factors hpos, ← prod_repeat p k,
    eq_repeat_of_mem fun d hd => h (prime_of_mem_factors hd) (dvd_of_mem_factors hd)]

/-- For positive `a` and `b`, the prime factors of `a * b` are the union of those of `a` and `b` -/
theorem perm_factors_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : (a * b).factors ~ a.factors ++ b.factors := by
  refine' (factors_unique _ _).symm
  · rw [List.prod_append, prod_factors ha, prod_factors hb]
    
  · intro p hp
    rw [List.mem_appendₓ] at hp
    cases hp <;> exact prime_of_mem_factors hp
    

/-- For coprime `a` and `b`, the prime factors of `a * b` are the union of those of `a` and `b` -/
theorem perm_factors_mul_of_coprime {a b : ℕ} (hab : Coprime a b) : (a * b).factors ~ a.factors ++ b.factors := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [← (coprime_zero_left _).mp hab]
    
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [← (coprime_zero_right _).mp hab]
    
  exact perm_factors_mul ha.ne' hb.ne'

theorem factors_sublist_right {n k : ℕ} (h : k ≠ 0) : n.factors <+ (n * k).factors := by
  cases n
  · rw [zero_mul]
    
  apply sublist_of_subperm_of_sorted _ (factors_sorted _) (factors_sorted _)
  rw [(perm_factors_mul n.succ_ne_zero h).subperm_left]
  exact (sublist_append_left _ _).Subperm

theorem factors_sublist_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) : n.factors <+ k.factors := by
  obtain ⟨a, rfl⟩ := h
  exact factors_sublist_right (right_ne_zero_of_mul h')

theorem factors_subset_right {n k : ℕ} (h : k ≠ 0) : n.factors ⊆ (n * k).factors :=
  (factors_sublist_right h).Subset

theorem factors_subset_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) : n.factors ⊆ k.factors :=
  (factors_sublist_of_dvd h h').Subset

theorem dvd_of_factors_subperm {a b : ℕ} (ha : a ≠ 0) (h : a.factors <+~ b.factors) : a ∣ b := by
  rcases b.eq_zero_or_pos with (rfl | hb)
  · exact dvd_zero _
    
  rcases a with (_ | _ | a)
  · exact (ha rfl).elim
    
  · exact one_dvd _
    
  use (b.factors.diff a.succ.succ.factors).Prod
  nth_rw 0[← Nat.prod_factors ha]
  rw [← List.prod_append, List.Perm.prod_eq <| List.subperm_append_diff_self_of_count_le <| list.subperm_ext_iff.mp h,
    Nat.prod_factors hb.ne']

end

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : Prime p) {m n k l : ℕ} (hpm : p ^ k ∣ m)
    (hpn : p ^ l ∣ n) (hpmn : p ^ (k + l + 1) ∣ m * n) : p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n :=
  have hpd : p ^ (k + l) * p ∣ m * n := by
    rwa [pow_succ'ₓ] at hpmn
  have hpd2 : p ∣ m * n / p ^ (k + l) := dvd_div_of_mul_dvd hpd
  have hpd3 : p ∣ m * n / (p ^ k * p ^ l) := by
    simpa [← pow_addₓ] using hpd2
  have hpd4 : p ∣ m / p ^ k * (n / p ^ l) := by
    simpa [← Nat.div_mul_div_comm hpm hpn] using hpd3
  have hpd5 : p ∣ m / p ^ k ∨ p ∣ n / p ^ l := (Prime.dvd_mul p_prime).1 hpd4
  suffices p ^ k * p ∣ m ∨ p ^ l * p ∣ n by
    rwa [pow_succ'ₓ, pow_succ'ₓ]
  hpd5.elim (fun this : p ∣ m / p ^ k => Or.inl <| mul_dvd_of_dvd_div hpm this) fun this : p ∣ n / p ^ l =>
    Or.inr <| mul_dvd_of_dvd_div hpn this

theorem prime_iff_prime_int {p : ℕ} : p.Prime ↔ Prime (p : ℤ) :=
  ⟨fun hp =>
    ⟨Int.coe_nat_ne_zero_iff_pos.2 hp.Pos, mt Int.is_unit_iff_nat_abs_eq.1 hp.ne_one, fun a b h => by
      rw [← Int.dvd_nat_abs, Int.coe_nat_dvd, Int.nat_abs_mul, hp.dvd_mul] at h <;>
        rwa [← Int.dvd_nat_abs, Int.coe_nat_dvd, ← Int.dvd_nat_abs, Int.coe_nat_dvd]⟩,
    fun hp =>
    Nat.prime_iff.2
      ⟨Int.coe_nat_ne_zero.1 hp.1,
        (mt Nat.is_unit_iff.1) fun h => by
          simpa [← h, ← not_prime_one] using hp,
        fun a b => by
        simpa only [← Int.coe_nat_dvd, ← (Int.coe_nat_mul _ _).symm] using hp.2.2 a b⟩⟩

/-- The type of prime numbers -/
def Primes :=
  { p : ℕ // p.Prime }

namespace Primes

instance : HasRepr Nat.Primes :=
  ⟨fun p => reprₓ p.val⟩

instance inhabitedPrimes : Inhabited Primes :=
  ⟨⟨2, prime_two⟩⟩

instance coeNat : Coe Nat.Primes ℕ :=
  ⟨Subtype.val⟩

theorem coe_nat_inj (p q : Nat.Primes) : (p : ℕ) = (q : ℕ) → p = q := fun h => Subtype.eq h

end Primes

instance monoid.primePow {α : Type _} [Monoidₓ α] : Pow α Primes :=
  ⟨fun x p => x ^ p.val⟩

end Nat

/-! ### Primality prover -/


open NormNum

namespace Tactic

namespace NormNum

theorem is_prime_helper (n : ℕ) (h₁ : 1 < n) (h₂ : Nat.minFac n = n) : Nat.Prime n :=
  Nat.prime_def_min_fac.2 ⟨h₁, h₂⟩

theorem min_fac_bit0 (n : ℕ) : Nat.minFac (bit0 n) = 2 := by
  simp [← Nat.min_fac_eq, ←
    show 2 ∣ bit0 n by
      simp [← bit0_eq_two_mul n]]

/-- A predicate representing partial progress in a proof of `min_fac`. -/
def MinFacHelper (n k : ℕ) : Prop :=
  0 < k ∧ bit1 k ≤ Nat.minFac (bit1 n)

theorem MinFacHelper.n_pos {n k : ℕ} (h : MinFacHelper n k) : 0 < n :=
  pos_iff_ne_zero.2 fun e => by
    rw [e] at h <;> exact not_le_of_lt (Nat.bit1_lt h.1) h.2

theorem min_fac_ne_bit0 {n k : ℕ} : Nat.minFac (bit1 n) ≠ bit0 k := by
  rw [bit0_eq_two_mul]
  refine' fun e => absurd ((Nat.dvd_add_iff_right _).2 (dvd_trans ⟨_, e⟩ (Nat.min_fac_dvd _))) _ <;> simp

theorem min_fac_helper_0 (n : ℕ) (h : 0 < n) : MinFacHelper n 1 := by
  refine' ⟨zero_lt_one, lt_of_le_of_neₓ _ min_fac_ne_bit0.symm⟩
  rw [Nat.succ_le_iff]
  refine' lt_of_le_of_neₓ (Nat.min_fac_pos _) fun e => Nat.not_prime_one _
  rw [e]
  exact Nat.min_fac_prime (Nat.bit1_lt h).ne'

theorem min_fac_helper_1 {n k k' : ℕ} (e : k + 1 = k') (np : Nat.minFac (bit1 n) ≠ bit1 k) (h : MinFacHelper n k) :
    MinFacHelper n k' := by
  rw [← e]
  refine'
    ⟨Nat.succ_posₓ _, (lt_of_le_of_neₓ (lt_of_le_of_neₓ _ _ : k + 1 + k < _) min_fac_ne_bit0.symm : bit0 (k + 1) < _)⟩
  · rw [add_right_commₓ]
    exact h.2
    
  · rw [add_right_commₓ]
    exact np.symm
    

theorem min_fac_helper_2 (n k k' : ℕ) (e : k + 1 = k') (np : ¬Nat.Prime (bit1 k)) (h : MinFacHelper n k) :
    MinFacHelper n k' := by
  refine' min_fac_helper_1 e _ h
  intro e₁
  rw [← e₁] at np
  exact np (Nat.min_fac_prime <| ne_of_gtₓ <| Nat.bit1_lt h.n_pos)

theorem min_fac_helper_3 (n k k' c : ℕ) (e : k + 1 = k') (nc : bit1 n % bit1 k = c) (c0 : 0 < c)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  refine' min_fac_helper_1 e _ h
  refine' mt _ (ne_of_gtₓ c0)
  intro e₁
  rw [← nc, ← Nat.dvd_iff_mod_eq_zeroₓ, ← e₁]
  apply Nat.min_fac_dvd

theorem min_fac_helper_4 (n k : ℕ) (hd : bit1 n % bit1 k = 0) (h : MinFacHelper n k) : Nat.minFac (bit1 n) = bit1 k :=
  by
  rw [← Nat.dvd_iff_mod_eq_zeroₓ] at hd
  exact le_antisymmₓ (Nat.min_fac_le_of_dvd (Nat.bit1_lt h.1) hd) h.2

theorem min_fac_helper_5 (n k k' : ℕ) (e : bit1 k * bit1 k = k') (hd : bit1 n < k') (h : MinFacHelper n k) :
    Nat.minFac (bit1 n) = bit1 n := by
  refine' (Nat.prime_def_min_fac.1 (Nat.prime_def_le_sqrt.2 ⟨Nat.bit1_lt h.n_pos, _⟩)).2
  rw [← e] at hd
  intro m m2 hm md
  have := le_transₓ h.2 (le_transₓ (Nat.min_fac_le_of_dvd m2 md) hm)
  rw [Nat.le_sqrt] at this
  exact not_le_of_lt hd this

/-- Given `e` a natural numeral and `d : nat` a factor of it, return `⊢ ¬ prime e`. -/
unsafe def prove_non_prime (e : expr) (n d₁ : ℕ) : tactic expr := do
  let e₁ := reflect d₁
  let c ← mk_instance_cache (quote.1 Nat)
  let (c, p₁) ← prove_lt_nat c (quote.1 1) e₁
  let d₂ := n / d₁
  let e₂ := reflect d₂
  let (c, e', p) ← prove_mul_nat c e₁ e₂
  guardₓ (expr.alpha_eqv e' e)
  let (c, p₂) ← prove_lt_nat c (quote.1 1) e₂
  return <| (quote.1 @Nat.not_prime_mul').mk_app [e₁, e₂, e, p, p₁, p₂]

/-- Given `a`,`a1 := bit1 a`, `n1` the value of `a1`, `b` and `p : min_fac_helper a b`,
  returns `(c, ⊢ min_fac a1 = c)`. -/
unsafe def prove_min_fac_aux (a a1 : expr) (n1 : ℕ) :
    instance_cache → expr → expr → tactic (instance_cache × expr × expr)
  | ic, b, p => do
    let k ← b.toNat
    let k1 := bit1 k
    let b1 := (quote.1 (bit1 : ℕ → ℕ)).mk_app [b]
    if n1 < k1 * k1 then do
        let (ic, e', p₁) ← prove_mul_nat ic b1 b1
        let (ic, p₂) ← prove_lt_nat ic a1 e'
        return (ic, a1, (quote.1 min_fac_helper_5).mk_app [a, b, e', p₁, p₂, p])
      else
        let d := k1
        if to_bool (d < k1) then do
          let k' := k + 1
          let e' := reflect k'
          let (ic, p₁) ← prove_succ ic b e'
          let p₂ ← prove_non_prime b1 k1 d
          prove_min_fac_aux ic e' <| (quote.1 min_fac_helper_2).mk_app [a, b, e', p₁, p₂, p]
        else do
          let nc := n1 % k1
          let (ic, c, pc) ← prove_div_mod ic a1 b1 tt
          if nc = 0 then return (ic, b1, (quote.1 min_fac_helper_4).mk_app [a, b, pc, p])
            else do
              let (ic, p₀) ← prove_pos ic c
              let k' := k + 1
              let e' := reflect k'
              let (ic, p₁) ← prove_succ ic b e'
              prove_min_fac_aux ic e' <| (quote.1 min_fac_helper_3).mk_app [a, b, e', c, p₁, pc, p₀, p]

/-- Given `a` a natural numeral, returns `(b, ⊢ min_fac a = b)`. -/
unsafe def prove_min_fac (ic : instance_cache) (e : expr) : tactic (instance_cache × expr × expr) :=
  match match_numeral e with
  | match_numeral_result.zero => return (ic, quote.1 (2 : ℕ), quote.1 Nat.min_fac_zero)
  | match_numeral_result.one => return (ic, quote.1 (1 : ℕ), quote.1 Nat.min_fac_one)
  | match_numeral_result.bit0 e => return (ic, quote.1 2, (quote.1 min_fac_bit0).mk_app [e])
  | match_numeral_result.bit1 e => do
    let n ← e.toNat
    let c ← mk_instance_cache (quote.1 Nat)
    let (c, p) ← prove_pos c e
    let a1 := (quote.1 (bit1 : ℕ → ℕ)).mk_app [e]
    prove_min_fac_aux e a1 (bit1 n) c (quote.1 1) ((quote.1 min_fac_helper_0).mk_app [e, p])
  | _ => failed

/-- A partial proof of `factors`. Asserts that `l` is a sorted list of primes, lower bounded by a
prime `p`, which multiplies to `n`. -/
def FactorsHelper (n p : ℕ) (l : List ℕ) : Prop :=
  p.Prime → List.Chain (· ≤ ·) p l ∧ (∀, ∀ a ∈ l, ∀, Nat.Prime a) ∧ List.prod l = n

theorem factors_helper_nil (a : ℕ) : FactorsHelper 1 a [] := fun pa =>
  ⟨List.Chain.nil, by
    rintro _ ⟨⟩, List.prod_nil⟩

theorem factors_helper_cons' (n m a b : ℕ) (l : List ℕ) (h₁ : b * m = n) (h₂ : a ≤ b) (h₃ : Nat.minFac b = b)
    (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) := fun pa =>
  have pb : b.Prime := Nat.prime_def_min_fac.2 ⟨le_transₓ pa.two_le h₂, h₃⟩
  let ⟨f₁, f₂, f₃⟩ := H pb
  ⟨List.Chain.cons h₂ f₁, fun c h => h.elim (fun e => e.symm ▸ pb) (f₂ _), by
    rw [List.prod_cons, f₃, h₁]⟩

theorem factors_helper_cons (n m a b : ℕ) (l : List ℕ) (h₁ : b * m = n) (h₂ : a < b) (h₃ : Nat.minFac b = b)
    (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) :=
  factors_helper_cons' _ _ _ _ _ h₁ h₂.le h₃ H

theorem factors_helper_sn (n a : ℕ) (h₁ : a < n) (h₂ : Nat.minFac n = n) : FactorsHelper n a [n] :=
  factors_helper_cons _ _ _ _ _ (mul_oneₓ _) h₁ h₂ (factors_helper_nil _)

theorem factors_helper_same (n m a : ℕ) (l : List ℕ) (h : a * m = n) (H : FactorsHelper m a l) :
    FactorsHelper n a (a :: l) := fun pa => factors_helper_cons' _ _ _ _ _ h le_rfl (Nat.prime_def_min_fac.1 pa).2 H pa

theorem factors_helper_same_sn (a : ℕ) : FactorsHelper a a [a] :=
  factors_helper_same _ _ _ _ (mul_oneₓ _) (factors_helper_nil _)

theorem factors_helper_end (n : ℕ) (l : List ℕ) (H : FactorsHelper n 2 l) : Nat.factors n = l :=
  let ⟨h₁, h₂, h₃⟩ := H Nat.prime_two
  have := (List.chain'_iff_pairwise (@le_transₓ _ _)).1 (@List.Chain'.tail _ _ (_ :: _) h₁)
  (List.eq_of_perm_of_sorted (Nat.factors_unique h₃ h₂) this (Nat.factors_sorted _)).symm

/-- Given `n` and `a` natural numerals, returns `(l, ⊢ factors_helper n a l)`. -/
unsafe def prove_factors_aux : instance_cache → expr → expr → ℕ → ℕ → tactic (instance_cache × expr × expr)
  | c, en, ea, n, a =>
    let b := n.minFac
    if b < n then do
      let m := n / b
      let (c, em) ← c.ofNat m
      if b = a then do
          let (c, _, p₁) ← prove_mul_nat c ea em
          let (c, l, p₂) ← prove_factors_aux c em ea m a
          pure (c, quote.1 ((%%ₓea) :: %%ₓl : List ℕ), (quote.1 factors_helper_same).mk_app [en, em, ea, l, p₁, p₂])
        else do
          let (c, eb) ← c b
          let (c, _, p₁) ← prove_mul_nat c eb em
          let (c, p₂) ← prove_lt_nat c ea eb
          let (c, _, p₃) ← prove_min_fac c eb
          let (c, l, p₄) ← prove_factors_aux c em eb m b
          pure
              (c, quote.1 ((%%ₓeb) :: %%ₓl : List ℕ),
                (quote.1 factors_helper_cons).mk_app [en, em, ea, eb, l, p₁, p₂, p₃, p₄])
    else
      if b = a then pure (c, quote.1 ([%%ₓea] : List ℕ), (quote.1 factors_helper_same_sn).mk_app [ea])
      else do
        let (c, p₁) ← prove_lt_nat c ea en
        let (c, _, p₂) ← prove_min_fac c en
        pure (c, quote.1 ([%%ₓen] : List ℕ), (quote.1 factors_helper_sn).mk_app [en, ea, p₁, p₂])

/-- Evaluates the `prime` and `min_fac` functions. -/
@[norm_num]
unsafe def eval_prime : expr → tactic (expr × expr)
  | quote.1 (Nat.Prime (%%ₓe)) => do
    let n ← e.toNat
    match n with
      | 0 => false_intro (quote.1 Nat.not_prime_zero)
      | 1 => false_intro (quote.1 Nat.not_prime_one)
      | _ =>
        let d₁ := n
        if d₁ < n then prove_non_prime e n d₁ >>= false_intro
        else do
          let e₁ := reflect d₁
          let c ← mk_instance_cache (quote.1 ℕ)
          let (c, p₁) ← prove_lt_nat c (quote.1 1) e₁
          let (c, e₁, p) ← prove_min_fac c e
          true_intro <| (quote.1 is_prime_helper).mk_app [e, p₁, p]
  | quote.1 (Nat.minFac (%%ₓe)) => do
    let ic ← mk_instance_cache (quote.1 ℕ)
    Prod.snd <$> prove_min_fac ic e
  | quote.1 (Nat.factors (%%ₓe)) => do
    let n ← e.toNat
    match n with
      | 0 => pure (quote.1 (@List.nil ℕ), quote.1 Nat.factors_zero)
      | 1 => pure (quote.1 (@List.nil ℕ), quote.1 Nat.factors_one)
      | _ => do
        let c ← mk_instance_cache (quote.1 ℕ)
        let (c, l, p) ← prove_factors_aux c e (quote.1 2) n 2
        pure (l, (quote.1 factors_helper_end).mk_app [e, l, p])
  | _ => failed

end NormNum

end Tactic

namespace Nat

theorem prime_three : Prime 3 := by
  norm_num

instance fact_prime_two : Fact (Prime 2) :=
  ⟨prime_two⟩

instance fact_prime_three : Fact (Prime 3) :=
  ⟨prime_three⟩

end Nat

namespace Nat

theorem mem_factors_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) {p : ℕ} :
    p ∈ (a * b).factors ↔ p ∈ a.factors ∨ p ∈ b.factors := by
  rw [mem_factors (mul_ne_zero ha hb), mem_factors ha, mem_factors hb, ← and_or_distrib_left]
  simpa only [← And.congr_right_iff] using prime.dvd_mul

/-- If `a`, `b` are positive, the prime divisors of `a * b` are the union of those of `a` and `b` -/
theorem factors_mul_to_finset {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factors.toFinset = a.factors.toFinset ∪ b.factors.toFinset :=
  (List.toFinset.ext fun x => (mem_factors_mul ha hb).trans List.mem_union.symm).trans <| List.to_finset_union _ _

theorem pow_succ_factors_to_finset (n k : ℕ) : (n ^ (k + 1)).factors.toFinset = n.factors.toFinset := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    
  induction' k with k ih
  · simp
    
  rw [pow_succₓ, factors_mul_to_finset hn (pow_ne_zero _ hn), ih, Finset.union_idempotent]

theorem pow_factors_to_finset (n : ℕ) {k : ℕ} (hk : k ≠ 0) : (n ^ k).factors.toFinset = n.factors.toFinset := by
  cases k
  · simpa using hk
    
  rw [pow_succ_factors_to_finset]

/-- The only prime divisor of positive prime power `p^k` is `p` itself -/
theorem prime_pow_prime_divisor {p k : ℕ} (hk : k ≠ 0) (hp : Prime p) : (p ^ k).factors.toFinset = {p} := by
  simp [← pow_factors_to_finset p hk, ← factors_prime hp]

/-- The sets of factors of coprime `a` and `b` are disjoint -/
theorem coprime_factors_disjoint {a b : ℕ} (hab : a.Coprime b) : List.Disjoint a.factors b.factors := by
  intro q hqa hqb
  apply not_prime_one
  rw [← eq_one_of_dvd_coprimes hab (dvd_of_mem_factors hqa) (dvd_of_mem_factors hqb)]
  exact prime_of_mem_factors hqa

theorem mem_factors_mul_of_coprime {a b : ℕ} (hab : Coprime a b) (p : ℕ) :
    p ∈ (a * b).factors ↔ p ∈ a.factors ∪ b.factors := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [← (coprime_zero_left _).mp hab]
    
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [← (coprime_zero_right _).mp hab]
    
  rw [mem_factors_mul ha.ne' hb.ne', List.mem_union]

theorem factors_mul_to_finset_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).factors.toFinset = a.factors.toFinset ∪ b.factors.toFinset :=
  (List.toFinset.ext <| mem_factors_mul_of_coprime hab).trans <| List.to_finset_union _ _

open List

/-- If `p` is a prime factor of `a` then `p` is also a prime factor of `a * b` for any `b > 0` -/
theorem mem_factors_mul_left {p a b : ℕ} (hpa : p ∈ a.factors) (hb : b ≠ 0) : p ∈ (a * b).factors := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simpa using hpa
    
  apply (mem_factors_mul ha hb).2 (Or.inl hpa)

/-- If `p` is a prime factor of `b` then `p` is also a prime factor of `a * b` for any `a > 0` -/
theorem mem_factors_mul_right {p a b : ℕ} (hpb : p ∈ b.factors) (ha : a ≠ 0) : p ∈ (a * b).factors := by
  rw [mul_comm]
  exact mem_factors_mul_left hpb ha

theorem eq_two_pow_or_exists_odd_prime_and_dvd (n : ℕ) : (∃ k : ℕ, n = 2 ^ k) ∨ ∃ p, Nat.Prime p ∧ p ∣ n ∧ Odd p :=
  (eq_or_ne n 0).elim (fun hn => Or.inr ⟨3, prime_three, hn.symm ▸ dvd_zero 3, ⟨1, rfl⟩⟩) fun hn =>
    or_iff_not_imp_right.mpr fun H =>
      ⟨n.factors.length,
        eq_prime_pow_of_unique_prime_dvd hn fun p hprime hdvd =>
          hprime.eq_two_or_odd'.resolve_right fun hodd => H ⟨p, hprime, hdvd, hodd⟩⟩

end Nat

namespace Int

theorem prime_two : Prime (2 : ℤ) :=
  Nat.prime_iff_prime_int.mp Nat.prime_two

theorem prime_three : Prime (3 : ℤ) :=
  Nat.prime_iff_prime_int.mp Nat.prime_three

end Int

section

open Finset

/-- Exactly `n / p` naturals in `[1, n]` are multiples of `p`. -/
theorem card_multiples (n p : ℕ) : card ((range n).filter fun e => p ∣ e + 1) = n / p := by
  induction' n with n hn
  · rw [Nat.zero_divₓ, range_zero, filter_empty, card_empty]
    
  · rw [Nat.succ_div, add_ite, add_zeroₓ, range_succ, filter_insert, apply_ite card,
      card_insert_of_not_mem (mem_filter.not.mpr (not_and_of_not_left _ not_mem_range_self)), hn]
    

end

