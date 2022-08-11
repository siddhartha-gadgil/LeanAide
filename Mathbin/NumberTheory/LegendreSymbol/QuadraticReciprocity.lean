/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
import Mathbin.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import Mathbin.NumberTheory.LegendreSymbol.QuadraticChar

/-!
# Legendre symbol and quadratic reciprocity.

This file contains results about quadratic residues modulo a prime number.

We define the Legendre symbol `(a / p)` as `legendre_sym p a`.
Note the order of arguments! The advantage of this form is that then `legendre_sym p`
is a multiplicative map.

The main results are the law of quadratic reciprocity, `quadratic_reciprocity`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`exists_sq_eq_prime_iff_of_mod_four_eq_one`, and
`exists_sq_eq_prime_iff_of_mod_four_eq_three`.

Also proven are conditions for `-1` and `2` to be a square modulo a prime,
`legende_sym_neg_one` and `exists_sq_eq_neg_one_iff` for `-1`, and
`exists_sq_eq_two_iff` for `2`

## Implementation notes

The proof of quadratic reciprocity implemented uses Gauss' lemma and Eisenstein's lemma
-/


open Finset Nat Charₓ

namespace Zmod

variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]

/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion_units (x : (Zmod p)ˣ) : (∃ y : (Zmod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 := by
  by_cases' hc : p = 2
  · subst hc
    simp only [← eq_iff_true_of_subsingleton, ← exists_const]
    
  · have h₀ :=
      FiniteField.unit_is_square_iff
        (by
          rwa [ring_char_zmod_n])
        x
    have hs : (∃ y : (Zmod p)ˣ, y ^ 2 = x) ↔ IsSquare x := by
      rw [is_square_iff_exists_sq x]
      simp_rw [eq_comm]
    rw [hs]
    rwa [card p] at h₀
    

/-- Euler's Criterion: a nonzero `a : zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion {a : Zmod p} (ha : a ≠ 0) : IsSquare (a : Zmod p) ↔ a ^ (p / 2) = 1 := by
  apply
    (iff_congr _
          (by
            simp [← Units.ext_iff])).mp
      (euler_criterion_units p (Units.mk0 a ha))
  simp only [← Units.ext_iff, ← sq, ← Units.coe_mk0, ← Units.coe_mul]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy.symm⟩
    
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by
      rintro rfl
      simpa [← zero_pow] using ha
    refine' ⟨Units.mk0 y hy, _⟩
    simp
    

theorem exists_sq_eq_neg_one_iff : IsSquare (-1 : Zmod p) ↔ p % 4 ≠ 3 := by
  have h := @is_square_neg_one_iff (Zmod p) _ _
  rw [card p] at h
  exact h

theorem mod_four_ne_three_of_sq_eq_neg_one {y : Zmod p} (hy : y ^ 2 = -1) : p % 4 ≠ 3 := by
  rw [pow_two] at hy
  exact (exists_sq_eq_neg_one_iff p).1 ⟨y, hy.symm⟩

theorem mod_four_ne_three_of_sq_eq_neg_sq' {x y : Zmod p} (hy : y ≠ 0) (hxy : x ^ 2 = -(y ^ 2)) : p % 4 ≠ 3 :=
  @mod_four_ne_three_of_sq_eq_neg_one p _ (x / y)
    (by
      apply_fun fun z => z / y ^ 2  at hxy
      rwa [neg_div, ← div_pow, ← div_pow, div_self hy, one_pow] at hxy)

theorem mod_four_ne_three_of_sq_eq_neg_sq {x y : Zmod p} (hx : x ≠ 0) (hxy : x ^ 2 = -(y ^ 2)) : p % 4 ≠ 3 := by
  apply_fun fun x => -x  at hxy
  rw [neg_negₓ] at hxy
  exact mod_four_ne_three_of_sq_eq_neg_sq' p hx hxy.symm

theorem pow_div_two_eq_neg_one_or_one {a : Zmod p} (ha : a ≠ 0) : a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 := by
  cases' Nat.Prime.eq_two_or_odd (Fact.out p.prime) with hp2 hp_odd
  · subst p
    revert a ha
    decide
    
  rw [← mul_self_eq_one_iff, ← pow_addₓ, ← two_mul, two_mul_odd_div_two hp_odd]
  exact pow_card_sub_one_eq_one ha

/-- The Legendre symbol of `a : ℤ` and a prime `p`, `legendre_sym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendre_sym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendreSym (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ :=
  quadraticChar (Zmod p) a

/-- We have the congruence `legendre_sym p a ≡ a ^ (p / 2) mod p`. -/
theorem legendre_sym_eq_pow (p : ℕ) (a : ℤ) [hp : Fact p.Prime] : (legendreSym p a : Zmod p) = a ^ (p / 2) := by
  rw [legendre_sym]
  by_cases' ha : (a : Zmod p) = 0
  · simp only [← ha, ← zero_pow (Nat.div_pos hp.1.two_le (succ_pos 1)), ← MulChar.map_zero, ← Int.cast_zeroₓ]
    
  by_cases' hp₁ : p = 2
  · subst p
    generalize (a : Zmod 2) = b
    revert b
    decide
    
  · have h₁ :=
      quadratic_char_eq_pow_of_char_ne_two
        (by
          rwa [ring_char_zmod_n p])
        ha
    rw [card p] at h₁
    rw [h₁]
    have h₂ :=
      Ringₓ.neg_one_ne_one_of_char_ne_two
        (by
          rwa [ring_char_zmod_n p])
    cases' pow_div_two_eq_neg_one_or_one p ha with h h
    · rw [if_pos h, h, Int.cast_oneₓ]
      
    · rw [h, if_neg h₂, Int.cast_neg, Int.cast_oneₓ]
      
    

/-- If `p ∤ a`, then `legendre_sym p a` is `1` or `-1`. -/
theorem legendre_sym_eq_one_or_neg_one (p : ℕ) [Fact p.Prime] (a : ℤ) (ha : (a : Zmod p) ≠ 0) :
    legendreSym p a = 1 ∨ legendreSym p a = -1 :=
  quadratic_char_dichotomy ha

theorem legendre_sym_eq_neg_one_iff_not_one {a : ℤ} (ha : (a : Zmod p) ≠ 0) :
    legendreSym p a = -1 ↔ ¬legendreSym p a = 1 :=
  quadratic_char_eq_neg_one_iff_not_one ha

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
theorem legendre_sym_eq_zero_iff (p : ℕ) [Fact p.Prime] (a : ℤ) : legendreSym p a = 0 ↔ (a : Zmod p) = 0 :=
  quadratic_char_eq_zero_iff

@[simp]
theorem legendre_sym_zero (p : ℕ) [Fact p.Prime] : legendreSym p 0 = 0 := by
  rw [legendre_sym, Int.cast_zeroₓ, MulChar.map_zero]

@[simp]
theorem legendre_sym_one (p : ℕ) [Fact p.Prime] : legendreSym p 1 = 1 := by
  rw [legendre_sym, Int.cast_oneₓ, MulChar.map_one]

/-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
theorem legendre_sym_mul (p : ℕ) [Fact p.Prime] (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b :=
  by
  rw [legendre_sym, legendre_sym, legendre_sym]
  push_cast
  exact quadratic_char_mul (a : Zmod p) b

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps]
def legendreSymHom (p : ℕ) [Fact p.Prime] : ℤ →*₀ ℤ where
  toFun := legendreSym p
  map_zero' := legendre_sym_zero p
  map_one' := legendre_sym_one p
  map_mul' := legendre_sym_mul p

/-- The square of the symbol is 1 if `p ∤ a`. -/
theorem legendre_sym_sq_one (p : ℕ) [Fact p.Prime] (a : ℤ) (ha : (a : Zmod p) ≠ 0) : legendreSym p a ^ 2 = 1 :=
  quadratic_char_sq_one ha

/-- The Legendre symbol of `a^2` at `p` is 1 if `p ∤ a`. -/
theorem legendre_sym_sq_one' (p : ℕ) [Fact p.Prime] (a : ℤ) (ha : (a : Zmod p) ≠ 0) : legendreSym p (a ^ 2) = 1 := by
  rw [legendre_sym]
  push_cast
  exact quadratic_char_sq_one' ha

/-- The Legendre symbol depends only on `a` mod `p`. -/
theorem legendre_sym_mod (p : ℕ) [Fact p.Prime] (a : ℤ) : legendreSym p a = legendreSym p (a % p) := by
  simp only [← legendre_sym, ← int_cast_mod]

/-- Gauss' lemma. The legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2` -/
theorem gauss_lemma {a : ℤ} (hp : p ≠ 2) (ha0 : (a : Zmod p) ≠ 0) :
    legendreSym p a = -1 ^ ((ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : Zmod p).val).card := by
  have hp' : Fact (p % 2 = 1) := ⟨nat.prime.mod_two_eq_one_iff_ne_two.mpr hp⟩
  have :
    (legendre_sym p a : Zmod p) =
      ((-1 ^ ((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : Zmod p).val).card : ℤ) : Zmod p) :=
    by
    rw [legendre_sym_eq_pow, LegendreSymbol.gauss_lemma_aux p ha0] <;> simp
  cases legendre_sym_eq_one_or_neg_one p a ha0 <;>
    cases neg_one_pow_eq_or ℤ ((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : Zmod p).val).card <;>
      simp_all [← ne_neg_self p one_ne_zero, ← (ne_neg_self p one_ne_zero).symm]

/-- When `p ∤ a`, then `legendre_sym p a = 1` iff `a` is a square mod `p`. -/
theorem legendre_sym_eq_one_iff {a : ℤ} (ha0 : (a : Zmod p) ≠ 0) : legendreSym p a = 1 ↔ IsSquare (a : Zmod p) :=
  quadratic_char_one_iff_is_square ha0

/-- `legendre_sym p a = -1` iff`a` is a nonsquare mod `p`. -/
theorem legendre_sym_eq_neg_one_iff {a : ℤ} : legendreSym p a = -1 ↔ ¬IsSquare (a : Zmod p) :=
  quadratic_char_neg_one_iff_not_is_square

/-- The number of square roots of `a` modulo `p` is determined by the Legendre symbol. -/
theorem legendre_sym_card_sqrts (hp : p ≠ 2) (a : ℤ) :
    ↑{ x : Zmod p | x ^ 2 = a }.toFinset.card = legendreSym p a + 1 := by
  have h : ringChar (Zmod p) ≠ 2 := by
    rw [ring_char_zmod_n]
    exact hp
  exact quadratic_char_card_sqrts h a

/-- `legendre_sym p (-1)` is given by `χ₄ p`. -/
theorem legendre_sym_neg_one (hp : p ≠ 2) : legendreSym p (-1) = χ₄ p := by
  have h : ringChar (Zmod p) ≠ 2 := by
    rw [ring_char_zmod_n]
    exact hp
  have h₁ := quadratic_char_neg_one h
  rw [card p] at h₁
  exact_mod_cast h₁

open BigOperators

theorem eisenstein_lemma (hp : p ≠ 2) {a : ℕ} (ha1 : a % 2 = 1) (ha0 : (a : Zmod p) ≠ 0) :
    legendreSym p a = -1 ^ ∑ x in ico 1 (p / 2).succ, x * a / p := by
  have hp' : Fact (p % 2 = 1) := ⟨nat.prime.mod_two_eq_one_iff_ne_two.mpr hp⟩
  have ha0' : ((a : ℤ) : Zmod p) ≠ 0 := by
    norm_cast
    exact ha0
  rw [neg_one_pow_eq_pow_mod_two, gauss_lemma p hp ha0', neg_one_pow_eq_pow_mod_two,
    (by
      norm_cast : ((a : ℤ) : Zmod p) = (a : Zmod p)),
    show _ = _ from LegendreSymbol.eisenstein_lemma_aux p ha1 ha0]

/-- **Quadratic reciprocity theorem** -/
theorem quadratic_reciprocity (hp1 : p ≠ 2) (hq1 : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = -1 ^ (p / 2 * (q / 2)) := by
  have hpq0 : (p : Zmod q) ≠ 0 := prime_ne_zero q p hpq.symm
  have hqp0 : (q : Zmod p) ≠ 0 := prime_ne_zero p q hpq
  rw [eisenstein_lemma q hq1 (nat.prime.mod_two_eq_one_iff_ne_two.mpr hp1) hpq0,
    eisenstein_lemma p hp1 (nat.prime.mod_two_eq_one_iff_ne_two.mpr hq1) hqp0, ← pow_addₓ,
    LegendreSymbol.sum_mul_div_add_sum_mul_div_eq_mul q p hpq0, mul_comm]

theorem legendre_sym_two (hp2 : p ≠ 2) : legendreSym p 2 = -1 ^ (p / 4 + p / 2) := by
  have hp1 := nat.prime.mod_two_eq_one_iff_ne_two.mpr hp2
  have hp22 : p / 2 / 2 = _ :=
    LegendreSymbol.div_eq_filter_card
      (show 0 < 2 by
        decide)
      (Nat.div_le_selfₓ (p / 2) 2)
  have hcard : (Ico 1 (p / 2).succ).card = p / 2 := by
    simp
  have hx2 : ∀, ∀ x ∈ Ico 1 (p / 2).succ, ∀, (2 * x : Zmod p).val = 2 * x := fun x hx => by
    have h2xp : 2 * x < p :=
      calc
        2 * x ≤ 2 * (p / 2) :=
          mul_le_mul_of_nonneg_left (le_of_lt_succ <| (mem_Ico.mp hx).2)
            (by
              decide)
        _ < _ := by
          conv_rhs => rw [← div_add_mod p 2, hp1] <;> exact lt_succ_self _
        
    rw [← Nat.cast_two, ← Nat.cast_mulₓ, val_cast_of_lt h2xp]
  have hdisj :
    Disjoint ((Ico 1 (p / 2).succ).filter fun x => p / 2 < ((2 : ℕ) * x : Zmod p).val)
      ((Ico 1 (p / 2).succ).filter fun x => x * 2 ≤ p / 2) :=
    disjoint_filter.2 fun x hx => by
      rw [Nat.cast_two, hx2 x hx, mul_comm]
      simp
  have hunion :
    (((Ico 1 (p / 2).succ).filter fun x => p / 2 < ((2 : ℕ) * x : Zmod p).val) ∪
        (Ico 1 (p / 2).succ).filter fun x => x * 2 ≤ p / 2) =
      Ico 1 (p / 2).succ :=
    by
    rw [filter_union_right]
    conv_rhs => rw [← @filter_true _ (Ico 1 (p / 2).succ)]
    exact
      filter_congr fun x hx => by
        rw [Nat.cast_two, hx2 x hx, mul_comm, iff_true_intro (lt_or_leₓ _ _)]
  have hp2' := prime_ne_zero p 2 hp2
  rw
    [(by
      norm_cast : ((2 : ℕ) : Zmod p) = (2 : ℤ))] at
    *
  erw [gauss_lemma p hp2 hp2', neg_one_pow_eq_pow_mod_two, @neg_one_pow_eq_pow_mod_two _ _ (p / 4 + p / 2)]
  refine' congr_arg2ₓ _ rfl ((eq_iff_modeq_nat 2).1 _)
  rw [show 4 = 2 * 2 from rfl, ← Nat.div_div_eq_div_mulₓ, hp22, Nat.cast_addₓ, ← sub_eq_iff_eq_add', sub_eq_add_neg,
    neg_eq_self_mod_two, ← Nat.cast_addₓ, ← card_disjoint_union hdisj, hunion, hcard]

theorem exists_sq_eq_two_iff (hp1 : p ≠ 2) : IsSquare (2 : Zmod p) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  have hp2 : ((2 : ℤ) : Zmod p) ≠ 0 := by
    exact_mod_cast prime_ne_zero p 2 hp1
  have hpm4 : p % 4 = p % 8 % 4 := (Nat.mod_mul_left_mod p 2 4).symm
  have hpm2 : p % 2 = p % 8 % 2 := (Nat.mod_mul_left_mod p 4 2).symm
  rw
    [show (2 : Zmod p) = (2 : ℤ) by
      simp ,
    ← legendre_sym_eq_one_iff p hp2]
  erw [legendre_sym_two p hp1,
    neg_one_pow_eq_one_iff_even
      (show (-1 : ℤ) ≠ 1 by
        decide),
    even_add, even_div, even_div]
  have :=
    Nat.mod_ltₓ p
      (show 0 < 8 by
        decide)
  have hp := nat.prime.mod_two_eq_one_iff_ne_two.mpr hp1
  revert this hp
  erw [hpm4, hpm2]
  generalize hm : p % 8 = m
  clear! p
  decide!

theorem exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q ≠ 2) :
    IsSquare (q : Zmod p) ↔ IsSquare (p : Zmod q) :=
  if hpq : p = q then by
    subst hpq
  else by
    have h1 : p / 2 * (q / 2) % 2 = 0 :=
      dvd_iff_mod_eq_zeroₓ.1
        (dvd_mul_of_dvd_left
          (dvd_iff_mod_eq_zeroₓ.2 <| by
            rw [← mod_mul_right_div_self, show 2 * 2 = 4 from rfl, hp1] <;> rfl)
          _)
    have hp_odd : p ≠ 2 := by
      by_contra
      simp [← h] at hp1
      norm_num  at hp1
    have hpq0 : ((p : ℤ) : Zmod q) ≠ 0 := by
      exact_mod_cast prime_ne_zero q p (Ne.symm hpq)
    have hqp0 : ((q : ℤ) : Zmod p) ≠ 0 := by
      exact_mod_cast prime_ne_zero p q hpq
    have := quadratic_reciprocity p q hp_odd hq1 hpq
    rw [neg_one_pow_eq_pow_mod_two, h1, pow_zeroₓ] at this
    rw
      [(by
        norm_cast : (p : Zmod q) = (p : ℤ)),
      (by
        norm_cast : (q : Zmod p) = (q : ℤ)),
      ← legendre_sym_eq_one_iff _ hpq0, ← legendre_sym_eq_one_iff _ hqp0]
    cases' legendre_sym_eq_one_or_neg_one p q hqp0 with h h
    · simp only [← h, ← eq_self_iff_true, ← true_iffₓ, ← mul_oneₓ] at this⊢
      exact this
      
    · simp only [← h, ← mul_neg, ← mul_oneₓ] at this⊢
      rw [eq_neg_of_eq_neg this.symm]
      

theorem exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) (hpq : p ≠ q) :
    IsSquare (q : Zmod p) ↔ ¬IsSquare (p : Zmod q) := by
  have h1 : p / 2 * (q / 2) % 2 = 1 :=
    Nat.odd_mul_odd
      (by
        rw [← mod_mul_right_div_self, show 2 * 2 = 4 from rfl, hp3] <;> rfl)
      (by
        rw [← mod_mul_right_div_self, show 2 * 2 = 4 from rfl, hq3] <;> rfl)
  have hp_odd : p ≠ 2 := by
    by_contra
    simp [← h] at hp3
    norm_num  at hp3
  have hq_odd : q ≠ 2 := by
    by_contra
    simp [← h] at hq3
    norm_num  at hq3
  have hpq0 : ((p : ℤ) : Zmod q) ≠ 0 := by
    exact_mod_cast prime_ne_zero q p (Ne.symm hpq)
  have hqp0 : ((q : ℤ) : Zmod p) ≠ 0 := by
    exact_mod_cast prime_ne_zero p q hpq
  have := quadratic_reciprocity p q hp_odd hq_odd hpq
  rw [neg_one_pow_eq_pow_mod_two, h1, pow_oneₓ] at this
  rw
    [(by
      norm_cast : (p : Zmod q) = (p : ℤ)),
    (by
      norm_cast : (q : Zmod p) = (q : ℤ)),
    ← legendre_sym_eq_one_iff _ hpq0, ← legendre_sym_eq_one_iff _ hqp0]
  cases' legendre_sym_eq_one_or_neg_one q p hpq0 with h h
  · simp only [← h, ← eq_self_iff_true, ← not_true, ← iff_falseₓ, ← one_mulₓ] at this⊢
    simp only [← this]
    norm_num
    
  · simp only [← h, ← neg_mul, ← one_mulₓ, ← neg_inj] at this⊢
    simp only [← this, ← eq_self_iff_true, ← true_iffₓ]
    norm_num
    

end Zmod

