/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.Algebra.BigOperators.NatAntidiagonal
import Mathbin.Data.Polynomial.RingDivision

/-!
# "Mirror" of a univariate polynomial

In this file we define `polynomial.mirror`, a variant of `polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`.

## Main definitions

- `polynomial.mirror`

## Main results

- `polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`

-/


namespace Polynomial

open Polynomial

section Semiringₓ

variable {R : Type _} [Semiringₓ R] (p q : R[X])

/-- mirror of a polynomial: reverses the coefficients while preserving `polynomial.nat_degree` -/
noncomputable def mirror :=
  p.reverse * X ^ p.natTrailingDegree

@[simp]
theorem mirror_zero : (0 : R[X]).mirror = 0 := by
  simp [← mirror]

theorem mirror_monomial (n : ℕ) (a : R) : (monomial n a).mirror = monomial n a := by
  classical
  by_cases' ha : a = 0
  · rw [ha, monomial_zero_right, mirror_zero]
    
  · rw [mirror, reverse, nat_degree_monomial n a, if_neg ha, nat_trailing_degree_monomial ha, ← C_mul_X_pow_eq_monomial,
      reflect_C_mul_X_pow, rev_at_le (le_reflₓ n), tsub_self, pow_zeroₓ, mul_oneₓ]
    

theorem mirror_C (a : R) : (c a).mirror = c a :=
  mirror_monomial 0 a

theorem mirror_X : x.mirror = (x : R[X]) :=
  mirror_monomial 1 (1 : R)

theorem mirror_nat_degree : p.mirror.natDegree = p.natDegree := by
  by_cases' hp : p = 0
  · rw [hp, mirror_zero]
    
  nontriviality R
  rw [mirror, nat_degree_mul', reverse_nat_degree, nat_degree_X_pow,
    tsub_add_cancel_of_le p.nat_trailing_degree_le_nat_degree]
  rwa [leading_coeff_X_pow, mul_oneₓ, reverse_leading_coeff, Ne, trailing_coeff_eq_zero]

theorem mirror_nat_trailing_degree : p.mirror.natTrailingDegree = p.natTrailingDegree := by
  by_cases' hp : p = 0
  · rw [hp, mirror_zero]
    
  · rw [mirror, nat_trailing_degree_mul_X_pow ((mt reverse_eq_zero.mp) hp), reverse_nat_trailing_degree, zero_addₓ]
    

theorem coeff_mirror (n : ℕ) : p.mirror.coeff n = p.coeff (revAt (p.natDegree + p.natTrailingDegree) n) := by
  by_cases' h2 : p.nat_degree < n
  · rw
      [coeff_eq_zero_of_nat_degree_lt
        (by
          rwa [mirror_nat_degree])]
    by_cases' h1 : n ≤ p.nat_degree + p.nat_trailing_degree
    · rw [rev_at_le h1, coeff_eq_zero_of_lt_nat_trailing_degree]
      exact (tsub_lt_iff_left h1).mpr (Nat.add_lt_add_rightₓ h2 _)
      
    · rw [← rev_at_fun_eq, rev_at_fun, if_neg h1, coeff_eq_zero_of_nat_degree_lt h2]
      
    
  rw [not_ltₓ] at h2
  rw [rev_at_le (h2.trans (Nat.le_add_rightₓ _ _))]
  by_cases' h3 : p.nat_trailing_degree ≤ n
  · rw [← tsub_add_eq_add_tsub h2, ← tsub_tsub_assoc h2 h3, mirror, coeff_mul_X_pow', if_pos h3, coeff_reverse,
      rev_at_le (tsub_le_self.trans h2)]
    
  rw [not_leₓ] at h3
  rw [coeff_eq_zero_of_nat_degree_lt (lt_tsub_iff_right.mpr (Nat.add_lt_add_leftₓ h3 _))]
  exact
    coeff_eq_zero_of_lt_nat_trailing_degree
      (by
        rwa [mirror_nat_trailing_degree])

--TODO: Extract `finset.sum_range_rev_at` lemma.
theorem mirror_eval_one : p.mirror.eval 1 = p.eval 1 := by
  simp_rw [eval_eq_sum_range, one_pow, mul_oneₓ, mirror_nat_degree]
  refine' Finset.sum_bij_ne_zero _ _ _ _ _
  · exact fun n hn hp => rev_at (p.nat_degree + p.nat_trailing_degree) n
    
  · intro n hn hp
    rw [Finset.mem_range_succ_iff] at *
    rw [rev_at_le (hn.trans (Nat.le_add_rightₓ _ _))]
    rw [tsub_le_iff_tsub_le, add_commₓ, add_tsub_cancel_right, ← mirror_nat_trailing_degree]
    exact nat_trailing_degree_le_of_ne_zero hp
    
  · exact fun n₁ n₂ hn₁ hp₁ hn₂ hp₂ h => by
      rw [← @rev_at_invol _ n₁, h, rev_at_invol]
    
  · intro n hn hp
    use rev_at (p.nat_degree + p.nat_trailing_degree) n
    refine' ⟨_, _, rev_at_invol.symm⟩
    · rw [Finset.mem_range_succ_iff] at *
      rw [rev_at_le (hn.trans (Nat.le_add_rightₓ _ _))]
      rw [tsub_le_iff_tsub_le, add_commₓ, add_tsub_cancel_right]
      exact nat_trailing_degree_le_of_ne_zero hp
      
    · change p.mirror.coeff _ ≠ 0
      rwa [coeff_mirror, rev_at_invol]
      
    
  · exact fun n hn hp => p.coeff_mirror n
    

theorem mirror_mirror : p.mirror.mirror = p :=
  Polynomial.ext fun n => by
    rw [coeff_mirror, coeff_mirror, mirror_nat_degree, mirror_nat_trailing_degree, rev_at_invol]

variable {p q}

theorem mirror_involutive : Function.Involutive (mirror : R[X] → R[X]) :=
  mirror_mirror

theorem mirror_eq_iff : p.mirror = q ↔ p = q.mirror :=
  mirror_involutive.eq_iff

@[simp]
theorem mirror_inj : p.mirror = q.mirror ↔ p = q :=
  mirror_involutive.Injective.eq_iff

@[simp]
theorem mirror_eq_zero : p.mirror = 0 ↔ p = 0 :=
  ⟨fun h => by
    rw [← p.mirror_mirror, h, mirror_zero], fun h => by
    rw [h, mirror_zero]⟩

variable (p q)

@[simp]
theorem mirror_trailing_coeff : p.mirror.trailingCoeff = p.leadingCoeff := by
  rw [leading_coeff, trailing_coeff, mirror_nat_trailing_degree, coeff_mirror, rev_at_le (Nat.le_add_leftₓ _ _),
    add_tsub_cancel_right]

@[simp]
theorem mirror_leading_coeff : p.mirror.leadingCoeff = p.trailingCoeff := by
  rw [← p.mirror_mirror, mirror_trailing_coeff, p.mirror_mirror]

theorem coeff_mul_mirror : (p * p.mirror).coeff (p.natDegree + p.natTrailingDegree) = p.Sum fun n => (· ^ 2) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine'
    (Finset.sum_congr rfl fun n hn => _).trans
      (p.sum_eq_of_subset (fun n => (· ^ 2)) (fun n => zero_pow zero_lt_two) _ fun n hn =>
          finset.mem_range_succ_iff.mpr ((le_nat_degree_of_mem_supp n hn).trans (Nat.le_add_rightₓ _ _))).symm
  rw [coeff_mirror, ← rev_at_le (finset.mem_range_succ_iff.mp hn), rev_at_invol, ← sq]

variable [NoZeroDivisors R]

theorem nat_degree_mul_mirror : (p * p.mirror).natDegree = 2 * p.natDegree := by
  by_cases' hp : p = 0
  · rw [hp, zero_mul, nat_degree_zero, mul_zero]
    
  rw [nat_degree_mul hp (mt mirror_eq_zero.mp hp), mirror_nat_degree, two_mul]

theorem nat_trailing_degree_mul_mirror : (p * p.mirror).natTrailingDegree = 2 * p.natTrailingDegree := by
  by_cases' hp : p = 0
  · rw [hp, zero_mul, nat_trailing_degree_zero, mul_zero]
    
  rw [nat_trailing_degree_mul hp (mt mirror_eq_zero.mp hp), mirror_nat_trailing_degree, two_mul]

end Semiringₓ

section Ringₓ

variable {R : Type _} [Ringₓ R] (p q : R[X])

theorem mirror_neg : (-p).mirror = -p.mirror := by
  rw [mirror, mirror, reverse_neg, nat_trailing_degree_neg, neg_mul_eq_neg_mulₓ]

variable [NoZeroDivisors R]

theorem mirror_mul_of_domain : (p * q).mirror = p.mirror * q.mirror := by
  by_cases' hp : p = 0
  · rw [hp, zero_mul, mirror_zero, zero_mul]
    
  by_cases' hq : q = 0
  · rw [hq, mul_zero, mirror_zero, mul_zero]
    
  rw [mirror, mirror, mirror, reverse_mul_of_domain, nat_trailing_degree_mul hp hq, pow_addₓ]
  rw [mul_assoc, ← mul_assoc q.reverse]
  conv_lhs => congr skip congr rw [← X_pow_mul]
  repeat'
    rw [mul_assoc]

theorem mirror_smul (a : R) : (a • p).mirror = a • p.mirror := by
  rw [← C_mul', ← C_mul', mirror_mul_of_domain, mirror_C]

end Ringₓ

section CommRingₓ

variable {R : Type _} [CommRingₓ R] [NoZeroDivisors R] {f : R[X]}

theorem irreducible_of_mirror (h1 : ¬IsUnit f)
    (h2 : ∀ k, f * f.mirror = k * k.mirror → k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror)
    (h3 : ∀ g, g ∣ f → g ∣ f.mirror → IsUnit g) : Irreducible f := by
  constructor
  · exact h1
    
  · intro g h fgh
    let k := g * h.mirror
    have key : f * f.mirror = k * k.mirror := by
      rw [fgh, mirror_mul_of_domain, mirror_mul_of_domain, mirror_mirror, mul_assoc, mul_comm h, mul_comm g.mirror,
        mul_assoc, ← mul_assoc]
    have g_dvd_f : g ∣ f := by
      rw [fgh]
      exact dvd_mul_right g h
    have h_dvd_f : h ∣ f := by
      rw [fgh]
      exact dvd_mul_left h g
    have g_dvd_k : g ∣ k := dvd_mul_right g h.mirror
    have h_dvd_k_rev : h ∣ k.mirror := by
      rw [mirror_mul_of_domain, mirror_mirror]
      exact dvd_mul_left h g.mirror
    have hk := h2 k key
    rcases hk with (hk | hk | hk | hk)
    · exact
        Or.inr
          (h3 h h_dvd_f
            (by
              rwa [← hk]))
      
    · exact
        Or.inr
          (h3 h h_dvd_f
            (by
              rwa [eq_neg_iff_eq_neg.mp hk, mirror_neg, dvd_neg]))
      
    · exact
        Or.inl
          (h3 g g_dvd_f
            (by
              rwa [← hk]))
      
    · exact
        Or.inl
          (h3 g g_dvd_f
            (by
              rwa [eq_neg_iff_eq_neg.mp hk, dvd_neg]))
      
    

end CommRingₓ

end Polynomial

