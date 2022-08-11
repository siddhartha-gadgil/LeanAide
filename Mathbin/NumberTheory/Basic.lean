/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathbin.Algebra.GeomSum
import Mathbin.RingTheory.Ideal.Quotient

/-!
# Basic results in number theory

This file should contain basic results in number theory. So far, it only contains the essential
lemma in the construction of the ring of Witt vectors.

## Main statement

`dvd_sub_pow_of_dvd_sub` proves that for elements `a` and `b` in a commutative ring `R` and for
all natural numbers `p` and `k` if `p` divides `a-b` in `R`, then `p ^ (k + 1)` divides
`a ^ (p ^ k) - b ^ (p ^ k)`.
-/


section

open Ideal Ideal.Quotient

theorem dvd_sub_pow_of_dvd_sub {R : Type _} [CommRingₓ R] {p : ℕ} {a b : R} (h : (p : R) ∣ a - b) (k : ℕ) :
    (p ^ (k + 1) : R) ∣ a ^ p ^ k - b ^ p ^ k := by
  induction' k with k ih
  · rwa [pow_oneₓ, pow_zeroₓ, pow_oneₓ, pow_oneₓ]
    
  rw [pow_succ'ₓ p k, pow_mulₓ, pow_mulₓ, ← geom_sum₂_mul, pow_succₓ]
  refine' mul_dvd_mul _ ih
  let I : Ideal R := span {p}
  let f : R →+* R ⧸ I := mk I
  have hp : (p : R ⧸ I) = 0 := by
    rw [← map_nat_cast f, eq_zero_iff_mem, mem_span_singleton]
  rw [← mem_span_singleton, ← Ideal.Quotient.eq] at h
  rw [← mem_span_singleton, ← eq_zero_iff_mem, RingHom.map_geom_sum₂, RingHom.map_pow, RingHom.map_pow, h,
    geom_sum₂_self, hp, zero_mul]

end

