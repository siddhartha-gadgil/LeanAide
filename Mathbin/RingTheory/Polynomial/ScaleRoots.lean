/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Devon Tuma
-/
import Mathbin.RingTheory.NonZeroDivisors
import Mathbin.Data.Polynomial.AlgebraMap

/-!
# Scaling the roots of a polynomial

This file defines `scale_roots p s` for a polynomial `p` in one variable and a ring element `s` to
be the polynomial with root `r * s` for each root `r` of `p` and proves some basic results about it.
-/


variable {A K R S : Type _} [CommRingₓ A] [IsDomain A] [Field K] [CommRingₓ R] [CommRingₓ S]

variable {M : Submonoid A}

namespace Polynomial

open BigOperators Polynomial

/-- `scale_roots p s` is a polynomial with root `r * s` for each root `r` of `p`. -/
noncomputable def scaleRoots (p : R[X]) (s : R) : R[X] :=
  ∑ i in p.support, monomial i (p.coeff i * s ^ (p.natDegree - i))

@[simp]
theorem coeff_scale_roots (p : R[X]) (s : R) (i : ℕ) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i) :=
  by
  simp (config := { contextual := true })[← scale_roots, ← coeff_monomial]

theorem coeff_scale_roots_nat_degree (p : R[X]) (s : R) : (scaleRoots p s).coeff p.natDegree = p.leadingCoeff := by
  rw [leading_coeff, coeff_scale_roots, tsub_self, pow_zeroₓ, mul_oneₓ]

@[simp]
theorem zero_scale_roots (s : R) : scaleRoots 0 s = 0 := by
  ext
  simp

theorem scale_roots_ne_zero {p : R[X]} (hp : p ≠ 0) (s : R) : scaleRoots p s ≠ 0 := by
  intro h
  have : p.coeff p.nat_degree ≠ 0 := mt leading_coeff_eq_zero.mp hp
  have : (scale_roots p s).coeff p.nat_degree = 0 := congr_fun (congr_arg (coeff : R[X] → ℕ → R) h) p.nat_degree
  rw [coeff_scale_roots_nat_degree] at this
  contradiction

theorem support_scale_roots_le (p : R[X]) (s : R) : (scaleRoots p s).support ≤ p.support := by
  intro
  simpa using left_ne_zero_of_mul

theorem support_scale_roots_eq (p : R[X]) {s : R} (hs : s ∈ nonZeroDivisors R) : (scaleRoots p s).support = p.support :=
  le_antisymmₓ (support_scale_roots_le p s)
    (by
      intro i
      simp only [← coeff_scale_roots, ← Polynomial.mem_support_iff]
      intro p_ne_zero ps_zero
      have := pow_mem hs (p.nat_degree - i) _ ps_zero
      contradiction)

@[simp]
theorem degree_scale_roots (p : R[X]) {s : R} : degree (scaleRoots p s) = degree p := by
  have := Classical.propDecidable
  by_cases' hp : p = 0
  · rw [hp, zero_scale_roots]
    
  have := scale_roots_ne_zero hp s
  refine' le_antisymmₓ (Finset.sup_mono (support_scale_roots_le p s)) (degree_le_degree _)
  rw [coeff_scale_roots_nat_degree]
  intro h
  have := leading_coeff_eq_zero.mp h
  contradiction

@[simp]
theorem nat_degree_scale_roots (p : R[X]) (s : R) : natDegree (scaleRoots p s) = natDegree p := by
  simp only [← nat_degree, ← degree_scale_roots]

theorem monic_scale_roots_iff {p : R[X]} (s : R) : Monic (scaleRoots p s) ↔ Monic p := by
  simp only [← monic, ← leading_coeff, ← nat_degree_scale_roots, ← coeff_scale_roots_nat_degree]

theorem scale_roots_eval₂_eq_zero {p : S[X]} (f : S →+* R) {r : R} {s : S} (hr : eval₂ f r p = 0) :
    eval₂ f (f s * r) (scaleRoots p s) = 0 :=
  calc
    eval₂ f (f s * r) (scaleRoots p s) =
        (scaleRoots p s).support.Sum fun i => f (coeff p i * s ^ (p.natDegree - i)) * (f s * r) ^ i :=
      by
      simp [← eval₂_eq_sum, ← sum_def]
    _ = p.support.Sum fun i => f (coeff p i * s ^ (p.natDegree - i)) * (f s * r) ^ i :=
      Finset.sum_subset (support_scale_roots_le p s) fun i hi hi' => by
        let this : coeff p i * s ^ (p.natDegree - i) = 0 := by
          simpa using hi'
        simp [← this]
    _ = p.support.Sum fun i : ℕ => f (p.coeff i) * f s ^ (p.natDegree - i + i) * r ^ i :=
      Finset.sum_congr rfl fun i hi => by
        simp_rw [f.map_mul, f.map_pow, pow_addₓ, mul_powₓ, mul_assoc]
    _ = p.support.Sum fun i : ℕ => f s ^ p.natDegree * (f (p.coeff i) * r ^ i) :=
      Finset.sum_congr rfl fun i hi => by
        rw [mul_assoc, mul_left_commₓ, tsub_add_cancel_of_le]
        exact le_nat_degree_of_ne_zero (polynomial.mem_support_iff.mp hi)
    _ = f s ^ p.natDegree * p.support.Sum fun i : ℕ => f (p.coeff i) * r ^ i := Finset.mul_sum.symm
    _ = f s ^ p.natDegree * eval₂ f r p := by
      simp [← eval₂_eq_sum, ← sum_def]
    _ = 0 := by
      rw [hr, _root_.mul_zero]
    

theorem scale_roots_aeval_eq_zero [Algebra S R] {p : S[X]} {r : R} {s : S} (hr : aeval r p = 0) :
    aeval (algebraMap S R s * r) (scaleRoots p s) = 0 :=
  scale_roots_eval₂_eq_zero (algebraMap S R) hr

theorem scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero {p : A[X]} {f : A →+* K} (hf : Function.Injective f) {r s : A}
    (hr : eval₂ f (f r / f s) p = 0) (hs : s ∈ nonZeroDivisors A) : eval₂ f (f r) (scaleRoots p s) = 0 := by
  convert scale_roots_eval₂_eq_zero f hr
  rw [← mul_div_assoc, mul_comm, mul_div_cancel]
  exact map_ne_zero_of_mem_non_zero_divisors _ hf hs

theorem scale_roots_aeval_eq_zero_of_aeval_div_eq_zero [Algebra A K] (inj : Function.Injective (algebraMap A K))
    {p : A[X]} {r s : A} (hr : aeval (algebraMap A K r / algebraMap A K s) p = 0) (hs : s ∈ nonZeroDivisors A) :
    aeval (algebraMap A K r) (scaleRoots p s) = 0 :=
  scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

end Polynomial

