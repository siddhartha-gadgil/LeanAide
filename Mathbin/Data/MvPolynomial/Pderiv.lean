/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Yury Kudryashov
-/
import Mathbin.Data.MvPolynomial.Variables
import Mathbin.Data.MvPolynomial.Derivation

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `mv_polynomial.pderiv i p` : the partial derivative of `p` with respect to `i`, as a bundled
  derivation of `mv_polynomial σ R`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_ring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/


noncomputable section

universe u v

namespace MvPolynomial

open Set Function Finsupp AddMonoidAlgebra

open Classical BigOperators

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

section Pderiv

variable {R} [CommSemiringₓ R]

/-- `pderiv i p` is the partial derivative of `p` with respect to `i` -/
def pderiv (i : σ) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R <| Pi.single i 1

@[simp]
theorem pderiv_monomial {i : σ} : pderiv i (monomial s a) = monomial (s - single i 1) (a * s i) := by
  simp only [← pderiv, ← mk_derivation_monomial, ← Finsupp.smul_sum, ← smul_eq_mul, smul_mul_assoc,
    (monomial _).map_smul]
  refine' (Finset.sum_eq_single i (fun j hj hne => _) fun hi => _).trans _
  · simp [← Pi.single_eq_of_ne hne]
    
  · rw [Finsupp.not_mem_support_iff] at hi
    simp [← hi]
    
  · simp
    

theorem pderiv_C {i : σ} : pderiv i (c a) = 0 :=
  derivation_C _ _

theorem pderiv_one {i : σ} : pderiv i (1 : MvPolynomial σ R) = 0 :=
  pderiv_C

@[simp]
theorem pderiv_X [d : DecidableEq σ] (i j : σ) : pderiv i (x j : MvPolynomial σ R) = @Pi.single σ _ d _ i 1 j :=
  (mk_derivation_X _ _ _).trans
    (by
      congr)

@[simp]
theorem pderiv_X_self (i : σ) : pderiv i (x i : MvPolynomial σ R) = 1 := by
  simp

@[simp]
theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv i (x j : MvPolynomial σ R) = 0 := by
  simp [← h]

theorem pderiv_eq_zero_of_not_mem_vars {i : σ} {f : MvPolynomial σ R} (h : i ∉ f.vars) : pderiv i f = 0 :=
  derivation_eq_zero_of_forall_mem_vars fun j hj => pderiv_X_of_ne <| ne_of_mem_of_not_mem hj h

theorem pderiv_monomial_single {i : σ} {n : ℕ} :
    pderiv i (monomial (single i n) a) = monomial (single i (n - 1)) (a * n) := by
  simp

theorem pderiv_mul {i : σ} {f g : MvPolynomial σ R} : pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  simp only [← (pderiv i).leibniz f g, ← smul_eq_mul, ← mul_comm, ← add_commₓ]

@[simp]
theorem pderiv_C_mul {f : MvPolynomial σ R} {i : σ} : pderiv i (c a * f) = c a * pderiv i f :=
  (derivation_C_mul _ _ _).trans C_mul'.symm

end Pderiv

end MvPolynomial

