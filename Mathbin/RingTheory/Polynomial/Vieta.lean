/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import Mathbin.RingTheory.Polynomial.Basic
import Mathbin.RingTheory.Polynomial.Symmetric

/-!
# Vieta's Formula

The main result is `vieta.prod_X_add_C_eq_sum_esymm`, which shows that the product of linear terms
`λ + X i` is equal to a linear combination of the symmetric polynomials `esymm σ R j`.

## Implementation Notes:

We first take the viewpoint where the "roots" `X i` are variables. This means we work over
`polynomial (mv_polynomial σ R)`, which enables us to talk about linear combinations of
`esymm σ R j`. We then derive Vieta's formula in `polynomial R` by giving a
valuation from each `X i` to `r i`.

-/


open BigOperators Polynomial

open Finset Polynomial Fintype

namespace MvPolynomial

variable {R : Type _} [CommSemiringₓ R]

variable (σ : Type _) [Fintype σ]

/-- A sum version of Vieta's formula. Viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
theorem prod_X_add_C_eq_sum_esymm :
    (∏ i : σ, Polynomial.c (x i) + Polynomial.x : Polynomial (MvPolynomial σ R)) =
      ∑ j in range (card σ + 1), Polynomial.c (esymm σ R j) * Polynomial.x ^ (card σ - j) :=
  by
  classical
  rw [prod_add, sum_powerset]
  refine'
    sum_congr
      (by
        congr)
      fun j hj => _
  rw [esymm, map_sum, sum_mul]
  refine' sum_congr rfl fun t ht => _
  have h : (univ \ t).card = card σ - j := by
    rw [card_sdiff (mem_powerset_len.mp ht).1]
    congr
    exact (mem_powerset_len.mp ht).2
  rw [map_prod, prod_const, ← h]

/-- A fully expanded sum version of Vieta's formula, evaluated at the roots.
The product of linear terms `X + r i` is equal to `∑ j in range (n + 1), e_j * X ^ (n - j)`,
where `e_j` is the `j`th symmetric polynomial of the constant terms `r i`. -/
theorem prod_X_add_C_eval (r : σ → R) :
    (∏ i : σ, Polynomial.c (r i) + Polynomial.x) =
      ∑ i in range (card σ + 1),
        (∑ t in powersetLen i (univ : Finset σ), ∏ i in t, Polynomial.c (r i)) * Polynomial.x ^ (card σ - i) :=
  by
  classical
  have h := @prod_X_add_C_eq_sum_esymm _ _ σ _
  apply_fun Polynomial.map (eval r)  at h
  rw [Polynomial.map_prod, Polynomial.map_sum] at h
  convert h
  simp only [← eval_X, ← Polynomial.map_add, ← Polynomial.map_C, ← Polynomial.map_X, ← eq_self_iff_true]
  funext
  simp only [← Function.funext_iffₓ, ← esymm, ← Polynomial.map_C, ← Polynomial.map_sum, ← map_sum, ← Polynomial.map_C, ←
    Polynomial.map_pow, ← Polynomial.map_X, ← Polynomial.map_mul]
  congr
  funext
  simp only [← eval_prod, ← eval_X, ← map_prod]

theorem esymm_to_sum (r : σ → R) (j : ℕ) :
    Polynomial.c (eval r (esymm σ R j)) = ∑ t in powersetLen j (univ : Finset σ), ∏ i in t, Polynomial.c (r i) := by
  simp only [← esymm, ← eval_sum, ← eval_prod, ← eval_X, ← map_sum, ← map_prod]

/-- Vieta's formula for the coefficients of the product of linear terms `X + r i`,
The `k`th coefficient is `∑ t in powerset_len (card σ - k) (univ : finset σ), ∏ i in t, r i`,
i.e. the symmetric polynomial `esymm σ R (card σ - k)` of the constant terms `r i`. -/
theorem prod_X_add_C_coeff (r : σ → R) (k : ℕ) (h : k ≤ card σ) :
    Polynomial.coeff (∏ i : σ, Polynomial.c (r i) + Polynomial.x) k =
      ∑ t in powersetLen (card σ - k) (univ : Finset σ), ∏ i in t, r i :=
  by
  have hk : filter (fun x : ℕ => k = card σ - x) (range (card σ + 1)) = {card σ - k} := by
    refine' Finset.ext fun a => ⟨fun ha => _, fun ha => _⟩
    rw [mem_singleton]
    have hσ := (tsub_eq_iff_eq_add_of_le (mem_range_succ_iff.mp (mem_filter.mp ha).1)).mp (mem_filter.mp ha).2.symm
    symm
    rwa [tsub_eq_iff_eq_add_of_le h, add_commₓ]
    rw [mem_filter]
    have haσ : a ∈ range (card σ + 1) := by
      rw [mem_singleton.mp ha]
      exact mem_range_succ_iff.mpr (@tsub_le_self _ _ _ _ _ k)
    refine' ⟨haσ, Eq.symm _⟩
    rw [tsub_eq_iff_eq_add_of_le (mem_range_succ_iff.mp haσ)]
    have hσ := (tsub_eq_iff_eq_add_of_le h).mp (mem_singleton.mp ha).symm
    rwa [add_commₓ]
  simp only [← prod_X_add_C_eval, esymm_to_sum, ← finset_sum_coeff, ← coeff_C_mul_X_pow, ← sum_ite, ← hk, ←
    sum_singleton, ← esymm, ← eval_sum, ← eval_prod, ← eval_X, ← add_zeroₓ, ← sum_const_zero]

end MvPolynomial

