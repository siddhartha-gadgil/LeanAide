/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.LinearAlgebra.Matrix.Adjugate
import Mathbin.RingTheory.MatrixAlgebra
import Mathbin.RingTheory.PolynomialAlgebra
import Mathbin.Tactic.ApplyFun
import Mathbin.Tactic.Squeeze

/-!
# Characteristic polynomials and the Cayley-Hamilton theorem

We define characteristic polynomials of matrices and
prove the Cayley–Hamilton theorem over arbitrary commutative rings.

See the file `matrix/charpoly/coeff` for corollaries of this theorem.

## Main definitions

* `matrix.charpoly` is the characteristic polynomial of a matrix.

## Implementation details

We follow a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/


noncomputable section

universe u v w

open Polynomial Matrix

open BigOperators Polynomial

variable {R : Type u} [CommRingₓ R]

variable {n : Type w} [DecidableEq n] [Fintype n]

open Finset

/-- The "characteristic matrix" of `M : matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (x : R[X]) - (c : R →+* R[X]).mapMatrix M

theorem charmatrix_apply (M : Matrix n n R) (i j : n) : charmatrix M i j = X * (1 : Matrix n n R[X]) i j - c (M i j) :=
  rfl

@[simp]
theorem charmatrix_apply_eq (M : Matrix n n R) (i : n) : charmatrix M i i = (x : R[X]) - c (M i i) := by
  simp only [← charmatrix, ← sub_left_inj, ← Pi.sub_apply, ← scalar_apply_eq, ← RingHom.map_matrix_apply, ← map_apply, ←
    Dmatrix.sub_apply]

@[simp]
theorem charmatrix_apply_ne (M : Matrix n n R) (i j : n) (h : i ≠ j) : charmatrix M i j = -c (M i j) := by
  simp only [← charmatrix, ← Pi.sub_apply, ← scalar_apply_ne _ _ _ h, ← zero_sub, ← RingHom.map_matrix_apply, ←
    map_apply, ← Dmatrix.sub_apply]

theorem mat_poly_equiv_charmatrix (M : Matrix n n R) : matPolyEquiv (charmatrix M) = X - c M := by
  ext k i j
  simp only [← mat_poly_equiv_coeff_apply, ← coeff_sub, ← Pi.sub_apply]
  by_cases' h : i = j
  · subst h
    rw [charmatrix_apply_eq, coeff_sub]
    simp only [← coeff_X, ← coeff_C]
    split_ifs <;> simp
    
  · rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C]
    split_ifs <;> simp [← h]
    

theorem charmatrix_reindex {m : Type v} [DecidableEq m] [Fintype m] (e : n ≃ m) (M : Matrix n n R) :
    charmatrix (reindex e e M) = reindex e e (charmatrix M) := by
  ext i j x
  by_cases' h : i = j
  all_goals
    simp [← h]

/-- The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$.
-/
def Matrix.charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det

theorem Matrix.charpoly_reindex {m : Type v} [DecidableEq m] [Fintype m] (e : n ≃ m) (M : Matrix n n R) :
    (reindex e e M).charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_reindex, Matrix.det_reindex_self]

/-- The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.

See `linear_map.aeval_self_charpoly` for the equivalent statement about endomorphisms.
-/
-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
theorem Matrix.aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0 := by
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `matrix n n R[X]`.
  have h : M.charpoly • (1 : Matrix n n R[X]) = adjugate (charmatrix M) * charmatrix M := (adjugate_mul _).symm
  -- Using the algebra isomorphism `matrix n n R[X] ≃ₐ[R] polynomial (matrix n n R)`,
  -- we have the same identity in `polynomial (matrix n n R)`.
  apply_fun matPolyEquiv  at h
  simp only [← mat_poly_equiv.map_mul, ← mat_poly_equiv_charmatrix] at h
  -- Because the coefficient ring `matrix n n R` is non-commutative,
  -- evaluation at `M` is not multiplicative.
  -- However, any polynomial which is a product of the form $N * (t I - M)$
  -- is sent to zero, because the evaluation function puts the polynomial variable
  -- to the right of any coefficients, so everything telescopes.
  apply_fun fun p => p.eval M  at h
  rw [eval_mul_X_sub_C] at h
  -- Now $χ_M (t) I$, when thought of as a polynomial of matrices
  -- and evaluated at some `N` is exactly $χ_M (N)$.
  rw [mat_poly_equiv_smul_one, eval_map] at h
  -- Thus we have $χ_M(M) = 0$, which is the desired result.
  exact h

