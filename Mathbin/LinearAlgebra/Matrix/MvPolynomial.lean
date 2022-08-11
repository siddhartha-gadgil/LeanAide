/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.Data.MvPolynomial.Basic
import Mathbin.Data.MvPolynomial.CommRing

/-!
# Matrices of multivariate polynomials

In this file, we prove results about matrices over an mv_polynomial ring.
In particular, we provide `matrix.mv_polynomial_X` which associates every entry of a matrix with a
unique variable.

## Tags

matrix determinant, multivariate polynomial
-/


variable {m n R S : Type _}

namespace Matrix

variable (m n R)

/-- The matrix with variable `X (i,j)` at location `(i,j)`. -/
@[simp]
noncomputable def mvPolynomialX [CommSemiringₓ R] : Matrix m n (MvPolynomial (m × n) R)
  | i, j => MvPolynomial.x (i, j)

variable {m n R S}

/-- Any matrix `A` can be expressed as the evaluation of `matrix.mv_polynomial_X`.

This is of particular use when `mv_polynomial (m × n) R` is an integral domain but `S` is
not, as if the `mv_polynomial.eval₂` can be pulled to the outside of a goal, it can be solved in
under cancellative assumptions. -/
theorem mv_polynomial_X_map_eval₂ [CommSemiringₓ R] [CommSemiringₓ S] (f : R →+* S) (A : Matrix m n S) :
    (mvPolynomialX m n R).map ((MvPolynomial.eval₂ f) fun p : m × n => A p.1 p.2) = A :=
  ext fun i j => MvPolynomial.eval₂_X _ (fun p : m × n => A p.1 p.2) (i, j)

/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `ring_hom` on the LHS. -/
theorem mv_polynomial_X_map_matrix_eval [Fintype m] [DecidableEq m] [CommSemiringₓ R] (A : Matrix m m R) :
    (MvPolynomial.eval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mv_polynomial_X_map_eval₂ _ A

variable (R)

/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `alg_hom` on the LHS. -/
theorem mv_polynomial_X_map_matrix_aeval [Fintype m] [DecidableEq m] [CommSemiringₓ R] [CommSemiringₓ S] [Algebra R S]
    (A : Matrix m m S) : (MvPolynomial.aeval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mv_polynomial_X_map_eval₂ _ A

variable (m R)

/-- In a nontrivial ring, `matrix.mv_polynomial_X m m R` has non-zero determinant. -/
theorem det_mv_polynomial_X_ne_zero [DecidableEq m] [Fintype m] [CommRingₓ R] [Nontrivial R] :
    det (mvPolynomialX m m R) ≠ 0 := by
  intro h_det
  have := congr_arg Matrix.det (mv_polynomial_X_map_matrix_eval (1 : Matrix m m R))
  rw [det_one, ← RingHom.map_det, h_det, RingHom.map_zero] at this
  exact zero_ne_one this

end Matrix

