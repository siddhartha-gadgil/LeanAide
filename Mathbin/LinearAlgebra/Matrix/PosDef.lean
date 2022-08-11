/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathbin.LinearAlgebra.Matrix.Spectrum
import Mathbin.LinearAlgebra.QuadraticForm.Basic

/-! # Positive Definite Matrices

This file defines positive definite matrices and connects this notion to positive definiteness of
quadratic forms.

## Main definition

 * `matrix.pos_def` : a matrix `M : matrix n n R` is positive definite if it is hermitian
   and `xᴴMx` is greater than zero for all nonzero `x`.

-/


namespace Matrix

variable {R : Type _} [OrderedSemiring R] [StarRing R] {n : Type _} [Fintype n]

open Matrix

/-- A matrix `M : matrix n n R` is positive definite if it is hermitian
   and `xᴴMx` is greater than zero for all nonzero `x`. -/
def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, x ≠ 0 → 0 < dotProduct (star x) (M.mulVec x)

theorem pos_def_of_to_quadratic_form' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hMq : M.toQuadraticForm'.PosDef) : M.PosDef := by
  refine' ⟨hM, fun x hx => _⟩
  simp only [← to_quadratic_form', ← QuadraticForm.PosDef, ← BilinForm.to_quadratic_form_apply, ←
    Matrix.to_bilin'_apply'] at hMq
  apply hMq x hx

theorem pos_def_to_quadratic_form' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) : M.toQuadraticForm'.PosDef := by
  intro x hx
  simp only [← to_quadratic_form', ← BilinForm.to_quadratic_form_apply, ← Matrix.to_bilin'_apply']
  apply hM.2 x hx

end Matrix

namespace QuadraticForm

variable {n : Type _} [Fintype n]

theorem pos_def_of_to_matrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)} (hQ : Q.toMatrix'.PosDef) : Q.PosDef := by
  rw [← to_quadratic_form_associated ℝ Q, ← bilin_form.to_matrix'.left_inv ((associated_hom _) Q)]
  apply Matrix.pos_def_to_quadratic_form' hQ

theorem pos_def_to_matrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)} (hQ : Q.PosDef) : Q.toMatrix'.PosDef := by
  rw [← to_quadratic_form_associated ℝ Q, ← bilin_form.to_matrix'.left_inv ((associated_hom _) Q)] at hQ
  apply Matrix.pos_def_of_to_quadratic_form' (is_symm_to_matrix' Q) hQ

end QuadraticForm

