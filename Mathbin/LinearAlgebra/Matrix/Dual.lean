/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.LinearAlgebra.Dual
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Dual space, linear maps and matrices.

This file contains some results on the matrix corresponding to the
transpose of a linear map (in the dual space).

## Tags

matrix, linear_map, transpose, dual
-/


open Matrix

section Transpose

variable {K V₁ V₂ ι₁ ι₂ : Type _} [Field K] [AddCommGroupₓ V₁] [Module K V₁] [AddCommGroupₓ V₂] [Module K V₂]
  [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {B₁ : Basis ι₁ K V₁} {B₂ : Basis ι₂ K V₂}

@[simp]
theorem LinearMap.to_matrix_transpose (u : V₁ →ₗ[K] V₂) :
    LinearMap.toMatrix B₂.dualBasis B₁.dualBasis (Module.Dual.transpose u) = (LinearMap.toMatrix B₁ B₂ u)ᵀ := by
  ext i j
  simp only [← LinearMap.to_matrix_apply, ← Module.Dual.transpose_apply, ← B₁.dual_basis_repr, ← B₂.dual_basis_apply, ←
    Matrix.transpose_apply, ← LinearMap.comp_apply]

@[simp]
theorem Matrix.to_lin_transpose (M : Matrix ι₁ ι₂ K) :
    Matrix.toLin B₁.dualBasis B₂.dualBasis Mᵀ = Module.Dual.transpose (Matrix.toLin B₂ B₁ M) := by
  apply (LinearMap.toMatrix B₁.dual_basis B₂.dual_basis).Injective
  rw [LinearMap.to_matrix_to_lin, LinearMap.to_matrix_transpose, LinearMap.to_matrix_to_lin]

end Transpose

