/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathbin.Analysis.InnerProductSpace.Spectrum
import Mathbin.LinearAlgebra.Matrix.Hermitian

/-! # Spectral theory of hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`diagonalization_basis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem

-/


namespace Matrix

variable {𝕜 : Type _} [IsROrC 𝕜] [DecidableEq 𝕜] {n : Type _} [Fintype n] [DecidableEq n]

variable {A : Matrix n n 𝕜}

open Matrix

namespace IsHermitian

variable (hA : A.IsHermitian)

/-- The eigenvalues of a hermitian matrix, indexed by `fin (fintype.card n)` where `n` is the index
type of the matrix. -/
noncomputable def eigenvalues₀ : Finₓ (Fintype.card n) → ℝ :=
  @InnerProductSpace.IsSelfAdjoint.eigenvalues 𝕜 _ _ (PiLp 2 fun _ : n => 𝕜) _ A.toLin'
    (is_hermitian_iff_is_self_adjoint.1 hA) _ (Fintype.card n) finrank_euclidean_space

/-- The eigenvalues of a hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ := fun i => hA.eigenvalues₀ <| (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i

/-- A choice of an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  (@InnerProductSpace.IsSelfAdjoint.eigenvectorBasis 𝕜 _ _ (PiLp 2 fun _ : n => 𝕜) _ A.toLin'
        (is_hermitian_iff_is_self_adjoint.1 hA) _ (Fintype.card n) finrank_euclidean_space).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))

/-- A matrix whose columns are an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvectorMatrix : Matrix n n 𝕜 :=
  (Pi.basisFun 𝕜 n).toMatrix (eigenvectorBasis hA).toBasis

/-- The inverse of `eigenvector_matrix` -/
noncomputable def eigenvectorMatrixInv : Matrix n n 𝕜 :=
  (eigenvectorBasis hA).toBasis.toMatrix (Pi.basisFun 𝕜 n)

theorem eigenvector_matrix_mul_inv : hA.eigenvectorMatrix ⬝ hA.eigenvectorMatrixInv = 1 := by
  apply Basis.to_matrix_mul_to_matrix_flip

/-- *Diagonalization theorem*, *spectral theorem* for matrices; A hermitian matrix can be
diagonalized by a change of basis.

For the spectral theorem on linear maps, see `diagonalization_basis_apply_self_apply`. -/
theorem spectral_theorem : hA.eigenvectorMatrixInv ⬝ A = diagonalₓ (coe ∘ hA.Eigenvalues) ⬝ hA.eigenvectorMatrixInv :=
  by
  rw [eigenvector_matrix_inv, basis_to_matrix_basis_fun_mul]
  ext i j
  convert
    @InnerProductSpace.IsSelfAdjoint.diagonalization_basis_apply_self_apply 𝕜 _ _ (PiLp 2 fun _ : n => 𝕜) _ A.to_lin'
      (is_hermitian_iff_is_self_adjoint.1 hA) _ (Fintype.card n) finrank_euclidean_space (EuclideanSpace.single j 1)
      ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
  · rw [eigenvector_basis, to_lin'_apply]
    simp only [← Basis.toMatrix, ← Basis.coe_to_orthonormal_basis_repr, ← Basis.equiv_fun_apply]
    simp_rw [OrthonormalBasis.coe_to_basis_repr_apply, OrthonormalBasis.reindex_repr, EuclideanSpace.single,
      PiLp.equiv_symm_apply', mul_vec_single, mul_oneₓ]
    rfl
    
  · simp only [← diagonal_mul, ← (· ∘ ·), ← eigenvalues, ← eigenvector_basis]
    rw [Basis.to_matrix_apply, OrthonormalBasis.coe_to_basis_repr_apply, OrthonormalBasis.reindex_repr,
      Pi.basis_fun_apply, eigenvalues₀, LinearMap.coe_std_basis, EuclideanSpace.single, PiLp.equiv_symm_apply']
    

end IsHermitian

end Matrix

