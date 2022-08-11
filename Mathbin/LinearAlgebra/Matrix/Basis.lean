/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.LinearAlgebra.Matrix.Reindex
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Bases and matrices

This file defines the map `basis.to_matrix` that sends a family of vectors to
the matrix of their coordinates with respect to some basis.

## Main definitions

 * `basis.to_matrix e v` is the matrix whose `i, j`th entry is `e.repr (v j) i`
 * `basis.to_matrix_equiv` is `basis.to_matrix` bundled as a linear equiv

## Main results

 * `linear_map.to_matrix_id_eq_basis_to_matrix`: `linear_map.to_matrix b c id`
   is equal to `basis.to_matrix b c`
 * `basis.to_matrix_mul_to_matrix`: multiplying `basis.to_matrix` with another
   `basis.to_matrix` gives a `basis.to_matrix`

## Tags

matrix, basis
-/


noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

section BasisToMatrix

variable {ι ι' κ κ' : Type _}

variable {R M : Type _} [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable {R₂ M₂ : Type _} [CommRingₓ R₂] [AddCommGroupₓ M₂] [Module R₂ M₂]

open Function Matrix

/-- From a basis `e : ι → M` and a family of vectors `v : ι' → M`, make the matrix whose columns
are the vectors `v i` written in the basis `e`. -/
def Basis.toMatrix (e : Basis ι R M) (v : ι' → M) : Matrix ι ι' R := fun i j => e.repr (v j) i

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

namespace Basis

theorem to_matrix_apply : e.toMatrix v i j = e.repr (v j) i :=
  rfl

theorem to_matrix_transpose_apply : (e.toMatrix v)ᵀ j = e.repr (v j) :=
  funext fun _ => rfl

theorem to_matrix_eq_to_matrix_constr [Fintype ι] [DecidableEq ι] (v : ι → M) :
    e.toMatrix v = LinearMap.toMatrix e e (e.constr ℕ v) := by
  ext
  rw [Basis.to_matrix_apply, LinearMap.to_matrix_apply, Basis.constr_basis]

-- TODO (maybe) Adjust the definition of `basis.to_matrix` to eliminate the transpose.
theorem CoePiBasisFun.to_matrix_eq_transpose [Fintype ι] :
    ((Pi.basisFun R ι).toMatrix : Matrix ι ι R → Matrix ι ι R) = Matrix.transposeₓ := by
  ext M i j
  rfl

@[simp]
theorem to_matrix_self [DecidableEq ι] : e.toMatrix e = 1 := by
  rw [Basis.toMatrix]
  ext i j
  simp [← Basis.equivFun, ← Matrix.one_apply, ← Finsupp.single, ← eq_comm]

theorem to_matrix_update [DecidableEq ι'] (x : M) :
    e.toMatrix (Function.update v j x) = Matrix.updateColumn (e.toMatrix v) j (e.repr x) := by
  ext i' k
  rw [Basis.toMatrix, Matrix.update_column_apply, e.to_matrix_apply]
  split_ifs
  · rw [h, update_same j x v]
    
  · rw [update_noteq h]
    

/-- The basis constructed by `units_smul` has vectors given by a diagonal matrix. -/
@[simp]
theorem to_matrix_units_smul [DecidableEq ι] (e : Basis ι R₂ M₂) (w : ι → R₂ˣ) :
    e.toMatrix (e.units_smul w) = diagonalₓ (coe ∘ w) := by
  ext i j
  by_cases' h : i = j
  · simp [← h, ← to_matrix_apply, ← units_smul_apply, ← Units.smul_def]
    
  · simp [← h, ← to_matrix_apply, ← units_smul_apply, ← Units.smul_def, ← Ne.symm h]
    

/-- The basis constructed by `is_unit_smul` has vectors given by a diagonal matrix. -/
@[simp]
theorem to_matrix_is_unit_smul [DecidableEq ι] (e : Basis ι R₂ M₂) {w : ι → R₂} (hw : ∀ i, IsUnit (w i)) :
    e.toMatrix (e.isUnitSmul hw) = diagonalₓ w :=
  e.to_matrix_units_smul _

@[simp]
theorem sum_to_matrix_smul_self [Fintype ι] : (∑ i : ι, e.toMatrix v i j • e i) = v j := by
  simp_rw [e.to_matrix_apply, e.sum_repr]

theorem to_matrix_map_vec_mul {S : Type _} [Ringₓ S] [Algebra R S] [Fintype ι] (b : Basis ι R S) (v : ι' → S) :
    ((b.toMatrix v).map <| algebraMap R S).vecMul b = v := by
  ext i
  simp_rw [vec_mul, dot_product, Matrix.map_apply, ← Algebra.commutes, ← Algebra.smul_def, sum_to_matrix_smul_self]

@[simp]
theorem to_lin_to_matrix [Fintype ι] [Fintype ι'] [DecidableEq ι'] (v : Basis ι' R M) :
    Matrix.toLin v e (e.toMatrix v) = id :=
  v.ext fun i => by
    rw [to_lin_self, id_apply, e.sum_to_matrix_smul_self]

/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
def toMatrixEquiv [Fintype ι] (e : Basis ι R M) : (ι → M) ≃ₗ[R] Matrix ι ι R where
  toFun := e.toMatrix
  map_add' := fun v w => by
    ext i j
    change _ = _ + _
    rw [e.to_matrix_apply, Pi.add_apply, LinearEquiv.map_add]
    rfl
  map_smul' := by
    intro c v
    ext i j
    rw [e.to_matrix_apply, Pi.smul_apply, LinearEquiv.map_smul]
    rfl
  invFun := fun m j => ∑ i, m i j • e i
  left_inv := by
    intro v
    ext j
    exact e.sum_to_matrix_smul_self v j
  right_inv := by
    intro m
    ext k l
    simp only [← e.to_matrix_apply, e.equiv_fun_apply, e.equiv_fun_symm_apply, ← LinearEquiv.apply_symm_apply]

end Basis

section MulLinearMapToMatrix

variable {N : Type _} [AddCommMonoidₓ N] [Module R N]

variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)

variable (f : M →ₗ[R] N)

open LinearMap

section Fintype

variable [Fintype ι'] [Fintype κ] [Fintype κ']

@[simp]
theorem basis_to_matrix_mul_linear_map_to_matrix [DecidableEq ι'] :
    c.toMatrix c' ⬝ LinearMap.toMatrix b' c' f = LinearMap.toMatrix b' c f :=
  (Matrix.toLin b' c).Injective
    (by
      have := Classical.decEq κ' <;>
        rw [to_lin_to_matrix, to_lin_mul b' c' c, to_lin_to_matrix, c.to_lin_to_matrix, id_comp])

variable [Fintype ι]

@[simp]
theorem linear_map_to_matrix_mul_basis_to_matrix [DecidableEq ι] [DecidableEq ι'] :
    LinearMap.toMatrix b' c' f ⬝ b'.toMatrix b = LinearMap.toMatrix b c' f :=
  (Matrix.toLin b c').Injective
    (by
      rw [to_lin_to_matrix, to_lin_mul b b' c', to_lin_to_matrix, b'.to_lin_to_matrix, comp_id])

theorem basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix [DecidableEq ι] [DecidableEq ι'] :
    c.toMatrix c' ⬝ LinearMap.toMatrix b' c' f ⬝ b'.toMatrix b = LinearMap.toMatrix b c f := by
  rw [basis_to_matrix_mul_linear_map_to_matrix, linear_map_to_matrix_mul_basis_to_matrix]

theorem basis_to_matrix_mul [DecidableEq κ] (b₁ : Basis ι R M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N)
    (A : Matrix ι' κ R) : b₁.toMatrix b₂ ⬝ A = LinearMap.toMatrix b₃ b₁ (toLin b₃ b₂ A) := by
  have := basis_to_matrix_mul_linear_map_to_matrix b₃ b₁ b₂ (Matrix.toLin b₃ b₂ A)
  rwa [LinearMap.to_matrix_to_lin] at this

theorem mul_basis_to_matrix [DecidableEq ι] [DecidableEq ι'] (b₁ : Basis ι R M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N)
    (A : Matrix κ ι R) : A ⬝ b₁.toMatrix b₂ = LinearMap.toMatrix b₂ b₃ (toLin b₁ b₃ A) := by
  have := linear_map_to_matrix_mul_basis_to_matrix b₂ b₁ b₃ (Matrix.toLin b₁ b₃ A)
  rwa [LinearMap.to_matrix_to_lin] at this

theorem basis_to_matrix_basis_fun_mul (b : Basis ι R (ι → R)) (A : Matrix ι ι R) :
    b.toMatrix (Pi.basisFun R ι) ⬝ A = of fun i j => b.repr (Aᵀ j) i := by
  classical
  simp only [← basis_to_matrix_mul _ _ (Pi.basisFun R ι), ← Matrix.to_lin_eq_to_lin']
  ext i j
  rw [LinearMap.to_matrix_apply, Matrix.to_lin'_apply, Pi.basis_fun_apply, Matrix.mul_vec_std_basis_apply,
    Matrix.of_apply]

/-- A generalization of `linear_map.to_matrix_id`. -/
@[simp]
theorem LinearMap.to_matrix_id_eq_basis_to_matrix [DecidableEq ι] : LinearMap.toMatrix b b' id = b'.toMatrix b := by
  have := Classical.decEq ι'
  rw [← @basis_to_matrix_mul_linear_map_to_matrix _ _ ι, to_matrix_id, Matrix.mul_one]

/-- See also `basis.to_matrix_reindex` which gives the `simp` normal form of this result. -/
theorem Basis.to_matrix_reindex' [DecidableEq ι] [DecidableEq ι'] (b : Basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
    (b.reindex e).toMatrix v = Matrix.reindexAlgEquiv _ e (b.toMatrix (v ∘ e)) := by
  ext
  simp only [← Basis.to_matrix_apply, ← Basis.reindex_repr, ← Matrix.reindex_alg_equiv_apply, ← Matrix.reindex_apply, ←
    Matrix.minor_apply, ← Function.comp_app, ← e.apply_symm_apply]

end Fintype

/-- A generalization of `basis.to_matrix_self`, in the opposite direction. -/
@[simp]
theorem Basis.to_matrix_mul_to_matrix {ι'' : Type _} [Fintype ι'] (b'' : ι'' → M) :
    b.toMatrix b' ⬝ b'.toMatrix b'' = b.toMatrix b'' := by
  have := Classical.decEq ι
  have := Classical.decEq ι'
  have := Classical.decEq ι''
  ext i j
  simp only [← Matrix.mul_apply, ← Basis.to_matrix_apply, ← Basis.sum_repr_mul_repr]

/-- `b.to_matrix b'` and `b'.to_matrix b` are inverses. -/
theorem Basis.to_matrix_mul_to_matrix_flip [DecidableEq ι] [Fintype ι'] : b.toMatrix b' ⬝ b'.toMatrix b = 1 := by
  rw [Basis.to_matrix_mul_to_matrix, Basis.to_matrix_self]

@[simp]
theorem Basis.to_matrix_reindex (b : Basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
    (b.reindex e).toMatrix v = (b.toMatrix v).minor e.symm id := by
  ext
  simp only [← Basis.to_matrix_apply, ← Basis.reindex_repr, ← Matrix.minor_apply, ← id.def]

@[simp]
theorem Basis.to_matrix_map (b : Basis ι R M) (f : M ≃ₗ[R] N) (v : ι → N) :
    (b.map f).toMatrix v = b.toMatrix (f.symm ∘ v) := by
  ext
  simp only [← Basis.to_matrix_apply, ← Basis.map, ← LinearEquiv.trans_apply]

end MulLinearMapToMatrix

end BasisToMatrix

