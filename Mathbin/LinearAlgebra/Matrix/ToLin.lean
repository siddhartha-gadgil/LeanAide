/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.Data.Matrix.Block
import Mathbin.Data.Matrix.Notation
import Mathbin.LinearAlgebra.Matrix.FiniteDimensional
import Mathbin.LinearAlgebra.StdBasis
import Mathbin.RingTheory.AlgebraTower
import Mathbin.Algebra.Module.Algebra

/-!
# Linear maps and matrices

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

 * `linear_map.to_matrix`: given bases `v₁ : ι → M₁` and `v₂ : κ → M₂`,
   the `R`-linear equivalence from `M₁ →ₗ[R] M₂` to `matrix κ ι R`
 * `matrix.to_lin`: the inverse of `linear_map.to_matrix`
 * `linear_map.to_matrix'`: the `R`-linear equivalence from `(m → R) →ₗ[R] (n → R)`
   to `matrix m n R` (with the standard basis on `m → R` and `n → R`)
 * `matrix.to_lin'`: the inverse of `linear_map.to_matrix'`
 * `alg_equiv_matrix`: given a basis indexed by `n`, the `R`-algebra equivalence between
   `R`-endomorphisms of `M` and `matrix n n R`

## Issues

This file was originally written without attention to non-commutative rings,
and so mostly only works in the commutative setting. This should be fixed.

In particular, `matrix.mul_vec` gives us a linear equivalence
`matrix m n R ≃ₗ[R] (n → R) →ₗ[Rᵐᵒᵖ] (m → R)`
while `matrix.vec_mul` gives us a linear equivalence
`matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] (n → R)`.
At present, the first equivalence is developed in detail but only for commutative rings
(and we omit the distinction between `Rᵐᵒᵖ` and `R`),
while the second equivalence is developed only in brief, but for not-necessarily-commutative rings.

Naming is slightly inconsistent between the two developments.
In the original (commutative) development `linear` is abbreviated to `lin`,
although this is not consistent with the rest of mathlib.
In the new (non-commutative) development `linear` is not abbreviated, and declarations use `_right`
to indicate they use the right action of matrices on vectors (via `matrix.vec_mul`).
When the two developments are made uniform, the names should be made uniform, too,
by choosing between `linear` and `lin` consistently,
and (presumably) adding `_left` where necessary.

## Tags

linear_map, matrix, linear_equiv, diagonal, det, trace
-/


noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

universe u v w

instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (R) [Fintype R] : Fintype (Matrix m n R) := by
  unfold Matrix <;> infer_instance

section ToMatrixRight

variable {R : Type _} [Semiringₓ R]

variable {l m n : Type _}

/-- `matrix.vec_mul M` is a linear map. -/
@[simps]
def Matrix.vecMulLinear [Fintype m] (M : Matrix m n R) : (m → R) →ₗ[R] n → R where
  toFun := fun x => M.vecMul x
  map_add' := fun v w => funext fun i => add_dot_product _ _ _
  map_smul' := fun c v => funext fun i => smul_dot_product _ _ _

variable [Fintype m] [DecidableEq m]

@[simp]
theorem Matrix.vec_mul_std_basis (M : Matrix m n R) (i j) : M.vecMul (stdBasis R (fun _ => R) i 1) j = M i j := by
  have : (∑ i', (if i = i' then 1 else 0) * M i' j) = M i j := by
    simp_rw [boole_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  convert this
  ext
  split_ifs with h <;> simp only [← std_basis_apply]
  · rw [h, Function.update_same]
    
  · rw [Function.update_noteq (Ne.symm h), Pi.zero_apply]
    

/-- Linear maps `(m → R) →ₗ[R] (n → R)` are linearly equivalent over `Rᵐᵒᵖ` to `matrix m n R`,
by having matrices act by right multiplication.
 -/
def LinearMap.toMatrixRight' : ((m → R) →ₗ[R] n → R) ≃ₗ[Rᵐᵒᵖ] Matrix m n R where
  toFun := fun f i j => f (stdBasis R (fun _ => R) i 1) j
  invFun := Matrix.vecMulLinear
  right_inv := fun M => by
    ext i j
    simp only [← Matrix.vec_mul_std_basis, ← Matrix.vec_mul_linear_apply]
  left_inv := fun f => by
    apply (Pi.basisFun R m).ext
    intro j
    ext i
    simp only [← Pi.basis_fun_apply, ← Matrix.vec_mul_std_basis, ← Matrix.vec_mul_linear_apply]
  map_add' := fun f g => by
    ext i j
    simp only [← Pi.add_apply, ← LinearMap.add_apply]
  map_smul' := fun c f => by
    ext i j
    simp only [← Pi.smul_apply, ← LinearMap.smul_apply, ← RingHom.id_apply]

/-- A `matrix m n R` is linearly equivalent over `Rᵐᵒᵖ` to a linear map `(m → R) →ₗ[R] (n → R)`,
by having matrices act by right multiplication. -/
abbrev Matrix.toLinearMapRight' : Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] n → R :=
  LinearMap.toMatrixRight'.symm

@[simp]
theorem Matrix.to_linear_map_right'_apply (M : Matrix m n R) (v : m → R) : Matrix.toLinearMapRight' M v = M.vecMul v :=
  rfl

@[simp]
theorem Matrix.to_linear_map_right'_mul [Fintype l] [DecidableEq l] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.toLinearMapRight' (M ⬝ N) = (Matrix.toLinearMapRight' N).comp (Matrix.toLinearMapRight' M) :=
  LinearMap.ext fun x => (vec_mul_vec_mul _ M N).symm

theorem Matrix.to_linear_map_right'_mul_apply [Fintype l] [DecidableEq l] (M : Matrix l m R) (N : Matrix m n R) (x) :
    Matrix.toLinearMapRight' (M ⬝ N) x = Matrix.toLinearMapRight' N (Matrix.toLinearMapRight' M x) :=
  (vec_mul_vec_mul _ M N).symm

@[simp]
theorem Matrix.to_linear_map_right'_one : Matrix.toLinearMapRight' (1 : Matrix m m R) = id := by
  ext
  simp [← LinearMap.one_apply, ← std_basis_apply]

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `n → A`
and `m → A` corresponding to `M.vec_mul` and `M'.vec_mul`. -/
@[simps]
def Matrix.toLinearEquivRight'OfInv [Fintype n] [DecidableEq n] {M : Matrix m n R} {M' : Matrix n m R}
    (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) : (n → R) ≃ₗ[R] m → R :=
  { LinearMap.toMatrixRight'.symm M' with toFun := M'.toLinearMapRight', invFun := M.toLinearMapRight',
    left_inv := fun x => by
      rw [← Matrix.to_linear_map_right'_mul_apply, hM'M, Matrix.to_linear_map_right'_one, id_apply],
    right_inv := fun x => by
      rw [← Matrix.to_linear_map_right'_mul_apply, hMM', Matrix.to_linear_map_right'_one, id_apply] }

end ToMatrixRight

/-!
From this point on, we only work with commutative rings,
and fail to distinguish between `Rᵐᵒᵖ` and `R`.
This should eventually be remedied.
-/


section ToMatrix'

variable {R : Type _} [CommSemiringₓ R]

variable {l m n : Type _}

/-- `matrix.mul_vec M` is a linear map. -/
@[simps]
def Matrix.mulVecLin [Fintype n] (M : Matrix m n R) : (n → R) →ₗ[R] m → R where
  toFun := M.mulVec
  map_add' := fun v w => funext fun i => dot_product_add _ _ _
  map_smul' := fun c v => funext fun i => dot_product_smul _ _ _

variable [Fintype n] [DecidableEq n]

theorem Matrix.mul_vec_std_basis (M : Matrix m n R) (i j) : M.mulVec (stdBasis R (fun _ => R) j 1) i = M i j :=
  (congr_fun (Matrix.mul_vec_single _ _ (1 : R)) i).trans <| mul_oneₓ _

@[simp]
theorem Matrix.mul_vec_std_basis_apply (M : Matrix m n R) (j) : M.mulVec (stdBasis R (fun _ => R) j 1) = Mᵀ j :=
  funext fun i => Matrix.mul_vec_std_basis M i j

/-- Linear maps `(n → R) →ₗ[R] (m → R)` are linearly equivalent to `matrix m n R`. -/
def LinearMap.toMatrix' : ((n → R) →ₗ[R] m → R) ≃ₗ[R] Matrix m n R where
  toFun := fun f => of fun i j => f (stdBasis R (fun _ => R) j 1) i
  invFun := Matrix.mulVecLin
  right_inv := fun M => by
    ext i j
    simp only [← Matrix.mul_vec_std_basis, ← Matrix.mul_vec_lin_apply, ← of_apply]
  left_inv := fun f => by
    apply (Pi.basisFun R n).ext
    intro j
    ext i
    simp only [← Pi.basis_fun_apply, ← Matrix.mul_vec_std_basis, ← Matrix.mul_vec_lin_apply, ← of_apply]
  map_add' := fun f g => by
    ext i j
    simp only [← Pi.add_apply, ← LinearMap.add_apply, ← of_apply]
  map_smul' := fun c f => by
    ext i j
    simp only [← Pi.smul_apply, ← LinearMap.smul_apply, ← RingHom.id_apply, ← of_apply]

/-- A `matrix m n R` is linearly equivalent to a linear map `(n → R) →ₗ[R] (m → R)`. -/
def Matrix.toLin' : Matrix m n R ≃ₗ[R] (n → R) →ₗ[R] m → R :=
  LinearMap.toMatrix'.symm

@[simp]
theorem LinearMap.to_matrix'_symm : (LinearMap.toMatrix'.symm : Matrix m n R ≃ₗ[R] _) = Matrix.toLin' :=
  rfl

@[simp]
theorem Matrix.to_lin'_symm : (Matrix.toLin'.symm : ((n → R) →ₗ[R] m → R) ≃ₗ[R] _) = LinearMap.toMatrix' :=
  rfl

@[simp]
theorem LinearMap.to_matrix'_to_lin' (M : Matrix m n R) : LinearMap.toMatrix' (Matrix.toLin' M) = M :=
  LinearMap.toMatrix'.apply_symm_apply M

@[simp]
theorem Matrix.to_lin'_to_matrix' (f : (n → R) →ₗ[R] m → R) : Matrix.toLin' (LinearMap.toMatrix' f) = f :=
  Matrix.toLin'.apply_symm_apply f

@[simp]
theorem LinearMap.to_matrix'_apply (f : (n → R) →ₗ[R] m → R) (i j) :
    LinearMap.toMatrix' f i j = f (fun j' => if j' = j then 1 else 0) i := by
  simp only [← LinearMap.toMatrix', ← LinearEquiv.coe_mk, ← of_apply]
  congr
  ext j'
  split_ifs with h
  · rw [h, std_basis_same]
    
  apply std_basis_ne _ _ _ _ h

@[simp]
theorem Matrix.to_lin'_apply (M : Matrix m n R) (v : n → R) : Matrix.toLin' M v = M.mulVec v :=
  rfl

@[simp]
theorem Matrix.to_lin'_one : Matrix.toLin' (1 : Matrix n n R) = id := by
  ext
  simp [← LinearMap.one_apply, ← std_basis_apply]

@[simp]
theorem LinearMap.to_matrix'_id : LinearMap.toMatrix' (LinearMap.id : (n → R) →ₗ[R] n → R) = 1 := by
  ext
  rw [Matrix.one_apply, LinearMap.to_matrix'_apply, id_apply]

@[simp]
theorem Matrix.to_lin'_mul [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.toLin' (M ⬝ N) = (Matrix.toLin' M).comp (Matrix.toLin' N) :=
  LinearMap.ext fun x => (mul_vec_mul_vec _ _ _).symm

/-- Shortcut lemma for `matrix.to_lin'_mul` and `linear_map.comp_apply` -/
theorem Matrix.to_lin'_mul_apply [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R) (x) :
    Matrix.toLin' (M ⬝ N) x = Matrix.toLin' M (Matrix.toLin' N x) := by
  rw [Matrix.to_lin'_mul, LinearMap.comp_apply]

theorem LinearMap.to_matrix'_comp [Fintype l] [DecidableEq l] (f : (n → R) →ₗ[R] m → R) (g : (l → R) →ₗ[R] n → R) :
    (f.comp g).toMatrix' = f.toMatrix' ⬝ g.toMatrix' := by
  suffices f.comp g = (f.toMatrix' ⬝ g.toMatrix').toLin' by
    rw [this, LinearMap.to_matrix'_to_lin']
  rw [Matrix.to_lin'_mul, Matrix.to_lin'_to_matrix', Matrix.to_lin'_to_matrix']

theorem LinearMap.to_matrix'_mul [Fintype m] [DecidableEq m] (f g : (m → R) →ₗ[R] m → R) :
    (f * g).toMatrix' = f.toMatrix' ⬝ g.toMatrix' :=
  LinearMap.to_matrix'_comp f g

@[simp]
theorem LinearMap.to_matrix'_algebra_map (x : R) :
    LinearMap.toMatrix' (algebraMap R (Module.End R (n → R)) x) = scalar n x := by
  simp [← Module.algebra_map_End_eq_smul_id]

theorem Matrix.ker_to_lin'_eq_bot_iff {M : Matrix n n R} : M.toLin'.ker = ⊥ ↔ ∀ v, M.mulVec v = 0 → v = 0 := by
  simp only [← Submodule.eq_bot_iff, ← LinearMap.mem_ker, ← Matrix.to_lin'_apply]

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `m → A`
and `n → A` corresponding to `M.mul_vec` and `M'.mul_vec`. -/
@[simps]
def Matrix.toLin'OfInv [Fintype m] [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (hMM' : M ⬝ M' = 1)
    (hM'M : M' ⬝ M = 1) : (m → R) ≃ₗ[R] n → R :=
  { Matrix.toLin' M' with toFun := Matrix.toLin' M', invFun := M.toLin',
    left_inv := fun x => by
      rw [← Matrix.to_lin'_mul_apply, hMM', Matrix.to_lin'_one, id_apply],
    right_inv := fun x => by
      rw [← Matrix.to_lin'_mul_apply, hM'M, Matrix.to_lin'_one, id_apply] }

/-- Linear maps `(n → R) →ₗ[R] (n → R)` are algebra equivalent to `matrix n n R`. -/
def LinearMap.toMatrixAlgEquiv' : ((n → R) →ₗ[R] n → R) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv LinearMap.toMatrix' LinearMap.to_matrix'_mul LinearMap.to_matrix'_algebra_map

/-- A `matrix n n R` is algebra equivalent to a linear map `(n → R) →ₗ[R] (n → R)`. -/
def Matrix.toLinAlgEquiv' : Matrix n n R ≃ₐ[R] (n → R) →ₗ[R] n → R :=
  LinearMap.toMatrixAlgEquiv'.symm

@[simp]
theorem LinearMap.to_matrix_alg_equiv'_symm :
    (LinearMap.toMatrixAlgEquiv'.symm : Matrix n n R ≃ₐ[R] _) = Matrix.toLinAlgEquiv' :=
  rfl

@[simp]
theorem Matrix.to_lin_alg_equiv'_symm :
    (Matrix.toLinAlgEquiv'.symm : ((n → R) →ₗ[R] n → R) ≃ₐ[R] _) = LinearMap.toMatrixAlgEquiv' :=
  rfl

@[simp]
theorem LinearMap.to_matrix_alg_equiv'_to_lin_alg_equiv' (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' M) = M :=
  LinearMap.toMatrixAlgEquiv'.apply_symm_apply M

@[simp]
theorem Matrix.to_lin_alg_equiv'_to_matrix_alg_equiv' (f : (n → R) →ₗ[R] n → R) :
    Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' f) = f :=
  Matrix.toLinAlgEquiv'.apply_symm_apply f

@[simp]
theorem LinearMap.to_matrix_alg_equiv'_apply (f : (n → R) →ₗ[R] n → R) (i j) :
    LinearMap.toMatrixAlgEquiv' f i j = f (fun j' => if j' = j then 1 else 0) i := by
  simp [← LinearMap.toMatrixAlgEquiv']

@[simp]
theorem Matrix.to_lin_alg_equiv'_apply (M : Matrix n n R) (v : n → R) : Matrix.toLinAlgEquiv' M v = M.mulVec v :=
  rfl

@[simp]
theorem Matrix.to_lin_alg_equiv'_one : Matrix.toLinAlgEquiv' (1 : Matrix n n R) = id :=
  Matrix.to_lin'_one

@[simp]
theorem LinearMap.to_matrix_alg_equiv'_id : LinearMap.toMatrixAlgEquiv' (LinearMap.id : (n → R) →ₗ[R] n → R) = 1 :=
  LinearMap.to_matrix'_id

@[simp]
theorem Matrix.to_lin_alg_equiv'_mul (M N : Matrix n n R) :
    Matrix.toLinAlgEquiv' (M ⬝ N) = (Matrix.toLinAlgEquiv' M).comp (Matrix.toLinAlgEquiv' N) :=
  Matrix.to_lin'_mul _ _

theorem LinearMap.to_matrix_alg_equiv'_comp (f g : (n → R) →ₗ[R] n → R) :
    (f.comp g).toMatrixAlgEquiv' = f.toMatrixAlgEquiv' ⬝ g.toMatrixAlgEquiv' :=
  LinearMap.to_matrix'_comp _ _

theorem LinearMap.to_matrix_alg_equiv'_mul (f g : (n → R) →ₗ[R] n → R) :
    (f * g).toMatrixAlgEquiv' = f.toMatrixAlgEquiv' ⬝ g.toMatrixAlgEquiv' :=
  LinearMap.to_matrix_alg_equiv'_comp f g

theorem Matrix.rank_vec_mul_vec {K m n : Type u} [Field K] [Fintype n] [DecidableEq n] (w : m → K) (v : n → K) :
    rank (vecMulVecₓ w v).toLin' ≤ 1 := by
  rw [vec_mul_vec_eq, Matrix.to_lin'_mul]
  refine' le_transₓ (rank_comp_le1 _ _) _
  refine' (rank_le_domain _).trans_eq _
  rw [dim_fun', Fintype.card_unit, Nat.cast_oneₓ]

end ToMatrix'

section ToMatrix

variable {R : Type _} [CommSemiringₓ R]

variable {l m n : Type _} [Fintype n] [Fintype m] [DecidableEq n]

variable {M₁ M₂ : Type _} [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the bases. -/
def LinearMap.toMatrix : (M₁ →ₗ[R] M₂) ≃ₗ[R] Matrix m n R :=
  LinearEquiv.trans (LinearEquiv.arrowCongr v₁.equivFun v₂.equivFun) LinearMap.toMatrix'

/-- `linear_map.to_matrix'` is a particular case of `linear_map.to_matrix`, for the standard basis
`pi.basis_fun R n`. -/
theorem LinearMap.to_matrix_eq_to_matrix' :
    LinearMap.toMatrix (Pi.basisFun R n) (Pi.basisFun R n) = LinearMap.toMatrix' :=
  rfl

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between matrices over `R` indexed by the bases and linear maps `M₁ →ₗ M₂`. -/
def Matrix.toLin : Matrix m n R ≃ₗ[R] M₁ →ₗ[R] M₂ :=
  (LinearMap.toMatrix v₁ v₂).symm

/-- `matrix.to_lin'` is a particular case of `matrix.to_lin`, for the standard basis
`pi.basis_fun R n`. -/
theorem Matrix.to_lin_eq_to_lin' : Matrix.toLin (Pi.basisFun R n) (Pi.basisFun R m) = Matrix.toLin' :=
  rfl

@[simp]
theorem LinearMap.to_matrix_symm : (LinearMap.toMatrix v₁ v₂).symm = Matrix.toLin v₁ v₂ :=
  rfl

@[simp]
theorem Matrix.to_lin_symm : (Matrix.toLin v₁ v₂).symm = LinearMap.toMatrix v₁ v₂ :=
  rfl

@[simp]
theorem Matrix.to_lin_to_matrix (f : M₁ →ₗ[R] M₂) : Matrix.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f := by
  rw [← Matrix.to_lin_symm, LinearEquiv.apply_symm_apply]

@[simp]
theorem LinearMap.to_matrix_to_lin (M : Matrix m n R) : LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M := by
  rw [← Matrix.to_lin_symm, LinearEquiv.symm_apply_apply]

theorem LinearMap.to_matrix_apply (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i := by
  rw [LinearMap.toMatrix, LinearEquiv.trans_apply, LinearMap.to_matrix'_apply, LinearEquiv.arrow_congr_apply,
    Basis.equiv_fun_symm_apply, Finset.sum_eq_single j, if_pos rfl, one_smul, Basis.equiv_fun_apply]
  · intro j' _ hj'
    rw [if_neg hj', zero_smul]
    
  · intro hj
    have := Finset.mem_univ j
    contradiction
    

theorem LinearMap.to_matrix_transpose_apply (f : M₁ →ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  funext fun i => f.to_matrix_apply _ _ i j

theorem LinearMap.to_matrix_apply' (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
  LinearMap.to_matrix_apply v₁ v₂ f i j

theorem LinearMap.to_matrix_transpose_apply' (f : M₁ →ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  LinearMap.to_matrix_transpose_apply v₁ v₂ f j

theorem Matrix.to_lin_apply (M : Matrix m n R) (v : M₁) : Matrix.toLin v₁ v₂ M v = ∑ j, M.mulVec (v₁.repr v) j • v₂ j :=
  show v₂.equivFun.symm (Matrix.toLin' M (v₁.repr v)) = _ by
    rw [Matrix.to_lin'_apply, v₂.equiv_fun_symm_apply]

@[simp]
theorem Matrix.to_lin_self (M : Matrix m n R) (i : n) : Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j := by
  rw [Matrix.to_lin_apply, Finset.sum_congr rfl fun j hj => _]
  rw [Basis.repr_self, Matrix.mulVecₓ, dot_product, Finset.sum_eq_single i, Finsupp.single_eq_same, mul_oneₓ]
  · intro i' _ i'_ne
    rw [Finsupp.single_eq_of_ne i'_ne.symm, mul_zero]
    
  · intros
    have := Finset.mem_univ i
    contradiction
    

/-- This will be a special case of `linear_map.to_matrix_id_eq_basis_to_matrix`. -/
theorem LinearMap.to_matrix_id : LinearMap.toMatrix v₁ v₁ id = 1 := by
  ext i j
  simp [← LinearMap.to_matrix_apply, ← Matrix.one_apply, ← Finsupp.single, ← eq_comm]

theorem LinearMap.to_matrix_one : LinearMap.toMatrix v₁ v₁ 1 = 1 :=
  LinearMap.to_matrix_id v₁

@[simp]
theorem Matrix.to_lin_one : Matrix.toLin v₁ v₁ 1 = id := by
  rw [← LinearMap.to_matrix_id v₁, Matrix.to_lin_to_matrix]

theorem LinearMap.to_matrix_reindex_range [DecidableEq M₁] [DecidableEq M₂] (f : M₁ →ₗ[R] M₂) (k : m) (i : n) :
    LinearMap.toMatrix v₁.reindexRange v₂.reindexRange f ⟨v₂ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
      LinearMap.toMatrix v₁ v₂ f k i :=
  by
  simp_rw [LinearMap.to_matrix_apply, Basis.reindex_range_self, Basis.reindex_range_repr]

variable {M₃ : Type _} [AddCommMonoidₓ M₃] [Module R M₃] (v₃ : Basis l R M₃)

theorem LinearMap.to_matrix_comp [Fintype l] [DecidableEq m] (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
    LinearMap.toMatrix v₁ v₃ (f.comp g) = LinearMap.toMatrix v₂ v₃ f ⬝ LinearMap.toMatrix v₁ v₂ g := by
  simp_rw [LinearMap.toMatrix, LinearEquiv.trans_apply, LinearEquiv.arrow_congr_comp _ v₂.equiv_fun,
    LinearMap.to_matrix'_comp]

theorem LinearMap.to_matrix_mul (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f ⬝ LinearMap.toMatrix v₁ v₁ g := by
  rw [show @Mul.mul (M₁ →ₗ[R] M₁) _ = LinearMap.comp from rfl, LinearMap.to_matrix_comp v₁ v₁ v₁ f g]

@[simp]
theorem LinearMap.to_matrix_algebra_map (x : R) :
    LinearMap.toMatrix v₁ v₁ (algebraMap R (Module.End R M₁) x) = scalar n x := by
  simp [← Module.algebra_map_End_eq_smul_id, ← LinearMap.to_matrix_id]

theorem LinearMap.to_matrix_mul_vec_repr (f : M₁ →ₗ[R] M₂) (x : M₁) :
    (LinearMap.toMatrix v₁ v₂ f).mulVec (v₁.repr x) = v₂.repr (f x) := by
  ext i
  rw [← Matrix.to_lin'_apply, LinearMap.toMatrix, LinearEquiv.trans_apply, Matrix.to_lin'_to_matrix',
    LinearEquiv.arrow_congr_apply, v₂.equiv_fun_apply]
  congr
  exact v₁.equiv_fun.symm_apply_apply x

theorem Matrix.to_lin_mul [Fintype l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R) :
    Matrix.toLin v₁ v₃ (A ⬝ B) = (Matrix.toLin v₂ v₃ A).comp (Matrix.toLin v₁ v₂ B) := by
  apply (LinearMap.toMatrix v₁ v₃).Injective
  have : DecidableEq l := fun _ _ => Classical.propDecidable _
  rw [LinearMap.to_matrix_comp v₁ v₂ v₃]
  repeat'
    rw [LinearMap.to_matrix_to_lin]

/-- Shortcut lemma for `matrix.to_lin_mul` and `linear_map.comp_apply`. -/
theorem Matrix.to_lin_mul_apply [Fintype l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R) (x) :
    Matrix.toLin v₁ v₃ (A ⬝ B) x = (Matrix.toLin v₂ v₃ A) (Matrix.toLin v₁ v₂ B x) := by
  rw [Matrix.to_lin_mul v₁ v₂, LinearMap.comp_apply]

/-- If `M` and `M` are each other's inverse matrices, `matrix.to_lin M` and `matrix.to_lin M'`
form a linear equivalence. -/
@[simps]
def Matrix.toLinOfInv [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
    M₁ ≃ₗ[R] M₂ :=
  { Matrix.toLin v₁ v₂ M with toFun := Matrix.toLin v₁ v₂ M, invFun := Matrix.toLin v₂ v₁ M',
    left_inv := fun x => by
      rw [← Matrix.to_lin_mul_apply, hM'M, Matrix.to_lin_one, id_apply],
    right_inv := fun x => by
      rw [← Matrix.to_lin_mul_apply, hMM', Matrix.to_lin_one, id_apply] }

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between linear maps `M₁ →ₗ M₁` and square matrices over `R` indexed by the basis. -/
def LinearMap.toMatrixAlgEquiv : (M₁ →ₗ[R] M₁) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv (LinearMap.toMatrix v₁ v₁) (LinearMap.to_matrix_mul v₁) (LinearMap.to_matrix_algebra_map v₁)

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between square matrices over `R` indexed by the basis and linear maps `M₁ →ₗ M₁`. -/
def Matrix.toLinAlgEquiv : Matrix n n R ≃ₐ[R] M₁ →ₗ[R] M₁ :=
  (LinearMap.toMatrixAlgEquiv v₁).symm

@[simp]
theorem LinearMap.to_matrix_alg_equiv_symm : (LinearMap.toMatrixAlgEquiv v₁).symm = Matrix.toLinAlgEquiv v₁ :=
  rfl

@[simp]
theorem Matrix.to_lin_alg_equiv_symm : (Matrix.toLinAlgEquiv v₁).symm = LinearMap.toMatrixAlgEquiv v₁ :=
  rfl

@[simp]
theorem Matrix.to_lin_alg_equiv_to_matrix_alg_equiv (f : M₁ →ₗ[R] M₁) :
    Matrix.toLinAlgEquiv v₁ (LinearMap.toMatrixAlgEquiv v₁ f) = f := by
  rw [← Matrix.to_lin_alg_equiv_symm, AlgEquiv.apply_symm_apply]

@[simp]
theorem LinearMap.to_matrix_alg_equiv_to_lin_alg_equiv (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv v₁ (Matrix.toLinAlgEquiv v₁ M) = M := by
  rw [← Matrix.to_lin_alg_equiv_symm, AlgEquiv.symm_apply_apply]

theorem LinearMap.to_matrix_alg_equiv_apply (f : M₁ →ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i := by
  simp [← LinearMap.toMatrixAlgEquiv, ← LinearMap.to_matrix_apply]

theorem LinearMap.to_matrix_alg_equiv_transpose_apply (f : M₁ →ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  funext fun i => f.to_matrix_apply _ _ i j

theorem LinearMap.to_matrix_alg_equiv_apply' (f : M₁ →ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i :=
  LinearMap.to_matrix_alg_equiv_apply v₁ f i j

theorem LinearMap.to_matrix_alg_equiv_transpose_apply' (f : M₁ →ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  LinearMap.to_matrix_alg_equiv_transpose_apply v₁ f j

theorem Matrix.to_lin_alg_equiv_apply (M : Matrix n n R) (v : M₁) :
    Matrix.toLinAlgEquiv v₁ M v = ∑ j, M.mulVec (v₁.repr v) j • v₁ j :=
  show v₁.equivFun.symm (Matrix.toLinAlgEquiv' M (v₁.repr v)) = _ by
    rw [Matrix.to_lin_alg_equiv'_apply, v₁.equiv_fun_symm_apply]

@[simp]
theorem Matrix.to_lin_alg_equiv_self (M : Matrix n n R) (i : n) :
    Matrix.toLinAlgEquiv v₁ M (v₁ i) = ∑ j, M j i • v₁ j :=
  Matrix.to_lin_self _ _ _ _

theorem LinearMap.to_matrix_alg_equiv_id : LinearMap.toMatrixAlgEquiv v₁ id = 1 := by
  simp_rw [LinearMap.toMatrixAlgEquiv, AlgEquiv.of_linear_equiv_apply, LinearMap.to_matrix_id]

@[simp]
theorem Matrix.to_lin_alg_equiv_one : Matrix.toLinAlgEquiv v₁ 1 = id := by
  rw [← LinearMap.to_matrix_alg_equiv_id v₁, Matrix.to_lin_alg_equiv_to_matrix_alg_equiv]

theorem LinearMap.to_matrix_alg_equiv_reindex_range [DecidableEq M₁] (f : M₁ →ₗ[R] M₁) (k i : n) :
    LinearMap.toMatrixAlgEquiv v₁.reindexRange f ⟨v₁ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
      LinearMap.toMatrixAlgEquiv v₁ f k i :=
  by
  simp_rw [LinearMap.to_matrix_alg_equiv_apply, Basis.reindex_range_self, Basis.reindex_range_repr]

theorem LinearMap.to_matrix_alg_equiv_comp (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f.comp g) = LinearMap.toMatrixAlgEquiv v₁ f ⬝ LinearMap.toMatrixAlgEquiv v₁ g := by
  simp [← LinearMap.toMatrixAlgEquiv, ← LinearMap.to_matrix_comp v₁ v₁ v₁ f g]

theorem LinearMap.to_matrix_alg_equiv_mul (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f * g) = LinearMap.toMatrixAlgEquiv v₁ f ⬝ LinearMap.toMatrixAlgEquiv v₁ g := by
  rw [show @Mul.mul (M₁ →ₗ[R] M₁) _ = LinearMap.comp from rfl, LinearMap.to_matrix_alg_equiv_comp v₁ f g]

theorem Matrix.to_lin_alg_equiv_mul (A B : Matrix n n R) :
    Matrix.toLinAlgEquiv v₁ (A ⬝ B) = (Matrix.toLinAlgEquiv v₁ A).comp (Matrix.toLinAlgEquiv v₁ B) := by
  convert Matrix.to_lin_mul v₁ v₁ v₁ A B

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
@[simp]
theorem Matrix.to_lin_fin_two_prod_apply (a b c d : R) (x : R × R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R)
        («expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation") x =
      (a * x.fst + b * x.snd, c * x.fst + d * x.snd) :=
  by
  simp [← Matrix.to_lin_apply, ← Matrix.mulVecₓ, ← Matrix.dotProduct]

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem Matrix.to_lin_fin_two_prod (a b c d : R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R)
        («expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation") =
      (a • LinearMap.fst R R R + b • LinearMap.snd R R R).Prod (c • LinearMap.fst R R R + d • LinearMap.snd R R R) :=
  LinearMap.ext <| Matrix.to_lin_fin_two_prod_apply _ _ _ _

end ToMatrix

namespace Algebra

section Lmul

variable {R S T : Type _} [CommRingₓ R] [CommRingₓ S] [CommRingₓ T]

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

variable {m n : Type _} [Fintype m] [DecidableEq m] [DecidableEq n]

variable (b : Basis m R S) (c : Basis n S T)

open Algebra

theorem to_matrix_lmul' (x : S) (i j) : LinearMap.toMatrix b b (lmul R S x) i j = b.repr (x * b j) i := by
  rw [LinearMap.to_matrix_apply', lmul_apply]

@[simp]
theorem to_matrix_lsmul (x : R) (i j) : LinearMap.toMatrix b b (Algebra.lsmul R S x) i j = if i = j then x else 0 := by
  rw [LinearMap.to_matrix_apply', Algebra.lsmul_coe, LinearEquiv.map_smul, Finsupp.smul_apply, b.repr_self_apply,
    smul_eq_mul, mul_boole]
  congr 1 <;> simp only [← eq_comm]

/-- `left_mul_matrix b x` is the matrix corresponding to the linear map `λ y, x * y`.

`left_mul_matrix_eq_repr_mul` gives a formula for the entries of `left_mul_matrix`.

This definition is useful for doing (more) explicit computations with `algebra.lmul`,
such as the trace form or norm map for algebras.
-/
noncomputable def leftMulMatrix : S →ₐ[R] Matrix m m R where
  toFun := fun x => LinearMap.toMatrix b b (Algebra.lmul R S x)
  map_zero' := by
    rw [AlgHom.map_zero, LinearEquiv.map_zero]
  map_one' := by
    rw [AlgHom.map_one, LinearMap.to_matrix_one]
  map_add' := fun x y => by
    rw [AlgHom.map_add, LinearEquiv.map_add]
  map_mul' := fun x y => by
    rw [AlgHom.map_mul, LinearMap.to_matrix_mul, Matrix.mul_eq_mul]
  commutes' := fun r => by
    ext
    rw [lmul_algebra_map, to_matrix_lsmul, algebra_map_matrix_apply, id.map_eq_self]

theorem left_mul_matrix_apply (x : S) : leftMulMatrix b x = LinearMap.toMatrix b b (lmul R S x) :=
  rfl

theorem left_mul_matrix_eq_repr_mul (x : S) (i j) : leftMulMatrix b x i j = b.repr (x * b j) i := by
  -- This is defeq to just `to_matrix_lmul' b x i j`,
  -- but the unfolding goes a lot faster with this explicit `rw`.
  rw [left_mul_matrix_apply, to_matrix_lmul' b x i j]

theorem left_mul_matrix_mul_vec_repr (x y : S) : (leftMulMatrix b x).mulVec (b.repr y) = b.repr (x * y) :=
  LinearMap.to_matrix_mul_vec_repr b b (Algebra.lmul R S x) y

@[simp]
theorem to_matrix_lmul_eq (x : S) : LinearMap.toMatrix b b (lmul R S x) = leftMulMatrix b x :=
  rfl

theorem left_mul_matrix_injective : Function.Injective (leftMulMatrix b) := fun x x' h =>
  calc
    x = Algebra.lmul R S x 1 := (mul_oneₓ x).symm
    _ = Algebra.lmul R S x' 1 := by
      rw [(LinearMap.toMatrix b b).Injective h]
    _ = x' := mul_oneₓ x'
    

variable [Fintype n]

theorem smul_left_mul_matrix (x) (ik jk) :
    leftMulMatrix (b.smul c) x ik jk = leftMulMatrix b (leftMulMatrix c x ik.2 jk.2) ik.1 jk.1 := by
  simp only [← left_mul_matrix_apply, ← LinearMap.to_matrix_apply, ← mul_comm, ← Basis.smul_apply, ← Basis.smul_repr, ←
    Finsupp.smul_apply, ← Algebra.lmul_apply, ← id.smul_eq_mul, ← LinearEquiv.map_smul, ← mul_smul_comm]

theorem smul_left_mul_matrix_algebra_map (x : S) :
    leftMulMatrix (b.smul c) (algebraMap _ _ x) = blockDiagonalₓ fun k => leftMulMatrix b x := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  rw [smul_left_mul_matrix, AlgHom.commutes, block_diagonal_apply, algebra_map_matrix_apply]
  split_ifs with h <;> simp [← h]

theorem smul_left_mul_matrix_algebra_map_eq (x : S) (i j k) :
    leftMulMatrix (b.smul c) (algebraMap _ _ x) (i, k) (j, k) = leftMulMatrix b x i j := by
  rw [smul_left_mul_matrix_algebra_map, block_diagonal_apply_eq]

theorem smul_left_mul_matrix_algebra_map_ne (x : S) (i j) {k k'} (h : k ≠ k') :
    leftMulMatrix (b.smul c) (algebraMap _ _ x) (i, k) (j, k') = 0 := by
  rw [smul_left_mul_matrix_algebra_map, block_diagonal_apply_ne _ _ _ h]

end Lmul

end Algebra

namespace LinearMap

section FiniteDimensional

open Classical

variable {K : Type _} [Field K]

variable {V : Type _} [AddCommGroupₓ V] [Module K V] [FiniteDimensional K V]

variable {W : Type _} [AddCommGroupₓ W] [Module K W] [FiniteDimensional K W]

instance finite_dimensional : FiniteDimensional K (V →ₗ[K] W) :=
  LinearEquiv.finite_dimensional (LinearMap.toMatrix (Basis.ofVectorSpace K V) (Basis.ofVectorSpace K W)).symm

section

variable {A : Type _} [Ringₓ A] [Algebra K A] [Module A V] [IsScalarTower K A V] [Module A W] [IsScalarTower K A W]

/-- Linear maps over a `k`-algebra are finite dimensional (over `k`) if both the source and
target are, since they form a subspace of all `k`-linear maps. -/
instance finite_dimensional' : FiniteDimensional K (V →ₗ[A] W) :=
  FiniteDimensional.of_injective (restrictScalarsLinearMap K A V W) (restrict_scalars_injective _)

end

/-- The dimension of the space of linear transformations is the product of the dimensions of the
domain and codomain.
-/
@[simp]
theorem finrank_linear_map :
    FiniteDimensional.finrank K (V →ₗ[K] W) = FiniteDimensional.finrank K V * FiniteDimensional.finrank K W := by
  let hbV := Basis.ofVectorSpace K V
  let hbW := Basis.ofVectorSpace K W
  rw [LinearEquiv.finrank_eq (LinearMap.toMatrix hbV hbW), Matrix.finrank_matrix,
    FiniteDimensional.finrank_eq_card_basis hbV, FiniteDimensional.finrank_eq_card_basis hbW, mul_comm]

end FiniteDimensional

end LinearMap

section

variable {R : Type v} [CommRingₓ R] {n : Type _} [DecidableEq n]

variable {M M₁ M₂ : Type _} [AddCommGroupₓ M] [Module R M]

variable [AddCommGroupₓ M₁] [Module R M₁] [AddCommGroupₓ M₂] [Module R M₂]

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
def algEquivMatrix' [Fintype n] : Module.End R (n → R) ≃ₐ[R] Matrix n n R :=
  { LinearMap.toMatrix' with map_mul' := LinearMap.to_matrix'_comp, map_add' := LinearMap.toMatrix'.map_add,
    commutes' := fun r => by
      change (r • (LinearMap.id : Module.End R _)).toMatrix' = r • 1
      rw [← LinearMap.to_matrix'_id]
      rfl
      infer_instance }

/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
def LinearEquiv.algConj (e : M₁ ≃ₗ[R] M₂) : Module.End R M₁ ≃ₐ[R] Module.End R M₂ :=
  { e.conj with
    map_mul' := fun f g => by
      apply e.arrow_congr_comp,
    map_add' := e.conj.map_add,
    commutes' := fun r => by
      change e.conj (r • LinearMap.id) = r • LinearMap.id
      rw [LinearEquiv.map_smul, LinearEquiv.conj_id] }

/-- A basis of a module induces an equivalence of algebras from the endomorphisms of the module to
square matrices. -/
def algEquivMatrix [Fintype n] (h : Basis n R M) : Module.End R M ≃ₐ[R] Matrix n n R :=
  h.equivFun.algConj.trans algEquivMatrix'

end

