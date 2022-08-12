/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.RingTheory.MatrixAlgebra
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Matrix.Basis
import Mathbin.Data.Matrix.Dmatrix

/-!
# Algebra isomorphism between matrices of polynomials and polynomials of matrices

Given `[comm_ring R] [ring A] [algebra R A]`
we show `polynomial A ≃ₐ[R] (A ⊗[R] R[X])`.
Combining this with the isomorphism `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)` proved earlier
in `ring_theory.matrix_algebra`, we obtain the algebra isomorphism
```
def mat_poly_equiv :
  matrix n n R[X] ≃ₐ[R] polynomial (matrix n n R)
```
which is characterized by
```
coeff (mat_poly_equiv m) k i j = coeff (m i j) k
```

We will use this algebra isomorphism to prove the Cayley-Hamilton theorem.
-/


universe u v w

open Polynomial TensorProduct

open Polynomial

open TensorProduct

open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R A : Type _)

variable [CommSemiringₓ R]

variable [Semiringₓ A] [Algebra R A]

namespace polyEquivTensor

/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] polynomial A`,
as a bilinear function of two arguments.
-/
@[simps apply_apply]
def toFunBilinear : A →ₗ[A] R[X] →ₗ[R] A[X] :=
  LinearMap.toSpanSingleton A _ (aeval (Polynomial.x : Polynomial A)).toLinearMap

theorem to_fun_bilinear_apply_eq_sum (a : A) (p : R[X]) :
    toFunBilinear R A a p = p.Sum fun n r => monomial n (a * algebraMap R A r) := by
  dsimp' [← to_fun_bilinear_apply_apply, ← aeval_def, ← eval₂_eq_sum, ← Polynomial.sum]
  rw [Finset.smul_sum]
  congr with i : 1
  rw [← Algebra.smul_def, ← C_mul', mul_smul_comm, C_mul_X_pow_eq_monomial, ← Algebra.commutes, ← Algebra.smul_def,
    smul_monomial]

/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] polynomial A`,
as a linear map.
-/
def toFunLinear : A ⊗[R] R[X] →ₗ[R] Polynomial A :=
  TensorProduct.lift (toFunBilinear R A)

@[simp]
theorem to_fun_linear_tmul_apply (a : A) (p : R[X]) : toFunLinear R A (a ⊗ₜ[R] p) = toFunBilinear R A a p :=
  lift.tmul _ _

-- We apparently need to provide the decidable instance here
-- in order to successfully rewrite by this lemma.
theorem to_fun_linear_mul_tmul_mul_aux_1 (p : R[X]) (k : ℕ) (h : Decidable ¬p.coeff k = 0) (a : A) :
    ite (¬coeff p k = 0) (a * (algebraMap R A) (coeff p k)) 0 = a * (algebraMap R A) (coeff p k) := by
  classical
  split_ifs <;> simp [*]

theorem to_fun_linear_mul_tmul_mul_aux_2 (k : ℕ) (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    a₁ * a₂ * (algebraMap R A) ((p₁ * p₂).coeff k) =
      (Finset.Nat.antidiagonal k).Sum fun x =>
        a₁ * (algebraMap R A) (coeff p₁ x.1) * (a₂ * (algebraMap R A) (coeff p₂ x.2)) :=
  by
  simp_rw [mul_assoc, Algebra.commutes, ← Finset.mul_sum, mul_assoc, ← Finset.mul_sum]
  congr
  simp_rw [Algebra.commutes (coeff p₂ _), coeff_mul, RingHom.map_sum, RingHom.map_mul]

theorem to_fun_linear_mul_tmul_mul (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    (toFunLinear R A) ((a₁ * a₂) ⊗ₜ[R] (p₁ * p₂)) = (toFunLinear R A) (a₁ ⊗ₜ[R] p₁) * (toFunLinear R A) (a₂ ⊗ₜ[R] p₂) :=
  by
  classical
  simp only [← to_fun_linear_tmul_apply, ← to_fun_bilinear_apply_eq_sum]
  ext k
  simp_rw [coeff_sum, coeff_monomial, sum_def, Finset.sum_ite_eq', mem_support_iff, Ne.def]
  conv_rhs => rw [coeff_mul]
  simp_rw [finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff, Ne.def, mul_ite, mul_zero, ite_mul,
    zero_mul]
  simp_rw [ite_mul_zero_left (¬coeff p₁ _ = 0) (a₁ * (algebraMap R A) (coeff p₁ _))]
  simp_rw [ite_mul_zero_right (¬coeff p₂ _ = 0) _ (_ * _)]
  simp_rw [to_fun_linear_mul_tmul_mul_aux_1, to_fun_linear_mul_tmul_mul_aux_2]

theorem to_fun_linear_algebra_map_tmul_one (r : R) :
    (toFunLinear R A) ((algebraMap R A) r ⊗ₜ[R] 1) = (algebraMap R (Polynomial A)) r := by
  rw [to_fun_linear_tmul_apply, to_fun_bilinear_apply_apply, Polynomial.aeval_one, algebra_map_smul,
    Algebra.algebra_map_eq_smul_one]

/-- (Implementation detail).
The algebra homomorphism `A ⊗[R] R[X] →ₐ[R] polynomial A`.
-/
def toFunAlgHom : A ⊗[R] R[X] →ₐ[R] Polynomial A :=
  algHomOfLinearMapTensorProduct (toFunLinear R A) (to_fun_linear_mul_tmul_mul R A)
    (to_fun_linear_algebra_map_tmul_one R A)

@[simp]
theorem to_fun_alg_hom_apply_tmul (a : A) (p : R[X]) :
    toFunAlgHom R A (a ⊗ₜ[R] p) = p.Sum fun n r => monomial n (a * (algebraMap R A) r) := by
  dsimp' [← to_fun_alg_hom]
  rw [to_fun_linear_tmul_apply, to_fun_bilinear_apply_eq_sum]

/-- (Implementation detail.)

The bare function `polynomial A → A ⊗[R] R[X]`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def invFun (p : A[X]) : A ⊗[R] R[X] :=
  p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (x : R[X]))

@[simp]
theorem inv_fun_add {p q} : invFun R A (p + q) = invFun R A p + invFun R A q := by
  simp only [← inv_fun, ← eval₂_add]

theorem inv_fun_monomial (n : ℕ) (a : A) : invFun R A (monomial n a) = includeLeft a * (1 : A) ⊗ₜ[R] (x : R[X]) ^ n :=
  eval₂_monomial _ _

theorem left_inv (x : A ⊗ R[X]) : invFun R A ((toFunAlgHom R A) x) = x := by
  apply TensorProduct.induction_on x
  · simp [← inv_fun]
    
  · intro a p
    dsimp' only [← inv_fun]
    rw [to_fun_alg_hom_apply_tmul, eval₂_sum]
    simp_rw [eval₂_monomial, AlgHom.coe_to_ring_hom, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.include_left_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_oneₓ, one_mulₓ, ←
      Algebra.commutes, ← Algebra.smul_def, smul_tmul, sum_def, ← tmul_sum]
    conv_rhs => rw [← sum_C_mul_X_eq p]
    simp only [← Algebra.smul_def]
    rfl
    
  · intro p q hp hq
    simp only [← AlgHom.map_add, ← inv_fun_add, ← hp, ← hq]
    

theorem right_inv (x : A[X]) : (toFunAlgHom R A) (invFun R A x) = x := by
  apply Polynomial.induction_on' x
  · intro p q hp hq
    simp only [← inv_fun_add, ← AlgHom.map_add, ← hp, ← hq]
    
  · intro n a
    rw [inv_fun_monomial, Algebra.TensorProduct.include_left_apply, Algebra.TensorProduct.tmul_pow, one_pow,
        Algebra.TensorProduct.tmul_mul_tmul, mul_oneₓ, one_mulₓ, to_fun_alg_hom_apply_tmul, X_pow_eq_monomial,
        sum_monomial_index] <;>
      simp
    

/-- (Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] R[X]) ≃ polynomial A`.
-/
def equiv : A ⊗[R] R[X] ≃ Polynomial A where
  toFun := toFunAlgHom R A
  invFun := invFun R A
  left_inv := left_inv R A
  right_inv := right_inv R A

end polyEquivTensor

open polyEquivTensor

/-- The `R`-algebra isomorphism `polynomial A ≃ₐ[R] (A ⊗[R] R[X])`.
-/
def polyEquivTensor : A[X] ≃ₐ[R] A ⊗[R] R[X] :=
  AlgEquiv.symm { PolyEquivTensor.toFunAlgHom R A, PolyEquivTensor.equiv R A with }

@[simp]
theorem poly_equiv_tensor_apply (p : A[X]) :
    polyEquivTensor R A p = p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (x : R[X])) :=
  rfl

@[simp]
theorem poly_equiv_tensor_symm_apply_tmul (a : A) (p : R[X]) :
    (polyEquivTensor R A).symm (a ⊗ₜ p) = p.Sum fun n r => monomial n (a * algebraMap R A r) :=
  to_fun_alg_hom_apply_tmul _ _ _ _

open Dmatrix Matrix

open BigOperators

variable {R}

variable {n : Type w} [DecidableEq n] [Fintype n]

/-- The algebra isomorphism stating "matrices of polynomials are the same as polynomials of matrices".

(You probably shouldn't attempt to use this underlying definition ---
it's an algebra equivalence, and characterised extensionally by the lemma
`mat_poly_equiv_coeff_apply` below.)
-/
noncomputable def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] Polynomial (Matrix n n R) :=
  ((matrixEquivTensor R R[X] n).trans (Algebra.TensorProduct.comm R _ _)).trans (polyEquivTensor R (Matrix n n R)).symm

open Finset

theorem mat_poly_equiv_coeff_apply_aux_1 (i j : n) (k : ℕ) (x : R) :
    matPolyEquiv (stdBasisMatrix i j <| monomial k x) = monomial k (stdBasisMatrix i j x) := by
  simp only [← matPolyEquiv, ← AlgEquiv.trans_apply, ← matrix_equiv_tensor_apply_std_basis]
  apply (polyEquivTensor R (Matrix n n R)).Injective
  simp only [← AlgEquiv.apply_symm_apply]
  convert Algebra.TensorProduct.comm_tmul _ _ _ _ _
  simp only [← poly_equiv_tensor_apply]
  convert eval₂_monomial _ _
  simp only [← Algebra.TensorProduct.tmul_mul_tmul, ← one_pow, ← one_mulₓ, ← Matrix.mul_one, ←
    Algebra.TensorProduct.tmul_pow, ← Algebra.TensorProduct.include_left_apply, ← mul_eq_mul]
  rw [monomial_eq_smul_X, ← TensorProduct.smul_tmul]
  congr with i' j' <;> simp

theorem mat_poly_equiv_coeff_apply_aux_2 (i j : n) (p : R[X]) (k : ℕ) :
    coeff (matPolyEquiv (stdBasisMatrix i j p)) k = stdBasisMatrix i j (coeff p k) := by
  apply Polynomial.induction_on' p
  · intro p q hp hq
    ext
    simp [← hp, ← hq, ← coeff_add, ← add_apply, ← std_basis_matrix_add]
    
  · intro k x
    simp only [← mat_poly_equiv_coeff_apply_aux_1, ← coeff_monomial]
    split_ifs <;>
      · funext
        simp
        
    

@[simp]
theorem mat_poly_equiv_coeff_apply (m : Matrix n n R[X]) (k : ℕ) (i j : n) :
    coeff (matPolyEquiv m) k i j = coeff (m i j) k := by
  apply Matrix.induction_on' m
  · simp
    
  · intro p q hp hq
    simp [← hp, ← hq]
    
  · intro i' j' x
    erw [mat_poly_equiv_coeff_apply_aux_2]
    dsimp' [← std_basis_matrix]
    split_ifs
    · rcases h with ⟨rfl, rfl⟩
      simp [← std_basis_matrix]
      
    · simp [← std_basis_matrix, ← h]
      
    

@[simp]
theorem mat_poly_equiv_symm_apply_coeff (p : (Matrix n n R)[X]) (i j : n) (k : ℕ) :
    coeff (matPolyEquiv.symm p i j) k = coeff p k i j := by
  have t : p = matPolyEquiv (mat_poly_equiv.symm p) := by
    simp
  conv_rhs => rw [t]
  simp only [← mat_poly_equiv_coeff_apply]

theorem mat_poly_equiv_smul_one (p : R[X]) : matPolyEquiv (p • 1) = p.map (algebraMap R (Matrix n n R)) := by
  ext m i j
  simp only [← coeff_map, ← one_apply, ← algebra_map_matrix_apply, ← mul_boole, ← Pi.smul_apply, ←
    mat_poly_equiv_coeff_apply]
  split_ifs <;> simp

theorem support_subset_support_mat_poly_equiv (m : Matrix n n R[X]) (i j : n) :
    support (m i j) ⊆ support (matPolyEquiv m) := by
  intro k
  contrapose
  simp only [← not_mem_support_iff]
  intro hk
  rw [← mat_poly_equiv_coeff_apply, hk]
  rfl

