/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Data.Matrix.Basis
import Mathbin.Data.Matrix.Dmatrix
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.LinearAlgebra.Matrix.Trace
import Mathbin.LinearAlgebra.Matrix.Reindex
import Mathbin.Tactic.FieldSimp

/-!
# Transvections

Transvections are matrices of the form `1 + std_basis_matrix i j c`, where `std_basis_matrix i j c`
is the basic matrix with a `c` at position `(i, j)`. Multiplying by such a transvection on the left
(resp. on the right) amounts to adding `c` times the `j`-th row to to the `i`-th row
(resp `c` times the `i`-th column to the `j`-th column). Therefore, they are useful to present
algorithms operating on rows and columns.

Transvections are a special case of *elementary matrices* (according to most references, these also
contain the matrices exchanging rows, and the matrices multiplying a row by a constant).

We show that, over a field, any matrix can be written as `L ⬝ D ⬝ L'`, where `L` and `L'` are
products of transvections and `D` is diagonal. In other words, one can reduce a matrix to diagonal
form by operations on its rows and columns, a variant of Gauss' pivot algorithm.

## Main definitions and results

* `transvection i j c` is the matrix equal to `1 + std_basis_matrix i j c`.
* `transvection_struct n R` is a structure containing the data of `i, j, c` and a proof that
  `i ≠ j`. These are often easier to manipulate than straight matrices, especially in inductive
  arguments.

* `exists_list_transvec_mul_diagonal_mul_list_transvec` states that any matrix `M` over a field can
  be written in the form `t_1 ⬝ ... ⬝ t_k ⬝ D ⬝ t'_1 ⬝ ... ⬝ t'_l`, where `D` is diagonal and
  the `t_i`, `t'_j` are transvections.

* `diagonal_transvection_induction` shows that a property which is true for diagonal matrices and
  transvections, and invariant under product, is true for all matrices.
* `diagonal_transvection_induction_of_det_ne_zero` is the same statement over invertible matrices.

## Implementation details

The proof of the reduction results is done inductively on the size of the matrices, reducing an
`(r + 1) × (r + 1)` matrix to a matrix whose last row and column are zeroes, except possibly for
the last diagonal entry. This step is done as follows.

If all the coefficients on the last row and column are zero, there is nothing to do. Otherwise,
one can put a nonzero coefficient in the last diagonal entry by a row or column operation, and then
subtract this last diagonal entry from the other entries in the last row and column to make them
vanish.

This step is done in the type `fin r ⊕ unit`, where `fin r` is useful to choose arbitrarily some
order in which we cancel the coefficients, and the sum structure is useful to use the formalism of
block matrices.

To proceed with the induction, we reindex our matrices to reduce to the above situation.
-/


universe u₁ u₂

namespace Matrix

open Matrix

variable (n p : Type _) (R : Type u₂) {𝕜 : Type _} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRingₓ R]

section Transvection

variable {R n} (i j : n)

/-- The transvection matrix `transvection i j c` is equal to the identity plus `c` at position
`(i, j)`. Multiplying by it on the left (as in `transvection i j c ⬝ M`) corresponds to adding
`c` times the `j`-th line of `M` to its `i`-th line. Multiplying by it on the right corresponds
to adding `c` times the `i`-th column to the `j`-th column. -/
def transvection (c : R) : Matrix n n R :=
  1 + Matrix.stdBasisMatrix i j c

@[simp]
theorem transvection_zero : transvection i j (0 : R) = 1 := by
  simp [← transvection]

section

variable [Fintype n]

/-- A transvection matrix is obtained from the identity by adding `c` times the `j`-th row to
the `i`-th row. -/
theorem update_row_eq_transvection (c : R) :
    updateRow (1 : Matrix n n R) i ((1 : Matrix n n R) i + c • (1 : Matrix n n R) j) = transvection i j c := by
  ext a b
  by_cases' ha : i = a
  by_cases' hb : j = b
  · simp only [← update_row, ← transvection, ← ha, ← hb, ← Function.update_same, ← std_basis_matrix.apply_same, ←
      Pi.add_apply, ← one_apply_eq, ← Pi.smul_apply, ← mul_oneₓ, ← Algebra.id.smul_eq_mul]
    
  · simp only [← update_row, ← transvection, ← ha, ← hb, ← std_basis_matrix.apply_of_ne, ← Function.update_same, ←
      Pi.add_apply, ← Ne.def, ← not_false_iff, ← Pi.smul_apply, ← and_falseₓ, ← one_apply_ne, ← Algebra.id.smul_eq_mul,
      ← mul_zero]
    
  · simp only [← update_row, ← transvection, ← ha, ← Ne.symm ha, ← std_basis_matrix.apply_of_ne, ← add_zeroₓ, ←
      Algebra.id.smul_eq_mul, ← Function.update_noteq, ← Ne.def, ← not_false_iff, ← Dmatrix.add_apply, ← Pi.smul_apply,
      ← mul_zero, ← false_andₓ]
    

theorem transvection_mul_transvection_same (h : i ≠ j) (c d : R) :
    transvection i j c ⬝ transvection i j d = transvection i j (c + d) := by
  simp [← transvection, ← Matrix.add_mul, ← Matrix.mul_add, ← h, ← h.symm, ← add_smul, ← add_assocₓ, ←
    std_basis_matrix_add]

@[simp]
theorem transvection_mul_apply_same (b : n) (c : R) (M : Matrix n n R) :
    (transvection i j c ⬝ M) i b = M i b + c * M j b := by
  simp [← transvection, ← Matrix.add_mul]

@[simp]
theorem mul_transvection_apply_same (a : n) (c : R) (M : Matrix n n R) :
    (M ⬝ transvection i j c) a j = M a j + c * M a i := by
  simp [← transvection, ← Matrix.mul_add, ← mul_comm]

@[simp]
theorem transvection_mul_apply_of_ne (a b : n) (ha : a ≠ i) (c : R) (M : Matrix n n R) :
    (transvection i j c ⬝ M) a b = M a b := by
  simp [← transvection, ← Matrix.add_mul, ← ha]

@[simp]
theorem mul_transvection_apply_of_ne (a b : n) (hb : b ≠ j) (c : R) (M : Matrix n n R) :
    (M ⬝ transvection i j c) a b = M a b := by
  simp [← transvection, ← Matrix.mul_add, ← hb]

@[simp]
theorem det_transvection_of_ne (h : i ≠ j) (c : R) : det (transvection i j c) = 1 := by
  rw [← update_row_eq_transvection i j, det_update_row_add_smul_self _ h, det_one]

end

variable (R n)

/-- A structure containing all the information from which one can build a nontrivial transvection.
This structure is easier to manipulate than transvections as one has a direct access to all the
relevant fields. -/
@[nolint has_inhabited_instance]
structure TransvectionStruct where
  (i j : n)
  hij : i ≠ j
  c : R

instance [Nontrivial n] : Nonempty (TransvectionStruct n R) := by
  choose x y hxy using exists_pair_ne n
  exact ⟨⟨x, y, hxy, 0⟩⟩

namespace TransvectionStruct

variable {R n}

/-- Associating to a `transvection_struct` the corresponding transvection matrix. -/
def toMatrix (t : TransvectionStruct n R) : Matrix n n R :=
  transvection t.i t.j t.c

@[simp]
theorem to_matrix_mk (i j : n) (hij : i ≠ j) (c : R) :
    TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ = transvection i j c :=
  rfl

@[simp]
protected theorem det [Fintype n] (t : TransvectionStruct n R) : det t.toMatrix = 1 :=
  det_transvection_of_ne _ _ t.hij _

@[simp]
theorem det_to_matrix_prod [Fintype n] (L : List (TransvectionStruct n 𝕜)) : det (L.map toMatrix).Prod = 1 := by
  induction' L with t L IH
  · simp
    
  · simp [← IH]
    

/-- The inverse of a `transvection_struct`, designed so that `t.inv.to_matrix` is the inverse of
`t.to_matrix`. -/
@[simps]
protected def inv (t : TransvectionStruct n R) : TransvectionStruct n R where
  i := t.i
  j := t.j
  hij := t.hij
  c := -t.c

section

variable [Fintype n]

theorem inv_mul (t : TransvectionStruct n R) : t.inv.toMatrix ⬝ t.toMatrix = 1 := by
  rcases t with ⟨⟩
  simp [← to_matrix, ← transvection_mul_transvection_same, ← t_hij]

theorem mul_inv (t : TransvectionStruct n R) : t.toMatrix ⬝ t.inv.toMatrix = 1 := by
  rcases t with ⟨⟩
  simp [← to_matrix, ← transvection_mul_transvection_same, ← t_hij]

theorem reverse_inv_prod_mul_prod (L : List (TransvectionStruct n R)) :
    (L.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod ⬝ (L.map toMatrix).Prod = 1 := by
  induction' L with t L IH
  · simp
    
  · suffices
      (L.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod ⬝ (t.inv.to_matrix ⬝ t.to_matrix) ⬝
          (L.map to_matrix).Prod =
        1
      by
      simpa [← Matrix.mul_assoc]
    simpa [← inv_mul] using IH
    

theorem prod_mul_reverse_inv_prod (L : List (TransvectionStruct n R)) :
    (L.map toMatrix).Prod ⬝ (L.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod = 1 := by
  induction' L with t L IH
  · simp
    
  · suffices
      t.to_matrix ⬝ ((L.map to_matrix).Prod ⬝ (L.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod) ⬝
          t.inv.to_matrix =
        1
      by
      simpa [← Matrix.mul_assoc]
    simp_rw [IH, Matrix.mul_one, t.mul_inv]
    

end

variable (p)

open Sum

/-- Given a `transvection_struct` on `n`, define the corresponding `transvection_struct` on `n ⊕ p`
using the identity on `p`. -/
def sumInl (t : TransvectionStruct n R) : TransvectionStruct (Sum n p) R where
  i := inl t.i
  j := inl t.j
  hij := by
    simp [← t.hij]
  c := t.c

theorem to_matrix_sum_inl (t : TransvectionStruct n R) : (t.sumInl p).toMatrix = fromBlocks t.toMatrix 0 0 1 := by
  cases t
  ext a b
  cases a <;> cases b
  · by_cases' h : a = b <;> simp [← transvection_struct.sum_inl, ← transvection, ← h, ← std_basis_matrix]
    
  · simp [← transvection_struct.sum_inl, ← transvection]
    
  · simp [← transvection_struct.sum_inl, ← transvection]
    
  · by_cases' h : a = b <;> simp [← transvection_struct.sum_inl, ← transvection, ← h]
    

@[simp]
theorem sum_inl_to_matrix_prod_mul [Fintype n] [Fintype p] (M : Matrix n n R) (L : List (TransvectionStruct n R))
    (N : Matrix p p R) :
    (L.map (to_matrix ∘ sumInl p)).Prod ⬝ fromBlocks M 0 0 N = fromBlocks ((L.map toMatrix).Prod ⬝ M) 0 0 N := by
  induction' L with t L IH
  · simp
    
  · simp [← Matrix.mul_assoc, ← IH, ← to_matrix_sum_inl, ← from_blocks_multiply]
    

@[simp]
theorem mul_sum_inl_to_matrix_prod [Fintype n] [Fintype p] (M : Matrix n n R) (L : List (TransvectionStruct n R))
    (N : Matrix p p R) :
    fromBlocks M 0 0 N ⬝ (L.map (to_matrix ∘ sumInl p)).Prod = fromBlocks (M ⬝ (L.map toMatrix).Prod) 0 0 N := by
  induction' L with t L IH generalizing M N
  · simp
    
  · simp [← IH, ← to_matrix_sum_inl, ← from_blocks_multiply]
    

variable {p}

/-- Given a `transvection_struct` on `n` and an equivalence between `n` and `p`, define the
corresponding `transvection_struct` on `p`. -/
def reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) : TransvectionStruct p R where
  i := e t.i
  j := e t.j
  hij := by
    simp [← t.hij]
  c := t.c

variable [Fintype n] [Fintype p]

theorem to_matrix_reindex_equiv (e : n ≃ p) (t : TransvectionStruct n R) :
    (t.reindexEquiv e).toMatrix = reindexAlgEquiv R e t.toMatrix := by
  cases t
  ext a b
  simp only [← reindex_equiv, ← transvection, ← mul_boole, ← Algebra.id.smul_eq_mul, ← to_matrix_mk, ← minor_apply, ←
    reindex_apply, ← Dmatrix.add_apply, ← Pi.smul_apply, ← reindex_alg_equiv_apply]
  by_cases' ha : e t_i = a <;>
    by_cases' hb : e t_j = b <;>
      by_cases' hab : a = b <;> simp [← ha, ← hb, ← hab, e.apply_eq_iff_eq_symm_apply, ← std_basis_matrix]

theorem to_matrix_reindex_equiv_prod (e : n ≃ p) (L : List (TransvectionStruct n R)) :
    (L.map (to_matrix ∘ reindexEquiv e)).Prod = reindexAlgEquiv R e (L.map toMatrix).Prod := by
  induction' L with t L IH
  · simp
    
  · simp only [← to_matrix_reindex_equiv, ← IH, ← Function.comp_app, ← List.prod_cons, ← mul_eq_mul, ←
      reindex_alg_equiv_apply, ← List.map]
    exact (reindex_alg_equiv_mul _ _ _ _).symm
    

end TransvectionStruct

end Transvection

/-!
# Reducing matrices by left and right multiplication by transvections

In this section, we show that any matrix can be reduced to diagonal form by left and right
multiplication by transvections (or, equivalently, by elementary operations on lines and columns).
The main step is to kill the last row and column of a matrix in `fin r ⊕ unit` with nonzero last
coefficient, by subtracting this coefficient from the other ones. The list of these operations is
recorded in `list_transvec_col M` and `list_transvec_row M`. We have to analyze inductively how
these operations affect the coefficients in the last row and the last column to conclude that they
have the desired effect.

Once this is done, one concludes the reduction by induction on the size
of the matrices, through a suitable reindexing to identify any fintype with `fin r ⊕ unit`.
-/


namespace Pivot

variable {R} {r : ℕ} (M : Matrix (Sum (Finₓ r) Unit) (Sum (Finₓ r) Unit) 𝕜)

open Sum Unit Finₓ TransvectionStruct

/-- A list of transvections such that multiplying on the left with these transvections will replace
the last column with zeroes. -/
def listTransvecCol : List (Matrix (Sum (Finₓ r) Unit) (Sum (Finₓ r) Unit) 𝕜) :=
  List.ofFnₓ fun i : Finₓ r => transvection (inl i) (inr star) <| -M (inl i) (inr star) / M (inr star) (inr star)

/-- A list of transvections such that multiplying on the right with these transvections will replace
the last row with zeroes. -/
def listTransvecRow : List (Matrix (Sum (Finₓ r) Unit) (Sum (Finₓ r) Unit) 𝕜) :=
  List.ofFnₓ fun i : Finₓ r => transvection (inr star) (inl i) <| -M (inr star) (inl i) / M (inr star) (inr star)

/-- Multiplying by some of the matrices in `list_transvec_col M` does not change the last row. -/
theorem list_transvec_col_mul_last_row_drop (i : Sum (Finₓ r) Unit) {k : ℕ} (hk : k ≤ r) :
    (((listTransvecCol M).drop k).Prod ⬝ M) (inr star) i = M (inr star) i := by
  apply Nat.decreasingInduction' _ hk
  · simp only [← list_transvec_col, ← List.length_of_fn, ← Matrix.one_mul, ← List.drop_eq_nil_of_leₓ, ← List.prod_nil]
    
  · intro n hn hk IH
    have hn' : n < (list_transvec_col M).length := by
      simpa [← list_transvec_col] using hn
    rw [← List.cons_nth_le_drop_succ hn']
    simpa [← list_transvec_col, ← Matrix.mul_assoc]
    

/-- Multiplying by all the matrices in `list_transvec_col M` does not change the last row. -/
theorem list_transvec_col_mul_last_row (i : Sum (Finₓ r) Unit) :
    ((listTransvecCol M).Prod ⬝ M) (inr star) i = M (inr star) i := by
  simpa using list_transvec_col_mul_last_row_drop M i (zero_le _)

/-- Multiplying by all the matrices in `list_transvec_col M` kills all the coefficients in the
last column but the last one. -/
theorem list_transvec_col_mul_last_col (hM : M (inr star) (inr star) ≠ 0) (i : Finₓ r) :
    ((listTransvecCol M).Prod ⬝ M) (inl i) (inr star) = 0 := by
  suffices H :
    ∀ k : ℕ,
      k ≤ r → (((list_transvec_col M).drop k).Prod ⬝ M) (inl i) (inr star) = if k ≤ i then 0 else M (inl i) (inr star)
  · simpa only [← if_true, ← List.dropₓ.equations._eqn_1] using H 0 (zero_le _)
    
  intro k hk
  apply Nat.decreasingInduction' _ hk
  · simp only [← list_transvec_col, ← List.length_of_fn, ← Matrix.one_mul, ← List.drop_eq_nil_of_leₓ, ← List.prod_nil]
    rw [if_neg]
    simpa only [← not_leₓ] using i.2
    
  · intro n hn hk IH
    have hn' : n < (list_transvec_col M).length := by
      simpa [← list_transvec_col] using hn
    let n' : Finₓ r := ⟨n, hn⟩
    rw [← List.cons_nth_le_drop_succ hn']
    have A :
      (list_transvec_col M).nthLe n hn' =
        transvection (inl n') (inr star) (-M (inl n') (inr star) / M (inr star) (inr star)) :=
      by
      simp [← list_transvec_col]
    simp only [← Matrix.mul_assoc, ← A, ← Matrix.mul_eq_mul, ← List.prod_cons]
    by_cases' h : n' = i
    · have hni : n = i := by
        cases i
        simp only [← Subtype.mk_eq_mk] at h
        simp [← h]
      rw [h, transvection_mul_apply_same, IH, list_transvec_col_mul_last_row_drop _ _ hn, ← hni]
      field_simp [← hM]
      
    · have hni : n ≠ i := by
        rintro rfl
        cases i
        simpa using h
      simp only [← transvection_mul_apply_of_ne, ← Ne.def, ← not_false_iff, ← Ne.symm h]
      rw [IH]
      rcases le_or_ltₓ (n + 1) i with (hi | hi)
      · simp only [← hi, ← n.le_succ.trans hi, ← if_true]
        
      · rw [if_neg, if_neg]
        · simpa only [← hni.symm, ← not_leₓ, ← or_falseₓ] using Nat.lt_succ_iff_lt_or_eq.1 hi
          
        · simpa only [← not_leₓ] using hi
          
        
      
    

/-- Multiplying by some of the matrices in `list_transvec_row M` does not change the last column. -/
theorem mul_list_transvec_row_last_col_take (i : Sum (Finₓ r) Unit) {k : ℕ} (hk : k ≤ r) :
    (M ⬝ ((listTransvecRow M).take k).Prod) i (inr star) = M i (inr star) := by
  induction' k with k IH
  · simp only [← Matrix.mul_one, ← List.take_zero, ← List.prod_nil]
    
  · have hkr : k < r := hk
    let k' : Finₓ r := ⟨k, hkr⟩
    have :
      (list_transvec_row M).nth k =
        ↑(transvection (inr Unit.star) (inl k') (-M (inr Unit.star) (inl k') / M (inr Unit.star) (inr Unit.star))) :=
      by
      simp only [← list_transvec_row, ← List.ofFnNthValₓ, ← hkr, ← dif_pos, ← List.nth_of_fn]
      rfl
    simp only [← List.take_succ, Matrix.mul_assoc, ← this, ← List.prod_append, ← Matrix.mul_one, ← Matrix.mul_eq_mul, ←
      List.prod_cons, ← List.prod_nil, ← Option.to_list_some]
    rw [mul_transvection_apply_of_ne, IH hkr.le]
    simp only [← Ne.def, ← not_false_iff]
    

/-- Multiplying by all the matrices in `list_transvec_row M` does not change the last column. -/
theorem mul_list_transvec_row_last_col (i : Sum (Finₓ r) Unit) :
    (M ⬝ (listTransvecRow M).Prod) i (inr star) = M i (inr star) := by
  have A : (list_transvec_row M).length = r := by
    simp [← list_transvec_row]
  rw [← List.take_length (list_transvec_row M), A]
  simpa using mul_list_transvec_row_last_col_take M i le_rfl

/-- Multiplying by all the matrices in `list_transvec_row M` kills all the coefficients in the
last row but the last one. -/
theorem mul_list_transvec_row_last_row (hM : M (inr star) (inr star) ≠ 0) (i : Finₓ r) :
    (M ⬝ (listTransvecRow M).Prod) (inr star) (inl i) = 0 := by
  suffices H :
    ∀ k : ℕ,
      k ≤ r → (M ⬝ ((list_transvec_row M).take k).Prod) (inr star) (inl i) = if k ≤ i then M (inr star) (inl i) else 0
  · have A : (list_transvec_row M).length = r := by
      simp [← list_transvec_row]
    rw [← List.take_length (list_transvec_row M), A]
    have : ¬r ≤ i := by
      simpa using i.2
    simpa only [← this, ← ite_eq_right_iff] using H r le_rfl
    
  intro k hk
  induction' k with n IH
  · simp only [← if_true, ← Matrix.mul_one, ← List.take_zero, ← zero_le', ← List.prod_nil]
    
  · have hnr : n < r := hk
    let n' : Finₓ r := ⟨n, hnr⟩
    have A :
      (list_transvec_row M).nth n =
        ↑(transvection (inr Unit.star) (inl n') (-M (inr Unit.star) (inl n') / M (inr Unit.star) (inr Unit.star))) :=
      by
      simp only [← list_transvec_row, ← List.ofFnNthValₓ, ← hnr, ← dif_pos, ← List.nth_of_fn]
      rfl
    simp only [← List.take_succ, ← A, Matrix.mul_assoc, ← List.prod_append, ← Matrix.mul_one, ← Matrix.mul_eq_mul, ←
      List.prod_cons, ← List.prod_nil, ← Option.to_list_some]
    by_cases' h : n' = i
    · have hni : n = i := by
        cases i
        simp only [← Subtype.mk_eq_mk] at h
        simp only [← h, ← coe_mk]
      have : ¬n.succ ≤ i := by
        simp only [hni, ← n.lt_succ_self, ← not_leₓ]
      simp only [← h, ← mul_transvection_apply_same, ← List.takeₓ, ← if_false, ←
        mul_list_transvec_row_last_col_take _ _ hnr.le, ← hni.le, ← this, ← if_true, ← IH hnr.le]
      field_simp [← hM]
      
    · have hni : n ≠ i := by
        rintro rfl
        cases i
        simpa using h
      simp only [← IH hnr.le, ← Ne.def, ← mul_transvection_apply_of_ne, ← not_false_iff, ← Ne.symm h]
      rcases le_or_ltₓ (n + 1) i with (hi | hi)
      · simp [← hi, ← n.le_succ.trans hi, ← if_true]
        
      · rw [if_neg, if_neg]
        · simpa only [← not_leₓ] using hi
          
        · simpa only [← hni.symm, ← not_leₓ, ← or_falseₓ] using Nat.lt_succ_iff_lt_or_eq.1 hi
          
        
      
    

/-- Multiplying by all the matrices either in `list_transvec_col M` and `list_transvec_row M` kills
all the coefficients in the last row but the last one. -/
theorem list_transvec_col_mul_mul_list_transvec_row_last_col (hM : M (inr star) (inr star) ≠ 0) (i : Finₓ r) :
    ((listTransvecCol M).Prod ⬝ M ⬝ (listTransvecRow M).Prod) (inr star) (inl i) = 0 := by
  have : list_transvec_row M = list_transvec_row ((list_transvec_col M).Prod ⬝ M) := by
    simp [← list_transvec_row, ← list_transvec_col_mul_last_row]
  rw [this]
  apply mul_list_transvec_row_last_row
  simpa [← list_transvec_col_mul_last_row] using hM

/-- Multiplying by all the matrices either in `list_transvec_col M` and `list_transvec_row M` kills
all the coefficients in the last column but the last one. -/
theorem list_transvec_col_mul_mul_list_transvec_row_last_row (hM : M (inr star) (inr star) ≠ 0) (i : Finₓ r) :
    ((listTransvecCol M).Prod ⬝ M ⬝ (listTransvecRow M).Prod) (inl i) (inr star) = 0 := by
  have : list_transvec_col M = list_transvec_col (M ⬝ (list_transvec_row M).Prod) := by
    simp [← list_transvec_col, ← mul_list_transvec_row_last_col]
  rw [this, Matrix.mul_assoc]
  apply list_transvec_col_mul_last_col
  simpa [← mul_list_transvec_row_last_col] using hM

/-- Multiplying by all the matrices either in `list_transvec_col M` and `list_transvec_row M` turns
the matrix in block-diagonal form. -/
theorem is_two_block_diagonal_list_transvec_col_mul_mul_list_transvec_row (hM : M (inr star) (inr star) ≠ 0) :
    IsTwoBlockDiagonal ((listTransvecCol M).Prod ⬝ M ⬝ (listTransvecRow M).Prod) := by
  constructor
  · ext i j
    have : j = star := by
      simp only [← eq_iff_true_of_subsingleton]
    simp [← to_blocks₁₂, ← this, ← list_transvec_col_mul_mul_list_transvec_row_last_row M hM]
    
  · ext i j
    have : i = star := by
      simp only [← eq_iff_true_of_subsingleton]
    simp [← to_blocks₂₁, ← this, ← list_transvec_col_mul_mul_list_transvec_row_last_col M hM]
    

/-- There exist two lists of `transvection_struct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal, when the last coefficient is nonzero. -/
theorem exists_is_two_block_diagonal_of_ne_zero (hM : M (inr star) (inr star) ≠ 0) :
    ∃ L L' : List (TransvectionStruct (Sum (Finₓ r) Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).Prod ⬝ M ⬝ (L'.map toMatrix).Prod) :=
  by
  let L : List (transvection_struct (Sum (Finₓ r) Unit) 𝕜) :=
    List.ofFnₓ fun i : Finₓ r =>
      ⟨inl i, inr star, by
        simp , -M (inl i) (inr star) / M (inr star) (inr star)⟩
  let L' : List (transvection_struct (Sum (Finₓ r) Unit) 𝕜) :=
    List.ofFnₓ fun i : Finₓ r =>
      ⟨inr star, inl i, by
        simp , -M (inr star) (inl i) / M (inr star) (inr star)⟩
  refine' ⟨L, L', _⟩
  have A : L.map to_matrix = list_transvec_col M := by
    simp [← L, ← list_transvec_col, ← (· ∘ ·)]
  have B : L'.map to_matrix = list_transvec_row M := by
    simp [← L, ← list_transvec_row, ← (· ∘ ·)]
  rw [A, B]
  exact is_two_block_diagonal_list_transvec_col_mul_mul_list_transvec_row M hM

/-- There exist two lists of `transvection_struct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal. -/
theorem exists_is_two_block_diagonal_list_transvec_mul_mul_list_transvec
    (M : Matrix (Sum (Finₓ r) Unit) (Sum (Finₓ r) Unit) 𝕜) :
    ∃ L L' : List (TransvectionStruct (Sum (Finₓ r) Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).Prod ⬝ M ⬝ (L'.map toMatrix).Prod) :=
  by
  by_cases' H : is_two_block_diagonal M
  · refine'
      ⟨List.nil, List.nil, by
        simpa using H⟩
    
  -- we have already proved this when the last coefficient is nonzero
  by_cases' hM : M (inr star) (inr star) ≠ 0
  · exact exists_is_two_block_diagonal_of_ne_zero M hM
    
  -- when the last coefficient is zero but there is a nonzero coefficient on the last row or the
  -- last column, we will first put this nonzero coefficient in last position, and then argue as
  -- above.
  push_neg  at hM
  simp [← not_and_distrib, ← is_two_block_diagonal, ← to_blocks₁₂, ← to_blocks₂₁, Matrix.ext_iff] at H
  have : ∃ i : Finₓ r, M (inl i) (inr star) ≠ 0 ∨ M (inr star) (inl i) ≠ 0 := by
    cases H
    · contrapose! H
      rintro i ⟨⟩
      exact (H i).1
      
    · contrapose! H
      rintro ⟨⟩ j
      exact (H j).2
      
  rcases this with ⟨i, h | h⟩
  · let M' := transvection (inr Unit.star) (inl i) 1 ⬝ M
    have hM' : M' (inr star) (inr star) ≠ 0 := by
      simpa [← M', ← hM]
    rcases exists_is_two_block_diagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩
    rw [Matrix.mul_assoc] at hLL'
    refine'
      ⟨L ++
          [⟨inr star, inl i, by
              simp , 1⟩],
        L', _⟩
    simp only [← List.map_append, ← List.prod_append, ← Matrix.mul_one, ← to_matrix_mk, ← List.prod_cons, ←
      List.prod_nil, ← mul_eq_mul, ← List.map, ← Matrix.mul_assoc (L.map to_matrix).Prod]
    exact hLL'
    
  · let M' := M ⬝ transvection (inl i) (inr star) 1
    have hM' : M' (inr star) (inr star) ≠ 0 := by
      simpa [← M', ← hM]
    rcases exists_is_two_block_diagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩
    refine'
      ⟨L,
        ⟨inl i, inr star, by
            simp , 1⟩ ::
          L',
        _⟩
    simp only [Matrix.mul_assoc, ← to_matrix_mk, ← List.prod_cons, ← mul_eq_mul, ← List.map]
    rw [Matrix.mul_assoc (L.map to_matrix).Prod]
    exact hLL'
    

/-- Inductive step for the reduction: if one knows that any size `r` matrix can be reduced to
diagonal form by elementary operations, then one deduces it for matrices over `fin r ⊕ unit`. -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
    (IH :
      ∀ M : Matrix (Finₓ r) (Finₓ r) 𝕜,
        ∃ (L₀ L₀' : List (TransvectionStruct (Finₓ r) 𝕜))(D₀ : Finₓ r → 𝕜),
          (L₀.map toMatrix).Prod ⬝ M ⬝ (L₀'.map toMatrix).Prod = diagonalₓ D₀)
    (M : Matrix (Sum (Finₓ r) Unit) (Sum (Finₓ r) Unit) 𝕜) :
    ∃ (L L' : List (TransvectionStruct (Sum (Finₓ r) Unit) 𝕜))(D : Sum (Finₓ r) Unit → 𝕜),
      (L.map toMatrix).Prod ⬝ M ⬝ (L'.map toMatrix).Prod = diagonalₓ D :=
  by
  rcases exists_is_two_block_diagonal_list_transvec_mul_mul_list_transvec M with ⟨L₁, L₁', hM⟩
  let M' := (L₁.map to_matrix).Prod ⬝ M ⬝ (L₁'.map to_matrix).Prod
  let M'' := to_blocks₁₁ M'
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩
  set c := M' (inr star) (inr star) with hc
  refine' ⟨L₀.map (sum_inl Unit) ++ L₁, L₁' ++ L₀'.map (sum_inl Unit), Sum.elim D₀ fun _ => M' (inr star) (inr star), _⟩
  suffices
    (L₀.map (to_matrix ∘ sum_inl Unit)).Prod ⬝ M' ⬝ (L₀'.map (to_matrix ∘ sum_inl Unit)).Prod =
      diagonal (Sum.elim D₀ fun _ => c)
    by
    simpa [← M', ← Matrix.mul_assoc, ← c]
  have : M' = from_blocks M'' 0 0 (diagonal fun _ => c) := by
    rw [← from_blocks_to_blocks M']
    congr
    · exact hM.1
      
    · exact hM.2
      
    · ext ⟨⟩ ⟨⟩
      rw [hc, to_blocks₂₂, of_apply]
      rfl
      
  rw [this]
  simp [← h₀]

variable {n p} [Fintype n] [Fintype p]

/-- Reduction to diagonal form by elementary operations is invariant under reindexing. -/
theorem reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix p p 𝕜) (e : p ≃ n)
    (H :
      ∃ (L L' : List (TransvectionStruct n 𝕜))(D : n → 𝕜),
        (L.map toMatrix).Prod ⬝ Matrix.reindexAlgEquiv 𝕜 e M ⬝ (L'.map toMatrix).Prod = diagonalₓ D) :
    ∃ (L L' : List (TransvectionStruct p 𝕜))(D : p → 𝕜),
      (L.map toMatrix).Prod ⬝ M ⬝ (L'.map toMatrix).Prod = diagonalₓ D :=
  by
  rcases H with ⟨L₀, L₀', D₀, h₀⟩
  refine' ⟨L₀.map (reindex_equiv e.symm), L₀'.map (reindex_equiv e.symm), D₀ ∘ e, _⟩
  have : M = reindex_alg_equiv 𝕜 e.symm (reindex_alg_equiv 𝕜 e M) := by
    simp only [← Equivₓ.symm_symm, ← minor_minor, ← reindex_apply, ← minor_id_id, ← Equivₓ.symm_comp_self, ←
      reindex_alg_equiv_apply]
  rw [this]
  simp only [← to_matrix_reindex_equiv_prod, ← List.map_mapₓ, ← reindex_alg_equiv_apply]
  simp only [reindex_alg_equiv_apply, reindex_alg_equiv_mul, ← h₀]
  simp only [← Equivₓ.symm_symm, ← reindex_apply, ← minor_diagonal_equiv, ← reindex_alg_equiv_apply]

/-- Any matrix can be reduced to diagonal form by elementary operations. Formulated here on `Type 0`
because we will make an induction using `fin r`.
See `exists_list_transvec_mul_mul_list_transvec_eq_diagonal` for the general version (which follows
from this one and reindexing). -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux (n : Type) [Fintype n] [DecidableEq n]
    (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜))(D : n → 𝕜),
      (L.map toMatrix).Prod ⬝ M ⬝ (L'.map toMatrix).Prod = diagonalₓ D :=
  by
  induction' hn : Fintype.card n with r IH generalizing n M
  · refine' ⟨List.nil, List.nil, fun _ => 1, _⟩
    ext i j
    rw [Fintype.card_eq_zero_iff] at hn
    exact hn.elim' i
    
  · have e : n ≃ Sum (Finₓ r) Unit := by
      refine' Fintype.equivOfCardEq _
      rw [hn]
      convert (@Fintype.card_sum (Finₓ r) Unit _ _).symm
      simp
    apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
    apply
      exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction fun N =>
        IH (Finₓ r) N
          (by
            simp )
    

/-- Any matrix can be reduced to diagonal form by elementary operations. -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜))(D : n → 𝕜),
      (L.map toMatrix).Prod ⬝ M ⬝ (L'.map toMatrix).Prod = diagonalₓ D :=
  by
  have e : n ≃ Finₓ (Fintype.card n) :=
    Fintype.equivOfCardEq
      (by
        simp )
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux

/-- Any matrix can be written as the product of transvections, a diagonal matrix, and
transvections.-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜))(D : n → 𝕜),
      M = (L.map toMatrix).Prod ⬝ diagonalₓ D ⬝ (L'.map toMatrix).Prod :=
  by
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine' ⟨L.reverse.map transvection_struct.inv, L'.reverse.map transvection_struct.inv, D, _⟩
  suffices
    M =
      (L.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod ⬝ (L.map to_matrix).Prod ⬝ M ⬝
        ((L'.map to_matrix).Prod ⬝ (L'.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod)
    by
    simpa [h, ← Matrix.mul_assoc]
  rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]

end Pivot

open Pivot TransvectionStruct

variable {n} [Fintype n]

/-- Induction principle for matrices based on transvections: if a property is true for all diagonal
matrices, all transvections, and is stable under product, then it is true for all matrices. This is
the useful way to say that matrices are generated by diagonal matrices and transvections.

We state a slightly more general version: to prove a property for a matrix `M`, it suffices to
assume that the diagonal matrices we consider have the same determinant as `M`. This is useful to
obtain similar principles for `SLₙ` or `GLₙ`. -/
theorem diagonal_transvection_induction (P : Matrix n n 𝕜 → Prop) (M : Matrix n n 𝕜)
    (hdiag : ∀ D : n → 𝕜, det (diagonalₓ D) = det M → P (diagonalₓ D))
    (htransvec : ∀ t : TransvectionStruct n 𝕜, P t.toMatrix) (hmul : ∀ A B, P A → P B → P (A ⬝ B)) : P M := by
  rcases exists_list_transvec_mul_diagonal_mul_list_transvec M with ⟨L, L', D, h⟩
  have PD : P (diagonal D) :=
    hdiag D
      (by
        simp [← h])
  suffices H :
    ∀ (L₁ L₂ : List (transvection_struct n 𝕜)) (E : Matrix n n 𝕜),
      P E → P ((L₁.map to_matrix).Prod ⬝ E ⬝ (L₂.map to_matrix).Prod)
  · rw [h]
    apply H L L'
    exact PD
    
  intro L₁ L₂ E PE
  induction' L₁ with t L₁ IH
  · simp only [← Matrix.one_mul, ← List.prod_nil, ← List.map]
    induction' L₂ with t L₂ IH generalizing E
    · simpa
      
    · simp only [Matrix.mul_assoc, ← List.prod_cons, ← mul_eq_mul, ← List.map]
      apply IH
      exact hmul _ _ PE (htransvec _)
      
    
  · simp only [← Matrix.mul_assoc, ← List.prod_cons, ← mul_eq_mul, ← List.map] at IH⊢
    exact hmul _ _ (htransvec _) IH
    

/-- Induction principle for invertible matrices based on transvections: if a property is true for
all invertible diagonal matrices, all transvections, and is stable under product of invertible
matrices, then it is true for all invertible matrices. This is the useful way to say that
invertible matrices are generated by invertible diagonal matrices and transvections. -/
theorem diagonal_transvection_induction_of_det_ne_zero (P : Matrix n n 𝕜 → Prop) (M : Matrix n n 𝕜) (hMdet : det M ≠ 0)
    (hdiag : ∀ D : n → 𝕜, det (diagonalₓ D) ≠ 0 → P (diagonalₓ D))
    (htransvec : ∀ t : TransvectionStruct n 𝕜, P t.toMatrix)
    (hmul : ∀ A B, det A ≠ 0 → det B ≠ 0 → P A → P B → P (A ⬝ B)) : P M := by
  let Q : Matrix n n 𝕜 → Prop := fun N => det N ≠ 0 ∧ P N
  have : Q M := by
    apply diagonal_transvection_induction Q M
    · intro D hD
      have detD : det (diagonal D) ≠ 0 := by
        rw [hD]
        exact hMdet
      exact ⟨detD, hdiag _ detD⟩
      
    · intro t
      exact
        ⟨by
          simp , htransvec t⟩
      
    · intro A B QA QB
      exact
        ⟨by
          simp [← QA.1, ← QB.1], hmul A B QA.1 QB.1 QA.2 QB.2⟩
      
  exact this.2

end Matrix

