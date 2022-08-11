/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Eric Wieser
-/
import Mathbin.LinearAlgebra.Determinant
import Mathbin.Topology.Algebra.InfiniteSum
import Mathbin.Topology.Algebra.Ring
import Mathbin.Topology.Algebra.Star

/-!
# Topological properties of matrices

This file is a place to collect topological results about matrices.

## Main definitions:

* `matrix.topological_ring`: square matrices form a topological ring

## Main results

* Continuity:
  * `continuous.matrix_det`: the determinant is continuous over a topological ring.
  * `continuous.matrix_adjugate`: the adjugate is continuous over a topological ring.
* Infinite sums
  * `matrix.transpose_tsum`: transpose commutes with infinite sums
  * `matrix.diagonal_tsum`: diagonal commutes with infinite sums
  * `matrix.block_diagonal_tsum`: block diagonal commutes with infinite sums
  * `matrix.block_diagonal'_tsum`: non-uniform block diagonal commutes with infinite sums
-/


open Matrix

open Matrix

variable {X α l m n p S R : Type _} {m' n' : l → Type _}

instance [TopologicalSpace R] : TopologicalSpace (Matrix m n R) :=
  Pi.topologicalSpace

instance [TopologicalSpace R] [T2Space R] : T2Space (Matrix m n R) :=
  Pi.t2_space

/-! ### Lemmas about continuity of operations -/


section Continuity

variable [TopologicalSpace X] [TopologicalSpace R]

instance [HasSmul α R] [HasContinuousConstSmul α R] : HasContinuousConstSmul α (Matrix m n R) :=
  Pi.has_continuous_const_smul

instance [TopologicalSpace α] [HasSmul α R] [HasContinuousSmul α R] : HasContinuousSmul α (Matrix m n R) :=
  Pi.has_continuous_smul

instance [Add R] [HasContinuousAdd R] : HasContinuousAdd (Matrix m n R) :=
  Pi.has_continuous_add

instance [Neg R] [HasContinuousNeg R] : HasContinuousNeg (Matrix m n R) :=
  Pi.has_continuous_neg

instance [AddGroupₓ R] [TopologicalAddGroup R] : TopologicalAddGroup (Matrix m n R) :=
  Pi.topological_add_group

/-- To show a function into matrices is continuous it suffices to show the coefficients of the
resulting matrix are continuous -/
@[continuity]
theorem continuous_matrix [TopologicalSpace α] {f : α → Matrix m n R} (h : ∀ i j, Continuous fun a => f a i j) :
    Continuous f :=
  continuous_pi fun _ => continuous_pi fun j => h _ _

theorem Continuous.matrix_elem {A : X → Matrix m n R} (hA : Continuous A) (i : m) (j : n) :
    Continuous fun x => A x i j :=
  (continuous_apply_apply i j).comp hA

@[continuity]
theorem Continuous.matrix_map [TopologicalSpace S] {A : X → Matrix m n S} {f : S → R} (hA : Continuous A)
    (hf : Continuous f) : Continuous fun x => (A x).map f :=
  continuous_matrix fun i j => hf.comp <| hA.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_transpose {A : X → Matrix m n R} (hA : Continuous A) : Continuous fun x => (A x)ᵀ :=
  continuous_matrix fun i j => hA.matrix_elem j i

theorem Continuous.matrix_conj_transpose [HasStar R] [HasContinuousStar R] {A : X → Matrix m n R} (hA : Continuous A) :
    Continuous fun x => (A x)ᴴ :=
  hA.matrix_transpose.matrix_map continuous_star

instance [HasStar R] [HasContinuousStar R] : HasContinuousStar (Matrix m m R) :=
  ⟨continuous_id.matrix_conj_transpose⟩

@[continuity]
theorem Continuous.matrix_col {A : X → n → R} (hA : Continuous A) : Continuous fun x => colₓ (A x) :=
  continuous_matrix fun i j => (continuous_apply _).comp hA

@[continuity]
theorem Continuous.matrix_row {A : X → n → R} (hA : Continuous A) : Continuous fun x => rowₓ (A x) :=
  continuous_matrix fun i j => (continuous_apply _).comp hA

@[continuity]
theorem Continuous.matrix_diagonal [Zero R] [DecidableEq n] {A : X → n → R} (hA : Continuous A) :
    Continuous fun x => diagonalₓ (A x) :=
  continuous_matrix fun i j => ((continuous_apply i).comp hA).if_const _ continuous_zero

@[continuity]
theorem Continuous.matrix_dot_product [Fintype n] [Mul R] [AddCommMonoidₓ R] [HasContinuousAdd R] [HasContinuousMul R]
    {A : X → n → R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => dotProduct (A x) (B x) :=
  (continuous_finset_sum _) fun i _ => ((continuous_apply i).comp hA).mul ((continuous_apply i).comp hB)

/-- For square matrices the usual `continuous_mul` can be used. -/
@[continuity]
theorem Continuous.matrix_mul [Fintype n] [Mul R] [AddCommMonoidₓ R] [HasContinuousAdd R] [HasContinuousMul R]
    {A : X → Matrix m n R} {B : X → Matrix n p R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).mul (B x) :=
  continuous_matrix fun i j => (continuous_finset_sum _) fun k _ => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

instance [Fintype n] [Mul R] [AddCommMonoidₓ R] [HasContinuousAdd R] [HasContinuousMul R] :
    HasContinuousMul (Matrix n n R) :=
  ⟨continuous_fst.matrix_mul continuous_snd⟩

instance [Fintype n] [NonUnitalNonAssocSemiringₓ R] [TopologicalSemiring R] : TopologicalSemiring (Matrix n n R) where

instance [Fintype n] [NonUnitalNonAssocRing R] [TopologicalRing R] : TopologicalRing (Matrix n n R) where

@[continuity]
theorem Continuous.matrix_vec_mul_vec [Mul R] [HasContinuousMul R] {A : X → m → R} {B : X → n → R} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => vecMulVecₓ (A x) (B x) :=
  continuous_matrix fun i j => ((continuous_apply _).comp hA).mul ((continuous_apply _).comp hB)

@[continuity]
theorem Continuous.matrix_mul_vec [NonUnitalNonAssocSemiringₓ R] [HasContinuousAdd R] [HasContinuousMul R] [Fintype n]
    {A : X → Matrix m n R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).mulVec (B x) :=
  continuous_pi fun i => ((continuous_apply i).comp hA).matrix_dot_product hB

@[continuity]
theorem Continuous.matrix_vec_mul [NonUnitalNonAssocSemiringₓ R] [HasContinuousAdd R] [HasContinuousMul R] [Fintype m]
    {A : X → m → R} {B : X → Matrix m n R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => vecMulₓ (A x) (B x) :=
  continuous_pi fun i => hA.matrix_dot_product <| continuous_pi fun j => hB.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_minor {A : X → Matrix l n R} (hA : Continuous A) (e₁ : m → l) (e₂ : p → n) :
    Continuous fun x => (A x).minor e₁ e₂ :=
  continuous_matrix fun i j => hA.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_reindex {A : X → Matrix l n R} (hA : Continuous A) (e₁ : l ≃ m) (e₂ : n ≃ p) :
    Continuous fun x => reindex e₁ e₂ (A x) :=
  hA.matrix_minor _ _

@[continuity]
theorem Continuous.matrix_diag {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => Matrix.diag (A x) :=
  continuous_pi fun _ => hA.matrix_elem _ _

-- note this doesn't elaborate well from the above
theorem continuous_matrix_diag : Continuous (Matrix.diag : Matrix n n R → n → R) :=
  show Continuous fun x : Matrix n n R => Matrix.diag x from continuous_id.matrix_diag

@[continuity]
theorem Continuous.matrix_trace [Fintype n] [AddCommMonoidₓ R] [HasContinuousAdd R] {A : X → Matrix n n R}
    (hA : Continuous A) : Continuous fun x => trace (A x) :=
  (continuous_finset_sum _) fun i hi => hA.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_det [Fintype n] [DecidableEq n] [CommRingₓ R] [TopologicalRing R] {A : X → Matrix n n R}
    (hA : Continuous A) : Continuous fun x => (A x).det := by
  simp_rw [Matrix.det_apply]
  refine' continuous_finset_sum _ fun l _ => Continuous.const_smul _ _
  refine' continuous_finset_prod _ fun l _ => hA.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_update_column [DecidableEq n] (i : n) {A : X → Matrix m n R} {B : X → m → R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => (A x).updateColumn i (B x) :=
  continuous_matrix fun j k =>
    (continuous_apply k).comp <| ((continuous_apply _).comp hA).update i ((continuous_apply _).comp hB)

@[continuity]
theorem Continuous.matrix_update_row [DecidableEq m] (i : m) {A : X → Matrix m n R} {B : X → n → R} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => (A x).updateRow i (B x) :=
  hA.update i hB

@[continuity]
theorem Continuous.matrix_cramer [Fintype n] [DecidableEq n] [CommRingₓ R] [TopologicalRing R] {A : X → Matrix n n R}
    {B : X → n → R} (hA : Continuous A) (hB : Continuous B) : Continuous fun x => (A x).cramer (B x) :=
  continuous_pi fun i => (hA.matrix_update_column _ hB).matrix_det

@[continuity]
theorem Continuous.matrix_adjugate [Fintype n] [DecidableEq n] [CommRingₓ R] [TopologicalRing R] {A : X → Matrix n n R}
    (hA : Continuous A) : Continuous fun x => (A x).adjugate :=
  continuous_matrix fun j k => (hA.matrix_transpose.matrix_update_column k continuous_const).matrix_det

/-- When `ring.inverse` is continuous at the determinant (such as in a `normed_ring`, or a
`topological_field`), so is `matrix.has_inv`. -/
theorem continuous_at_matrix_inv [Fintype n] [DecidableEq n] [CommRingₓ R] [TopologicalRing R] (A : Matrix n n R)
    (h : ContinuousAt Ring.inverse A.det) : ContinuousAt Inv.inv A :=
  (h.comp continuous_id.matrix_det.ContinuousAt).smul continuous_id.matrix_adjugate.ContinuousAt

-- lemmas about functions in `data/matrix/block.lean`
section BlockMatrices

@[continuity]
theorem Continuous.matrix_from_blocks {A : X → Matrix n l R} {B : X → Matrix n m R} {C : X → Matrix p l R}
    {D : X → Matrix p m R} (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x) :=
  continuous_matrix fun i j => by
    cases i <;> cases j <;> refine' Continuous.matrix_elem _ i j <;> assumption

@[continuity]
theorem Continuous.matrix_block_diagonal [Zero R] [DecidableEq p] {A : X → p → Matrix m n R} (hA : Continuous A) :
    Continuous fun x => blockDiagonalₓ (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ =>
    (((continuous_apply i₂).comp hA).matrix_elem i₁ j₁).if_const _ continuous_zero

@[continuity]
theorem Continuous.matrix_block_diag {A : X → Matrix (m × p) (n × p) R} (hA : Continuous A) :
    Continuous fun x => blockDiagₓ (A x) :=
  continuous_pi fun i => continuous_matrix fun j k => hA.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_block_diagonal' [Zero R] [DecidableEq l] {A : X → ∀ i, Matrix (m' i) (n' i) R}
    (hA : Continuous A) : Continuous fun x => blockDiagonal'ₓ (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    dsimp' only [← block_diagonal']
    split_ifs
    · subst h
      exact ((continuous_apply i₁).comp hA).matrix_elem i₂ j₂
      
    · exact continuous_const
      

@[continuity]
theorem Continuous.matrix_block_diag' {A : X → Matrix (Σi, m' i) (Σi, n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiag'ₓ (A x) :=
  continuous_pi fun i => continuous_matrix fun j k => hA.matrix_elem _ _

end BlockMatrices

end Continuity

/-! ### Lemmas about infinite sums -/


section tsum

variable [Semiringₓ α] [AddCommMonoidₓ R] [TopologicalSpace R] [Module α R]

theorem HasSum.matrix_transpose {f : X → Matrix m n R} {a : Matrix m n R} (hf : HasSum f a) :
    HasSum (fun x => (f x)ᵀ) aᵀ :=
  (hf.map (@Matrix.transposeAddEquiv m n R _) continuous_id.matrix_transpose : _)

theorem Summable.matrix_transpose {f : X → Matrix m n R} (hf : Summable f) : Summable fun x => (f x)ᵀ :=
  hf.HasSum.matrix_transpose.Summable

@[simp]
theorem summable_matrix_transpose {f : X → Matrix m n R} : (Summable fun x => (f x)ᵀ) ↔ Summable f :=
  (Summable.map_iff_of_equiv (@Matrix.transposeAddEquiv m n R _) (@continuous_id (Matrix m n R) _).matrix_transpose
    continuous_id.matrix_transpose :
    _)

theorem Matrix.transpose_tsum [T2Space R] {f : X → Matrix m n R} : (∑' x, f x)ᵀ = ∑' x, (f x)ᵀ := by
  by_cases' hf : Summable f
  · exact hf.has_sum.matrix_transpose.tsum_eq.symm
    
  · have hft := summable_matrix_transpose.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft, transpose_zero]
    

theorem HasSum.matrix_conj_transpose [StarAddMonoid R] [HasContinuousStar R] {f : X → Matrix m n R} {a : Matrix m n R}
    (hf : HasSum f a) : HasSum (fun x => (f x)ᴴ) aᴴ :=
  (hf.map (@Matrix.conjTransposeAddEquiv m n R _ _) continuous_id.matrix_conj_transpose : _)

theorem Summable.matrix_conj_transpose [StarAddMonoid R] [HasContinuousStar R] {f : X → Matrix m n R}
    (hf : Summable f) : Summable fun x => (f x)ᴴ :=
  hf.HasSum.matrix_conj_transpose.Summable

@[simp]
theorem summable_matrix_conj_transpose [StarAddMonoid R] [HasContinuousStar R] {f : X → Matrix m n R} :
    (Summable fun x => (f x)ᴴ) ↔ Summable f :=
  (Summable.map_iff_of_equiv (@Matrix.conjTransposeAddEquiv m n R _ _)
    (@continuous_id (Matrix m n R) _).matrix_conj_transpose continuous_id.matrix_conj_transpose :
    _)

theorem Matrix.conj_transpose_tsum [StarAddMonoid R] [HasContinuousStar R] [T2Space R] {f : X → Matrix m n R} :
    (∑' x, f x)ᴴ = ∑' x, (f x)ᴴ := by
  by_cases' hf : Summable f
  · exact hf.has_sum.matrix_conj_transpose.tsum_eq.symm
    
  · have hft := summable_matrix_conj_transpose.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft, conj_transpose_zero]
    

theorem HasSum.matrix_diagonal [DecidableEq n] {f : X → n → R} {a : n → R} (hf : HasSum f a) :
    HasSum (fun x => diagonalₓ (f x)) (diagonalₓ a) :=
  (hf.map (diagonalAddMonoidHom n R) <| Continuous.matrix_diagonal <| continuous_id : _)

theorem Summable.matrix_diagonal [DecidableEq n] {f : X → n → R} (hf : Summable f) :
    Summable fun x => diagonalₓ (f x) :=
  hf.HasSum.matrix_diagonal.Summable

@[simp]
theorem summable_matrix_diagonal [DecidableEq n] {f : X → n → R} : (Summable fun x => diagonalₓ (f x)) ↔ Summable f :=
  (Summable.map_iff_of_left_inverse (@Matrix.diagonalAddMonoidHom n R _ _) (Matrix.diagAddMonoidHom n R)
    (Continuous.matrix_diagonal continuous_id) continuous_matrix_diag fun A => diag_diagonal A :
    _)

theorem Matrix.diagonal_tsum [DecidableEq n] [T2Space R] {f : X → n → R} :
    diagonalₓ (∑' x, f x) = ∑' x, diagonalₓ (f x) := by
  by_cases' hf : Summable f
  · exact hf.has_sum.matrix_diagonal.tsum_eq.symm
    
  · have hft := summable_matrix_diagonal.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft]
    exact diagonal_zero
    

theorem HasSum.matrix_diag {f : X → Matrix n n R} {a : Matrix n n R} (hf : HasSum f a) :
    HasSum (fun x => diag (f x)) (diag a) :=
  (hf.map (diagAddMonoidHom n R) continuous_matrix_diag : _)

theorem Summable.matrix_diag {f : X → Matrix n n R} (hf : Summable f) : Summable fun x => diag (f x) :=
  hf.HasSum.matrix_diag.Summable

section BlockMatrices

theorem HasSum.matrix_block_diagonal [DecidableEq p] {f : X → p → Matrix m n R} {a : p → Matrix m n R}
    (hf : HasSum f a) : HasSum (fun x => blockDiagonalₓ (f x)) (blockDiagonalₓ a) :=
  (hf.map (blockDiagonalAddMonoidHom m n p R) <| Continuous.matrix_block_diagonal <| continuous_id : _)

theorem Summable.matrix_block_diagonal [DecidableEq p] {f : X → p → Matrix m n R} (hf : Summable f) :
    Summable fun x => blockDiagonalₓ (f x) :=
  hf.HasSum.matrix_block_diagonal.Summable

theorem summable_matrix_block_diagonal [DecidableEq p] {f : X → p → Matrix m n R} :
    (Summable fun x => blockDiagonalₓ (f x)) ↔ Summable f :=
  (Summable.map_iff_of_left_inverse (Matrix.blockDiagonalAddMonoidHom m n p R) (Matrix.blockDiagAddMonoidHom m n p R)
    (Continuous.matrix_block_diagonal continuous_id) (Continuous.matrix_block_diag continuous_id) fun A =>
    block_diag_block_diagonal A :
    _)

theorem Matrix.block_diagonal_tsum [DecidableEq p] [T2Space R] {f : X → p → Matrix m n R} :
    blockDiagonalₓ (∑' x, f x) = ∑' x, blockDiagonalₓ (f x) := by
  by_cases' hf : Summable f
  · exact hf.has_sum.matrix_block_diagonal.tsum_eq.symm
    
  · have hft := summable_matrix_block_diagonal.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft]
    exact block_diagonal_zero
    

theorem HasSum.matrix_block_diag {f : X → Matrix (m × p) (n × p) R} {a : Matrix (m × p) (n × p) R} (hf : HasSum f a) :
    HasSum (fun x => blockDiagₓ (f x)) (blockDiagₓ a) :=
  (hf.map (blockDiagAddMonoidHom m n p R) <| Continuous.matrix_block_diag continuous_id : _)

theorem Summable.matrix_block_diag {f : X → Matrix (m × p) (n × p) R} (hf : Summable f) :
    Summable fun x => blockDiagₓ (f x) :=
  hf.HasSum.matrix_block_diag.Summable

theorem HasSum.matrix_block_diagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R}
    {a : ∀ i, Matrix (m' i) (n' i) R} (hf : HasSum f a) : HasSum (fun x => blockDiagonal'ₓ (f x)) (blockDiagonal'ₓ a) :=
  (hf.map (blockDiagonal'AddMonoidHom m' n' R) <| Continuous.matrix_block_diagonal' <| continuous_id : _)

theorem Summable.matrix_block_diagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R} (hf : Summable f) :
    Summable fun x => blockDiagonal'ₓ (f x) :=
  hf.HasSum.matrix_block_diagonal'.Summable

theorem summable_matrix_block_diagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R} :
    (Summable fun x => blockDiagonal'ₓ (f x)) ↔ Summable f :=
  (Summable.map_iff_of_left_inverse (Matrix.blockDiagonal'AddMonoidHom m' n' R) (Matrix.blockDiag'AddMonoidHom m' n' R)
    (Continuous.matrix_block_diagonal' continuous_id) (Continuous.matrix_block_diag' continuous_id) fun A =>
    block_diag'_block_diagonal' A :
    _)

theorem Matrix.block_diagonal'_tsum [DecidableEq l] [T2Space R] {f : X → ∀ i, Matrix (m' i) (n' i) R} :
    blockDiagonal'ₓ (∑' x, f x) = ∑' x, blockDiagonal'ₓ (f x) := by
  by_cases' hf : Summable f
  · exact hf.has_sum.matrix_block_diagonal'.tsum_eq.symm
    
  · have hft := summable_matrix_block_diagonal'.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft]
    exact block_diagonal'_zero
    

theorem HasSum.matrix_block_diag' {f : X → Matrix (Σi, m' i) (Σi, n' i) R} {a : Matrix (Σi, m' i) (Σi, n' i) R}
    (hf : HasSum f a) : HasSum (fun x => blockDiag'ₓ (f x)) (blockDiag'ₓ a) :=
  (hf.map (blockDiag'AddMonoidHom m' n' R) <| Continuous.matrix_block_diag' continuous_id : _)

theorem Summable.matrix_block_diag' {f : X → Matrix (Σi, m' i) (Σi, n' i) R} (hf : Summable f) :
    Summable fun x => blockDiag'ₓ (f x) :=
  hf.HasSum.matrix_block_diag'.Summable

end BlockMatrices

end tsum

