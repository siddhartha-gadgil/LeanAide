/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.Tactic.FinCases

/-!
# Block matrices and their determinant

This file defines a predicate `matrix.block_triangular_matrix` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

 * `matrix.block_triangular_matrix` expresses that a `o` by `o` matrix is block triangular,
   if the rows and columns are ordered according to some order `b : o → ℕ`

## Main results
  * `det_of_block_triangular_matrix`: the determinant of a block triangular matrix
    is equal to the product of the determinants of all the blocks
  * `det_of_upper_triangular` and `det_of_lower_triangular`: the determinant of
    a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/


open BigOperators

universe v

variable {m n : Type _} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRingₓ R]

namespace Matrix

theorem det_to_block (M : Matrix m m R) (p : m → Prop) [DecidablePred p] :
    M.det =
      (Matrix.fromBlocks (toBlock M p p) (toBlock M p fun j => ¬p j) (toBlock M (fun j => ¬p j) p)
          (toBlock M (fun j => ¬p j) fun j => ¬p j)).det :=
  by
  rw [← Matrix.det_reindex_self (Equivₓ.sumCompl p).symm M]
  rw [det_apply', det_apply']
  congr
  ext σ
  congr
  ext
  generalize hy : σ x = y
  cases x <;>
    cases y <;>
      simp only [← Matrix.reindex_apply, ← to_block_apply, ← Equivₓ.symm_symm, ← Equivₓ.sum_compl_apply_inr, ←
        Equivₓ.sum_compl_apply_inl, ← from_blocks_apply₁₁, ← from_blocks_apply₁₂, ← from_blocks_apply₂₁, ←
        from_blocks_apply₂₂, ← Matrix.minor_apply]

theorem det_to_square_block (M : Matrix m m R) {n : Nat} (b : m → Finₓ n) (k : Finₓ n) :
    (toSquareBlock M b k).det = (toSquareBlockProp M fun i => b i = k).det := by
  simp

theorem det_to_square_block' (M : Matrix m m R) (b : m → ℕ) (k : ℕ) :
    (toSquareBlock' M b k).det = (toSquareBlockProp M fun i => b i = k).det := by
  simp

theorem two_block_triangular_det (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
    (h : ∀ (i) (h1 : ¬p i) (j) (h2 : p j), M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [det_to_block M p]
  convert
    det_from_blocks_zero₂₁ (to_block M p p) (to_block M p fun j => ¬p j) (to_block M (fun j => ¬p j) fun j => ¬p j)
  ext
  exact h (↑i) i.2 (↑j) j.2

theorem equiv_block_det (M : Matrix m m R) {p q : m → Prop} [DecidablePred p] [DecidablePred q] (e : ∀ x, q x ↔ p x) :
    (toSquareBlockProp M p).det = (toSquareBlockProp M q).det := by
  convert Matrix.det_reindex_self (Equivₓ.subtypeEquivRight e) (to_square_block_prop M q)

theorem to_square_block_det'' (M : Matrix m m R) {n : Nat} (b : m → Finₓ n) (k : Finₓ n) :
    (toSquareBlock M b k).det = (toSquareBlock' M (fun i => ↑(b i)) ↑k).det := by
  rw [to_square_block_def', to_square_block_def]
  apply equiv_block_det
  intro x
  apply (Finₓ.ext_iff _ _).symm

/-- Let `b` map rows and columns of a square matrix `M` to `n` blocks. Then
  `block_triangular_matrix' M n b` says the matrix is block triangular. -/
def BlockTriangularMatrix' {o : Type _} (M : Matrix o o R) {n : ℕ} (b : o → Finₓ n) : Prop :=
  ∀ i j, b j < b i → M i j = 0

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[["using", ident h]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[["using", ident h_1]]
theorem upper_two_block_triangular' {m n : Type _} (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    BlockTriangularMatrix' (fromBlocks A B 0 D) (Sum.elim (fun i => (0 : Finₓ 2)) fun j => 1) := by
  intro k1 k2 hk12
  have h0 : ∀ k : Sum m n, Sum.elim (fun i => (0 : Finₓ 2)) (fun j => 1) k = 0 → ∃ i, k = Sum.inl i := by
    simp
  have h1 : ∀ k : Sum m n, Sum.elim (fun i => (0 : Finₓ 2)) (fun j => 1) k = 1 → ∃ j, k = Sum.inr j := by
    simp
  set mk1 := (Sum.elim (fun i => (0 : Finₓ 2)) fun j => 1) k1 with hmk1
  set mk2 := (Sum.elim (fun i => (0 : Finₓ 2)) fun j => 1) k2 with hmk2
  fin_cases mk1 <;> fin_cases mk2 <;> rw [h, h_1] at hk12
  · exact absurd hk12 (Nat.not_lt_zeroₓ 0)
    
  · exact
      absurd hk12
        (by
          norm_num)
    
  · rw [hmk1] at h
    obtain ⟨i, hi⟩ := h1 k1 h
    rw [hmk2] at h_1
    obtain ⟨j, hj⟩ := h0 k2 h_1
    rw [hi, hj]
    simp
    
  · exact absurd hk12 (irrefl 1)
    

/-- Let `b` map rows and columns of a square matrix `M` to blocks indexed by `ℕ`s. Then
  `block_triangular_matrix M n b` says the matrix is block triangular. -/
def BlockTriangularMatrix {o : Type _} (M : Matrix o o R) (b : o → ℕ) : Prop :=
  ∀ i j, b j < b i → M i j = 0

theorem upper_two_block_triangular {m n : Type _} (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    BlockTriangularMatrix (fromBlocks A B 0 D) (Sum.elim (fun i => 0) fun j => 1) := by
  intro k1 k2 hk12
  have h01 : ∀ k : Sum m n, Sum.elim (fun i => 0) (fun j => 1) k = 0 ∨ Sum.elim (fun i => 0) (fun j => 1) k = 1 := by
    simp
  have h0 : ∀ k : Sum m n, Sum.elim (fun i => 0) (fun j => 1) k = 0 → ∃ i, k = Sum.inl i := by
    simp
  have h1 : ∀ k : Sum m n, Sum.elim (fun i => 0) (fun j => 1) k = 1 → ∃ j, k = Sum.inr j := by
    simp
  cases' h01 k1 with hk1 hk1 <;> cases' h01 k2 with hk2 hk2 <;> rw [hk1, hk2] at hk12
  · exact absurd hk12 (Nat.not_lt_zeroₓ 0)
    
  · exact absurd hk12 (Nat.not_lt_zeroₓ 1)
    
  · obtain ⟨i, hi⟩ := h1 k1 hk1
    obtain ⟨j, hj⟩ := h0 k2 hk2
    rw [hi, hj]
    simp
    
  · exact absurd hk12 (irrefl 1)
    

theorem det_of_block_triangular_matrix (M : Matrix m m R) (b : m → ℕ) (h : BlockTriangularMatrix M b) :
    ∀ (n : ℕ) (hn : ∀ i, b i < n), M.det = ∏ k in Finset.range n, (toSquareBlock' M b k).det := by
  intro n hn
  induction' n with n hi generalizing m M b
  · rw [Finset.prod_range_zero]
    apply det_eq_one_of_card_eq_zero
    apply fintype.card_eq_zero_iff.mpr
    exact ⟨fun i => Nat.not_lt_zeroₓ (b i) (hn i)⟩
    
  · rw [Finset.prod_range_succ_comm]
    have h2 : (M.to_square_block_prop fun i : m => b i = n.succ).det = (M.to_square_block' b n.succ).det := by
      dunfold to_square_block'
      dunfold to_square_block_prop
      rfl
    rw [two_block_triangular_det M fun i => ¬b i = n]
    · rw [mul_comm]
      apply congr (congr_arg Mul.mul _)
      · let m' := { a // ¬b a = n }
        let b' := fun i : m' => b ↑i
        have h' : block_triangular_matrix (M.to_square_block_prop fun i : m => ¬b i = n) b' := by
          intro i j
          apply h ↑i ↑j
        have hni : ∀ i : { a // ¬b a = n }, b' i < n := fun i =>
          (Ne.le_iff_lt i.property).mp (nat.lt_succ_iff.mp (hn ↑i))
        have h1 := hi (M.to_square_block_prop fun i : m => ¬b i = n) b' h' hni
        rw [← Finₓ.prod_univ_eq_prod_range] at h1⊢
        convert h1
        ext k
        simp only [← to_square_block_def', ← to_square_block_def]
        let he : { a // b' a = ↑k } ≃ { a // b a = ↑k } := by
          have hc : ∀ i : m, (fun a => b a = ↑k) i → (fun a => ¬b a = n) i := by
            intro i hbi
            rw [hbi]
            exact ne_of_ltₓ (Finₓ.is_lt k)
          exact Equivₓ.subtypeSubtypeEquivSubtype hc
        exact Matrix.det_reindex_self he fun i j : { a // b' a = ↑k } => M ↑i ↑j
        
      · rw [det_to_square_block' M b n]
        have hh : ∀ a, b a = n ↔ ¬(fun i : m => ¬b i = n) a := by
          intro i
          simp only [← not_not]
        exact equiv_block_det M hh
        
      
    · intro i hi j hj
      apply h i
      simp only [← not_not] at hi
      rw [hi]
      exact (Ne.le_iff_lt hj).mp (nat.lt_succ_iff.mp (hn j))
      
    

theorem det_of_block_triangular_matrix'' (M : Matrix m m R) (b : m → ℕ) (h : BlockTriangularMatrix M b) :
    M.det = ∏ k in Finset.image b Finset.univ, (toSquareBlock' M b k).det := by
  let n : ℕ := (Sup (Finset.image b Finset.univ : Set ℕ)).succ
  have hn : ∀ i, b i < n := by
    have hbi : ∀ i, b i ∈ Finset.image b Finset.univ := by
      simp
    intro i
    dsimp' only [← n]
    apply nat.lt_succ_iff.mpr
    exact le_cSup (Finset.bdd_above _) (hbi i)
  rw [det_of_block_triangular_matrix M b h n hn]
  refine' (Finset.prod_subset _ _).symm
  · intro a ha
    apply finset.mem_range.mpr
    obtain ⟨i, ⟨hi, hbi⟩⟩ := finset.mem_image.mp ha
    rw [← hbi]
    exact hn i
    
  · intro k hk hbk
    apply det_eq_one_of_card_eq_zero
    apply fintype.card_eq_zero_iff.mpr
    constructor
    simp only [← Subtype.forall]
    intro a hba
    apply hbk
    apply finset.mem_image.mpr
    use a
    exact ⟨Finset.mem_univ a, hba⟩
    

theorem det_of_block_triangular_matrix' (M : Matrix m m R) {n : ℕ} (b : m → Finₓ n) (h : BlockTriangularMatrix' M b) :
    M.det = ∏ k : Finₓ n, (toSquareBlock M b k).det := by
  let b2 : m → ℕ := fun i => ↑(b i)
  simp_rw [to_square_block_det'']
  rw [Finₓ.prod_univ_eq_prod_range (fun k : ℕ => (M.to_square_block' b2 k).det) n]
  apply det_of_block_triangular_matrix
  · intro i j hij
    exact h i j (fin.coe_fin_lt.mp hij)
    
  · intro i
    exact Finₓ.is_lt (b i)
    

theorem det_of_upper_triangular {n : ℕ} (M : Matrix (Finₓ n) (Finₓ n) R) (h : ∀ i j : Finₓ n, j < i → M i j = 0) :
    M.det = ∏ i : Finₓ n, M i i := by
  convert det_of_block_triangular_matrix' M id h
  ext i
  have h2 : ∀ j : { a // id a = i }, j = ⟨i, rfl⟩ := fun j : { a // id a = i } => Subtype.ext j.property
  have : Unique { a // id a = i } := ⟨⟨⟨i, rfl⟩⟩, h2⟩
  simp [← h2 default]

theorem det_of_lower_triangular {n : ℕ} (M : Matrix (Finₓ n) (Finₓ n) R) (h : ∀ i j : Finₓ n, i < j → M i j = 0) :
    M.det = ∏ i : Finₓ n, M i i := by
  rw [← det_transpose]
  exact det_of_upper_triangular _ fun (i j : Finₓ n) (hji : j < i) => h j i hji

end Matrix

