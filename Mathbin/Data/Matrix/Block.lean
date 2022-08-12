/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/
import Mathbin.Data.Matrix.Basic

/-!
# Block Matrices

## Main definitions

* `matrix.from_blocks`: build a block matrix out of 4 blocks
* `matrix.to_blocks₁₁`, `matrix.to_blocks₁₂`, `matrix.to_blocks₂₁`, `matrix.to_blocks₂₂`:
  extract each of the four blocks from `matrix.from_blocks`.
* `matrix.block_diagonal`: block diagonal of equally sized blocks. On square blocks, this is a
  ring homomorphisms, `matrix.block_diagonal_ring_hom`.
* `matrix.block_diag`: extract the blocks from the diagonal of a block diagonal matrix.
* `matrix.block_diagonal'`: block diagonal of unequally sized blocks. On square blocks, this is a
  ring homomorphisms, `matrix.block_diagonal'_ring_hom`.
* `matrix.block_diag'`: extract the blocks from the diagonal of a block diagonal matrix.
-/


variable {l m n o p q : Type _} {m' n' p' : o → Type _}

variable {R : Type _} {S : Type _} {α : Type _} {β : Type _}

open Matrix

namespace Matrix

section BlockMatrices

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
@[pp_nodot]
def fromBlocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    Matrix (Sum n o) (Sum l m) α :=
  of <| Sum.elim (fun i => Sum.elim (A i) (B i)) fun i => Sum.elim (C i) (D i)

@[simp]
theorem from_blocks_apply₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : n)
    (j : l) : fromBlocks A B C D (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp]
theorem from_blocks_apply₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : n)
    (j : m) : fromBlocks A B C D (Sum.inl i) (Sum.inr j) = B i j :=
  rfl

@[simp]
theorem from_blocks_apply₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : o)
    (j : l) : fromBlocks A B C D (Sum.inr i) (Sum.inl j) = C i j :=
  rfl

@[simp]
theorem from_blocks_apply₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : o)
    (j : m) : fromBlocks A B C D (Sum.inr i) (Sum.inr j) = D i j :=
  rfl

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top left" submatrix. -/
def toBlocks₁₁ (M : Matrix (Sum n o) (Sum l m) α) : Matrix n l α :=
  of fun i j => M (Sum.inl i) (Sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top right" submatrix. -/
def toBlocks₁₂ (M : Matrix (Sum n o) (Sum l m) α) : Matrix n m α :=
  of fun i j => M (Sum.inl i) (Sum.inr j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom left" submatrix. -/
def toBlocks₂₁ (M : Matrix (Sum n o) (Sum l m) α) : Matrix o l α :=
  of fun i j => M (Sum.inr i) (Sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom right" submatrix. -/
def toBlocks₂₂ (M : Matrix (Sum n o) (Sum l m) α) : Matrix o m α :=
  of fun i j => M (Sum.inr i) (Sum.inr j)

theorem from_blocks_to_blocks (M : Matrix (Sum n o) (Sum l m) α) :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

@[simp]
theorem to_blocks_from_blocks₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).toBlocks₁₁ = A :=
  rfl

@[simp]
theorem to_blocks_from_blocks₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).toBlocks₁₂ = B :=
  rfl

@[simp]
theorem to_blocks_from_blocks₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).toBlocks₂₁ = C :=
  rfl

@[simp]
theorem to_blocks_from_blocks₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).toBlocks₂₂ = D :=
  rfl

theorem from_blocks_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (f : α → β) :
    (fromBlocks A B C D).map f = fromBlocks (A.map f) (B.map f) (C.map f) (D.map f) := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [← from_blocks]

theorem from_blocks_transpose (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D)ᵀ = fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [← from_blocks]

theorem from_blocks_conj_transpose [HasStar α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᴴ = fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ := by
  simp only [← conj_transpose, ← from_blocks_transpose, ← from_blocks_map]

@[simp]
theorem from_blocks_minor_sum_swap_left (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
    (f : p → Sum l m) : (fromBlocks A B C D).minor Sum.swap f = (fromBlocks C D A B).minor id f := by
  ext i j
  cases i <;> dsimp' <;> cases f j <;> rfl

@[simp]
theorem from_blocks_minor_sum_swap_right (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
    (f : p → Sum n o) : (fromBlocks A B C D).minor f Sum.swap = (fromBlocks B A D C).minor f id := by
  ext i j
  cases j <;> dsimp' <;> cases f i <;> rfl

theorem from_blocks_minor_sum_swap_sum_swap {l m n o α : Type _} (A : Matrix n l α) (B : Matrix n m α)
    (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D).minor Sum.swap Sum.swap = fromBlocks D C B A := by
  simp

/-- A 2x2 block matrix is block diagonal if the blocks outside of the diagonal vanish -/
def IsTwoBlockDiagonal [Zero α] (A : Matrix (Sum n o) (Sum l m) α) : Prop :=
  toBlocks₁₂ A = 0 ∧ toBlocks₂₁ A = 0

/-- Let `p` pick out certain rows and `q` pick out certain columns of a matrix `M`. Then
  `to_block M p q` is the corresponding block matrix. -/
def toBlock (M : Matrix m n α) (p : m → Prop) (q : n → Prop) : Matrix { a // p a } { a // q a } α :=
  M.minor coe coe

@[simp]
theorem to_block_apply (M : Matrix m n α) (p : m → Prop) (q : n → Prop) (i : { a // p a }) (j : { a // q a }) :
    toBlock M p q i j = M ↑i ↑j :=
  rfl

/-- Let `b` map rows and columns of a square matrix `M` to blocks. Then
  `to_square_block M b k` is the block `k` matrix. -/
def toSquareBlock (M : Matrix m m α) {n : Nat} (b : m → Finₓ n) (k : Finₓ n) :
    Matrix { a // b a = k } { a // b a = k } α :=
  M.minor coe coe

@[simp]
theorem to_square_block_def (M : Matrix m m α) {n : Nat} (b : m → Finₓ n) (k : Finₓ n) :
    toSquareBlock M b k = fun i j => M ↑i ↑j :=
  rfl

/-- Alternate version with `b : m → nat`. Let `b` map rows and columns of a square matrix `M` to
  blocks. Then `to_square_block' M b k` is the block `k` matrix. -/
def toSquareBlock' (M : Matrix m m α) (b : m → Nat) (k : Nat) : Matrix { a // b a = k } { a // b a = k } α :=
  M.minor coe coe

@[simp]
theorem to_square_block_def' (M : Matrix m m α) (b : m → Nat) (k : Nat) : toSquareBlock' M b k = fun i j => M ↑i ↑j :=
  rfl

/-- Let `p` pick out certain rows and columns of a square matrix `M`. Then
  `to_square_block_prop M p` is the corresponding block matrix. -/
def toSquareBlockProp (M : Matrix m m α) (p : m → Prop) : Matrix { a // p a } { a // p a } α :=
  M.minor coe coe

@[simp]
theorem to_square_block_prop_def (M : Matrix m m α) (p : m → Prop) : toSquareBlockProp M p = fun i j => M ↑i ↑j :=
  rfl

theorem from_blocks_smul [HasSmul R α] (x : R) (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : x • fromBlocks A B C D = fromBlocks (x • A) (x • B) (x • C) (x • D) := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [← from_blocks]

theorem from_blocks_add [Add α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
    (A' : Matrix n l α) (B' : Matrix n m α) (C' : Matrix o l α) (D' : Matrix o m α) :
    fromBlocks A B C D + fromBlocks A' B' C' D' = fromBlocks (A + A') (B + B') (C + C') (D + D') := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

theorem from_blocks_multiply [Fintype l] [Fintype m] [NonUnitalNonAssocSemiringₓ α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (A' : Matrix l p α) (B' : Matrix l q α) (C' : Matrix m p α)
    (D' : Matrix m q α) :
    fromBlocks A B C D ⬝ fromBlocks A' B' C' D' =
      fromBlocks (A ⬝ A' + B ⬝ C') (A ⬝ B' + B ⬝ D') (C ⬝ A' + D ⬝ C') (C ⬝ B' + D ⬝ D') :=
  by
  ext i j
  rcases i with ⟨⟩ <;>
    rcases j with ⟨⟩ <;>
      simp only [← from_blocks, ← mul_apply, ← Fintype.sum_sum_type, ← Sum.elim_inl, ← Sum.elim_inr, ← Pi.add_apply, ←
        of_apply]

theorem from_blocks_mul_vec [Fintype l] [Fintype m] [NonUnitalNonAssocSemiringₓ α] (A : Matrix n l α) (B : Matrix n m α)
    (C : Matrix o l α) (D : Matrix o m α) (x : Sum l m → α) :
    mulVecₓ (fromBlocks A B C D) x =
      Sum.elim (mulVecₓ A (x ∘ Sum.inl) + mulVecₓ B (x ∘ Sum.inr))
        (mulVecₓ C (x ∘ Sum.inl) + mulVecₓ D (x ∘ Sum.inr)) :=
  by
  ext i
  cases i <;> simp [← mul_vec, ← dot_product]

theorem vec_mul_from_blocks [Fintype n] [Fintype o] [NonUnitalNonAssocSemiringₓ α] (A : Matrix n l α) (B : Matrix n m α)
    (C : Matrix o l α) (D : Matrix o m α) (x : Sum n o → α) :
    vecMulₓ x (fromBlocks A B C D) =
      Sum.elim (vecMulₓ (x ∘ Sum.inl) A + vecMulₓ (x ∘ Sum.inr) C)
        (vecMulₓ (x ∘ Sum.inl) B + vecMulₓ (x ∘ Sum.inr) D) :=
  by
  ext i
  cases i <;> simp [← vec_mul, ← dot_product]

variable [DecidableEq l] [DecidableEq m]

@[simp]
theorem from_blocks_diagonal [Zero α] (d₁ : l → α) (d₂ : m → α) :
    fromBlocks (diagonalₓ d₁) 0 0 (diagonalₓ d₂) = diagonalₓ (Sum.elim d₁ d₂) := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [← diagonal]

@[simp]
theorem from_blocks_one [Zero α] [One α] : fromBlocks (1 : Matrix l l α) 0 0 (1 : Matrix m m α) = 1 := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [← one_apply]

end BlockMatrices

section BlockDiagonal

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/-- `matrix.block_diagonal M` turns a homogenously-indexed collection of matrices
`M : o → matrix m n α'` into a `m × o`-by-`n × o` block matrix which has the entries of `M` along
the diagonal and zero elsewhere.

See also `matrix.block_diagonal'` if the matrices may not have the same size everywhere.
-/
def blockDiagonalₓ (M : o → Matrix m n α) : Matrix (m × o) (n × o) α
  | ⟨i, k⟩, ⟨j, k'⟩ => if k = k' then M k i j else 0

theorem block_diagonal_apply (M : o → Matrix m n α) (ik jk) :
    blockDiagonalₓ M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 := by
  cases ik
  cases jk
  rfl

@[simp]
theorem block_diagonal_apply_eq (M : o → Matrix m n α) (i j k) : blockDiagonalₓ M (i, k) (j, k) = M k i j :=
  if_pos rfl

theorem block_diagonal_apply_ne (M : o → Matrix m n α) (i j) {k k'} (h : k ≠ k') :
    blockDiagonalₓ M (i, k) (j, k') = 0 :=
  if_neg h

theorem block_diagonal_map (M : o → Matrix m n α) (f : α → β) (hf : f 0 = 0) :
    (blockDiagonalₓ M).map f = blockDiagonalₓ fun k => (M k).map f := by
  ext
  simp only [← map_apply, ← block_diagonal_apply, ← eq_comm]
  rw [apply_ite f, hf]

@[simp]
theorem block_diagonal_transpose (M : o → Matrix m n α) : (blockDiagonalₓ M)ᵀ = blockDiagonalₓ fun k => (M k)ᵀ := by
  ext
  simp only [← transpose_apply, ← block_diagonal_apply, ← eq_comm]
  split_ifs with h
  · rw [h]
    
  · rfl
    

@[simp]
theorem block_diagonal_conj_transpose {α : Type _} [AddMonoidₓ α] [StarAddMonoid α] (M : o → Matrix m n α) :
    (blockDiagonalₓ M)ᴴ = blockDiagonalₓ fun k => (M k)ᴴ := by
  simp only [← conj_transpose, ← block_diagonal_transpose]
  rw [block_diagonal_map _ star (star_zero α)]

@[simp]
theorem block_diagonal_zero : blockDiagonalₓ (0 : o → Matrix m n α) = 0 := by
  ext
  simp [← block_diagonal_apply]

@[simp]
theorem block_diagonal_diagonal [DecidableEq m] (d : o → m → α) :
    (blockDiagonalₓ fun k => diagonalₓ (d k)) = diagonalₓ fun ik => d ik.2 ik.1 := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [← block_diagonal_apply, ← diagonal, ← Prod.mk.inj_iff, ite_and]
  congr 1
  rw [and_comm]

@[simp]
theorem block_diagonal_one [DecidableEq m] [One α] : blockDiagonalₓ (1 : o → Matrix m m α) = 1 :=
  show (blockDiagonalₓ fun _ : o => diagonalₓ fun _ : m => (1 : α)) = diagonalₓ fun _ => 1 by
    rw [block_diagonal_diagonal]

end Zero

@[simp]
theorem block_diagonal_add [AddZeroClassₓ α] (M N : o → Matrix m n α) :
    blockDiagonalₓ (M + N) = blockDiagonalₓ M + blockDiagonalₓ N := by
  ext
  simp only [← block_diagonal_apply, ← Pi.add_apply]
  split_ifs <;> simp

section

variable (o m n α)

/-- `matrix.block_diagonal` as an `add_monoid_hom`. -/
@[simps]
def blockDiagonalAddMonoidHom [AddZeroClassₓ α] : (o → Matrix m n α) →+ Matrix (m × o) (n × o) α where
  toFun := blockDiagonalₓ
  map_zero' := block_diagonal_zero
  map_add' := block_diagonal_add

end

@[simp]
theorem block_diagonal_neg [AddGroupₓ α] (M : o → Matrix m n α) : blockDiagonalₓ (-M) = -blockDiagonalₓ M :=
  map_neg (blockDiagonalAddMonoidHom m n o α) M

@[simp]
theorem block_diagonal_sub [AddGroupₓ α] (M N : o → Matrix m n α) :
    blockDiagonalₓ (M - N) = blockDiagonalₓ M - blockDiagonalₓ N :=
  map_sub (blockDiagonalAddMonoidHom m n o α) M N

@[simp]
theorem block_diagonal_mul [Fintype n] [Fintype o] [NonUnitalNonAssocSemiringₓ α] (M : o → Matrix m n α)
    (N : o → Matrix n p α) : (blockDiagonalₓ fun k => M k ⬝ N k) = blockDiagonalₓ M ⬝ blockDiagonalₓ N := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [← block_diagonal_apply, ← mul_apply, Finset.univ_product_univ, ← Finset.sum_product]
  split_ifs with h <;> simp [← h]

section

variable (α m o)

/-- `matrix.block_diagonal` as a `ring_hom`. -/
@[simps]
def blockDiagonalRingHom [DecidableEq m] [Fintype o] [Fintype m] [NonAssocSemiringₓ α] :
    (o → Matrix m m α) →+* Matrix (m × o) (m × o) α :=
  { blockDiagonalAddMonoidHom m m o α with toFun := blockDiagonalₓ, map_one' := block_diagonal_one,
    map_mul' := block_diagonal_mul }

end

@[simp]
theorem block_diagonal_pow [DecidableEq m] [Fintype o] [Fintype m] [Semiringₓ α] (M : o → Matrix m m α) (n : ℕ) :
    blockDiagonalₓ (M ^ n) = blockDiagonalₓ M ^ n :=
  map_pow (blockDiagonalRingHom m o α) M n

@[simp]
theorem block_diagonal_smul {R : Type _} [Monoidₓ R] [AddMonoidₓ α] [DistribMulAction R α] (x : R)
    (M : o → Matrix m n α) : blockDiagonalₓ (x • M) = x • blockDiagonalₓ M := by
  ext
  simp only [← block_diagonal_apply, ← Pi.smul_apply]
  split_ifs <;> simp

end BlockDiagonal

section BlockDiag

/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `matrix.diag`, and the left-inverse of `matrix.block_diagonal`. -/
def blockDiagₓ (M : Matrix (m × o) (n × o) α) (k : o) : Matrix m n α
  | i, j => M (i, k) (j, k)

theorem block_diag_map (M : Matrix (m × o) (n × o) α) (f : α → β) :
    blockDiagₓ (M.map f) = fun k => (blockDiagₓ M k).map f :=
  rfl

@[simp]
theorem block_diag_transpose (M : Matrix (m × o) (n × o) α) (k : o) : blockDiagₓ Mᵀ k = (blockDiagₓ M k)ᵀ :=
  ext fun i j => rfl

@[simp]
theorem block_diag_conj_transpose {α : Type _} [AddMonoidₓ α] [StarAddMonoid α] (M : Matrix (m × o) (n × o) α) (k : o) :
    blockDiagₓ Mᴴ k = (blockDiagₓ M k)ᴴ :=
  ext fun i j => rfl

section Zero

variable [Zero α] [Zero β]

@[simp]
theorem block_diag_zero : blockDiagₓ (0 : Matrix (m × o) (n × o) α) = 0 :=
  rfl

@[simp]
theorem block_diag_diagonal [DecidableEq o] [DecidableEq m] (d : m × o → α) (k : o) :
    blockDiagₓ (diagonalₓ d) k = diagonalₓ fun i => d (i, k) :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [block_diag, diagonal_apply_eq, diagonal_apply_eq]
      
    · rw [block_diag, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt _ hij)]
      exact prod.fst_eq_iff.mpr
      

@[simp]
theorem block_diag_block_diagonal [DecidableEq o] (M : o → Matrix m n α) : blockDiagₓ (blockDiagonalₓ M) = M :=
  funext fun k => ext fun i j => block_diagonal_apply_eq _ _ _ _

@[simp]
theorem block_diag_one [DecidableEq o] [DecidableEq m] [One α] : blockDiagₓ (1 : Matrix (m × o) (m × o) α) = 1 :=
  funext <| block_diag_diagonal _

end Zero

@[simp]
theorem block_diag_add [AddZeroClassₓ α] (M N : Matrix (m × o) (n × o) α) :
    blockDiagₓ (M + N) = blockDiagₓ M + blockDiagₓ N :=
  rfl

section

variable (o m n α)

/-- `matrix.block_diag` as an `add_monoid_hom`. -/
@[simps]
def blockDiagAddMonoidHom [AddZeroClassₓ α] : Matrix (m × o) (n × o) α →+ o → Matrix m n α where
  toFun := blockDiagₓ
  map_zero' := block_diag_zero
  map_add' := block_diag_add

end

@[simp]
theorem block_diag_neg [AddGroupₓ α] (M : Matrix (m × o) (n × o) α) : blockDiagₓ (-M) = -blockDiagₓ M :=
  map_neg (blockDiagAddMonoidHom m n o α) M

@[simp]
theorem block_diag_sub [AddGroupₓ α] (M N : Matrix (m × o) (n × o) α) :
    blockDiagₓ (M - N) = blockDiagₓ M - blockDiagₓ N :=
  map_sub (blockDiagAddMonoidHom m n o α) M N

@[simp]
theorem block_diag_smul {R : Type _} [Monoidₓ R] [AddMonoidₓ α] [DistribMulAction R α] (x : R)
    (M : Matrix (m × o) (n × o) α) : blockDiagₓ (x • M) = x • blockDiagₓ M :=
  rfl

end BlockDiag

section BlockDiagonal'

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/-- `matrix.block_diagonal' M` turns `M : Π i, matrix (m i) (n i) α` into a
`Σ i, m i`-by-`Σ i, n i` block matrix which has the entries of `M` along the diagonal
and zero elsewhere.

This is the dependently-typed version of `matrix.block_diagonal`. -/
def blockDiagonal'ₓ (M : ∀ i, Matrix (m' i) (n' i) α) : Matrix (Σi, m' i) (Σi, n' i) α
  | ⟨k, i⟩, ⟨k', j⟩ => if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0

theorem block_diagonal'_eq_block_diagonal (M : o → Matrix m n α) {k k'} (i j) :
    blockDiagonalₓ M (i, k) (j, k') = blockDiagonal'ₓ M ⟨k, i⟩ ⟨k', j⟩ :=
  rfl

theorem block_diagonal'_minor_eq_block_diagonal (M : o → Matrix m n α) :
    (blockDiagonal'ₓ M).minor (Prod.toSigma ∘ Prod.swap) (Prod.toSigma ∘ Prod.swap) = blockDiagonalₓ M :=
  Matrix.ext fun ⟨k, i⟩ ⟨k', j⟩ => rfl

theorem block_diagonal'_apply (M : ∀ i, Matrix (m' i) (n' i) α) (ik jk) :
    blockDiagonal'ₓ M ik jk = if h : ik.1 = jk.1 then M ik.1 ik.2 (cast (congr_arg n' h.symm) jk.2) else 0 := by
  cases ik
  cases jk
  rfl

@[simp]
theorem block_diagonal'_apply_eq (M : ∀ i, Matrix (m' i) (n' i) α) (k i j) :
    blockDiagonal'ₓ M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
  dif_pos rfl

theorem block_diagonal'_apply_ne (M : ∀ i, Matrix (m' i) (n' i) α) {k k'} (i j) (h : k ≠ k') :
    blockDiagonal'ₓ M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
  dif_neg h

theorem block_diagonal'_map (M : ∀ i, Matrix (m' i) (n' i) α) (f : α → β) (hf : f 0 = 0) :
    (blockDiagonal'ₓ M).map f = blockDiagonal'ₓ fun k => (M k).map f := by
  ext
  simp only [← map_apply, ← block_diagonal'_apply, ← eq_comm]
  rw [apply_dite f, hf]

@[simp]
theorem block_diagonal'_transpose (M : ∀ i, Matrix (m' i) (n' i) α) :
    (blockDiagonal'ₓ M)ᵀ = blockDiagonal'ₓ fun k => (M k)ᵀ := by
  ext ⟨ii, ix⟩ ⟨ji, jx⟩
  simp only [← transpose_apply, ← block_diagonal'_apply]
  split_ifs <;> cc

@[simp]
theorem block_diagonal'_conj_transpose {α} [AddMonoidₓ α] [StarAddMonoid α] (M : ∀ i, Matrix (m' i) (n' i) α) :
    (blockDiagonal'ₓ M)ᴴ = blockDiagonal'ₓ fun k => (M k)ᴴ := by
  simp only [← conj_transpose, ← block_diagonal'_transpose]
  exact block_diagonal'_map _ star (star_zero α)

@[simp]
theorem block_diagonal'_zero : blockDiagonal'ₓ (0 : ∀ i, Matrix (m' i) (n' i) α) = 0 := by
  ext
  simp [← block_diagonal'_apply]

@[simp]
theorem block_diagonal'_diagonal [∀ i, DecidableEq (m' i)] (d : ∀ i, m' i → α) :
    (blockDiagonal'ₓ fun k => diagonalₓ (d k)) = diagonalₓ fun ik => d ik.1 ik.2 := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [← block_diagonal'_apply, ← diagonal]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp
    
  · simp [← hij]
    

@[simp]
theorem block_diagonal'_one [∀ i, DecidableEq (m' i)] [One α] : blockDiagonal'ₓ (1 : ∀ i, Matrix (m' i) (m' i) α) = 1 :=
  show (blockDiagonal'ₓ fun i : o => diagonalₓ fun _ : m' i => (1 : α)) = diagonalₓ fun _ => 1 by
    rw [block_diagonal'_diagonal]

end Zero

@[simp]
theorem block_diagonal'_add [AddZeroClassₓ α] (M N : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal'ₓ (M + N) = blockDiagonal'ₓ M + blockDiagonal'ₓ N := by
  ext
  simp only [← block_diagonal'_apply, ← Pi.add_apply]
  split_ifs <;> simp

section

variable (m' n' α)

/-- `matrix.block_diagonal'` as an `add_monoid_hom`. -/
@[simps]
def blockDiagonal'AddMonoidHom [AddZeroClassₓ α] : (∀ i, Matrix (m' i) (n' i) α) →+ Matrix (Σi, m' i) (Σi, n' i) α where
  toFun := blockDiagonal'ₓ
  map_zero' := block_diagonal'_zero
  map_add' := block_diagonal'_add

end

@[simp]
theorem block_diagonal'_neg [AddGroupₓ α] (M : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal'ₓ (-M) = -blockDiagonal'ₓ M :=
  map_neg (blockDiagonal'AddMonoidHom m' n' α) M

@[simp]
theorem block_diagonal'_sub [AddGroupₓ α] (M N : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal'ₓ (M - N) = blockDiagonal'ₓ M - blockDiagonal'ₓ N :=
  map_sub (blockDiagonal'AddMonoidHom m' n' α) M N

@[simp]
theorem block_diagonal'_mul [NonUnitalNonAssocSemiringₓ α] [∀ i, Fintype (n' i)] [Fintype o]
    (M : ∀ i, Matrix (m' i) (n' i) α) (N : ∀ i, Matrix (n' i) (p' i) α) :
    (blockDiagonal'ₓ fun k => M k ⬝ N k) = blockDiagonal'ₓ M ⬝ blockDiagonal'ₓ N := by
  ext ⟨k, i⟩ ⟨k', j⟩
  simp only [← block_diagonal'_apply, ← mul_apply, Finset.univ_sigma_univ, ← Finset.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · split_ifs <;> simp
    
  · intro j' hj'
    exact
      Finset.sum_eq_zero fun _ _ => by
        rw [dif_neg hj'.symm, zero_mul]
    

section

variable (α m')

/-- `matrix.block_diagonal'` as a `ring_hom`. -/
@[simps]
def blockDiagonal'RingHom [∀ i, DecidableEq (m' i)] [Fintype o] [∀ i, Fintype (m' i)] [NonAssocSemiringₓ α] :
    (∀ i, Matrix (m' i) (m' i) α) →+* Matrix (Σi, m' i) (Σi, m' i) α :=
  { blockDiagonal'AddMonoidHom m' m' α with toFun := blockDiagonal'ₓ, map_one' := block_diagonal'_one,
    map_mul' := block_diagonal'_mul }

end

@[simp]
theorem block_diagonal'_pow [∀ i, DecidableEq (m' i)] [Fintype o] [∀ i, Fintype (m' i)] [Semiringₓ α]
    (M : ∀ i, Matrix (m' i) (m' i) α) (n : ℕ) : blockDiagonal'ₓ (M ^ n) = blockDiagonal'ₓ M ^ n :=
  map_pow (blockDiagonal'RingHom m' α) M n

@[simp]
theorem block_diagonal'_smul {R : Type _} [Semiringₓ R] [AddCommMonoidₓ α] [Module R α] (x : R)
    (M : ∀ i, Matrix (m' i) (n' i) α) : blockDiagonal'ₓ (x • M) = x • blockDiagonal'ₓ M := by
  ext
  simp only [← block_diagonal'_apply, ← Pi.smul_apply]
  split_ifs <;> simp

end BlockDiagonal'

section BlockDiag'

/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `matrix.diag`, and the left-inverse of `matrix.block_diagonal'`. -/
def blockDiag'ₓ (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) : Matrix (m' k) (n' k) α
  | i, j => M ⟨k, i⟩ ⟨k, j⟩

theorem block_diag'_map (M : Matrix (Σi, m' i) (Σi, n' i) α) (f : α → β) :
    blockDiag'ₓ (M.map f) = fun k => (blockDiag'ₓ M k).map f :=
  rfl

@[simp]
theorem block_diag'_transpose (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) : blockDiag'ₓ Mᵀ k = (blockDiag'ₓ M k)ᵀ :=
  ext fun i j => rfl

@[simp]
theorem block_diag'_conj_transpose {α : Type _} [AddMonoidₓ α] [StarAddMonoid α] (M : Matrix (Σi, m' i) (Σi, n' i) α)
    (k : o) : blockDiag'ₓ Mᴴ k = (blockDiag'ₓ M k)ᴴ :=
  ext fun i j => rfl

section Zero

variable [Zero α] [Zero β]

@[simp]
theorem block_diag'_zero : blockDiag'ₓ (0 : Matrix (Σi, m' i) (Σi, n' i) α) = 0 :=
  rfl

@[simp]
theorem block_diag'_diagonal [DecidableEq o] [∀ i, DecidableEq (m' i)] (d : (Σi, m' i) → α) (k : o) :
    blockDiag'ₓ (diagonalₓ d) k = diagonalₓ fun i => d ⟨k, i⟩ :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [block_diag', diagonal_apply_eq, diagonal_apply_eq]
      
    · rw [block_diag', diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt (fun h => _) hij)]
      cases h
      rfl
      

@[simp]
theorem block_diag'_block_diagonal' [DecidableEq o] (M : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiag'ₓ (blockDiagonal'ₓ M) = M :=
  funext fun k => ext fun i j => block_diagonal'_apply_eq _ _ _ _

@[simp]
theorem block_diag'_one [DecidableEq o] [∀ i, DecidableEq (m' i)] [One α] :
    blockDiag'ₓ (1 : Matrix (Σi, m' i) (Σi, m' i) α) = 1 :=
  funext <| block_diag'_diagonal _

end Zero

@[simp]
theorem block_diag'_add [AddZeroClassₓ α] (M N : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag'ₓ (M + N) = blockDiag'ₓ M + blockDiag'ₓ N :=
  rfl

section

variable (m' n' α)

/-- `matrix.block_diag'` as an `add_monoid_hom`. -/
@[simps]
def blockDiag'AddMonoidHom [AddZeroClassₓ α] : Matrix (Σi, m' i) (Σi, n' i) α →+ ∀ i, Matrix (m' i) (n' i) α where
  toFun := blockDiag'ₓ
  map_zero' := block_diag'_zero
  map_add' := block_diag'_add

end

@[simp]
theorem block_diag'_neg [AddGroupₓ α] (M : Matrix (Σi, m' i) (Σi, n' i) α) : blockDiag'ₓ (-M) = -blockDiag'ₓ M :=
  map_neg (blockDiag'AddMonoidHom m' n' α) M

@[simp]
theorem block_diag'_sub [AddGroupₓ α] (M N : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag'ₓ (M - N) = blockDiag'ₓ M - blockDiag'ₓ N :=
  map_sub (blockDiag'AddMonoidHom m' n' α) M N

@[simp]
theorem block_diag'_smul {R : Type _} [Monoidₓ R] [AddMonoidₓ α] [DistribMulAction R α] (x : R)
    (M : Matrix (Σi, m' i) (Σi, n' i) α) : blockDiag'ₓ (x • M) = x • blockDiag'ₓ M :=
  rfl

end BlockDiag'

end Matrix

