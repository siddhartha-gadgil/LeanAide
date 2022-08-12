/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathbin.Analysis.InnerProductSpace.Spectrum

/-! # Hermitian matrices

This file defines hermitian matrices and some basic results about them.

## Main definition

 * `matrix.is_hermitian` : a matrix `A : matrix n n α` is hermitian if `Aᴴ = A`.

## Tags

self-adjoint matrix, hermitian matrix

-/


namespace Matrix

variable {α β : Type _} {m n : Type _} {A : Matrix n n α}

open Matrix

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner α (PiLp 2 fun _ : n => α) _ x y

section NonUnitalSemiringₓ

variable [NonUnitalSemiringₓ α] [StarRing α] [NonUnitalSemiringₓ β] [StarRing β]

/-- A matrix is hermitian if it is equal to its conjugate transpose. On the reals, this definition
captures symmetric matrices. -/
def IsHermitian (A : Matrix n n α) : Prop :=
  Aᴴ = A

theorem IsHermitian.eq {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ = A :=
  h

@[ext]
theorem IsHermitian.ext {A : Matrix n n α} : (∀ i j, star (A j i) = A i j) → A.IsHermitian := by
  intro h
  ext i j
  exact h i j

theorem IsHermitian.apply {A : Matrix n n α} (h : A.IsHermitian) (i j : n) : star (A j i) = A i j := by
  unfold is_hermitian  at h
  rw [← h, conj_transpose_apply, star_star, h]

theorem IsHermitian.ext_iff {A : Matrix n n α} : A.IsHermitian ↔ ∀ i j, star (A j i) = A i j :=
  ⟨IsHermitian.apply, IsHermitian.ext⟩

theorem is_hermitian_mul_conj_transpose_self [Fintype n] (A : Matrix n n α) : (A ⬝ Aᴴ).IsHermitian := by
  rw [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose]

theorem is_hermitian_transpose_mul_self [Fintype n] (A : Matrix n n α) : (Aᴴ ⬝ A).IsHermitian := by
  rw [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose]

theorem is_hermitian_add_transpose_self (A : Matrix n n α) : (A + Aᴴ).IsHermitian := by
  simp [← is_hermitian, ← add_commₓ]

theorem is_hermitian_transpose_add_self (A : Matrix n n α) : (Aᴴ + A).IsHermitian := by
  simp [← is_hermitian, ← add_commₓ]

@[simp]
theorem is_hermitian_zero : (0 : Matrix n n α).IsHermitian :=
  conj_transpose_zero

@[simp]
theorem IsHermitian.map {A : Matrix n n α} (h : A.IsHermitian) (f : α → β) (hf : Function.Semiconj f star star) :
    (A.map f).IsHermitian :=
  (conj_transpose_map f hf).symm.trans <| h.Eq.symm ▸ rfl

@[simp]
theorem IsHermitian.transpose {A : Matrix n n α} (h : A.IsHermitian) : Aᵀ.IsHermitian := by
  rw [is_hermitian, conj_transpose, transpose_map]
  congr
  exact h

@[simp]
theorem IsHermitian.conj_transpose {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ.IsHermitian :=
  (h.transpose.map _) fun _ => rfl

@[simp]
theorem IsHermitian.add {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) : (A + B).IsHermitian :=
  (conj_transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]
theorem IsHermitian.minor {A : Matrix n n α} (h : A.IsHermitian) (f : m → n) : (A.minor f f).IsHermitian :=
  (conj_transpose_minor _ _ _).trans (h.symm ▸ rfl)

/-- The real diagonal matrix `diagonal v` is hermitian. -/
@[simp]
theorem is_hermitian_diagonal [DecidableEq n] (v : n → ℝ) : (diagonalₓ v).IsHermitian :=
  diagonal_conj_transpose _

/-- A block matrix `A.from_blocks B C D` is hermitian,
    if `A` and `D` are hermitian and `Bᴴ = C`. -/
theorem IsHermitian.from_blocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α} {D : Matrix n n α}
    (hA : A.IsHermitian) (hBC : Bᴴ = C) (hD : D.IsHermitian) : (A.fromBlocks B C D).IsHermitian := by
  have hCB : Cᴴ = B := by
    rw [← hBC]
    simp
  unfold Matrix.IsHermitian
  rw [from_blocks_conj_transpose]
  congr <;> assumption

/-- This is the `iff` version of `matrix.is_hermitian.from_blocks`. -/
theorem is_hermitian_from_blocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α} {D : Matrix n n α} :
    (A.fromBlocks B C D).IsHermitian ↔ A.IsHermitian ∧ Bᴴ = C ∧ Cᴴ = B ∧ D.IsHermitian :=
  ⟨fun h => ⟨congr_arg toBlocks₁₁ h, congr_arg toBlocks₂₁ h, congr_arg toBlocks₁₂ h, congr_arg toBlocks₂₂ h⟩,
    fun ⟨hA, hBC, hCB, hD⟩ => IsHermitian.from_blocks hA hBC hD⟩

end NonUnitalSemiringₓ

section Semiringₓ

variable [Semiringₓ α] [StarRing α] [Semiringₓ β] [StarRing β]

@[simp]
theorem is_hermitian_one [DecidableEq n] : (1 : Matrix n n α).IsHermitian :=
  conj_transpose_one

end Semiringₓ

section Ringₓ

variable [Ringₓ α] [StarRing α] [Ringₓ β] [StarRing β]

@[simp]
theorem IsHermitian.neg {A : Matrix n n α} (h : A.IsHermitian) : (-A).IsHermitian :=
  (conj_transpose_neg _).trans (congr_arg _ h)

@[simp]
theorem IsHermitian.sub {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) : (A - B).IsHermitian :=
  (conj_transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

end Ringₓ

section IsROrC

variable [IsROrC α] [IsROrC β]

/-- A matrix is hermitian iff the corresponding linear map is self adjoint. -/
theorem is_hermitian_iff_is_self_adjoint [Fintype n] [DecidableEq n] {A : Matrix n n α} :
    IsHermitian A ↔
      InnerProductSpace.IsSelfAdjoint
        ((PiLp.linearEquiv α fun _ : n => α).symm.conj A.toLin' : Module.End α (PiLp 2 _)) :=
  by
  rw [InnerProductSpace.IsSelfAdjoint, (PiLp.equiv 2 fun _ : n => α).symm.Surjective.Forall₂]
  simp only [← LinearEquiv.conj_apply, ← LinearMap.comp_apply, ← LinearEquiv.coe_coe, ← PiLp.linear_equiv_apply, ←
    PiLp.linear_equiv_symm_apply, ← LinearEquiv.symm_symm]
  simp_rw [EuclideanSpace.inner_eq_star_dot_product, Equivₓ.apply_symm_apply, to_lin'_apply, star_mul_vec,
    dot_product_mul_vec]
  constructor
  · rintro (h : Aᴴ = A) x y
    rw [h]
    
  · intro h
    ext i j
    simpa only [← (Pi.single_star i 1).symm, star_mul_vec, ← mul_oneₓ, ← dot_product_single, ← single_vec_mul, ←
      star_one, ← one_mulₓ] using
      h (@Pi.single _ _ _ (fun i => AddZeroClassₓ.toHasZero α) i 1)
        (@Pi.single _ _ _ (fun i => AddZeroClassₓ.toHasZero α) j 1)
    

end IsROrC

end Matrix

