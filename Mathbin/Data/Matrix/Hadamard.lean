/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import Mathbin.LinearAlgebra.Matrix.Trace

/-!
# Hadamard product of matrices

This file defines the Hadamard product `matrix.hadamard`
and contains basic properties about them.

## Main definition

- `matrix.hadamard`: defines the Hadamard product,
  which is the pointwise product of two matrices of the same size.

## Notation

* `⊙`: the Hadamard product `matrix.hadamard`;

## References

*  <https://en.wikipedia.org/wiki/hadamard_product_(matrices)>

## Tags

hadamard product, hadamard
-/


variable {α β γ m n : Type _}

variable {R : Type _}

namespace Matrix

open Matrix BigOperators

/-- `matrix.hadamard` defines the Hadamard product,
    which is the pointwise product of two matrices of the same size.-/
@[simp]
def hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α
  | i, j => A i j * B i j

-- mathport name: «expr ⊙ »
localized [Matrix] infixl:100 " ⊙ " => Matrix.hadamard

section BasicProperties

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

-- commutativity
theorem hadamard_comm [CommSemigroupₓ α] : A ⊙ B = B ⊙ A :=
  ext fun _ _ => mul_comm _ _

-- associativity
theorem hadamard_assoc [Semigroupₓ α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
  ext fun _ _ => mul_assoc _ _ _

-- distributivity
theorem hadamard_add [Distribₓ α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
  ext fun _ _ => left_distrib _ _ _

theorem add_hadamard [Distribₓ α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
  ext fun _ _ => right_distrib _ _ _

-- scalar multiplication
section Scalar

@[simp]
theorem smul_hadamard [Mul α] [HasSmul R α] [IsScalarTower R α α] (k : R) : (k • A) ⊙ B = k • A ⊙ B :=
  ext fun _ _ => smul_mul_assoc _ _ _

@[simp]
theorem hadamard_smul [Mul α] [HasSmul R α] [SmulCommClass R α α] (k : R) : A ⊙ (k • B) = k • A ⊙ B :=
  ext fun _ _ => mul_smul_comm _ _ _

end Scalar

section Zero

variable [MulZeroClassₓ α]

@[simp]
theorem hadamard_zero : A ⊙ (0 : Matrix m n α) = 0 :=
  ext fun _ _ => mul_zero _

@[simp]
theorem zero_hadamard : (0 : Matrix m n α) ⊙ A = 0 :=
  ext fun _ _ => zero_mul _

end Zero

section One

variable [DecidableEq n] [MulZeroOneClassₓ α]

variable (M : Matrix n n α)

theorem hadamard_one : M ⊙ (1 : Matrix n n α) = diagonalₓ fun i => M i i := by
  ext
  by_cases' h : i = j <;> simp [← h]

theorem one_hadamard : (1 : Matrix n n α) ⊙ M = diagonalₓ fun i => M i i := by
  ext
  by_cases' h : i = j <;> simp [← h]

end One

section Diagonal

variable [DecidableEq n] [MulZeroClassₓ α]

theorem diagonal_hadamard_diagonal (v : n → α) (w : n → α) : diagonalₓ v ⊙ diagonalₓ w = diagonalₓ (v * w) :=
  ext fun _ _ => (apply_ite2 _ _ _ _ _ _).trans (congr_arg _ <| zero_mul 0)

end Diagonal

section trace

variable [Fintype m] [Fintype n]

variable (R) [Semiringₓ α] [Semiringₓ R] [Module R α]

theorem sum_hadamard_eq : (∑ (i : m) (j : n), (A ⊙ B) i j) = trace (A ⬝ Bᵀ) :=
  rfl

theorem dot_product_vec_mul_hadamard [DecidableEq m] [DecidableEq n] (v : m → α) (w : n → α) :
    dotProduct (vecMulₓ v (A ⊙ B)) w = trace (diagonalₓ v ⬝ A ⬝ (B ⬝ diagonalₓ w)ᵀ) := by
  rw [← sum_hadamard_eq, Finset.sum_comm]
  simp [← dot_product, ← vec_mul, ← Finset.sum_mul, ← mul_assoc]

end trace

end BasicProperties

end Matrix

