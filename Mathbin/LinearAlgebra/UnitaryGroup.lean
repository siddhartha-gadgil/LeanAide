/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.Algebra.Star.Unitary

/-!
# The Unitary Group

This file defines elements of the unitary group `unitary_group n α`, where `α` is a `star_ring`.
This consists of all `n` by `n` matrices with entries in `α` such that the star-transpose is its
inverse. In addition, we define the group structure on `unitary_group n α`, and the embedding into
the general linear group `general_linear_group α (n → α)`.

We also define the orthogonal group `orthogonal_group n β`, where `β` is a `comm_ring`.

## Main Definitions

 * `matrix.unitary_group` is the type of matrices where the star-transpose is the inverse
 * `matrix.unitary_group.group` is the group structure (under multiplication)
 * `matrix.unitary_group.embedding_GL` is the embedding `unitary_group n α → GLₙ(α)`
 * `matrix.orthogonal_group` is the type of matrices where the transpose is the inverse

## References

 * https://en.wikipedia.org/wiki/Unitary_group

## Tags

matrix group, group, unitary group, orthogonal group

-/


universe u v

namespace Matrix

open LinearMap

open Matrix

section

variable (n : Type u) [DecidableEq n] [Fintype n]

variable (α : Type v) [CommRingₓ α] [StarRing α]

/-- `unitary_group n` is the group of `n` by `n` matrices where the star-transpose is the inverse.
-/
abbrev unitaryGroup :=
  unitary (Matrix n n α)

end

variable {n : Type u} [DecidableEq n] [Fintype n]

variable {α : Type v} [CommRingₓ α] [StarRing α]

theorem mem_unitary_group_iff {A : Matrix n n α} : A ∈ Matrix.unitaryGroup n α ↔ A * star A = 1 := by
  refine' ⟨And.right, fun hA => ⟨_, hA⟩⟩
  simpa only [← Matrix.mul_eq_mul, ← Matrix.mul_eq_one_comm] using hA

namespace UnitaryGroup

instance coeMatrix : Coe (unitaryGroup n α) (Matrix n n α) :=
  ⟨Subtype.val⟩

instance coeFun : CoeFun (unitaryGroup n α) fun _ => n → n → α where coe := fun A => A.val

/-- `to_lin' A` is matrix multiplication of vectors by `A`, as a linear map.

After the group structure on `unitary_group n` is defined,
we show in `to_linear_equiv` that this gives a linear equivalence.
-/
def toLin' (A : unitaryGroup n α) :=
  Matrix.toLin' A

theorem ext_iff (A B : unitaryGroup n α) : A = B ↔ ∀ i j, A i j = B i j :=
  Subtype.ext_iff_val.trans ⟨fun h i j => congr_fun (congr_fun h i) j, Matrix.ext⟩

@[ext]
theorem ext (A B : unitaryGroup n α) : (∀ i j, A i j = B i j) → A = B :=
  (unitaryGroup.ext_iff A B).mpr

@[simp]
theorem star_mul_self (A : unitaryGroup n α) : star A ⬝ A = 1 :=
  A.2.1

section CoeLemmas

variable (A B : unitaryGroup n α)

@[simp]
theorem inv_val : ↑A⁻¹ = (star A : Matrix n n α) :=
  rfl

@[simp]
theorem inv_apply : ⇑A⁻¹ = (star A : Matrix n n α) :=
  rfl

@[simp]
theorem mul_val : ↑(A * B) = A ⬝ B :=
  rfl

@[simp]
theorem mul_apply : ⇑(A * B) = A ⬝ B :=
  rfl

@[simp]
theorem one_val : ↑(1 : unitaryGroup n α) = (1 : Matrix n n α) :=
  rfl

@[simp]
theorem one_apply : ⇑(1 : unitaryGroup n α) = (1 : Matrix n n α) :=
  rfl

@[simp]
theorem to_lin'_mul : toLin' (A * B) = (toLin' A).comp (toLin' B) :=
  Matrix.to_lin'_mul A B

@[simp]
theorem to_lin'_one : toLin' (1 : unitaryGroup n α) = LinearMap.id :=
  Matrix.to_lin'_one

end CoeLemmas

/-- `to_linear_equiv A` is matrix multiplication of vectors by `A`, as a linear equivalence. -/
def toLinearEquiv (A : unitaryGroup n α) : (n → α) ≃ₗ[α] n → α :=
  { Matrix.toLin' A with invFun := toLin' A⁻¹,
    left_inv := fun x =>
      calc
        (toLin' A⁻¹).comp (toLin' A) x = (toLin' (A⁻¹ * A)) x := by
          rw [← to_lin'_mul]
        _ = x := by
          rw [mul_left_invₓ, to_lin'_one, id_apply]
        ,
    right_inv := fun x =>
      calc
        (toLin' A).comp (toLin' A⁻¹) x = toLin' (A * A⁻¹) x := by
          rw [← to_lin'_mul]
        _ = x := by
          rw [mul_right_invₓ, to_lin'_one, id_apply]
         }

/-- `to_GL` is the map from the unitary group to the general linear group -/
def toGL (A : unitaryGroup n α) : GeneralLinearGroup α (n → α) :=
  GeneralLinearGroup.ofLinearEquiv (toLinearEquiv A)

theorem coe_to_GL (A : unitaryGroup n α) : ↑(toGL A) = toLin' A :=
  rfl

@[simp]
theorem to_GL_one : toGL (1 : unitaryGroup n α) = 1 := by
  ext1 v i
  rw [coe_to_GL, to_lin'_one]
  rfl

@[simp]
theorem to_GL_mul (A B : unitaryGroup n α) : toGL (A * B) = toGL A * toGL B := by
  ext1 v i
  rw [coe_to_GL, to_lin'_mul]
  rfl

/-- `unitary_group.embedding_GL` is the embedding from `unitary_group n α`
to `general_linear_group n α`. -/
def embeddingGL : unitaryGroup n α →* GeneralLinearGroup α (n → α) :=
  ⟨fun A => toGL A, by
    simp , by
    simp ⟩

end UnitaryGroup

section OrthogonalGroup

variable (n) (β : Type v) [CommRingₓ β]

attribute [local instance] starRingOfComm

/-- `orthogonal_group n` is the group of `n` by `n` matrices where the transpose is the inverse.
-/
abbrev orthogonalGroup :=
  unitaryGroup n β

theorem mem_orthogonal_group_iff {A : Matrix n n β} : A ∈ Matrix.orthogonalGroup n β ↔ A * star A = 1 := by
  refine' ⟨And.right, fun hA => ⟨_, hA⟩⟩
  simpa only [← Matrix.mul_eq_mul, ← Matrix.mul_eq_one_comm] using hA

end OrthogonalGroup

end Matrix

