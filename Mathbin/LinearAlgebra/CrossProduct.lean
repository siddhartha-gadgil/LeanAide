/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller, Eric Wieser
-/
import Mathbin.Data.Matrix.Notation
import Mathbin.LinearAlgebra.BilinearMap
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.Algebra.Lie.Basic

/-!
# Cross products

This module defines the cross product of vectors in $R^3$ for $R$ a commutative ring,
as a bilinear map.

## Main definitions

* `cross_product` is the cross product of pairs of vectors in $R^3$.

## Main results

* `triple_product_eq_det`
* `cross_dot_cross`
* `jacobi_cross`

## Notation

The locale `matrix` gives the following notation:

* `×₃` for the cross product

## Tags

crossproduct
-/


open Matrix

open Matrix

variable {R : Type _} [CommRingₓ R]

/-- The cross product of two vectors in $R^3$ for $R$ a commutative ring. -/
def crossProduct : (Finₓ 3 → R) →ₗ[R] (Finₓ 3 → R) →ₗ[R] Finₓ 3 → R := by
  apply LinearMap.mk₂ R fun a b : Finₓ 3 → R => ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
  · intros
    simp [← vec3_add (_ : R), ← add_commₓ, ← add_assocₓ, ← add_left_commₓ, ← add_mulₓ, ← sub_eq_add_neg]
    
  · intros
    simp [← smul_vec3 (_ : R) (_ : R), ← mul_comm, ← mul_assoc, ← mul_left_commₓ, ← mul_addₓ, ← sub_eq_add_neg]
    
  · intros
    simp [← vec3_add (_ : R), ← add_commₓ, ← add_assocₓ, ← add_left_commₓ, ← mul_addₓ, ← sub_eq_add_neg]
    
  · intros
    simp [← smul_vec3 (_ : R) (_ : R), ← mul_comm, ← mul_assoc, ← mul_left_commₓ, ← mul_addₓ, ← sub_eq_add_neg]
    

-- mathport name: «expr ×₃ »
localized [Matrix] infixl:74 " ×₃ " => crossProduct

theorem cross_apply (a b : Finₓ 3 → R) :
    a ×₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] :=
  rfl

section ProductsProperties

@[simp]
theorem cross_anticomm (v w : Finₓ 3 → R) : -(v ×₃ w) = w ×₃ v := by
  simp [← cross_apply, ← mul_comm]

alias cross_anticomm ← neg_cross

@[simp]
theorem cross_anticomm' (v w : Finₓ 3 → R) : v ×₃ w + w ×₃ v = 0 := by
  rw [add_eq_zero_iff_eq_neg, cross_anticomm]

@[simp]
theorem cross_self (v : Finₓ 3 → R) : v ×₃ v = 0 := by
  simp [← cross_apply, ← mul_comm]

/-- The cross product of two vectors is perpendicular to the first vector. -/
@[simp]
theorem dot_self_cross (v w : Finₓ 3 → R) : v ⬝ᵥ v ×₃ w = 0 := by
  simp [← cross_apply, ← vec3_dot_product, ← mul_sub, ← mul_assoc, ← mul_left_commₓ]

/-- The cross product of two vectors is perpendicular to the second vector. -/
@[simp]
theorem dot_cross_self (v w : Finₓ 3 → R) : w ⬝ᵥ v ×₃ w = 0 := by
  rw [← cross_anticomm, Matrix.dot_product_neg, dot_self_cross, neg_zero]

/-- Cyclic permutations preserve the triple product. See also `triple_product_eq_det`. -/
theorem triple_product_permutation (u v w : Finₓ 3 → R) : u ⬝ᵥ v ×₃ w = v ⬝ᵥ w ×₃ u := by
  simp only [← cross_apply, ← vec3_dot_product, ← Matrix.head_cons, ← Matrix.cons_vec_bit0_eq_alt0, ←
    Matrix.empty_append, ← Matrix.cons_val_one, ← Matrix.cons_vec_alt0, ← Matrix.cons_append, ← Matrix.cons_val_zero]
  ring

/-- The triple product of `u`, `v`, and `w` is equal to the determinant of the matrix
    with those vectors as its rows. -/
theorem triple_product_eq_det (u v w : Finₓ 3 → R) : u ⬝ᵥ v ×₃ w = Matrix.det ![u, v, w] := by
  simp only [← vec3_dot_product, ← cross_apply, ← Matrix.det_fin_three, ← Matrix.head_cons, ←
    Matrix.cons_vec_bit0_eq_alt0, ← Matrix.empty_vec_alt0, ← Matrix.cons_vec_alt0, ← Matrix.vec_head_vec_alt0, ←
    Finₓ.fin_append_apply_zero, ← Matrix.empty_append, ← Matrix.cons_append, ← Matrix.cons_val', ← Matrix.cons_val_one,
    ← Matrix.cons_val_zero]
  ring

/-- The scalar quadruple product identity, related to the Binet-Cauchy identity. -/
theorem cross_dot_cross (u v w x : Finₓ 3 → R) : u ×₃ v ⬝ᵥ w ×₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w := by
  simp only [← vec3_dot_product, ← cross_apply, ← cons_append, ← cons_vec_bit0_eq_alt0, ← cons_val_one, ← cons_vec_alt0,
    ← LinearMap.mk₂_apply, ← cons_val_zero, ← head_cons, ← empty_append]
  ring_nf

end ProductsProperties

section LeibnizProperties

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- The cross product satisfies the Leibniz lie property. -/
theorem leibniz_cross (u v w : Finₓ 3 → R) : u ×₃ (v ×₃ w) = u ×₃ v ×₃ w + v ×₃ (u ×₃ w) := by
  dsimp' only [← cross_apply]
  ext i
  fin_cases i <;> norm_num <;> ring

/-- The three-dimensional vectors together with the operations + and ×₃ form a Lie ring.
    Note we do not make this an instance as a conflicting one already exists
    via `lie_ring.of_associative_ring`. -/
def Cross.lieRing : LieRing (Finₓ 3 → R) :=
  { Pi.addCommGroup with bracket := fun u v => u ×₃ v, add_lie := LinearMap.map_add₂ _,
    lie_add := fun u => LinearMap.map_add _, lie_self := cross_self, leibniz_lie := leibniz_cross }

attribute [local instance] Cross.lieRing

theorem cross_cross (u v w : Finₓ 3 → R) : u ×₃ v ×₃ w = u ×₃ (v ×₃ w) - v ×₃ (u ×₃ w) :=
  lie_lie u v w

/-- Jacobi identity: For a cross product of three vectors,
    their sum over the three even permutations is equal to the zero vector. -/
theorem jacobi_cross (u v w : Finₓ 3 → R) : u ×₃ (v ×₃ w) + v ×₃ (w ×₃ u) + w ×₃ (u ×₃ v) = 0 :=
  lie_jacobi u v w

end LeibnizProperties

