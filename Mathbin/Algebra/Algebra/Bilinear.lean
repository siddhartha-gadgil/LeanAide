/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Hom.Iterate
import Mathbin.LinearAlgebra.TensorProduct

/-!
# Facts about algebras involving bilinear maps and tensor products

We move a few basic statements about algebras out of `algebra.algebra.basic`,
in order to avoid importing `linear_algebra.bilinear_map` and
`linear_algebra.tensor_product` unnecessarily.
-/


universe u v w

namespace Algebra

open TensorProduct

open Module

section

variable (R A : Type _) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

/-- The multiplication in an algebra is a bilinear map.

A weaker version of this for semirings exists as `add_monoid_hom.mul`. -/
def lmul : A →ₐ[R] End R A :=
  { show A →ₗ[R] A →ₗ[R] A from
      LinearMap.mk₂ R (· * ·) (fun x y z => add_mulₓ x y z)
        (fun c x y => by
          rw [smul_def, smul_def, mul_assoc _ x y])
        (fun x y z => mul_addₓ x y z) fun c x y => by
        rw [smul_def, smul_def, left_comm] with
    map_one' := by
      ext a
      exact one_mulₓ a,
    map_mul' := by
      intro a b
      ext c
      exact mul_assoc a b c,
    map_zero' := by
      ext a
      exact zero_mul a,
    commutes' := by
      intro r
      ext a
      dsimp'
      rw [smul_def] }

variable {R A}

@[simp]
theorem lmul_apply (p q : A) : lmul R A p q = p * q :=
  rfl

variable (R)

/-- The multiplication on the left in an algebra is a linear map. -/
def lmulLeft (r : A) : A →ₗ[R] A :=
  lmul R A r

@[simp]
theorem lmul_left_to_add_monoid_hom (r : A) : (lmulLeft R r : A →+ A) = AddMonoidHom.mulLeft r :=
  FunLike.coe_injective rfl

/-- The multiplication on the right in an algebra is a linear map. -/
def lmulRight (r : A) : A →ₗ[R] A :=
  (lmul R A).toLinearMap.flip r

@[simp]
theorem lmul_right_to_add_monoid_hom (r : A) : (lmulRight R r : A →+ A) = AddMonoidHom.mulRight r :=
  FunLike.coe_injective rfl

/-- Simultaneous multiplication on the left and right is a linear map. -/
def lmulLeftRight (vw : A × A) : A →ₗ[R] A :=
  (lmulRight R vw.2).comp (lmulLeft R vw.1)

theorem commute_lmul_left_right (a b : A) : Commute (lmulLeft R a) (lmulRight R b) := by
  ext c
  exact (mul_assoc a c b).symm

/-- The multiplication map on an algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
def lmul' : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (lmul R A).toLinearMap

variable {R A}

@[simp]
theorem lmul'_apply {x y : A} : lmul' R (x ⊗ₜ y) = x * y := by
  simp only [← Algebra.lmul', ← TensorProduct.lift.tmul, ← AlgHom.to_linear_map_apply, ← lmul_apply]

@[simp]
theorem lmul_left_apply (p q : A) : lmulLeft R p q = p * q :=
  rfl

@[simp]
theorem lmul_right_apply (p q : A) : lmulRight R p q = q * p :=
  rfl

@[simp]
theorem lmul_left_right_apply (vw : A × A) (p : A) : lmulLeftRight R vw p = vw.1 * p * vw.2 :=
  rfl

@[simp]
theorem lmul_left_one : lmulLeft R (1 : A) = LinearMap.id := by
  ext
  simp only [← LinearMap.id_coe, ← one_mulₓ, ← id.def, ← lmul_left_apply]

@[simp]
theorem lmul_left_mul (a b : A) : lmulLeft R (a * b) = (lmulLeft R a).comp (lmulLeft R b) := by
  ext
  simp only [← lmul_left_apply, ← LinearMap.comp_apply, ← mul_assoc]

@[simp]
theorem lmul_right_one : lmulRight R (1 : A) = LinearMap.id := by
  ext
  simp only [← LinearMap.id_coe, ← mul_oneₓ, ← id.def, ← lmul_right_apply]

@[simp]
theorem lmul_right_mul (a b : A) : lmulRight R (a * b) = (lmulRight R b).comp (lmulRight R a) := by
  ext
  simp only [← lmul_right_apply, ← LinearMap.comp_apply, ← mul_assoc]

@[simp]
theorem lmul_left_zero_eq_zero : lmulLeft R (0 : A) = 0 :=
  (lmul R A).map_zero

@[simp]
theorem lmul_right_zero_eq_zero : lmulRight R (0 : A) = 0 :=
  (lmul R A).toLinearMap.flip.map_zero

@[simp]
theorem lmul_left_eq_zero_iff (a : A) : lmulLeft R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · rw [← mul_oneₓ a, ← lmul_left_apply a 1, h, LinearMap.zero_apply]
    
  · rw [h]
    exact lmul_left_zero_eq_zero
    

@[simp]
theorem lmul_right_eq_zero_iff (a : A) : lmulRight R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · rw [← one_mulₓ a, ← lmul_right_apply a 1, h, LinearMap.zero_apply]
    
  · rw [h]
    exact lmul_right_zero_eq_zero
    

@[simp]
theorem pow_lmul_left (a : A) (n : ℕ) : lmulLeft R a ^ n = lmulLeft R (a ^ n) :=
  ((lmul R A).map_pow a n).symm

@[simp]
theorem pow_lmul_right (a : A) (n : ℕ) : lmulRight R a ^ n = lmulRight R (a ^ n) :=
  LinearMap.coe_injective <| ((lmulRight R a).coe_pow n).symm ▸ mul_right_iterate a n

end

section

variable {R A : Type _} [CommSemiringₓ R] [Ringₓ A] [Algebra R A]

theorem lmul_left_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) : Function.Injective (lmulLeft R x) := by
  let this : IsDomain A := { ‹Ringₓ A›, ‹NoZeroDivisors A› with exists_pair_ne := ⟨x, 0, hx⟩ }
  exact mul_right_injective₀ hx

theorem lmul_right_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) : Function.Injective (lmulRight R x) := by
  let this : IsDomain A := { ‹Ringₓ A›, ‹NoZeroDivisors A› with exists_pair_ne := ⟨x, 0, hx⟩ }
  exact mul_left_injective₀ hx

theorem lmul_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) : Function.Injective (lmul R A x) := by
  let this : IsDomain A := { ‹Ringₓ A›, ‹NoZeroDivisors A› with exists_pair_ne := ⟨x, 0, hx⟩ }
  exact mul_right_injective₀ hx

end

end Algebra

