/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
import Mathbin.Algebra.Star.SelfAdjoint
import Mathbin.Algebra.Module.Equiv
import Mathbin.LinearAlgebra.Prod

/-!
# The star operation, bundled as a star-linear equiv

We define `star_linear_equiv`, which is the star operation bundled as a star-linear map.
It is defined on a star algebra `A` over the base ring `R`.

This file also provides some lemmas that need `algebra.module.basic` imported to prove.

## TODO

- Define `star_linear_equiv` for noncommutative `R`. We only the commutative case for now since,
  in the noncommutative case, the ring hom needs to reverse the order of multiplication. This
  requires a ring hom of type `R →+* Rᵐᵒᵖ`, which is very undesirable in the commutative case.
  One way out would be to define a new typeclass `is_op R S` and have an instance `is_op R R`
  for commutative `R`.
- Also note that such a definition involving `Rᵐᵒᵖ` or `is_op R S` would require adding
  the appropriate `ring_hom_inv_pair` instances to be able to define the semilinear
  equivalence.
-/


section SmulLemmas

variable {R M : Type _}

@[simp]
theorem star_int_cast_smul [Ringₓ R] [AddCommGroupₓ M] [Module R M] [StarAddMonoid M] (n : ℤ) (x : M) :
    star ((n : R) • x) = (n : R) • star x :=
  map_int_cast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
theorem star_nat_cast_smul [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [StarAddMonoid M] (n : ℕ) (x : M) :
    star ((n : R) • x) = (n : R) • star x :=
  map_nat_cast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
theorem star_inv_int_cast_smul [DivisionRing R] [AddCommGroupₓ M] [Module R M] [StarAddMonoid M] (n : ℤ) (x : M) :
    star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_int_cast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
theorem star_inv_nat_cast_smul [DivisionRing R] [AddCommGroupₓ M] [Module R M] [StarAddMonoid M] (n : ℕ) (x : M) :
    star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_nat_cast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
theorem star_rat_cast_smul [DivisionRing R] [AddCommGroupₓ M] [Module R M] [StarAddMonoid M] (n : ℚ) (x : M) :
    star ((n : R) • x) = (n : R) • star x :=
  map_rat_cast_smul (starAddEquiv : M ≃+ M) _ _ _ x

@[simp]
theorem star_rat_smul {R : Type _} [AddCommGroupₓ R] [StarAddMonoid R] [Module ℚ R] (x : R) (n : ℚ) :
    star (n • x) = n • star x :=
  map_rat_smul (starAddEquiv : R ≃+ R) _ _

end SmulLemmas

/-- If `A` is a module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
@[simps]
def starLinearEquiv (R : Type _) {A : Type _} [CommRingₓ R] [StarRing R] [Semiringₓ A] [StarRing A] [Module R A]
    [StarModule R A] : A ≃ₗ⋆[R] A :=
  { starAddEquiv with toFun := star, map_smul' := star_smul }

variable (R : Type _) (A : Type _) [Semiringₓ R] [StarSemigroup R] [HasTrivialStar R] [AddCommGroupₓ A] [Module R A]
  [StarAddMonoid A] [StarModule R A]

/-- The self-adjoint elements of a star module, as a submodule. -/
def selfAdjoint.submodule : Submodule R A :=
  { selfAdjoint A with smul_mem' := selfAdjoint.smul_mem }

/-- The skew-adjoint elements of a star module, as a submodule. -/
def skewAdjoint.submodule : Submodule R A :=
  { skewAdjoint A with smul_mem' := skewAdjoint.smul_mem }

variable {A} [Invertible (2 : R)]

/-- The self-adjoint part of an element of a star module, as a linear map. -/
@[simps]
def selfAdjointPart : A →ₗ[R] selfAdjoint A where
  toFun := fun x =>
    ⟨(⅟ 2 : R) • (x + star x), by
      simp only [← selfAdjoint.mem_iff, ← star_smul, ← add_commₓ, ← StarAddMonoid.star_add, ← star_inv', ← star_bit0, ←
        star_one, ← star_star, ← star_inv_of (2 : R), ← star_trivial]⟩
  map_add' := fun x y => by
    ext
    simp [← add_add_add_commₓ]
  map_smul' := fun r x => by
    ext
    simp [mul_smul, ← show ⅟ 2 * r = r * ⅟ 2 from Commute.inv_of_left (Commute.one_left r).bit0_left]

/-- The skew-adjoint part of an element of a star module, as a linear map. -/
@[simps]
def skewAdjointPart : A →ₗ[R] skewAdjoint A where
  toFun := fun x =>
    ⟨(⅟ 2 : R) • (x - star x), by
      simp only [← skewAdjoint.mem_iff, ← star_smul, ← star_sub, ← star_star, ← star_trivial, smul_neg, ← neg_sub]⟩
  map_add' := fun x y => by
    ext
    simp only [← sub_add, smul_add, ← sub_sub_eq_add_sub, ← star_add, ← AddSubgroup.coe_mk, ← AddSubgroup.coe_add]
  map_smul' := fun r x => by
    ext
    simp [mul_smul, smul_sub, ← show r * ⅟ 2 = ⅟ 2 * r from Commute.inv_of_right (Commute.one_right r).bit0_right]

theorem StarModule.self_adjoint_part_add_skew_adjoint_part (x : A) :
    (selfAdjointPart R x : A) + skewAdjointPart R x = x := by
  simp only [← smul_sub, ← self_adjoint_part_apply_coe, ← smul_add, ← skew_adjoint_part_apply_coe, ← add_add_sub_cancel,
    ← inv_of_two_smul_add_inv_of_two_smul]

variable (A)

/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a linear equivalence. -/
@[simps]
def StarModule.decomposeProdAdjoint : A ≃ₗ[R] selfAdjoint A × skewAdjoint A :=
  LinearEquiv.ofLinear ((selfAdjointPart R).Prod (skewAdjointPart R))
    ((selfAdjoint.submodule R A).Subtype.coprod (skewAdjoint.submodule R A).Subtype)
    (by
      ext <;> simp )
    (LinearMap.ext <| StarModule.self_adjoint_part_add_skew_adjoint_part R)

