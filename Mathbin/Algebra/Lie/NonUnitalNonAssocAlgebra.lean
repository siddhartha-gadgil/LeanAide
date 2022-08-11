/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Hom.NonUnitalAlg
import Mathbin.Algebra.Lie.Basic

/-!
# Lie algebras as non-unital, non-associative algebras

The definition of Lie algebras uses the `has_bracket` typeclass for multiplication whereas we have a
separate `has_mul` typeclass used for general algebras.

It is useful to have a special typeclass for Lie algebras because:
 * it enables us to use the traditional notation `⁅x, y⁆` for the Lie multiplication,
 * associative algebras carry a natural Lie algebra structure via the ring commutator and so we need
   them to carry both `has_mul` and `has_bracket` simultaneously,
 * more generally, Poisson algebras (not yet defined) need both typeclasses.

However there are times when it is convenient to be able to regard a Lie algebra as a general
algebra and we provide some basic definitions for doing so here.

## Main definitions

  * `lie_ring.to_non_unital_non_assoc_semiring`
  * `lie_hom.to_non_unital_alg_hom`

## Tags

lie algebra, non-unital, non-associative
-/


universe u v w

variable (R : Type u) (L : Type v) [CommRingₓ R] [LieRing L] [LieAlgebra R L]

/-- A `lie_ring` can be regarded as a `non_unital_non_assoc_semiring` by turning its
`has_bracket` (denoted `⁅, ⁆`) into a `has_mul` (denoted `*`). -/
def LieRing.toNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiringₓ L :=
  { (inferInstance : AddCommMonoidₓ L) with mul := HasBracket.bracket, left_distrib := lie_add,
    right_distrib := add_lie, zero_mul := zero_lie, mul_zero := lie_zero }

attribute [local instance] LieRing.toNonUnitalNonAssocSemiring

namespace LieAlgebra

/-- Regarding the `lie_ring` of a `lie_algebra` as a `non_unital_non_assoc_semiring`, we can
reinterpret the `smul_lie` law as an `is_scalar_tower`. -/
instance is_scalar_tower : IsScalarTower R L L :=
  ⟨smul_lie⟩

/-- Regarding the `lie_ring` of a `lie_algebra` as a `non_unital_non_assoc_semiring`, we can
reinterpret the `lie_smul` law as an `smul_comm_class`. -/
instance smul_comm_class : SmulCommClass R L L :=
  ⟨fun t x y => (lie_smul t x y).symm⟩

end LieAlgebra

namespace LieHom

variable {R L} {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

/-- Regarding the `lie_ring` of a `lie_algebra` as a `non_unital_non_assoc_semiring`, we can
regard a `lie_hom` as a `non_unital_alg_hom`. -/
@[simps]
def toNonUnitalAlgHom (f : L →ₗ⁅R⁆ L₂) : L →ₙₐ[R] L₂ :=
  { f with toFun := f, map_zero' := f.map_zero, map_mul' := f.map_lie }

theorem to_non_unital_alg_hom_injective : Function.Injective (toNonUnitalAlgHom : _ → L →ₙₐ[R] L₂) := fun f g h =>
  ext <| NonUnitalAlgHom.congr_fun h

end LieHom

