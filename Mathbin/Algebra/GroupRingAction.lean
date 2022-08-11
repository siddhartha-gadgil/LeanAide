/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Ring.Equiv
import Mathbin.GroupTheory.GroupAction.Group
import Mathbin.RingTheory.Subring.Basic

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `mul_semiring_action M R`,
and the corresponding typeclass of invariant subrings.

Note that `algebra` does not satisfy the axioms of `mul_semiring_action`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `mul_semiring_action`.

## Tags

group action, invariant subring

-/


universe u v

open BigOperators

/-- Typeclass for multiplicative actions by monoids on semirings.

This combines `distrib_mul_action` with `mul_distrib_mul_action`. -/
class MulSemiringAction (M : Type u) (R : Type v) [Monoidₓ M] [Semiringₓ R] extends DistribMulAction M R where
  smul_one : ∀ g : M, (g • 1 : R) = 1
  smul_mul : ∀ (g : M) (x y : R), g • (x * y) = g • x * g • y

section Semiringₓ

variable (M G : Type u) [Monoidₓ M] [Groupₓ G]

variable (A R S F : Type v) [AddMonoidₓ A] [Semiringₓ R] [CommSemiringₓ S] [DivisionRing F]

-- note we could not use `extends` since these typeclasses are made with `old_structure_cmd`
instance (priority := 100) MulSemiringAction.toMulDistribMulAction [h : MulSemiringAction M R] :
    MulDistribMulAction M R :=
  { h with }

/-- Each element of the monoid defines a semiring homomorphism. -/
@[simps]
def MulSemiringAction.toRingHom [MulSemiringAction M R] (x : M) : R →+* R :=
  { MulDistribMulAction.toMonoidHom R x, DistribMulAction.toAddMonoidHom R x with }

theorem to_ring_hom_injective [MulSemiringAction M R] [HasFaithfulSmul M R] :
    Function.Injective (MulSemiringAction.toRingHom M R) := fun m₁ m₂ h =>
  eq_of_smul_eq_smul fun r => RingHom.ext_iff.1 h r

/-- Each element of the group defines a semiring isomorphism. -/
@[simps]
def MulSemiringAction.toRingEquiv [MulSemiringAction G R] (x : G) : R ≃+* R :=
  { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }

section

variable {M G R}

/-- A stronger version of `submonoid.distrib_mul_action`. -/
instance Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) : MulSemiringAction H R :=
  { H.MulDistribMulAction, H.DistribMulAction with smul := (· • ·) }

/-- A stronger version of `subgroup.distrib_mul_action`. -/
instance Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) : MulSemiringAction H R :=
  H.toSubmonoid.MulSemiringAction

/-- A stronger version of `subsemiring.distrib_mul_action`. -/
instance Subsemiring.mulSemiringAction {R'} [Semiringₓ R'] [MulSemiringAction R' R] (H : Subsemiring R') :
    MulSemiringAction H R :=
  H.toSubmonoid.MulSemiringAction

/-- A stronger version of `subring.distrib_mul_action`. -/
instance Subring.mulSemiringAction {R'} [Ringₓ R'] [MulSemiringAction R' R] (H : Subring R') : MulSemiringAction H R :=
  H.toSubsemiring.MulSemiringAction

end

section SimpLemmas

variable {M G A R F}

attribute [simp] smul_one smul_mul' smul_zero smul_add

/-- Note that `smul_inv'` refers to the group case, and `smul_inv` has an additional inverse
on `x`. -/
@[simp]
theorem smul_inv'' [MulSemiringAction M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
  (MulSemiringAction.toRingHom M F x).map_inv _

end SimpLemmas

end Semiringₓ

section Ringₓ

variable (M : Type u) [Monoidₓ M] {R : Type v} [Ringₓ R] [MulSemiringAction M R]

variable (S : Subring R)

open MulAction

/-- A typeclass for subrings invariant under a `mul_semiring_action`. -/
class IsInvariantSubring : Prop where
  smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S

instance IsInvariantSubring.toMulSemiringAction [IsInvariantSubring M S] : MulSemiringAction M S where
  smul := fun m x => ⟨m • x, IsInvariantSubring.smul_mem m x.2⟩
  one_smul := fun s => Subtype.eq <| one_smul M s
  mul_smul := fun m₁ m₂ s => Subtype.eq <| mul_smul m₁ m₂ s
  smul_add := fun m s₁ s₂ => Subtype.eq <| smul_add m s₁ s₂
  smul_zero := fun m => Subtype.eq <| smul_zero m
  smul_one := fun m => Subtype.eq <| smul_one m
  smul_mul := fun m s₁ s₂ => Subtype.eq <| smul_mul' m s₁ s₂

end Ringₓ

