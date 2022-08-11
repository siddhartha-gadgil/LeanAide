/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Group.Ulift
import Mathbin.Algebra.Ring.Equiv

/-!
# `ulift` instances for ring

This file defines instances for ring, semiring and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.ring_equiv : ulift R ≃+* R`.
-/


universe u v

variable {α : Type u} {x y : ULift.{v} α}

namespace ULift

instance mulZeroClass [MulZeroClassₓ α] : MulZeroClassₓ (ULift α) := by
  refine_struct { zero := (0 : ULift α), mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance distrib [Distribₓ α] : Distribₓ (ULift α) := by
  refine_struct { add := (· + ·), mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiringₓ α] : NonUnitalNonAssocSemiringₓ (ULift α) := by
  refine_struct { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonAssocSemiring [NonAssocSemiringₓ α] : NonAssocSemiringₓ (ULift α) := by
  refine_struct
      { ULift.addMonoidWithOne with zero := (0 : ULift α), one := 1, add := (· + ·), mul := (· * ·),
        nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalSemiring [NonUnitalSemiringₓ α] : NonUnitalSemiringₓ (ULift α) := by
  refine_struct { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance semiring [Semiringₓ α] : Semiringₓ (ULift α) := by
  refine_struct
      { ULift.addMonoidWithOne with zero := (0 : ULift α), one := 1, add := (· + ·), mul := (· * ·),
        nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

/-- The ring equivalence between `ulift α` and `α`.
-/
def ringEquiv [NonUnitalNonAssocSemiringₓ α] : ULift α ≃+* α where
  toFun := ULift.down
  invFun := ULift.up
  map_mul' := fun x y => rfl
  map_add' := fun x y => rfl
  left_inv := by
    tidy
  right_inv := by
    tidy

instance nonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring (ULift α) := by
  refine_struct { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance commSemiring [CommSemiringₓ α] : CommSemiringₓ (ULift α) := by
  refine_struct
      { ULift.semiring with zero := (0 : ULift α), one := 1, add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul,
        npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (ULift α) := by
  refine_struct
      { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalRing [NonUnitalRing α] : NonUnitalRing (ULift α) := by
  refine_struct
      { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonAssocRing [NonAssocRing α] : NonAssocRing (ULift α) := by
  refine_struct
      { ULift.addGroupWithOne with zero := (0 : ULift α), one := 1, add := (· + ·), mul := (· * ·), sub := Sub.sub,
        neg := Neg.neg, nsmul := AddMonoidₓ.nsmul, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance ring [Ringₓ α] : Ringₓ (ULift α) := by
  refine_struct
      { ULift.semiring, ULift.addGroupWithOne with zero := (0 : ULift α), one := 1, add := (· + ·), mul := (· * ·),
        sub := Sub.sub, neg := Neg.neg, nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow,
        zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing (ULift α) := by
  refine_struct
      { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance commRing [CommRingₓ α] : CommRingₓ (ULift α) := by
  refine_struct { ULift.ring with } <;>
    run_tac
      tactic.pi_instance_derive_field

instance field [Field α] : Field (ULift α) := by
  refine_struct
      { @ULift.nontrivial α _, ULift.commRing with zero := (0 : ULift α), inv := Inv.inv, div := Div.div,
        zpow := fun n a => ULift.up (a.down ^ n) } <;>
    run_tac
      tactic.pi_instance_derive_field
  -- `mul_inv_cancel` requires special attention: it leaves the goal `∀ {a}, a ≠ 0 → a * a⁻¹ = 1`.
  cases a
  tauto

end ULift

