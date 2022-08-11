/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Int.Cast.Defs
import Mathbin.Algebra.Hom.Equiv

/-!
# `ulift` instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We use `tactic.pi_instance_derive_field`, even though it wasn't intended for this purpose,
which seems to work fine.

We also provide `ulift.mul_equiv : ulift R ≃* R` (and its additive analogue).
-/


universe u v

variable {α : Type u} {x y : ULift.{v} α}

namespace ULift

@[to_additive]
instance hasOne [One α] : One (ULift α) :=
  ⟨⟨1⟩⟩

@[simp, to_additive]
theorem one_down [One α] : (1 : ULift α).down = 1 :=
  rfl

@[to_additive]
instance hasMul [Mul α] : Mul (ULift α) :=
  ⟨fun f g => ⟨f.down * g.down⟩⟩

@[simp, to_additive]
theorem mul_down [Mul α] : (x * y).down = x.down * y.down :=
  rfl

@[to_additive]
instance hasDiv [Div α] : Div (ULift α) :=
  ⟨fun f g => ⟨f.down / g.down⟩⟩

@[simp, to_additive]
theorem div_down [Div α] : (x / y).down = x.down / y.down :=
  rfl

@[to_additive]
instance hasInv [Inv α] : Inv (ULift α) :=
  ⟨fun f => ⟨f.down⁻¹⟩⟩

@[simp, to_additive]
theorem inv_down [Inv α] : x⁻¹.down = x.down⁻¹ :=
  rfl

/-- The multiplicative equivalence between `ulift α` and `α`.
-/
@[to_additive "The additive equivalence between `ulift α` and `α`."]
def _root_.mul_equiv.ulift [Mul α] : ULift α ≃* α :=
  { Equivₓ.ulift with map_mul' := fun x y => rfl }

@[to_additive]
instance semigroup [Semigroupₓ α] : Semigroupₓ (ULift α) :=
  (MulEquiv.ulift.Injective.Semigroup _) fun x y => rfl

@[to_additive]
instance commSemigroup [CommSemigroupₓ α] : CommSemigroupₓ (ULift α) :=
  (Equivₓ.ulift.Injective.CommSemigroup _) fun x y => rfl

@[to_additive]
instance mulOneClass [MulOneClassₓ α] : MulOneClassₓ (ULift α) :=
  (Equivₓ.ulift.Injective.MulOneClass _ rfl) fun x y => rfl

instance mulZeroOneClass [MulZeroOneClassₓ α] : MulZeroOneClassₓ (ULift α) :=
  (Equivₓ.ulift.Injective.MulZeroOneClass _ rfl rfl) fun x y => rfl

@[to_additive]
instance hasSmul {β : Type _} [HasSmul α β] : HasSmul α (ULift β) :=
  ⟨fun n x => up (n • x.down)⟩

@[to_additive HasSmul, to_additive_reorder 1]
instance hasPow {β : Type _} [Pow α β] : Pow (ULift α) β :=
  ⟨fun x n => up (x.down ^ n)⟩

@[to_additive]
instance monoid [Monoidₓ α] : Monoidₓ (ULift α) :=
  Equivₓ.ulift.Injective.Monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance addMonoidWithOne [AddMonoidWithOneₓ α] : AddMonoidWithOneₓ (ULift α) :=
  { ULift.hasOne, ULift.addMonoid with natCast := fun n => ⟨n⟩, nat_cast_zero := congr_arg ULift.up Nat.cast_zeroₓ,
    nat_cast_succ := fun n => congr_arg ULift.up (Nat.cast_succₓ _) }

@[to_additive]
instance commMonoid [CommMonoidₓ α] : CommMonoidₓ (ULift α) :=
  Equivₓ.ulift.Injective.CommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance monoidWithZero [MonoidWithZeroₓ α] : MonoidWithZeroₓ (ULift α) :=
  Equivₓ.ulift.Injective.MonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

instance commMonoidWithZero [CommMonoidWithZero α] : CommMonoidWithZero (ULift α) :=
  Equivₓ.ulift.Injective.CommMonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance divInvMonoid [DivInvMonoidₓ α] : DivInvMonoidₓ (ULift α) :=
  Equivₓ.ulift.Injective.DivInvMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ =>
    rfl

@[to_additive]
instance group [Groupₓ α] : Groupₓ (ULift α) :=
  Equivₓ.ulift.Injective.Group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance addGroupWithOne [AddGroupWithOneₓ α] : AddGroupWithOneₓ (ULift α) :=
  { ULift.addMonoidWithOne, ULift.addGroup with intCast := fun n => ⟨n⟩,
    int_cast_of_nat := fun n => congr_arg ULift.up (Int.cast_of_nat _),
    int_cast_neg_succ_of_nat := fun n => congr_arg ULift.up (Int.cast_neg_succ_of_nat _) }

@[to_additive]
instance commGroup [CommGroupₓ α] : CommGroupₓ (ULift α) :=
  Equivₓ.ulift.Injective.CommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ =>
    rfl

instance groupWithZero [GroupWithZeroₓ α] : GroupWithZeroₓ (ULift α) :=
  Equivₓ.ulift.Injective.GroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

instance commGroupWithZero [CommGroupWithZero α] : CommGroupWithZero (ULift α) :=
  Equivₓ.ulift.Injective.CommGroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

@[to_additive AddLeftCancelSemigroup]
instance leftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (ULift α) :=
  Equivₓ.ulift.Injective.LeftCancelSemigroup _ fun _ _ => rfl

@[to_additive AddRightCancelSemigroup]
instance rightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (ULift α) :=
  Equivₓ.ulift.Injective.RightCancelSemigroup _ fun _ _ => rfl

@[to_additive AddLeftCancelMonoid]
instance leftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (ULift α) :=
  Equivₓ.ulift.Injective.LeftCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive AddRightCancelMonoid]
instance rightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (ULift α) :=
  Equivₓ.ulift.Injective.RightCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive AddCancelMonoid]
instance cancelMonoid [CancelMonoid α] : CancelMonoid (ULift α) :=
  Equivₓ.ulift.Injective.CancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive AddCancelMonoid]
instance cancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (ULift α) :=
  Equivₓ.ulift.Injective.CancelCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance nontrivial [Nontrivial α] : Nontrivial (ULift α) :=
  Equivₓ.ulift.symm.Injective.Nontrivial

-- TODO we don't do `ordered_cancel_comm_monoid` or `ordered_comm_group`
-- We'd need to add instances for `ulift` in `order.basic`.
end ULift

