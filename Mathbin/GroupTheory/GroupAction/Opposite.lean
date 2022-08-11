/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Group.Opposite
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Scalar actions on and by `Mᵐᵒᵖ`

This file defines the actions on the opposite type `has_smul R Mᵐᵒᵖ`, and actions by the opposite
type, `has_smul Rᵐᵒᵖ M`.

Note that `mul_opposite.has_smul` is provided in an earlier file as it is needed to provide the
`add_monoid.nsmul` and `add_comm_group.gsmul` fields.
-/


variable (α : Type _)

/-! ### Actions _on_ the opposite type

Actions on the opposite type just act on the underlying type.
-/


namespace MulOpposite

@[to_additive]
instance (R : Type _) [Monoidₓ R] [MulAction R α] : MulAction R αᵐᵒᵖ :=
  { MulOpposite.hasSmul α R with one_smul := fun x => unop_injective <| one_smul R (unop x),
    mul_smul := fun r₁ r₂ x => unop_injective <| mul_smul r₁ r₂ (unop x) }

instance (R : Type _) [Monoidₓ R] [AddMonoidₓ α] [DistribMulAction R α] : DistribMulAction R αᵐᵒᵖ :=
  { MulOpposite.mulAction α R with smul_add := fun r x₁ x₂ => unop_injective <| smul_add r (unop x₁) (unop x₂),
    smul_zero := fun r => unop_injective <| smul_zero r }

instance (R : Type _) [Monoidₓ R] [Monoidₓ α] [MulDistribMulAction R α] : MulDistribMulAction R αᵐᵒᵖ :=
  { MulOpposite.mulAction α R with smul_mul := fun r x₁ x₂ => unop_injective <| smul_mul' r (unop x₂) (unop x₁),
    smul_one := fun r => unop_injective <| smul_one r }

instance {M N} [HasSmul M N] [HasSmul M α] [HasSmul N α] [IsScalarTower M N α] : IsScalarTower M N αᵐᵒᵖ :=
  ⟨fun x y z => unop_injective <| smul_assoc _ _ _⟩

@[to_additive]
instance {M N} [HasSmul M α] [HasSmul N α] [SmulCommClass M N α] : SmulCommClass M N αᵐᵒᵖ :=
  ⟨fun x y z => unop_injective <| smul_comm _ _ _⟩

instance (R : Type _) [HasSmul R α] [HasSmul Rᵐᵒᵖ α] [IsCentralScalar R α] : IsCentralScalar R αᵐᵒᵖ :=
  ⟨fun r m => unop_injective <| op_smul_eq_smul _ _⟩

theorem op_smul_eq_op_smul_op {R : Type _} [HasSmul R α] [HasSmul Rᵐᵒᵖ α] [IsCentralScalar R α] (r : R) (a : α) :
    op (r • a) = op r • op a :=
  (op_smul_eq_smul r (op a)).symm

theorem unop_smul_eq_unop_smul_unop {R : Type _} [HasSmul R α] [HasSmul Rᵐᵒᵖ α] [IsCentralScalar R α] (r : Rᵐᵒᵖ)
    (a : αᵐᵒᵖ) : unop (r • a) = unop r • unop a :=
  (unop_smul_eq_smul r (unop a)).symm

end MulOpposite

/-! ### Actions _by_ the opposite type (right actions)

In `has_mul.to_has_smul` in another file, we define the left action `a₁ • a₂ = a₁ * a₂`. For the
multiplicative opposite, we define `mul_opposite.op a₁ • a₂ = a₂ * a₁`, with the multiplication
reversed.
-/


open MulOpposite

/-- Like `has_mul.to_has_smul`, but multiplies on the right.

See also `monoid.to_opposite_mul_action` and `monoid_with_zero.to_opposite_mul_action_with_zero`. -/
@[to_additive]
instance Mul.toHasOppositeSmul [Mul α] : HasSmul αᵐᵒᵖ α where smul := fun c x => x * c.unop

@[to_additive]
theorem op_smul_eq_mul [Mul α] {a a' : α} : op a • a' = a' * a :=
  rfl

@[simp, to_additive]
theorem MulOpposite.smul_eq_mul_unop [Mul α] {a : αᵐᵒᵖ} {a' : α} : a • a' = a' * a.unop :=
  rfl

/-- The right regular action of a group on itself is transitive. -/
@[to_additive "The right regular action of an additive group on itself is transitive."]
instance MulAction.OppositeRegular.is_pretransitive {G : Type _} [Groupₓ G] : MulAction.IsPretransitive Gᵐᵒᵖ G :=
  ⟨fun x y => ⟨op (x⁻¹ * y), mul_inv_cancel_left _ _⟩⟩

@[to_additive]
instance Semigroupₓ.opposite_smul_comm_class [Semigroupₓ α] :
    SmulCommClass αᵐᵒᵖ α α where smul_comm := fun x y z => mul_assoc _ _ _

@[to_additive]
instance Semigroupₓ.opposite_smul_comm_class' [Semigroupₓ α] : SmulCommClass α αᵐᵒᵖ α :=
  SmulCommClass.symm _ _ _

instance CommSemigroupₓ.is_central_scalar [CommSemigroupₓ α] : IsCentralScalar α α :=
  ⟨fun r m => mul_comm _ _⟩

/-- Like `monoid.to_mul_action`, but multiplies on the right. -/
@[to_additive]
instance Monoidₓ.toOppositeMulAction [Monoidₓ α] : MulAction αᵐᵒᵖ α where
  smul := (· • ·)
  one_smul := mul_oneₓ
  mul_smul := fun x y r => (mul_assoc _ _ _).symm

instance IsScalarTower.opposite_mid {M N} [Mul N] [HasSmul M N] [SmulCommClass M N N] : IsScalarTower M Nᵐᵒᵖ N :=
  ⟨fun x y z => mul_smul_comm _ _ _⟩

instance SmulCommClass.opposite_mid {M N} [Mul N] [HasSmul M N] [IsScalarTower M N N] : SmulCommClass M Nᵐᵒᵖ N :=
  ⟨fun x y z => by
    induction y using MulOpposite.rec
    simp [← smul_mul_assoc]⟩

-- The above instance does not create an unwanted diamond, the two paths to
-- `mul_action αᵐᵒᵖ αᵐᵒᵖ` are defeq.
example [Monoidₓ α] : Monoidₓ.toMulAction αᵐᵒᵖ = MulOpposite.mulAction α αᵐᵒᵖ :=
  rfl

/-- `monoid.to_opposite_mul_action` is faithful on cancellative monoids. -/
@[to_additive]
instance LeftCancelMonoid.to_has_faithful_opposite_scalar [LeftCancelMonoid α] : HasFaithfulSmul αᵐᵒᵖ α :=
  ⟨fun x y h => unop_injective <| mul_left_cancelₓ (h 1)⟩

/-- `monoid.to_opposite_mul_action` is faithful on nontrivial cancellative monoids with zero. -/
instance CancelMonoidWithZero.to_has_faithful_opposite_scalar [CancelMonoidWithZero α] [Nontrivial α] :
    HasFaithfulSmul αᵐᵒᵖ α :=
  ⟨fun x y h => unop_injective <| mul_left_cancel₀ one_ne_zero (h 1)⟩

