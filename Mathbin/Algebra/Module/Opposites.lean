/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Module.Equiv
import Mathbin.GroupTheory.GroupAction.Opposite

/-!
# Module operations on `Mᵐᵒᵖ`

This file contains definitions that build on top of the group action definitions in
`group_theory.group_action.opposite`.
-/


namespace MulOpposite

universe u v

variable (R : Type u) {M : Type v} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

/-- `mul_opposite.distrib_mul_action` extends to a `module` -/
instance : Module R (MulOpposite M) :=
  { MulOpposite.distribMulAction M R with add_smul := fun r₁ r₂ x => unop_injective <| add_smul r₁ r₂ (unop x),
    zero_smul := fun x => unop_injective <| zero_smul _ (unop x) }

/-- The function `op` is a linear equivalence. -/
def opLinearEquiv : M ≃ₗ[R] Mᵐᵒᵖ :=
  { opAddEquiv with map_smul' := MulOpposite.op_smul }

@[simp]
theorem coe_op_linear_equiv : (opLinearEquiv R : M → Mᵐᵒᵖ) = op :=
  rfl

@[simp]
theorem coe_op_linear_equiv_symm : ((opLinearEquiv R).symm : Mᵐᵒᵖ → M) = unop :=
  rfl

@[simp]
theorem coe_op_linear_equiv_to_linear_map : ((opLinearEquiv R).toLinearMap : M → Mᵐᵒᵖ) = op :=
  rfl

@[simp]
theorem coe_op_linear_equiv_symm_to_linear_map : ((opLinearEquiv R).symm.toLinearMap : Mᵐᵒᵖ → M) = unop :=
  rfl

@[simp]
theorem op_linear_equiv_to_add_equiv : (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = op_add_equiv :=
  rfl

@[simp]
theorem op_linear_equiv_symm_to_add_equiv : (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm.toAddEquiv = opAddEquiv.symm :=
  rfl

end MulOpposite

