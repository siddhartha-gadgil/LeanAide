/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Module.Pi

/-!
# Bundled hom instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on bundled `_hom` types.

These are analogous to the instances in `algebra.module.pi`, but for bundled instead of unbundled
functions.
-/


variable {R S A B : Type _}

namespace AddMonoidHom

section

variable [Monoidₓ R] [Monoidₓ S] [AddMonoidₓ A] [AddCommMonoidₓ B]

variable [DistribMulAction R B] [DistribMulAction S B]

instance : DistribMulAction R (A →+ B) where
  smul := fun r f =>
    { toFun := r • f,
      map_zero' := by
        simp ,
      map_add' := fun x y => by
        simp [← smul_add] }
  one_smul := fun f => by
    simp
  mul_smul := fun r s f => by
    simp [← mul_smul]
  smul_add := fun r f g =>
    ext fun x => by
      simp [← smul_add]
  smul_zero := fun r =>
    ext fun x => by
      simp [← smul_zero]

@[simp]
theorem coe_smul (r : R) (f : A →+ B) : ⇑(r • f) = r • f :=
  rfl

theorem smul_apply (r : R) (f : A →+ B) (x : A) : (r • f) x = r • f x :=
  rfl

instance [SmulCommClass R S B] : SmulCommClass R S (A →+ B) :=
  ⟨fun a b f => ext fun x => smul_comm _ _ _⟩

instance [HasSmul R S] [IsScalarTower R S B] : IsScalarTower R S (A →+ B) :=
  ⟨fun a b f => ext fun x => smul_assoc _ _ _⟩

instance [DistribMulAction Rᵐᵒᵖ B] [IsCentralScalar R B] : IsCentralScalar R (A →+ B) :=
  ⟨fun a b => ext fun x => op_smul_eq_smul _ _⟩

end

instance [Semiringₓ R] [AddMonoidₓ A] [AddCommMonoidₓ B] [Module R B] : Module R (A →+ B) :=
  { AddMonoidHom.distribMulAction with
    add_smul := fun r s x =>
      ext fun y => by
        simp [← add_smul],
    zero_smul := fun x =>
      ext fun y => by
        simp [← zero_smul] }

end AddMonoidHom

