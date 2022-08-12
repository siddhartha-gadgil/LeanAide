/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Ring.Ulift
import Mathbin.Algebra.Module.Equiv

/-!
# `ulift` instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.module_equiv : ulift M ≃ₗ[R] M`.

-/


namespace ULift

universe u v w

variable {R : Type u}

variable {M : Type v}

variable {N : Type w}

instance hasSmulLeft [HasSmul R M] : HasSmul (ULift R) M :=
  ⟨fun s x => s.down • x⟩

@[simp]
theorem smul_down [HasSmul R M] (s : ULift R) (x : M) : s • x = s.down • x :=
  rfl

@[simp]
theorem smul_down' [HasSmul R M] (s : R) (x : ULift M) : (s • x).down = s • x.down :=
  rfl

instance is_scalar_tower [HasSmul R M] [HasSmul M N] [HasSmul R N] [IsScalarTower R M N] :
    IsScalarTower (ULift R) M N :=
  ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩

instance is_scalar_tower' [HasSmul R M] [HasSmul M N] [HasSmul R N] [IsScalarTower R M N] :
    IsScalarTower R (ULift M) N :=
  ⟨fun x y z => show (x • y.down) • z = x • y.down • z from smul_assoc _ _ _⟩

instance is_scalar_tower'' [HasSmul R M] [HasSmul M N] [HasSmul R N] [IsScalarTower R M N] :
    IsScalarTower R M (ULift N) :=
  ⟨fun x y z =>
    show up ((x • y) • z.down) = ⟨x • y • z.down⟩ by
      rw [smul_assoc]⟩

instance [HasSmul R M] [HasSmul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (ULift M) :=
  ⟨fun r m => congr_arg up <| op_smul_eq_smul r m.down⟩

instance mulAction [Monoidₓ R] [MulAction R M] : MulAction (ULift R) M where
  smul := (· • ·)
  mul_smul := fun _ _ => mul_smul _ _
  one_smul := one_smul _

instance mulAction' [Monoidₓ R] [MulAction R M] : MulAction R (ULift M) where
  smul := (· • ·)
  mul_smul := fun r s f => by
    cases f
    ext
    simp [← mul_smul]
  one_smul := fun f => by
    ext
    simp [← one_smul]

instance distribMulAction [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : DistribMulAction (ULift R) M where
  smul_zero := fun _ => smul_zero _
  smul_add := fun _ => smul_add _

instance distribMulAction' [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : DistribMulAction R (ULift M) :=
  { ULift.mulAction' with
    smul_zero := fun c => by
      ext
      simp [← smul_zero],
    smul_add := fun c f g => by
      ext
      simp [← smul_add] }

instance mulDistribMulAction [Monoidₓ R] [Monoidₓ M] [MulDistribMulAction R M] : MulDistribMulAction (ULift R) M where
  smul_one := fun _ => smul_one _
  smul_mul := fun _ => smul_mul' _

instance mulDistribMulAction' [Monoidₓ R] [Monoidₓ M] [MulDistribMulAction R M] : MulDistribMulAction R (ULift M) :=
  { ULift.mulAction' with
    smul_one := fun _ => by
      ext
      simp [← smul_one],
    smul_mul := fun c f g => by
      ext
      simp [← smul_mul'] }

instance smulWithZero [Zero R] [Zero M] [SmulWithZero R M] : SmulWithZero (ULift R) M :=
  { ULift.hasSmulLeft with smul_zero := fun _ => smul_zero' _ _, zero_smul := zero_smul _ }

instance smulWithZero' [Zero R] [Zero M] [SmulWithZero R M] : SmulWithZero R (ULift M) where
  smul_zero := fun _ => ULift.ext _ _ <| smul_zero' _ _
  zero_smul := fun _ => ULift.ext _ _ <| zero_smul _ _

instance mulActionWithZero [MonoidWithZeroₓ R] [Zero M] [MulActionWithZero R M] : MulActionWithZero (ULift R) M :=
  { ULift.smulWithZero with }

instance mulActionWithZero' [MonoidWithZeroₓ R] [Zero M] [MulActionWithZero R M] : MulActionWithZero R (ULift M) :=
  { ULift.smulWithZero' with }

instance module [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module (ULift R) M :=
  { ULift.smulWithZero with add_smul := fun _ _ => add_smul _ _ }

instance module' [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module R (ULift M) :=
  { ULift.smulWithZero' with add_smul := fun _ _ _ => ULift.ext _ _ <| add_smul _ _ _ }

/-- The `R`-linear equivalence between `ulift M` and `M`.
-/
def moduleEquiv [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : ULift M ≃ₗ[R] M where
  toFun := ULift.down
  invFun := ULift.up
  map_smul' := fun r x => rfl
  map_add' := fun x y => rfl
  left_inv := by
    tidy
  right_inv := by
    tidy

end ULift

