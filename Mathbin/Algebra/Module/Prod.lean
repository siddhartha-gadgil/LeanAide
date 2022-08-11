/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.GroupTheory.GroupAction.Prod

/-!
# Prod instances for module and multiplicative actions

This file defines instances for binary product of modules
-/


variable {R : Type _} {S : Type _} {M : Type _} {N : Type _}

namespace Prod

instance smulWithZero [Zero R] [Zero M] [Zero N] [SmulWithZero R M] [SmulWithZero R N] : SmulWithZero R (M × N) :=
  { Prod.hasSmul with smul_zero := fun r => Prod.extₓ (smul_zero' _ _) (smul_zero' _ _),
    zero_smul := fun ⟨m, n⟩ => Prod.extₓ (zero_smul _ _) (zero_smul _ _) }

instance mulActionWithZero [MonoidWithZeroₓ R] [Zero M] [Zero N] [MulActionWithZero R M] [MulActionWithZero R N] :
    MulActionWithZero R (M × N) :=
  { Prod.mulAction with smul_zero := fun r => Prod.extₓ (smul_zero' _ _) (smul_zero' _ _),
    zero_smul := fun ⟨m, n⟩ => Prod.extₓ (zero_smul _ _) (zero_smul _ _) }

instance {r : Semiringₓ R} [AddCommMonoidₓ M] [AddCommMonoidₓ N] [Module R M] [Module R N] : Module R (M × N) :=
  { Prod.distribMulAction with add_smul := fun a p₁ p₂ => mk.inj_iff.mpr ⟨add_smul _ _ _, add_smul _ _ _⟩,
    zero_smul := fun ⟨b, c⟩ => mk.inj_iff.mpr ⟨zero_smul _ _, zero_smul _ _⟩ }

instance {r : Semiringₓ R} [AddCommMonoidₓ M] [AddCommMonoidₓ N] [Module R M] [Module R N] [NoZeroSmulDivisors R M]
    [NoZeroSmulDivisors R N] : NoZeroSmulDivisors R (M × N) :=
  ⟨fun c ⟨x, y⟩ h =>
    or_iff_not_imp_left.mpr fun hc =>
      mk.inj_iff.mpr
        ⟨(smul_eq_zero.mp (congr_arg fst h)).resolve_left hc, (smul_eq_zero.mp (congr_arg snd h)).resolve_left hc⟩⟩

end Prod

