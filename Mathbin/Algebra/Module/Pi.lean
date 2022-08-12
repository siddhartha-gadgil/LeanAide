/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Regular.Smul
import Mathbin.Algebra.Ring.Pi
import Mathbin.GroupTheory.GroupAction.Pi

/-!
# Pi instances for modules

This file defines instances for module and related structures on Pi Types
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

namespace Pi

theorem _root_.is_smul_regular.pi {α : Type _} [∀ i, HasSmul α <| f i] {k : α} (hk : ∀ i, IsSmulRegular (f i) k) :
    IsSmulRegular (∀ i, f i) k := fun _ _ h => funext fun i => hk i (congr_fun h i : _)

instance smulWithZero (α) [Zero α] [∀ i, Zero (f i)] [∀ i, SmulWithZero α (f i)] : SmulWithZero α (∀ i, f i) :=
  { Pi.hasSmul with smul_zero := fun _ => funext fun _ => smul_zero' (f _) _,
    zero_smul := fun _ => funext fun _ => zero_smul _ _ }

instance smulWithZero' {g : I → Type _} [∀ i, Zero (g i)] [∀ i, Zero (f i)] [∀ i, SmulWithZero (g i) (f i)] :
    SmulWithZero (∀ i, g i) (∀ i, f i) :=
  { Pi.hasSmul' with smul_zero := fun _ => funext fun _ => smul_zero' (f _) _,
    zero_smul := fun _ => funext fun _ => zero_smul _ _ }

instance mulActionWithZero (α) [MonoidWithZeroₓ α] [∀ i, Zero (f i)] [∀ i, MulActionWithZero α (f i)] :
    MulActionWithZero α (∀ i, f i) :=
  { Pi.mulAction _, Pi.smulWithZero _ with }

instance mulActionWithZero' {g : I → Type _} [∀ i, MonoidWithZeroₓ (g i)] [∀ i, Zero (f i)]
    [∀ i, MulActionWithZero (g i) (f i)] : MulActionWithZero (∀ i, g i) (∀ i, f i) :=
  { Pi.mulAction', Pi.smulWithZero' with }

variable (I f)

instance module (α) {r : Semiringₓ α} {m : ∀ i, AddCommMonoidₓ <| f i} [∀ i, Module α <| f i] :
    @Module α (∀ i : I, f i) r (@Pi.addCommMonoid I f m) :=
  { Pi.distribMulAction _ with add_smul := fun c f g => funext fun i => add_smul _ _ _,
    zero_smul := fun f => funext fun i => zero_smul α _ }

/-- A special case of `pi.module` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this. -/
/- Extra instance to short-circuit type class resolution.
For unknown reasons, this is necessary for certain inference problems. E.g., for this to succeed:
```lean
example (β X : Type*) [normed_group β] [normed_space ℝ β] : module ℝ (X → β) := by apply_instance
```
See: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/281296989
-/
instance _root_.function.module (α β : Type _) [Semiringₓ α] [AddCommMonoidₓ β] [Module α β] : Module α (I → β) :=
  Pi.module _ _ _

variable {I f}

instance module' {g : I → Type _} {r : ∀ i, Semiringₓ (f i)} {m : ∀ i, AddCommMonoidₓ (g i)} [∀ i, Module (f i) (g i)] :
    Module (∀ i, f i) (∀ i, g i) where
  add_smul := by
    intros
    ext1
    apply add_smul
  zero_smul := by
    intros
    ext1
    apply zero_smul

instance (α) {r : Semiringₓ α} {m : ∀ i, AddCommMonoidₓ <| f i} [∀ i, Module α <| f i]
    [∀ i, NoZeroSmulDivisors α <| f i] : NoZeroSmulDivisors α (∀ i : I, f i) :=
  ⟨fun c x h => or_iff_not_imp_left.mpr fun hc => funext fun i => (smul_eq_zero.mp (congr_fun h i)).resolve_left hc⟩

end Pi

