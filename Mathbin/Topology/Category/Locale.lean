/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.Frame

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/


universe u

open CategoryTheory Opposite Order TopologicalSpace

/-- The category of locales. -/
def Locale :=
  Frameᵒᵖderiving LargeCategory

namespace Locale

instance : CoeSort Locale (Type _) :=
  ⟨fun X => X.unop⟩

instance (X : Locale) : Frame X :=
  X.unop.str

/-- Construct a bundled `Locale` from a `frame`. -/
def of (α : Type _) [Frame α] : Locale :=
  op <| Frame.of α

@[simp]
theorem coe_of (α : Type _) [Frame α] : ↥(of α) = α :=
  rfl

instance : Inhabited Locale :=
  ⟨of PUnit⟩

end Locale

/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
@[simps]
def topToLocale : Top ⥤ Locale :=
  topOpToFrame.rightOp

-- Note, `CompHaus` is too strong. We only need `t0_space`.
instance CompHausToLocale.faithful : Faithful (compHausToTop ⋙ topToLocale.{u}) :=
  ⟨fun X Y f g h => by
    dsimp'  at h
    exact opens.comap_injective (Quiver.Hom.op_inj h)⟩

