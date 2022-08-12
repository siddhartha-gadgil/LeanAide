/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Algebra.Category.Group.Basic
import Mathbin.CategoryTheory.Category.Bipointed

/-!
# The category of groups with zero

This file defines `GroupWithZero`, the category of groups with zero.
-/


universe u

open CategoryTheory Order

/-- The category of groups with zero. -/
def GroupWithZeroₓₓ :=
  Bundled GroupWithZeroₓ

namespace GroupWithZeroₓₓ

instance : CoeSort GroupWithZeroₓₓ (Type _) :=
  bundled.has_coe_to_sort

instance (X : GroupWithZeroₓₓ) : GroupWithZeroₓ X :=
  X.str

/-- Construct a bundled `GroupWithZero` from a `group_with_zero`. -/
def of (α : Type _) [GroupWithZeroₓ α] : GroupWithZeroₓₓ :=
  Bundled.of α

instance : Inhabited GroupWithZeroₓₓ :=
  ⟨of (WithZero PUnit)⟩

instance : LargeCategory.{u} GroupWithZeroₓₓ where
  Hom := fun X Y => MonoidWithZeroHom X Y
  id := fun X => MonoidWithZeroHom.id X
  comp := fun X Y Z f g => g.comp f
  id_comp' := fun X Y => MonoidWithZeroHom.comp_id
  comp_id' := fun X Y => MonoidWithZeroHom.id_comp
  assoc' := fun W X Y Z _ _ _ => MonoidWithZeroHom.comp_assoc _ _ _

instance : ConcreteCategory GroupWithZeroₓₓ where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y f g h => FunLike.coe_injective h⟩

instance hasForgetToBipointed :
    HasForget₂ GroupWithZeroₓₓ
      Bipointed where forget₂ := { obj := fun X => ⟨X, 0, 1⟩, map := fun X Y f => ⟨f, f.map_zero', f.map_one'⟩ }

instance hasForgetToMon :
    HasForget₂ GroupWithZeroₓₓ
      Mon where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y => MonoidWithZeroHom.toMonoidHom }

/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps]
def Iso.mk {α β : GroupWithZeroₓₓ.{u}} (e : α ≃* β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _

end GroupWithZeroₓₓ

