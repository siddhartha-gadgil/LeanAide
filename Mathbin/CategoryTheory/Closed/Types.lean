/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Presheaf
import Mathbin.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathbin.CategoryTheory.Limits.Shapes.Types
import Mathbin.CategoryTheory.Closed.Cartesian

/-!
# Cartesian closure of Type

Show that `Type u₁` is cartesian closed, and `C ⥤ Type u₁` is cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is cartesian closed.
-/


namespace CategoryTheory

noncomputable section

open Category Limits

universe v₁ v₂ u₁ u₂

variable {C : Type v₂} [Category.{v₁} C]

section CartesianClosed

instance (X : Type v₁) : IsLeftAdjoint (Types.binaryProductFunctor.obj X) where
  right := { obj := fun Y => X ⟶ Y, map := fun Y₁ Y₂ f g => g ≫ f }
  adj :=
    Adjunction.mkOfUnitCounit
      { Unit := { app := fun Z (z : Z) x => ⟨x, z⟩ }, counit := { app := fun Z xf => xf.2 xf.1 } }

instance : HasFiniteProducts (Type v₁) :=
  has_finite_products_of_has_products.{v₁} _

instance :
    CartesianClosed
      (Type v₁) where closed' := fun X => { isAdj := Adjunction.leftAdjointOfNatIso (Types.binaryProductIsoProd.app X) }

instance {C : Type u₁} [Category.{v₁} C] : HasFiniteProducts (C ⥤ Type u₁) :=
  has_finite_products_of_has_products.{u₁} _

instance {C : Type v₁} [SmallCategory C] :
    CartesianClosed (C ⥤ Type v₁) where closed' := fun F =>
    { isAdj := by
        let this := functor_category.prod_preserves_colimits F
        apply is_left_adjoint_of_preserves_colimits (prod.functor.obj F) }

end CartesianClosed

end CategoryTheory

