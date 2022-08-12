/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Preadditive.Opposite
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.Algebra.Category.Group.Preadditive

/-!
# The Yoneda embedding for preadditive categories

The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure.

We also show that this presheaf is additive and that it is compatible with the normal Yoneda
embedding in the expected way and deduce that the preadditive Yoneda embedding is fully faithful.

## TODO
* The Yoneda embedding is additive itself

-/


universe v u

open CategoryTheory.Preadditive Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the `End Y`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditiveYonedaObj (Y : C) : Cᵒᵖ ⥤ ModuleCat.{v} (End Y) where
  obj := fun X => ModuleCat.of _ (X.unop ⟶ Y)
  map := fun X X' f =>
    { toFun := fun g => f.unop ≫ g, map_add' := fun g g' => comp_add _ _ _ _ _ _,
      map_smul' := fun r g => Eq.symm <| Category.assoc _ _ _ }

/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure, see `preadditive_yoneda_obj`.
-/
@[simps]
def preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupₓₓ.{v} where
  obj := fun Y => preadditiveYonedaObj Y ⋙ forget₂ _ _
  map := fun Y Y' f =>
    { app := fun X =>
        { toFun := fun g => g ≫ f, map_zero' := Limits.zero_comp, map_add' := fun g g' => add_comp _ _ _ _ _ _ },
      naturality' := fun X X' g => (AddCommGroupₓₓ.ext _ _ _ _) fun x => Category.assoc _ _ _ }
  map_id' := fun X => by
    ext
    simp
  map_comp' := fun X Y Z f g => by
    ext
    simp

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the `End X`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditiveCoyonedaObj (X : Cᵒᵖ) : C ⥤ ModuleCat.{v} (End X) where
  obj := fun Y => ModuleCat.of _ (unop X ⟶ Y)
  map := fun Y Y' f =>
    { toFun := fun g => g ≫ f, map_add' := fun g g' => add_comp _ _ _ _ _ _,
      map_smul' := fun r g => Category.assoc _ _ _ }

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End X`-module
structure, see `preadditive_coyoneda_obj`.
-/
@[simps]
def preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupₓₓ.{v} where
  obj := fun X => preadditiveCoyonedaObj X ⋙ forget₂ _ _
  map := fun X X' f =>
    { app := fun Y =>
        { toFun := fun g => f.unop ≫ g, map_zero' := Limits.comp_zero, map_add' := fun g g' => comp_add _ _ _ _ _ _ },
      naturality' := fun Y Y' g => (AddCommGroupₓₓ.ext _ _ _ _) fun x => Eq.symm <| Category.assoc _ _ _ }
  map_id' := fun X => by
    ext
    simp
  map_comp' := fun X Y Z f g => by
    ext
    simp

instance additive_yoneda_obj (X : C) : Functor.Additive (preadditiveYonedaObj X) where

instance additive_yoneda_obj' (X : C) : Functor.Additive (preadditiveYoneda.obj X) where

instance additive_coyoneda_obj (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyonedaObj X) where

instance additive_coyoneda_obj' (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyoneda.obj X) where

/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
theorem whiskering_preadditive_yoneda :
    preadditive_yoneda ⋙ (whiskeringRight Cᵒᵖ AddCommGroupₓₓ (Type v)).obj (forget AddCommGroupₓₓ) = yoneda :=
  rfl

/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
theorem whiskering_preadditive_coyoneda :
    preadditive_coyoneda ⋙ (whiskeringRight C AddCommGroupₓₓ (Type v)).obj (forget AddCommGroupₓₓ) = coyoneda :=
  rfl

instance preadditiveYonedaFull : Full (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupₓₓ) :=
  let yoneda_full :
    Full (preadditive_yoneda ⋙ (whiskeringRight Cᵒᵖ AddCommGroupₓₓ (Type v)).obj (forget AddCommGroupₓₓ)) :=
    yoneda.yonedaFull
  full.of_comp_faithful preadditive_yoneda ((whiskering_right Cᵒᵖ AddCommGroupₓₓ (Type v)).obj (forget AddCommGroupₓₓ))

instance preadditiveCoyonedaFull : Full (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupₓₓ) :=
  let coyoneda_full :
    Full (preadditive_coyoneda ⋙ (whiskeringRight C AddCommGroupₓₓ (Type v)).obj (forget AddCommGroupₓₓ)) :=
    coyoneda.coyonedaFull
  full.of_comp_faithful preadditive_coyoneda ((whiskering_right C AddCommGroupₓₓ (Type v)).obj (forget AddCommGroupₓₓ))

instance preadditive_yoneda_faithful : Faithful (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupₓₓ) :=
  Faithful.of_comp_eq whiskering_preadditive_yoneda

instance preadditive_coyoneda_faithful : Faithful (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupₓₓ) :=
  Faithful.of_comp_eq whiskering_preadditive_coyoneda

end CategoryTheory

