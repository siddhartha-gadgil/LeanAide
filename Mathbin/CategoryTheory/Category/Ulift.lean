/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathbin.CategoryTheory.Category.Basic
import Mathbin.CategoryTheory.Equivalence
import Mathbin.CategoryTheory.EqToHom

/-!
# Basic API for ulift

This file contains a very basic API for working with the categorical
instance on `ulift C` where `C` is a type with a category instance.

1. `category_theory.ulift.up` is the functorial version of the usual `ulift.up`.
2. `category_theory.ulift.down` is the functorial version of the usual `ulift.down`.
3. `category_theory.ulift.equivalence` is the categorical equivalence between
  `C` and `ulift C`.

# ulift_hom

Given a type `C : Type u`, `ulift_hom.{w} C` is just an alias for `C`.
If we have `category.{v} C`, then `ulift_hom.{w} C` is endowed with a category instance
whose morphisms are obtained by applying `ulift.{w}` to the morphisms from `C`.

This is a category equivalent to `C`. The forward direction of the equivalence is `ulift_hom.up`,
the backward direction is `ulift_hom.donw` and the equivalence is `ulift_hom.equiv`.

# as_small

This file also contains a construction which takes a type `C : Type u` with a
category instance `category.{v} C` and makes a small category
`as_small.{w} C : Type (max w v u)` equivalent to `C`.

The forward direction of the equivalence, `C ⥤ as_small C`, is denoted `as_small.up`
and the backward direction is `as_small.down`. The equivalence itself is `as_small.equiv`.
-/


universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- The functorial version of `ulift.up`. -/
@[simps]
def Ulift.upFunctor : C ⥤ ULift.{u₂} C where
  obj := ULift.up
  map := fun X Y f => f

/-- The functorial version of `ulift.down`. -/
@[simps]
def Ulift.downFunctor : ULift.{u₂} C ⥤ C where
  obj := ULift.down
  map := fun X Y f => f

/-- The categorical equivalence between `C` and `ulift C`. -/
@[simps]
def Ulift.equivalence : C ≌ ULift.{u₂} C where
  Functor := Ulift.upFunctor
  inverse := Ulift.downFunctor
  unitIso := { Hom := 𝟙 _, inv := 𝟙 _ }
  counitIso :=
    { Hom :=
        { app := fun X => 𝟙 _,
          naturality' := fun X Y f => by
            change f ≫ 𝟙 _ = 𝟙 _ ≫ f
            simp },
      inv :=
        { app := fun X => 𝟙 _,
          naturality' := fun X Y f => by
            change f ≫ 𝟙 _ = 𝟙 _ ≫ f
            simp },
      hom_inv_id' := by
        ext
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp ,
      inv_hom_id' := by
        ext
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp }
  functor_unit_iso_comp' := fun X => by
    change 𝟙 X ≫ 𝟙 X = 𝟙 X
    simp

section UliftHom

/-- `ulift_hom.{w} C` is an alias for `C`, which is endowed with a category instance
  whose morphisms are obtained by applying `ulift.{w}` to the morphisms from `C`.
-/
def UliftHom.{w, u} (C : Type u) :=
  C

instance {C} [Inhabited C] : Inhabited (UliftHom C) :=
  ⟨(arbitrary C : C)⟩

/-- The obvious function `ulift_hom C → C`. -/
def UliftHom.objDown {C} (A : UliftHom C) : C :=
  A

/-- The obvious function `C → ulift_hom C`. -/
def UliftHom.objUp {C} (A : C) : UliftHom C :=
  A

@[simp]
theorem obj_down_obj_up {C} (A : C) : (UliftHom.objUp A).objDown = A :=
  rfl

@[simp]
theorem obj_up_obj_down {C} (A : UliftHom C) : UliftHom.objUp A.objDown = A :=
  rfl

instance : Category.{max v₂ v₁} (UliftHom.{v₂} C) where
  Hom := fun A B => ULift.{v₂} <| A.objDown ⟶ B.objDown
  id := fun A => ⟨𝟙 _⟩
  comp := fun A B C f g => ⟨f.down ≫ g.down⟩

/-- One half of the quivalence between `C` and `ulift_hom C`. -/
@[simps]
def UliftHom.up : C ⥤ UliftHom C where
  obj := UliftHom.objUp
  map := fun X Y f => ⟨f⟩

/-- One half of the quivalence between `C` and `ulift_hom C`. -/
@[simps]
def UliftHom.down : UliftHom C ⥤ C where
  obj := UliftHom.objDown
  map := fun X Y f => f.down

/-- The equivalence between `C` and `ulift_hom C`. -/
def UliftHom.equiv : C ≌ UliftHom C where
  Functor := UliftHom.up
  inverse := UliftHom.down
  unitIso :=
    NatIso.ofComponents (fun A => eqToIso rfl)
      (by
        tidy)
  counitIso :=
    NatIso.ofComponents (fun A => eqToIso rfl)
      (by
        tidy)

end UliftHom

/-- `as_small C` is a small category equivalent to `C`.
  More specifically, if `C : Type u` is endowed with `category.{v} C`, then
  `as_small.{w} C : Type (max w v u)` is endowed with an instance of a small category.

  The objects and morphisms of `as_small C` are defined by applying `ulift` to the
  objects and morphisms of `C`.

  Note: We require a category instance for this definition in order to have direct
  access to the universe level `v`.
-/
@[nolint unused_arguments]
def AsSmall.{w, v, u} (C : Type u) [Category.{v} C] :=
  ULift.{max w v} C

instance : SmallCategory (AsSmall.{w₁} C) where
  Hom := fun X Y => ULift.{max w₁ u₁} <| X.down ⟶ Y.down
  id := fun X => ⟨𝟙 _⟩
  comp := fun X Y Z f g => ⟨f.down ≫ g.down⟩

/-- One half of the equivalence between `C` and `as_small C`. -/
@[simps]
def AsSmall.up : C ⥤ AsSmall C where
  obj := fun X => ⟨X⟩
  map := fun X Y f => ⟨f⟩

/-- One half of the equivalence between `C` and `as_small C`. -/
@[simps]
def AsSmall.down : AsSmall C ⥤ C where
  obj := fun X => X.down
  map := fun X Y f => f.down

/-- The equivalence between `C` and `as_small C`. -/
@[simps]
def AsSmall.equiv : C ≌ AsSmall C where
  Functor := AsSmall.up
  inverse := AsSmall.down
  unitIso :=
    NatIso.ofComponents (fun X => eqToIso rfl)
      (by
        tidy)
  counitIso :=
    NatIso.ofComponents
      (fun X =>
        eq_to_iso <| by
          ext
          rfl)
      (by
        tidy)

instance [Inhabited C] : Inhabited (AsSmall C) :=
  ⟨⟨arbitrary _⟩⟩

/-- The equivalence between `C` and `ulift_hom (ulift C)`. -/
def UliftHomUliftCategory.equiv.{v', u', v, u} (C : Type u) [Category.{v} C] : C ≌ UliftHom.{v'} (ULift.{u'} C) :=
  Ulift.equivalence.trans UliftHom.equiv

end CategoryTheory

