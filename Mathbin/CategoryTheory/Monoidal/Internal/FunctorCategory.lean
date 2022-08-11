/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.CommMon_
import Mathbin.CategoryTheory.Monoidal.FunctorCategory

/-!
# `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`

When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing as functors from `C` into the monoid objects of `D`.

This is formalised as:
* `Mon_functor_category_equivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`

The intended application is that as `Ring ≌ Mon_ Ab` (not yet constructed!),
we have `presheaf Ring X ≌ presheaf (Mon_ Ab) X ≌ Mon_ (presheaf Ab X)`,
and we can model a module over a presheaf of rings as a module object in `presheaf Ab X`.

## Future work
Presumably this statement is not specific to monoids,
and could be generalised to any internal algebraic objects,
if the appropriate framework was available.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable (C : Type u₁) [Category.{v₁} C]

variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace MonFunctorCategoryEquivalence

variable {C D}

/-- Functor translating a monoid object in a functor category
to a functor into the category of monoid objects.
-/
@[simps]
def functor : Mon_ (C ⥤ D) ⥤ C ⥤ Mon_ D where
  obj := fun A =>
    { obj := fun X =>
        { x := A.x.obj X, one := A.one.app X, mul := A.mul.app X, one_mul' := congr_app A.one_mul X,
          mul_one' := congr_app A.mul_one X, mul_assoc' := congr_app A.mul_assoc X },
      map := fun X Y f =>
        { Hom := A.x.map f,
          one_hom' := by
            rw [← A.one.naturality, tensor_unit_map]
            dsimp'
            rw [category.id_comp],
          mul_hom' := by
            dsimp'
            rw [← A.mul.naturality, tensor_obj_map] },
      map_id' := fun X => by
        ext
        dsimp'
        rw [CategoryTheory.Functor.map_id],
      map_comp' := fun X Y Z f g => by
        ext
        dsimp'
        rw [functor.map_comp] }
  map := fun A B f =>
    { app := fun X => { Hom := f.Hom.app X, one_hom' := congr_app f.OneHom X, mul_hom' := congr_app f.MulHom X } }

/-- Functor translating a functor into the category of monoid objects
to a monoid object in the functor category
-/
@[simps]
def inverse : (C ⥤ Mon_ D) ⥤ Mon_ (C ⥤ D) where
  obj := fun F =>
    { x := F ⋙ Mon_.forget D, one := { app := fun X => (F.obj X).one }, mul := { app := fun X => (F.obj X).mul },
      one_mul' := by
        ext X
        exact (F.obj X).one_mul,
      mul_one' := by
        ext X
        exact (F.obj X).mul_one,
      mul_assoc' := by
        ext X
        exact (F.obj X).mul_assoc }
  map := fun F G α =>
    { Hom := { app := fun X => (α.app X).Hom, naturality' := fun X Y f => congr_arg Mon_.Hom.hom (α.naturality f) },
      one_hom' := by
        ext x
        dsimp'
        rw [(α.app x).OneHom],
      mul_hom' := by
        ext x
        dsimp'
        rw [(α.app x).MulHom] }

/-- The unit for the equivalence `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`.
-/
@[simps]
def unitIso : 𝟭 (Mon_ (C ⥤ D)) ≅ Functor ⋙ inverse :=
  NatIso.ofComponents
    (fun A =>
      { Hom :=
          { Hom := { app := fun _ => 𝟙 _ },
            one_hom' := by
              ext X
              dsimp'
              simp only [← category.comp_id],
            mul_hom' := by
              ext X
              dsimp'
              simp only [← tensor_id, ← category.id_comp, ← category.comp_id] },
        inv :=
          { Hom := { app := fun _ => 𝟙 _ },
            one_hom' := by
              ext X
              dsimp'
              simp only [← category.comp_id],
            mul_hom' := by
              ext X
              dsimp'
              simp only [← tensor_id, ← category.id_comp, ← category.comp_id] } })
    fun A B f => by
    ext X
    simp only [← functor.id_map, ← functor.comp_map, ← functor_map_app_hom, ← Mon_.comp_hom', ← category.id_comp, ←
      category.comp_id, ← inverse_map_hom_app, ← nat_trans.comp_app]

/-- The counit for the equivalence `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`.
-/
@[simps]
def counitIso : inverse ⋙ Functor ≅ 𝟭 (C ⥤ Mon_ D) :=
  NatIso.ofComponents
    (fun A =>
      NatIso.ofComponents (fun X => { Hom := { Hom := 𝟙 _ }, inv := { Hom := 𝟙 _ } })
        (by
          tidy))
    (by
      tidy)

end MonFunctorCategoryEquivalence

open MonFunctorCategoryEquivalence

/-- When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the monoid objects of `D`.
-/
@[simps]
def monFunctorCategoryEquivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D where
  Functor := Functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

variable [BraidedCategory.{v₂} D]

namespace CommMonFunctorCategoryEquivalence

variable {C D}

/-- Functor translating a commutative monoid object in a functor category
to a functor into the category of commutative monoid objects.
-/
@[simps]
def functor : CommMon_ (C ⥤ D) ⥤ C ⥤ CommMon_ D where
  obj := fun A =>
    { (monFunctorCategoryEquivalence C D).Functor.obj A.toMon_ with
      obj := fun X =>
        { ((monFunctorCategoryEquivalence C D).Functor.obj A.toMon_).obj X with mul_comm' := congr_app A.mul_comm X } }
  map := fun A B f => { app := fun X => ((monFunctorCategoryEquivalence C D).Functor.map f).app X }

/-- Functor translating a functor into the category of commutative monoid objects
to a commutative monoid object in the functor category
-/
@[simps]
def inverse : (C ⥤ CommMon_ D) ⥤ CommMon_ (C ⥤ D) where
  obj := fun F =>
    { (monFunctorCategoryEquivalence C D).inverse.obj (F ⋙ CommMon_.forget₂Mon_ D) with
      mul_comm' := by
        ext X
        exact (F.obj X).mul_comm }
  map := fun F G α => (monFunctorCategoryEquivalence C D).inverse.map (whiskerRight α _)

/-- The unit for the equivalence `CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D`.
-/
@[simps]
def unitIso : 𝟭 (CommMon_ (C ⥤ D)) ≅ Functor ⋙ inverse :=
  NatIso.ofComponents
    (fun A =>
      { Hom :=
          { Hom := { app := fun _ => 𝟙 _ },
            one_hom' := by
              ext X
              dsimp'
              simp only [← category.comp_id],
            mul_hom' := by
              ext X
              dsimp'
              simp only [← tensor_id, ← category.id_comp, ← category.comp_id] },
        inv :=
          { Hom := { app := fun _ => 𝟙 _ },
            one_hom' := by
              ext X
              dsimp'
              simp only [← category.comp_id],
            mul_hom' := by
              ext X
              dsimp'
              simp only [← tensor_id, ← category.id_comp, ← category.comp_id] } })
    fun A B f => by
    ext X
    dsimp'
    simp only [← category.id_comp, ← category.comp_id]

/-- The counit for the equivalence `CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D`.
-/
@[simps]
def counitIso : inverse ⋙ Functor ≅ 𝟭 (C ⥤ CommMon_ D) :=
  NatIso.ofComponents
    (fun A =>
      NatIso.ofComponents (fun X => { Hom := { Hom := 𝟙 _ }, inv := { Hom := 𝟙 _ } })
        (by
          tidy))
    (by
      tidy)

end CommMonFunctorCategoryEquivalence

open CommMonFunctorCategoryEquivalence

/-- When `D` is a braided monoidal category,
commutative monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the commutative monoid objects of `D`.
-/
@[simps]
def commMonFunctorCategoryEquivalence : CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D where
  Functor := Functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

end CategoryTheory.Monoidal

