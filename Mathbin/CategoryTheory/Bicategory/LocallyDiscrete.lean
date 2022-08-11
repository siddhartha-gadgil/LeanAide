/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.CategoryTheory.Bicategory.Functor
import Mathbin.CategoryTheory.Bicategory.Strict

/-!
# Locally discrete bicategories

A category `C` can be promoted to a strict bicategory `locally_discrete C`. The objects and the
1-morphisms in `locally_discrete C` are the same as the objects and the morphisms, respectively,
in `C`, and the 2-morphisms in `locally_discrete C` are the equalities between 1-morphisms. In
other words, the category consisting of the 1-morphisms between each pair of objects `X` and `Y`
in `locally_discrete C` is defined as the discrete category associated with the type `X ⟶ Y`.
-/


namespace CategoryTheory

open Bicategory Discrete

open Bicategory

universe w₂ v v₁ v₂ u u₁ u₂

variable {C : Type u}

/-- A type synonym for promoting any type to a category,
with the only morphisms being equalities.
-/
def LocallyDiscrete (C : Type u) :=
  C

namespace LocallyDiscrete

instance : ∀ [Inhabited C], Inhabited (LocallyDiscrete C) :=
  id

instance [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C) where
  Hom := fun X Y : C => Discrete (X ⟶ Y)
  id := fun X : C => ⟨𝟙 X⟩
  comp := fun X Y Z f g => ⟨f.as ≫ g.as⟩

variable {C} [CategoryStruct.{v} C]

instance (priority := 900) homSmallCategory (X Y : LocallyDiscrete C) : SmallCategory (X ⟶ Y) :=
  CategoryTheory.discreteCategory (X ⟶ Y)

/-- Extract the equation from a 2-morphism in a locally discrete 2-category. -/
theorem eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g := by
  have : discrete.mk f.as = discrete.mk g.as := congr_arg discrete.mk (eq_of_hom η)
  simpa using this

end LocallyDiscrete

variable (C) [Category.{v} C]

/-- The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
instance locallyDiscreteBicategory : Bicategory (LocallyDiscrete C) where
  whiskerLeft := fun X Y Z f g h η => eqToHom (congr_arg2ₓ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight := fun X Y Z f g η h => eqToHom (congr_arg2ₓ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
  associator := fun W X Y Z f g h =>
    eq_to_iso <| by
      unfold_projs
      simp only [← category.assoc]
  leftUnitor := fun X Y f =>
    eq_to_iso <| by
      unfold_projs
      simp only [← category.id_comp, ← mk_as]
  rightUnitor := fun X Y f =>
    eq_to_iso <| by
      unfold_projs
      simp only [← category.comp_id, ← mk_as]

/-- A locally discrete bicategory is strict. -/
instance locallyDiscreteBicategory.strict : Strict (LocallyDiscrete C) where
  id_comp' := by
    intros
    ext1
    unfold_projs
    apply category.id_comp
  comp_id' := by
    intros
    ext1
    unfold_projs
    apply category.comp_id
  assoc' := by
    intros
    ext1
    unfold_projs
    apply category.assoc

variable {I : Type u₁} [Category.{v₁} I] {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]

/-- If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `locally_discrete I` to `B`.
-/
@[simps]
def Functor.toOplaxFunctor (F : I ⥤ B) : OplaxFunctor (LocallyDiscrete I) B where
  obj := F.obj
  map := fun X Y f => F.map f.as
  map₂ := fun i j f g η => eqToHom (congr_arg _ (eq_of_hom η))
  map_id := fun i => eqToHom (F.map_id i)
  map_comp := fun i j k f g => eqToHom (F.map_comp f.as g.as)

end CategoryTheory

