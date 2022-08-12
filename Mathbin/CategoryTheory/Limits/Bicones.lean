/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.Cones
import Mathbin.CategoryTheory.StructuredArrow
import Mathbin.CategoryTheory.FinCategory

/-!
# Bicones

Given a category `J`, a walking `bicone J` is a category whose objects are the objects of `J` and
two extra vertices `bicone.left` and `bicone.right`. The morphisms are the morphisms of `J` and
`left ⟶ j`, `right ⟶ j` for each `j : J` such that `⬝ ⟶ j` and `⬝ ⟶ k` commutes with each
`f : j ⟶ k`.

Given a diagram `F : J ⥤ C` and two `cone F`s, we can join them into a diagram `bicone J ⥤ C` via
`bicone_mk`.

This is used in `category_theory.flat_functors.preserves_finite_limits_of_flat`.
-/


universe v₁ u₁

noncomputable section

open CategoryTheory.Limits

open Classical

namespace CategoryTheory

section Bicone

variable (J : Type u₁)

/-- Given a category `J`, construct a walking `bicone J` by adjoining two elements. -/
inductive Bicone
  | left : bicone
  | right : bicone
  | diagram (val : J) : bicone
  deriving DecidableEq

instance : Inhabited (Bicone J) :=
  ⟨Bicone.left⟩

instance finBicone [Fintype J] : Fintype (Bicone J) where
  elems := [Bicone.left, Bicone.right].toFinset ∪ Finset.image Bicone.diagram (Fintype.elems J)
  complete := fun j => by
    cases j <;> simp
    exact Fintype.complete j

variable [Category.{v₁} J]

/-- The homs for a walking `bicone J`. -/
inductive BiconeHom : Bicone J → Bicone J → Type max u₁ v₁
  | left_id : bicone_hom Bicone.left Bicone.left
  | right_id : bicone_hom Bicone.right Bicone.right
  | left (j : J) : bicone_hom Bicone.left (Bicone.diagram j)
  | right (j : J) : bicone_hom Bicone.right (Bicone.diagram j)
  | diagram {j k : J} (f : j ⟶ k) : bicone_hom (Bicone.diagram j) (Bicone.diagram k)

instance : Inhabited (BiconeHom J Bicone.left Bicone.left) :=
  ⟨BiconeHom.left_id⟩

instance BiconeHom.decidableEq {j k : Bicone J} : DecidableEq (BiconeHom J j k) := fun f g => by
  cases f <;> cases g <;> simp <;> infer_instance

@[simps]
instance biconeCategoryStruct : CategoryStruct (Bicone J) where
  Hom := BiconeHom J
  id := fun j => Bicone.casesOn j BiconeHom.left_id BiconeHom.right_id fun k => BiconeHom.diagram (𝟙 k)
  comp := fun X Y Z f g => by
    cases f
    exact g
    exact g
    cases g
    exact bicone_hom.left g_k
    cases g
    exact bicone_hom.right g_k
    cases g
    exact bicone_hom.diagram (f_f ≫ g_f)

instance biconeCategory : Category (Bicone J) where
  id_comp' := fun X Y f => by
    cases f <;> simp
  comp_id' := fun X Y f => by
    cases f <;> simp
  assoc' := fun W X Y Z f g h => by
    cases f <;> cases g <;> cases h <;> simp

end Bicone

section SmallCategory

variable (J : Type v₁) [SmallCategory J]

/-- Given a diagram `F : J ⥤ C` and two `cone F`s, we can join them into a diagram `bicone J ⥤ C`.
-/
@[simps]
def biconeMk {C : Type u₁} [Category.{v₁} C] {F : J ⥤ C} (c₁ c₂ : Cone F) : Bicone J ⥤ C where
  obj := fun X => Bicone.casesOn X c₁.x c₂.x fun j => F.obj j
  map := fun X Y f => by
    cases f
    exact 𝟙 _
    exact 𝟙 _
    exact c₁.π.app f_1
    exact c₂.π.app f_1
    exact F.map f_f
  map_id' := fun X => by
    cases X <;> simp
  map_comp' := fun X Y Z f g => by
    cases f
    exact (category.id_comp _).symm
    exact (category.id_comp _).symm
    cases g
    exact (category.id_comp _).symm.trans (c₁.π.naturality g_f : _)
    cases g
    exact (category.id_comp _).symm.trans (c₂.π.naturality g_f : _)
    cases g
    exact F.map_comp _ _

instance finBiconeHom [FinCategory J] (j k : Bicone J) : Fintype (j ⟶ k) := by
  cases j <;> cases k
  exact
    { elems := {bicone_hom.left_id},
      complete := fun f => by
        cases f
        simp }
  exact
    { elems := ∅,
      complete := fun f => by
        cases f }
  exact
    { elems := {bicone_hom.left k},
      complete := fun f => by
        cases f
        simp }
  exact
    { elems := ∅,
      complete := fun f => by
        cases f }
  exact
    { elems := {bicone_hom.right_id},
      complete := fun f => by
        cases f
        simp }
  exact
    { elems := {bicone_hom.right k},
      complete := fun f => by
        cases f
        simp }
  exact
    { elems := ∅,
      complete := fun f => by
        cases f }
  exact
    { elems := ∅,
      complete := fun f => by
        cases f }
  exact
    { elems := Finset.image bicone_hom.diagram (Fintype.elems (j ⟶ k)),
      complete := fun f => by
        cases f
        simp only [← Finset.mem_image]
        use f_f
        simpa using Fintype.complete _ }

instance biconeSmallCategory : SmallCategory (Bicone J) :=
  CategoryTheory.biconeCategory J

instance biconeFinCategory [FinCategory J] : FinCategory (Bicone J) where

end SmallCategory

end CategoryTheory

