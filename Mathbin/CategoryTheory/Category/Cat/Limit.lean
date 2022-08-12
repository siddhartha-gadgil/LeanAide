/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.CategoryTheory.Limits.Types
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# The category of small categories has all small limits.

An object in the limit consists of a family of objects,
which are carried to one another by the functors in the diagram.
A morphism between two such objects is a family of morphisms between the corresponding objects,
which are carried to one another by the action on morphisms of the functors in the diagram.

## Future work
Can the indexing category live in a lower universe?
-/


noncomputable section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

variable {J : Type v} [SmallCategory J]

namespace Cat

namespace HasLimits

instance categoryObjects {F : J ⥤ Cat.{u, u}} {j} : SmallCategory ((F ⋙ Cat.objects.{u, u}).obj j) :=
  (F.obj j).str

/-- Auxiliary definition:
the diagram whose limit gives the morphism space between two objects of the limit category. -/
@[simps]
def homDiagram {F : J ⥤ Cat.{v, v}} (X Y : limit (F ⋙ Cat.objects.{v, v})) : J ⥤ Type v where
  obj := fun j => limit.π (F ⋙ Cat.objects) j X ⟶ limit.π (F ⋙ Cat.objects) j Y
  map := fun j j' f g => by
    refine' eq_to_hom _ ≫ (F.map f).map g ≫ eq_to_hom _
    exact (congr_fun (limit.w (F ⋙ Cat.objects) f) X).symm
    exact congr_fun (limit.w (F ⋙ Cat.objects) f) Y
  map_id' := fun X => by
    ext f
    dsimp'
    simp [← functor.congr_hom (F.map_id X) f]
  map_comp' := fun X Y Z f g => by
    ext h
    dsimp'
    simp [← functor.congr_hom (F.map_comp f g) h, ← eq_to_hom_map]
    rfl

@[simps]
instance (F : J ⥤ Cat.{v, v}) : Category (limit (F ⋙ Cat.objects)) where
  Hom := fun X Y => limit (homDiagram X Y)
  id := fun X =>
    Types.Limit.mk.{v, v} (homDiagram X X) (fun j => 𝟙 _) fun j j' f => by
      simp
  comp := fun X Y Z f g =>
    Types.Limit.mk.{v, v} (homDiagram X Z) (fun j => limit.π (homDiagram X Y) j f ≫ limit.π (homDiagram Y Z) j g)
      fun j j' h => by
      rw [← congr_fun (limit.w (hom_diagram X Y) h) f, ← congr_fun (limit.w (hom_diagram Y Z) h) g]
      dsimp'
      simp

/-- Auxiliary definition: the limit category. -/
@[simps]
def limitConeX (F : J ⥤ Cat.{v, v}) : Cat.{v, v} where α := limit (F ⋙ Cat.objects)

/-- Auxiliary definition: the cone over the limit category. -/
@[simps]
def limitCone (F : J ⥤ Cat.{v, v}) : Cone F where
  x := limitConeX F
  π :=
    { app := fun j => { obj := limit.π (F ⋙ Cat.objects) j, map := fun X Y => limit.π (homDiagram X Y) j },
      naturality' := fun j j' f =>
        CategoryTheory.Functor.ext (fun X => (congr_fun (limit.w (F ⋙ Cat.objects) f) X).symm) fun X Y h =>
          (congr_fun (limit.w (homDiagram X Y) f) h).symm }

/-- Auxiliary definition: the universal morphism to the proposed limit cone. -/
@[simps]
def limitConeLift (F : J ⥤ Cat.{v, v}) (s : Cone F) : s.x ⟶ limitConeX F where
  obj :=
    limit.lift (F ⋙ Cat.objects)
      { x := s.x,
        π :=
          { app := fun j => (s.π.app j).obj,
            naturality' := fun j j' f => (congr_arg Functor.obj (s.π.naturality f) : _) } }
  map := fun X Y f => by
    fapply Types.Limit.mk.{v, v}
    · intro j
      refine' eq_to_hom _ ≫ (s.π.app j).map f ≫ eq_to_hom _ <;> simp
      
    · intro j j' h
      dsimp'
      simp only [← category.assoc, ← functor.map_comp, ← eq_to_hom_map, ← eq_to_hom_trans, ← eq_to_hom_trans_assoc]
      rw [← functor.comp_map]
      have := (s.π.naturality h).symm
      conv at this => congr skip dsimp simp
      erw [functor.congr_hom this f]
      dsimp'
      simp
      

@[simp]
theorem limit_π_hom_diagram_eq_to_hom {F : J ⥤ Cat.{v, v}} (X Y : limit (F ⋙ Cat.objects.{v, v})) (j : J) (h : X = Y) :
    limit.π (homDiagram X Y) j (eqToHom h) = eqToHom (congr_arg (limit.π (F ⋙ Cat.objects.{v, v}) j) h) := by
  subst h
  simp

/-- Auxiliary definition: the proposed cone is a limit cone. -/
def limitConeIsLimit (F : J ⥤ Cat.{v, v}) : IsLimit (limitCone F) where
  lift := limitConeLift F
  fac' := fun s j =>
    CategoryTheory.Functor.ext
      (by
        tidy)
      fun X Y f => Types.Limit.π_mk _ _ _ _
  uniq' := fun s m w => by
    symm
    fapply CategoryTheory.Functor.ext
    · intro X
      ext
      dsimp'
      simp only [← types.limit.lift_π_apply', w j]
      rfl
      
    · intro X Y f
      dsimp'
      simp [← fun j => functor.congr_hom (w j).symm f]
      congr
      

end HasLimits

/-- The category of small categories has all small limits. -/
instance :
    HasLimits
      Cat.{v,
        v} where HasLimitsOfShape := fun J _ =>
    { HasLimit := fun F => ⟨⟨⟨has_limits.limit_cone F, has_limits.limit_cone_is_limit F⟩⟩⟩ }

instance :
    PreservesLimits
      Cat.objects.{v,
        v} where PreservesLimitsOfShape := fun J _ =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (has_limits.limit_cone_is_limit F)
          (limits.is_limit.of_iso_limit (limit.is_limit (F ⋙ Cat.objects))
            (cones.ext
              (by
                rfl)
              (by
                tidy))) }

end Cat

end CategoryTheory

