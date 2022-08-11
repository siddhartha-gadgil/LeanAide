/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.CategoryTheory.Functor.Category
import Mathbin.CategoryTheory.Functor.Const

/-!
# Monoidal structure on `C ⥤ D` when `D` is monoidal.

When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.

The initial intended application is tensor product of presheaves.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace FunctorCategory

variable (F G F' G' : C ⥤ D)

/-- (An auxiliary definition for `functor_category_monoidal`.)
Tensor product of functors `C ⥤ D`, when `D` is monoidal.
 -/
@[simps]
def tensorObj : C ⥤ D where
  obj := fun X => F.obj X ⊗ G.obj X
  map := fun X Y f => F.map f ⊗ G.map f
  map_id' := fun X => by
    rw [F.map_id, G.map_id, tensor_id]
  map_comp' := fun X Y Z f g => by
    rw [F.map_comp, G.map_comp, tensor_comp]

variable {F G F' G'}

variable (α : F ⟶ G) (β : F' ⟶ G')

/-- (An auxiliary definition for `functor_category_monoidal`.)
Tensor product of natural transformations into `D`, when `D` is monoidal.
-/
@[simps]
def tensorHom : tensorObj F F' ⟶ tensorObj G G' where
  app := fun X => α.app X ⊗ β.app X
  naturality' := fun X Y f => by
    dsimp'
    rw [← tensor_comp, α.naturality, β.naturality, tensor_comp]

end FunctorCategory

open CategoryTheory.Monoidal.FunctorCategory

/-- When `C` is any category, and `D` is a monoidal category,
the functor category `C ⥤ D` has a natural pointwise monoidal structure,
where `(F ⊗ G).obj X = F.obj X ⊗ G.obj X`.
-/
instance functorCategoryMonoidal : MonoidalCategory (C ⥤ D) where
  tensorObj := fun F G => tensorObj F G
  tensorHom := fun F G F' G' α β => tensorHom α β
  tensor_id' := fun F G => by
    ext
    dsimp'
    rw [tensor_id]
  tensor_comp' := fun F G H F' G' H' α β γ δ => by
    ext
    dsimp'
    rw [tensor_comp]
  tensorUnit := (CategoryTheory.Functor.const C).obj (𝟙_ D)
  leftUnitor := fun F =>
    NatIso.ofComponents (fun X => λ_ (F.obj X)) fun X Y f => by
      dsimp'
      rw [left_unitor_naturality]
  rightUnitor := fun F =>
    NatIso.ofComponents (fun X => ρ_ (F.obj X)) fun X Y f => by
      dsimp'
      rw [right_unitor_naturality]
  associator := fun F G H =>
    NatIso.ofComponents (fun X => α_ (F.obj X) (G.obj X) (H.obj X)) fun X Y f => by
      dsimp'
      rw [associator_naturality]
  left_unitor_naturality' := fun F G α => by
    ext X
    dsimp'
    rw [left_unitor_naturality]
  right_unitor_naturality' := fun F G α => by
    ext X
    dsimp'
    rw [right_unitor_naturality]
  associator_naturality' := fun F G H F' G' H' α β γ => by
    ext X
    dsimp'
    rw [associator_naturality]
  triangle' := fun F G => by
    ext X
    dsimp'
    rw [triangle]
  pentagon' := fun F G H K => by
    ext X
    dsimp'
    rw [pentagon]

@[simp]
theorem tensor_unit_obj {X} : (𝟙_ (C ⥤ D)).obj X = 𝟙_ D :=
  rfl

@[simp]
theorem tensor_unit_map {X Y} {f : X ⟶ Y} : (𝟙_ (C ⥤ D)).map f = 𝟙 (𝟙_ D) :=
  rfl

@[simp]
theorem tensor_obj_obj {F G : C ⥤ D} {X} : (F ⊗ G).obj X = F.obj X ⊗ G.obj X :=
  rfl

@[simp]
theorem tensor_obj_map {F G : C ⥤ D} {X Y} {f : X ⟶ Y} : (F ⊗ G).map f = F.map f ⊗ G.map f :=
  rfl

@[simp]
theorem tensor_hom_app {F G F' G' : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G'} {X} : (α ⊗ β).app X = α.app X ⊗ β.app X :=
  rfl

@[simp]
theorem left_unitor_hom_app {F : C ⥤ D} {X} : ((λ_ F).Hom : 𝟙_ _ ⊗ F ⟶ F).app X = (λ_ (F.obj X)).Hom :=
  rfl

@[simp]
theorem left_unitor_inv_app {F : C ⥤ D} {X} : ((λ_ F).inv : F ⟶ 𝟙_ _ ⊗ F).app X = (λ_ (F.obj X)).inv :=
  rfl

@[simp]
theorem right_unitor_hom_app {F : C ⥤ D} {X} : ((ρ_ F).Hom : F ⊗ 𝟙_ _ ⟶ F).app X = (ρ_ (F.obj X)).Hom :=
  rfl

@[simp]
theorem right_unitor_inv_app {F : C ⥤ D} {X} : ((ρ_ F).inv : F ⟶ F ⊗ 𝟙_ _).app X = (ρ_ (F.obj X)).inv :=
  rfl

@[simp]
theorem associator_hom_app {F G H : C ⥤ D} {X} :
    ((α_ F G H).Hom : (F ⊗ G) ⊗ H ⟶ F ⊗ G ⊗ H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).Hom :=
  rfl

@[simp]
theorem associator_inv_app {F G H : C ⥤ D} {X} :
    ((α_ F G H).inv : F ⊗ G ⊗ H ⟶ (F ⊗ G) ⊗ H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).inv :=
  rfl

section BraidedCategory

open CategoryTheory.BraidedCategory

variable [BraidedCategory.{v₂} D]

/-- When `C` is any category, and `D` is a braided monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also braided.
-/
instance functorCategoryBraided : BraidedCategory (C ⥤ D) where
  braiding := fun F G =>
    NatIso.ofComponents (fun X => β_ _ _)
      (by
        tidy)
  hexagon_forward' := fun F G H => by
    ext X
    apply hexagon_forward
  hexagon_reverse' := fun F G H => by
    ext X
    apply hexagon_reverse

example : BraidedCategory (C ⥤ D) :=
  CategoryTheory.Monoidal.functorCategoryBraided

end BraidedCategory

section SymmetricCategory

open CategoryTheory.SymmetricCategory

variable [SymmetricCategory.{v₂} D]

/-- When `C` is any category, and `D` is a symmetric monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also symmetric.
-/
instance functorCategorySymmetric :
    SymmetricCategory (C ⥤ D) where symmetry' := fun F G => by
    ext X
    apply symmetry

end SymmetricCategory

end CategoryTheory.Monoidal

