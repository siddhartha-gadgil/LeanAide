/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathbin.CategoryTheory.Functor.Category
import Mathbin.CategoryTheory.Isomorphism

/-!
# Natural isomorphisms

For the most part, natural isomorphisms are just another sort of isomorphism.

We provide some special support for extracting components:
* if `α : F ≅ G`, then `a.app X : F.obj X ≅ G.obj X`,
and building natural isomorphisms from components:
*
```
nat_iso.of_components
  (app : ∀ X : C, F.obj X ≅ G.obj X)
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f) :
F ≅ G
```
only needing to check naturality in one direction.

## Implementation

Note that `nat_iso` is a namespace without a corresponding definition;
we put some declarations that are specifically about natural isomorphisms in the `iso`
namespace so that they are available using dot notation.
-/


open CategoryTheory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

namespace Iso

/-- The application of a natural isomorphism to an object. We put this definition in a different
namespace, so that we can use `α.app` -/
@[simps]
def app {F G : C ⥤ D} (α : F ≅ G) (X : C) : F.obj X ≅ G.obj X where
  Hom := α.Hom.app X
  inv := α.inv.app X
  hom_inv_id' := by
    rw [← comp_app, iso.hom_inv_id]
    rfl
  inv_hom_id' := by
    rw [← comp_app, iso.inv_hom_id]
    rfl

@[simp, reassoc]
theorem hom_inv_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) : α.Hom.app X ≫ α.inv.app X = 𝟙 (F.obj X) :=
  congr_fun (congr_arg NatTrans.app α.hom_inv_id) X

@[simp, reassoc]
theorem inv_hom_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) : α.inv.app X ≫ α.Hom.app X = 𝟙 (G.obj X) :=
  congr_fun (congr_arg NatTrans.app α.inv_hom_id) X

end Iso

namespace NatIso

open CategoryTheory.Category CategoryTheory.Functor

@[simp]
theorem trans_app {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) : (α ≪≫ β).app X = α.app X ≪≫ β.app X :=
  rfl

theorem app_hom {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).Hom = α.Hom.app X :=
  rfl

theorem app_inv {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).inv = α.inv.app X :=
  rfl

variable {F G : C ⥤ D}

instance hom_app_is_iso (α : F ≅ G) (X : C) : IsIso (α.Hom.app X) :=
  ⟨⟨α.inv.app X,
      ⟨by
        rw [← comp_app, iso.hom_inv_id, ← id_app], by
        rw [← comp_app, iso.inv_hom_id, ← id_app]⟩⟩⟩

instance inv_app_is_iso (α : F ≅ G) (X : C) : IsIso (α.inv.app X) :=
  ⟨⟨α.Hom.app X,
      ⟨by
        rw [← comp_app, iso.inv_hom_id, ← id_app], by
        rw [← comp_app, iso.hom_inv_id, ← id_app]⟩⟩⟩

section

/-!
Unfortunately we need a separate set of cancellation lemmas for components of natural isomorphisms,
because the `simp` normal form is `α.hom.app X`, rather than `α.app.hom X`.

(With the later, the morphism would be visibly part of an isomorphism, so general lemmas about
isomorphisms would apply.)

In the future, we should consider a redesign that changes this simp norm form,
but for now it breaks too many proofs.
-/


variable (α : F ≅ G)

@[simp]
theorem cancel_nat_iso_hom_left {X : C} {Z : D} (g g' : G.obj X ⟶ Z) : α.Hom.app X ≫ g = α.Hom.app X ≫ g' ↔ g = g' := by
  simp only [← cancel_epi]

@[simp]
theorem cancel_nat_iso_inv_left {X : C} {Z : D} (g g' : F.obj X ⟶ Z) : α.inv.app X ≫ g = α.inv.app X ≫ g' ↔ g = g' := by
  simp only [← cancel_epi]

@[simp]
theorem cancel_nat_iso_hom_right {X : D} {Y : C} (f f' : X ⟶ F.obj Y) : f ≫ α.Hom.app Y = f' ≫ α.Hom.app Y ↔ f = f' :=
  by
  simp only [← cancel_mono]

@[simp]
theorem cancel_nat_iso_inv_right {X : D} {Y : C} (f f' : X ⟶ G.obj Y) : f ≫ α.inv.app Y = f' ≫ α.inv.app Y ↔ f = f' :=
  by
  simp only [← cancel_mono]

@[simp]
theorem cancel_nat_iso_hom_right_assoc {W X X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ F.obj Y) (f' : W ⟶ X')
    (g' : X' ⟶ F.obj Y) : f ≫ g ≫ α.Hom.app Y = f' ≫ g' ≫ α.Hom.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [category.assoc, ← cancel_mono]

@[simp]
theorem cancel_nat_iso_inv_right_assoc {W X X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ G.obj Y) (f' : W ⟶ X')
    (g' : X' ⟶ G.obj Y) : f ≫ g ≫ α.inv.app Y = f' ≫ g' ≫ α.inv.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [category.assoc, ← cancel_mono]

@[simp]
theorem inv_inv_app {F G : C ⥤ D} (e : F ≅ G) (X : C) : inv (e.inv.app X) = e.Hom.app X := by
  ext
  simp

end

variable {X Y : C}

theorem naturality_1 (α : F ≅ G) (f : X ⟶ Y) : α.inv.app X ≫ F.map f ≫ α.Hom.app Y = G.map f := by
  simp

theorem naturality_2 (α : F ≅ G) (f : X ⟶ Y) : α.Hom.app X ≫ G.map f ≫ α.inv.app Y = F.map f := by
  simp

theorem naturality_1' (α : F ⟶ G) (f : X ⟶ Y) [IsIso (α.app X)] : inv (α.app X) ≫ F.map f ≫ α.app Y = G.map f := by
  simp

@[simp, reassoc]
theorem naturality_2' (α : F ⟶ G) (f : X ⟶ Y) [IsIso (α.app Y)] : α.app X ≫ G.map f ≫ inv (α.app Y) = F.map f := by
  rw [← category.assoc, ← naturality, category.assoc, is_iso.hom_inv_id, category.comp_id]

/-- The components of a natural isomorphism are isomorphisms.
-/
instance is_iso_app_of_is_iso (α : F ⟶ G) [IsIso α] (X) : IsIso (α.app X) :=
  ⟨⟨(inv α).app X,
      ⟨congr_fun (congr_arg NatTrans.app (IsIso.hom_inv_id α)) X,
        congr_fun (congr_arg NatTrans.app (IsIso.inv_hom_id α)) X⟩⟩⟩

@[simp]
theorem is_iso_inv_app (α : F ⟶ G) [IsIso α] (X) : (inv α).app X = inv (α.app X) := by
  ext
  rw [← nat_trans.comp_app]
  simp

@[simp]
theorem inv_map_inv_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
    inv ((F.map e.inv).app Z) = (F.map e.Hom).app Z := by
  ext
  simp

/-- Construct a natural isomorphism between functors by giving object level isomorphisms,
and checking naturality only in the forward direction.
-/
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).Hom = (app X).Hom ≫ G.map f) : F ≅ G where
  Hom := { app := fun X => (app X).Hom }
  inv :=
    { app := fun X => (app X).inv,
      naturality' := fun X Y f => by
        have h := congr_arg (fun f => (app X).inv ≫ f ≫ (app Y).inv) (naturality f).symm
        simp only [← iso.inv_hom_id_assoc, ← iso.hom_inv_id, ← assoc, ← comp_id, ← cancel_mono] at h
        exact h }

@[simp]
theorem ofComponents.app (app' : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
    (ofComponents app' naturality).app X = app' X := by
  tidy

@[simp]
theorem ofComponents.hom_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
    (ofComponents app naturality).Hom.app X = (app X).Hom :=
  rfl

@[simp]
theorem ofComponents.inv_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
    (ofComponents app naturality).inv.app X = (app X).inv := by
  simp [← of_components]

/-- A natural transformation is an isomorphism if all its components are isomorphisms.
-/
-- Making this an instance would cause a typeclass inference loop with `is_iso_app_of_is_iso`.
theorem is_iso_of_is_iso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  ⟨(IsIso.of_iso
        (ofComponents (fun X => asIso (α.app X))
          (by
            tidy))).1⟩

/-- Horizontal composition of natural isomorphisms. -/
def hcomp {F G : C ⥤ D} {H I : D ⥤ E} (α : F ≅ G) (β : H ≅ I) : F ⋙ H ≅ G ⋙ I := by
  refine' ⟨α.hom ◫ β.hom, α.inv ◫ β.inv, _, _⟩
  · ext
    rw [← nat_trans.exchange]
    simp
    rfl
    
  ext
  rw [← nat_trans.exchange]
  simp
  rfl

end NatIso

end CategoryTheory

