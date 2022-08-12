/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!

# `with_initial` and `with_terminal`

Given a category `C`, this file constructs two objects:
1. `with_terminal C`, the category built from `C` by formally adjoining a terminal object.
2. `with_initial C`, the category built from `C` by formally adjoining an initial object.

The terminal resp. initial object is `with_terminal.star` resp. `with_initial.star`, and
the proofs that these are terminal resp. initial are in `with_terminal.star_terminal`
and `with_initial.star_initial`.

The inclusion from `C` intro `with_terminal C` resp. `with_initial C` is denoted
`with_terminal.incl` resp. `with_initial.incl`.

The relevant constructions needed for the universal properties of these constructions are:
1. `lift`, which lifts `F : C ⥤ D` to a functor from `with_terminal C` resp. `with_initial C` in
  the case where an object `Z : D` is provided satisfying some additional conditions.
2. `incl_lift` shows that the composition of `lift` with `incl` is isomorphic to the
  functor which was lifted.
3. `lift_unique` provides the uniqueness property of `lift`.

In addition to this, we provide `with_terminal.map` and `with_initinal.map` providing the
functoriality of these constructions with respect to functors on the base categories.

-/


namespace CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]

/-- Formally adjoin a terminal object to a category. -/
inductive WithTerminal : Type u
  | of : C → with_terminal
  | star : with_terminal
  deriving Inhabited

/-- Formally adjoin an initial object to a category. -/
inductive WithInitial : Type u
  | of : C → with_initial
  | star : with_initial
  deriving Inhabited

namespace WithTerminal

attribute [local tidy] tactic.case_bash

variable {C}

/-- Morphisms for `with_terminal C`. -/
@[simp, nolint has_inhabited_instance]
def Homₓ : WithTerminal C → WithTerminal C → Type v
  | of X, of Y => X ⟶ Y
  | star, of X => Pempty
  | _, star => PUnit

/-- Identity morphisms for `with_terminal C`. -/
@[simp]
def idₓ : ∀ X : WithTerminal C, Homₓ X X
  | of X => 𝟙 _
  | star => PUnit.unit

/-- Composition of morphisms for `with_terminal C`. -/
@[simp]
def compₓ : ∀ {X Y Z : WithTerminal C}, Homₓ X Y → Homₓ Y Z → Homₓ X Z
  | of X, of Y, of Z => fun f g => f ≫ g
  | of X, _, star => fun f g => PUnit.unit
  | star, of X, _ => fun f g => Pempty.elimₓ f
  | _, star, of Y => fun f g => Pempty.elimₓ g
  | star, star, star => fun _ _ => PUnit.unit

instance : Category.{v} (WithTerminal C) where
  Hom := fun X Y => Homₓ X Y
  id := fun X => idₓ _
  comp := fun X Y Z f g => compₓ f g

/-- The inclusion from `C` into `with_terminal C`. -/
def incl : C ⥤ WithTerminal C where
  obj := of
  map := fun X Y f => f

instance : Full (incl : C ⥤ _) where preimage := fun X Y f => f

instance : Faithful (incl : C ⥤ _) where

/-- Map `with_terminal` with respect to a functor `F : C ⥤ D`. -/
def map {D : Type _} [Category D] (F : C ⥤ D) : WithTerminal C ⥤ WithTerminal D where
  obj := fun X =>
    match X with
    | of x => of <| F.obj x
    | star => star
  map := fun X Y f =>
    match X, Y, f with
    | of x, of y, f => F.map f
    | of x, star, PUnit.unit => PUnit.unit
    | star, star, PUnit.unit => PUnit.unit

instance {X : WithTerminal C} : Unique (X ⟶ star) where
  default :=
    match X with
    | of x => PUnit.unit
    | star => PUnit.unit
  uniq := by
    tidy

/-- `with_terminal.star` is terminal. -/
def starTerminal : Limits.IsTerminal (star : WithTerminal C) :=
  Limits.IsTerminal.ofUnique _

/-- Lift a functor `F : C ⥤ D` to `with_term C ⥤ D`. -/
@[simps]
def lift {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : WithTerminal C ⥤ D where
  obj := fun X =>
    match X with
    | of x => F.obj x
    | star => Z
  map := fun X Y f =>
    match X, Y, f with
    | of x, of y, f => F.map f
    | of x, star, PUnit.unit => M x
    | star, star, PUnit.unit => 𝟙 Z

/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps]
def inclLift {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : incl ⋙ lift F M hM ≅ F where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }

/-- The isomorphism between `(lift F _ _).obj with_terminal.star` with `Z`. -/
@[simps]
def liftStar {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl

theorem lift_map_lift_star {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (x : C) :
    (lift F M hM).map (starTerminal.from (incl.obj x)) ≫ (liftStar F M hM).Hom = (inclLift F M hM).Hom.app x ≫ M x := by
  erw [category.id_comp, category.comp_id]
  rfl

/-- The uniqueness of `lift`. -/
@[simp]
def liftUnique {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z) (hh : ∀ x : C, G.map (starTerminal.from (incl.obj x)) ≫ hG.Hom = h.Hom.app x ≫ M x) :
    G ≅ lift F M hM :=
  NatIso.ofComponents
    (fun X =>
      match X with
      | of x => h.app x
      | star => hG)
    (by
      rintro (X | X) (Y | Y) f
      · apply h.hom.naturality
        
      · cases f
        exact hh _
        
      · cases f
        
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp
        )

/-- A variant of `lift` with `Z` a terminal object. -/
@[simps]
def liftToTerminal {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) : WithTerminal C ⥤ D :=
  lift F (fun x => hZ.from _) fun x y f => hZ.hom_ext _ _

/-- A variant of `incl_lift` with `Z` a terminal object. -/
@[simps]
def inclLiftToTerminal {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    incl ⋙ liftToTerminal F hZ ≅ F :=
  inclLift _ _ _

/-- A variant of `lift_unique` with `Z` a terminal object. -/
@[simps]
def liftToTerminalUnique {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z)
    (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToTerminal F hZ :=
  liftUnique F (fun z => hZ.from _) (fun x y f => hZ.hom_ext _ _) G h hG fun x => hZ.hom_ext _ _

/-- Constructs a morphism to `star` from `of X`. -/
@[simp]
def homFrom (X : C) : incl.obj X ⟶ star :=
  starTerminal.from _

instance is_iso_of_from_star {X : WithTerminal C} (f : star ⟶ X) : IsIso f := by
  tidy

end WithTerminal

namespace WithInitial

attribute [local tidy] tactic.case_bash

variable {C}

/-- Morphisms for `with_initial C`. -/
@[simp, nolint has_inhabited_instance]
def Homₓ : WithInitial C → WithInitial C → Type v
  | of X, of Y => X ⟶ Y
  | of X, _ => Pempty
  | star, _ => PUnit

/-- Identity morphisms for `with_initial C`. -/
@[simp]
def idₓ : ∀ X : WithInitial C, Homₓ X X
  | of X => 𝟙 _
  | star => PUnit.unit

/-- Composition of morphisms for `with_initial C`. -/
@[simp]
def compₓ : ∀ {X Y Z : WithInitial C}, Homₓ X Y → Homₓ Y Z → Homₓ X Z
  | of X, of Y, of Z => fun f g => f ≫ g
  | star, _, of X => fun f g => PUnit.unit
  | _, of X, star => fun f g => Pempty.elimₓ g
  | of Y, star, _ => fun f g => Pempty.elimₓ f
  | star, star, star => fun _ _ => PUnit.unit

instance : Category.{v} (WithInitial C) where
  Hom := fun X Y => Homₓ X Y
  id := fun X => idₓ _
  comp := fun X Y Z f g => compₓ f g

/-- The inclusion of `C` into `with_initial C`. -/
def incl : C ⥤ WithInitial C where
  obj := of
  map := fun X Y f => f

instance : Full (incl : C ⥤ _) where preimage := fun X Y f => f

instance : Faithful (incl : C ⥤ _) where

/-- Map `with_initial` with respect to a functor `F : C ⥤ D`. -/
def map {D : Type _} [Category D] (F : C ⥤ D) : WithInitial C ⥤ WithInitial D where
  obj := fun X =>
    match X with
    | of x => of <| F.obj x
    | star => star
  map := fun X Y f =>
    match X, Y, f with
    | of x, of y, f => F.map f
    | star, of x, PUnit.unit => PUnit.unit
    | star, star, PUnit.unit => PUnit.unit

instance {X : WithInitial C} : Unique (star ⟶ X) where
  default :=
    match X with
    | of x => PUnit.unit
    | star => PUnit.unit
  uniq := by
    tidy

/-- `with_initial.star` is initial. -/
def starInitial : Limits.IsInitial (star : WithInitial C) :=
  Limits.IsInitial.ofUnique _

/-- Lift a functor `F : C ⥤ D` to `with_initial C ⥤ D`. -/
@[simps]
def lift {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : WithInitial C ⥤ D where
  obj := fun X =>
    match X with
    | of x => F.obj x
    | star => Z
  map := fun X Y f =>
    match X, Y, f with
    | of x, of y, f => F.map f
    | star, of x, PUnit.unit => M _
    | star, star, PUnit.unit => 𝟙 _

/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps]
def inclLift {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : incl ⋙ lift F M hM ≅ F where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }

/-- The isomorphism between `(lift F _ _).obj with_term.star` with `Z`. -/
@[simps]
def liftStar {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl

theorem lift_star_lift_map {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (x : C) :
    (liftStar F M hM).Hom ≫ (lift F M hM).map (starInitial.to (incl.obj x)) = M x ≫ (inclLift F M hM).Hom.app x := by
  erw [category.id_comp, category.comp_id]
  rfl

/-- The uniqueness of `lift`. -/
@[simp]
def liftUnique {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, hG.symm.Hom ≫ G.map (starInitial.to (incl.obj x)) = M x ≫ h.symm.Hom.app x) : G ≅ lift F M hM :=
  NatIso.ofComponents
    (fun X =>
      match X with
      | of x => h.app x
      | star => hG)
    (by
      rintro (X | X) (Y | Y) f
      · apply h.hom.naturality
        
      · cases f
        
      · cases f
        change G.map _ ≫ h.hom.app _ = hG.hom ≫ _
        symm
        erw [← iso.eq_inv_comp, ← category.assoc, hh]
        simpa
        
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp
        )

/-- A variant of `lift` with `Z` an initial object. -/
@[simps]
def liftToInitial {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) : WithInitial C ⥤ D :=
  lift F (fun x => hZ.to _) fun x y f => hZ.hom_ext _ _

/-- A variant of `incl_lift` with `Z` an initial object. -/
@[simps]
def inclLiftToInitial {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    incl ⋙ liftToInitial F hZ ≅ F :=
  inclLift _ _ _

/-- A variant of `lift_unique` with `Z` an initial object. -/
@[simps]
def liftToInitialUnique {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) (G : WithInitial C ⥤ D)
    (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToInitial F hZ :=
  liftUnique F (fun z => hZ.to _) (fun x y f => hZ.hom_ext _ _) G h hG fun x => hZ.hom_ext _ _

/-- Constructs a morphism from `star` to `of X`. -/
@[simp]
def homTo (X : C) : star ⟶ incl.obj X :=
  starInitial.to _

instance is_iso_of_to_star {X : WithInitial C} (f : X ⟶ star) : IsIso f := by
  tidy

end WithInitial

end CategoryTheory

