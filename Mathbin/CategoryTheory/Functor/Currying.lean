/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Products.Bifunctor

/-!
# Curry and uncurry, as functors.

We define `curry : ((C × D) ⥤ E) ⥤ (C ⥤ (D ⥤ E))` and `uncurry : (C ⥤ (D ⥤ E)) ⥤ ((C × D) ⥤ E)`,
and verify that they provide an equivalence of categories
`currying : (C ⥤ (D ⥤ E)) ≌ ((C × D) ⥤ E)`.

-/


namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

/-- The uncurrying functor, taking a functor `C ⥤ (D ⥤ E)` and producing a functor `(C × D) ⥤ E`.
-/
def uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E where
  obj := fun F =>
    { obj := fun X => (F.obj X.1).obj X.2, map := fun X Y f => (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2,
      map_comp' := fun X Y Z f g => by
        simp only [← prod_comp_fst, ← prod_comp_snd, ← functor.map_comp, ← nat_trans.comp_app, ← category.assoc]
        slice_lhs 2 3 => rw [← nat_trans.naturality]
        rw [category.assoc] }
  map := fun F G T =>
    { app := fun X => (T.app X.1).app X.2,
      naturality' := fun X Y f => by
        simp only [← prod_comp_fst, ← prod_comp_snd, ← category.comp_id, ← category.assoc, ← Functor.map_id, ←
          functor.map_comp, ← nat_trans.id_app, ← nat_trans.comp_app]
        slice_lhs 2 3 => rw [nat_trans.naturality]
        slice_lhs 1 2 => rw [← nat_trans.comp_app, nat_trans.naturality, nat_trans.comp_app]
        rw [category.assoc] }

/-- The object level part of the currying functor. (See `curry` for the functorial version.)
-/
def curryObj (F : C × D ⥤ E) : C ⥤ D ⥤ E where
  obj := fun X => { obj := fun Y => F.obj (X, Y), map := fun Y Y' g => F.map (𝟙 X, g) }
  map := fun X X' f => { app := fun Y => F.map (f, 𝟙 Y) }

/-- The currying functor, taking a functor `(C × D) ⥤ E` and producing a functor `C ⥤ (D ⥤ E)`.
-/
def curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E where
  obj := fun F => curryObj F
  map := fun F G T =>
    { app := fun X =>
        { app := fun Y => T.app (X, Y),
          naturality' := fun Y Y' g => by
            dsimp' [← curry_obj]
            rw [nat_trans.naturality] },
      naturality' := fun X X' f => by
        ext
        dsimp' [← curry_obj]
        rw [nat_trans.naturality] }

@[simp]
theorem uncurry.obj_obj {F : C ⥤ D ⥤ E} {X : C × D} : (uncurry.obj F).obj X = (F.obj X.1).obj X.2 :=
  rfl

@[simp]
theorem uncurry.obj_map {F : C ⥤ D ⥤ E} {X Y : C × D} {f : X ⟶ Y} :
    (uncurry.obj F).map f = (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2 :=
  rfl

@[simp]
theorem uncurry.map_app {F G : C ⥤ D ⥤ E} {α : F ⟶ G} {X : C × D} : (uncurry.map α).app X = (α.app X.1).app X.2 :=
  rfl

@[simp]
theorem curry.obj_obj_obj {F : C × D ⥤ E} {X : C} {Y : D} : ((curry.obj F).obj X).obj Y = F.obj (X, Y) :=
  rfl

@[simp]
theorem curry.obj_obj_map {F : C × D ⥤ E} {X : C} {Y Y' : D} {g : Y ⟶ Y'} :
    ((curry.obj F).obj X).map g = F.map (𝟙 X, g) :=
  rfl

@[simp]
theorem curry.obj_map_app {F : C × D ⥤ E} {X X' : C} {f : X ⟶ X'} {Y} : ((curry.obj F).map f).app Y = F.map (f, 𝟙 Y) :=
  rfl

@[simp]
theorem curry.map_app_app {F G : C × D ⥤ E} {α : F ⟶ G} {X} {Y} : ((curry.map α).app X).app Y = α.app (X, Y) :=
  rfl

/-- The equivalence of functor categories given by currying/uncurrying.
-/
-- create projection simp lemmas even though this isn't a `{ .. }`.
@[simps]
def currying : C ⥤ D ⥤ E ≌ C × D ⥤ E :=
  Equivalence.mk uncurry curry
    (NatIso.ofComponents
      (fun F =>
        NatIso.ofComponents
          (fun X =>
            NatIso.ofComponents (fun Y => Iso.refl _)
              (by
                tidy))
          (by
            tidy))
      (by
        tidy))
    (NatIso.ofComponents
      (fun F =>
        NatIso.ofComponents
          (fun X =>
            eqToIso
              (by
                simp ))
          (by
            tidy))
      (by
        tidy))

/-- `F.flip` is isomorphic to uncurrying `F`, swapping the variables, and currying. -/
@[simps]
def flipIsoCurrySwapUncurry (F : C ⥤ D ⥤ E) : F.flip ≅ curry.obj (prod.swap _ _ ⋙ uncurry.obj F) :=
  NatIso.ofComponents
    (fun d =>
      NatIso.ofComponents (fun c => Iso.refl _)
        (by
          tidy))
    (by
      tidy)

/-- The uncurrying of `F.flip` is isomorphic to
swapping the factors followed by the uncurrying of `F`. -/
@[simps]
def uncurryObjFlip (F : C ⥤ D ⥤ E) : uncurry.obj F.flip ≅ prod.swap _ _ ⋙ uncurry.obj F :=
  NatIso.ofComponents (fun p => Iso.refl _)
    (by
      tidy)

end CategoryTheory

