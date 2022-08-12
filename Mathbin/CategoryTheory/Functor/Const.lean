/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Opposites

/-!
# The constant functor

`const J : C ⥤ (J ⥤ C)` is the functor that sends an object `X : C` to the functor `J ⥤ C` sending
every object in `J` to `X`, and every morphism to `𝟙 X`.

When `J` is nonempty, `const` is faithful.

We have `(const J).obj X ⋙ F ≅ (const J).obj (F.obj X)` for any `F : C ⥤ D`.
-/


-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory.Functor

variable (J : Type u₁) [Category.{v₁} J]

variable {C : Type u₂} [Category.{v₂} C]

/-- The functor sending `X : C` to the constant functor `J ⥤ C` sending everything to `X`.
-/
def const : C ⥤ J ⥤ C where
  obj := fun X => { obj := fun j => X, map := fun j j' f => 𝟙 X }
  map := fun X Y f => { app := fun j => f }

namespace Const

open Opposite

variable {J}

@[simp]
theorem obj_obj (X : C) (j : J) : ((const J).obj X).obj j = X :=
  rfl

@[simp]
theorem obj_map (X : C) {j j' : J} (f : j ⟶ j') : ((const J).obj X).map f = 𝟙 X :=
  rfl

@[simp]
theorem map_app {X Y : C} (f : X ⟶ Y) (j : J) : ((const J).map f).app j = f :=
  rfl

/-- The contant functor `Jᵒᵖ ⥤ Cᵒᵖ` sending everything to `op X`
is (naturally isomorphic to) the opposite of the constant functor `J ⥤ C` sending everything to `X`.
-/
def opObjOp (X : C) : (const Jᵒᵖ).obj (op X) ≅ ((const J).obj X).op where
  Hom := { app := fun j => 𝟙 _ }
  inv := { app := fun j => 𝟙 _ }

@[simp]
theorem op_obj_op_hom_app (X : C) (j : Jᵒᵖ) : (opObjOp X).Hom.app j = 𝟙 _ :=
  rfl

@[simp]
theorem op_obj_op_inv_app (X : C) (j : Jᵒᵖ) : (opObjOp X).inv.app j = 𝟙 _ :=
  rfl

/-- The contant functor `Jᵒᵖ ⥤ C` sending everything to `unop X`
is (naturally isomorphic to) the opposite of
the constant functor `J ⥤ Cᵒᵖ` sending everything to `X`.
-/
def opObjUnop (X : Cᵒᵖ) : (const Jᵒᵖ).obj (unop X) ≅ ((const J).obj X).leftOp where
  Hom := { app := fun j => 𝟙 _ }
  inv := { app := fun j => 𝟙 _ }

-- Lean needs some help with universes here.
@[simp]
theorem op_obj_unop_hom_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).Hom.app j = 𝟙 _ :=
  rfl

@[simp]
theorem op_obj_unop_inv_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).inv.app j = 𝟙 _ :=
  rfl

@[simp]
theorem unop_functor_op_obj_map (X : Cᵒᵖ) {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    (unop ((Functor.op (const J)).obj X)).map f = 𝟙 (unop X) :=
  rfl

end Const

section

variable {D : Type u₃} [Category.{v₃} D]

/-- These are actually equal, of course, but not definitionally equal
  (the equality requires F.map (𝟙 _) = 𝟙 _). A natural isomorphism is
  more convenient than an equality between functors (compare id_to_iso). -/
@[simps]
def constComp (X : C) (F : C ⥤ D) : (const J).obj X ⋙ F ≅ (const J).obj (F.obj X) where
  Hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

/-- If `J` is nonempty, then the constant functor over `J` is faithful. -/
instance [Nonempty J] :
    Faithful (const J : C ⥤ J ⥤ C) where map_injective' := fun X Y f g e => NatTrans.congr_app e (Classical.arbitrary J)

end

end CategoryTheory.Functor

