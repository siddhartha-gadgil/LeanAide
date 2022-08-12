/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import Mathbin.CategoryTheory.Products.Basic
import Mathbin.CategoryTheory.Types

/-!
The hom functor, sending `(X, Y)` to the type `X ⟶ Y`.
-/


universe v u

open Opposite

open CategoryTheory

namespace CategoryTheory.Functor

variable (C : Type u) [Category.{v} C]

/-- `functor.hom` is the hom-pairing, sending `(X, Y)` to `X ⟶ Y`, contravariant in `X` and
covariant in `Y`. -/
def hom : Cᵒᵖ × C ⥤ Type v where
  obj := fun p => unop p.1 ⟶ p.2
  map := fun X Y f => fun h => f.1.unop ≫ h ≫ f.2

@[simp]
theorem hom_obj (X : Cᵒᵖ × C) : (hom C).obj X = (unop X.1 ⟶ X.2) :=
  rfl

@[simp]
theorem hom_pairing_map {X Y : Cᵒᵖ × C} (f : X ⟶ Y) : (hom C).map f = fun h => f.1.unop ≫ h ≫ f.2 :=
  rfl

end CategoryTheory.Functor

