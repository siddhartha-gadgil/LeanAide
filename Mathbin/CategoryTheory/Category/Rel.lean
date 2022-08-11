/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Category.Basic

/-!
The category of types with binary relations as morphisms.
-/


namespace CategoryTheory

universe u

/-- A type synonym for `Type`, which carries the category instance for which
    morphisms are binary relations. -/
def Rel :=
  Type u

instance Rel.inhabited : Inhabited Rel := by
  unfold Rel <;> infer_instance

/-- The category of types with binary relations as morphisms. -/
instance rel : LargeCategory Rel where
  Hom := fun X Y => X → Y → Prop
  id := fun X => fun x y => x = y
  comp := fun X Y Z f g x z => ∃ y, f x y ∧ g y z

end CategoryTheory

