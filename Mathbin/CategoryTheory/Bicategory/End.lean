/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Bicategory.Basic
import Mathbin.CategoryTheory.Monoidal.Category

/-!
# Endomorphisms of an object in a bicategory, as a monoidal category.
-/


namespace CategoryTheory

variable {C : Type _} [Bicategory C]

/-- The endomorphisms of an object in a bicategory can be considered as a monoidal category. -/
def EndMonoidal (X : C) :=
  X ⟶ X deriving Category

instance (X : C) : Inhabited (EndMonoidal X) :=
  ⟨𝟙 X⟩

open Bicategory

open MonoidalCategory

open Bicategory

instance (X : C) : MonoidalCategory (EndMonoidal X) where
  tensorObj := fun f g => f ≫ g
  tensorHom := fun f g h i η θ => η ▷ h ≫ g ◁ θ
  tensorUnit := 𝟙 _
  associator := fun f g h => α_ f g h
  leftUnitor := fun f => λ_ f
  rightUnitor := fun f => ρ_ f
  tensor_comp' := by
    intros
    rw [bicategory.whisker_left_comp, bicategory.comp_whisker_right, category.assoc, category.assoc,
      bicategory.whisker_exchange_assoc]

end CategoryTheory

