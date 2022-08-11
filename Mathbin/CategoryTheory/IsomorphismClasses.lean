/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.CategoryTheory.Groupoid
import Mathbin.CategoryTheory.Types

/-!
# Objects of a category up to an isomorphism

`is_isomorphic X Y := nonempty (X ≅ Y)` is an equivalence relation on the objects of a category.
The quotient with respect to this relation defines a functor from our category to `Type`.
-/


universe v u

namespace CategoryTheory

section Category

variable {C : Type u} [Category.{v} C]

/-- An object `X` is isomorphic to an object `Y`, if `X ≅ Y` is not empty. -/
def IsIsomorphic : C → C → Prop := fun X Y => Nonempty (X ≅ Y)

variable (C)

/-- `is_isomorphic` defines a setoid. -/
def isIsomorphicSetoid : Setoidₓ C where
  R := IsIsomorphic
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun X Y ⟨α⟩ => ⟨α.symm⟩, fun X Y Z ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩⟩

end Category

/-- The functor that sends each category to the quotient space of its objects up to an isomorphism.
-/
def isomorphismClasses : Cat.{v, u} ⥤ Type u where
  obj := fun C => Quotientₓ (isIsomorphicSetoid C.α)
  map := fun C D F => (Quot.map F.obj) fun X Y ⟨f⟩ => ⟨F.mapIso f⟩

theorem Groupoid.is_isomorphic_iff_nonempty_hom {C : Type u} [Groupoid.{v} C] {X Y : C} :
    IsIsomorphic X Y ↔ Nonempty (X ⟶ Y) :=
  (Groupoid.isoEquivHom X Y).nonempty_congr

-- PROJECT: define `skeletal`, and show every category is equivalent to a skeletal category,
-- using the axiom of choice to pick a representative of every isomorphism class.
end CategoryTheory

