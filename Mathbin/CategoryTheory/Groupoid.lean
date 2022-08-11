/-
Copyright (c) 2018 Reid Barton All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison, David Wärn
-/
import Mathbin.CategoryTheory.FullSubcategory
import Mathbin.CategoryTheory.Products.Basic
import Mathbin.CategoryTheory.Pi.Basic

/-!
# Groupoids

We define `groupoid` as a typeclass extending `category`,
asserting that all morphisms have inverses.

The instance `is_iso.of_groupoid (f : X ⟶ Y) : is_iso f` means that you can then write
`inv f` to access the inverse of any morphism `f`.

`groupoid.iso_equiv_hom : (X ≅ Y) ≃ (X ⟶ Y)` provides the equivalence between
isomorphisms and morphisms in a groupoid.

We provide a (non-instance) constructor `groupoid.of_is_iso` from an existing category
with `is_iso f` for every `f`.

## See also

See also `category_theory.core` for the groupoid of isomorphisms in a category.
-/


namespace CategoryTheory

universe v v₂ u u₂

/-- A `groupoid` is a category such that all morphisms are isomorphisms. -/
-- morphism levels before object levels. See note [category_theory universes].
class Groupoid (obj : Type u) extends Category.{v} obj : Type max u (v + 1) where
  inv : ∀ {X Y : obj}, (X ⟶ Y) → (Y ⟶ X)
  inv_comp' : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y := by
    run_tac
      obviously
  comp_inv' : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X := by
    run_tac
      obviously

restate_axiom groupoid.inv_comp'

restate_axiom groupoid.comp_inv'

attribute [simp] groupoid.inv_comp groupoid.comp_inv

/-- A `large_groupoid` is a groupoid
where the objects live in `Type (u+1)` while the morphisms live in `Type u`.
-/
abbrev LargeGroupoid (C : Type (u + 1)) : Type (u + 1) :=
  Groupoid.{u} C

/-- A `small_groupoid` is a groupoid
where the objects and morphisms live in the same universe.
-/
abbrev SmallGroupoid (C : Type u) : Type (u + 1) :=
  Groupoid.{u} C

section

variable {C : Type u} [Groupoid.{v} C] {X Y : C}

-- see Note [lower instance priority]
instance (priority := 100) IsIso.of_groupoid (f : X ⟶ Y) : IsIso f :=
  ⟨⟨Groupoid.inv f, by
      simp ⟩⟩

variable (X Y)

/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
def Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y) where
  toFun := Iso.hom
  invFun := fun f => ⟨f, Groupoid.inv f⟩
  left_inv := fun i => Iso.ext rfl
  right_inv := fun f => rfl

end

section

variable {C : Type u} [Category.{v} C]

/-- A category where every morphism `is_iso` is a groupoid. -/
noncomputable def Groupoid.ofIsIso (all_is_iso : ∀ {X Y : C} (f : X ⟶ Y), IsIso f) :
    Groupoid.{v} C where inv := fun X Y f => inv f

/-- A category with a unique morphism between any two objects is a groupoid -/
def Groupoid.ofHomUnique (all_unique : ∀ {X Y : C}, Unique (X ⟶ Y)) :
    Groupoid.{v} C where inv := fun X Y f => all_unique.default

end

instance InducedCategory.groupoid {C : Type u} (D : Type u₂) [Groupoid.{v} D] (F : C → D) :
    Groupoid.{v} (InducedCategory D F) :=
  { InducedCategory.category F with inv := fun X Y f => Groupoid.inv f, inv_comp' := fun X Y f => Groupoid.inv_comp f,
    comp_inv' := fun X Y f => Groupoid.comp_inv f }

section

instance groupoidPi {I : Type u} {J : I → Type u₂} [∀ i, Groupoid.{v} (J i)] :
    Groupoid.{max u v}
      (∀ i : I, J i) where inv := fun (x y : ∀ i, J i) (f : ∀ i, x i ⟶ y i) => fun i : I => Groupoid.inv (f i)

instance groupoidProd {α : Type u} {β : Type v} [Groupoid.{u₂} α] [Groupoid.{v₂} β] :
    Groupoid.{max u₂ v₂} (α × β) where inv := fun (x y : α × β) (f : x ⟶ y) => (Groupoid.inv f.1, Groupoid.inv f.2)

end

end CategoryTheory

