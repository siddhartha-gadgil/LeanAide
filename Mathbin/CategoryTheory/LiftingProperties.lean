/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.Arrow

/-!
# Lifting properties

This file defines the lifting property of two arrows in a category and shows basic properties of
this notion.
We also construct the subcategory consisting of those morphisms which have the right lifting
property with respect to arrows in a given diagram.

## Main results
- `has_lifting_property`: the definition of the lifting property
- `iso_has_right_lifting_property`: any isomorphism satisfies the right lifting property (rlp)
- `id_has_right_lifting_property`: any identity has the rlp
- `right_lifting_property_initial_iff`: spells out the rlp with respect to a map whose source is an
  initial object
- `right_lifting_subcat`: given a set of arrows `F : D → arrow C`, we construct the subcategory
  of those morphisms `p` in `C` that satisfy the rlp w.r.t. `F i`, for any element `i` of `D`.

## Tags
lifting property
-/


open CategoryTheory.Limits

namespace CategoryTheory

universe v u v₁

variable {C : Type u} [Category.{v} C]

variable {D : Type v₁}

variable {X Y Z : C}

/-- The lifting property of a morphism `i` with respect to a morphism `p`.
This can be interpreted as the right lifting property of `i` with respect to `p`,
or the left lifting property of `p` with respect to `i`. -/
class HasLiftingProperty (i p : Arrow C) : Prop where
  sq_has_lift : ∀ sq : i ⟶ p, Arrow.HasLift sq

-- see Note [lower instance priority]
instance (priority := 100) has_lifting_property' {i p : Arrow C} [HasLiftingProperty i p] (sq : i ⟶ p) :
    Arrow.HasLift sq :=
  HasLiftingProperty.sq_has_lift sq

/-- Any isomorphism has the right lifting property with respect to any map.
A    → X
↓i    ↓p≅
B    → Y
-/
theorem iso_has_right_lifting_property (i : Arrow C) (p : X ≅ Y) : HasLiftingProperty i (Arrow.mk p.Hom) :=
  ⟨fun sq => ⟨⟨{ lift := sq.right ≫ p.inv }⟩⟩⟩

/-- Any identity has the right lifting property with respect to any map. -/
-- the lift is obtained by p⁻¹ ∘ (B → Y)
theorem id_has_right_lifting_property (i : Arrow C) : HasLiftingProperty i (Arrow.mk (𝟙 X)) :=
  iso_has_right_lifting_property i (Iso.refl _)

/-- An equivalent characterization for right lifting with respect to a map `i` whose source is
initial.
∅ → X
↓   ↓
B → Y has a lifting iff there is a map B → X making the right part commute.
-/
theorem right_lifting_property_initial_iff (i p : Arrow C) (h : IsInitial i.left) :
    HasLiftingProperty i p ↔ ∀ {e : i.right ⟶ p.right}, ∃ l : i.right ⟶ p.left, l ≫ p.Hom = e := by
  fconstructor
  · intro hlift e
    have comm : is_initial.to h p.left ≫ p.hom = i.hom ≫ e := is_initial.hom_ext h _ _
    use arrow.lift (arrow.hom_mk comm)
    simp
    
  · refine' fun hlift => ⟨fun sq => _⟩
    obtain ⟨l, hl⟩ : ∃ l : i.right ⟶ p.left, l ≫ p.hom = sq.right := hlift
    exact arrow.has_lift.mk ⟨l, is_initial.hom_ext h _ _⟩
    

/-- The condition of having the rlp with respect to a morphism `i` is stable under composition. -/
theorem has_right_lifting_property_comp {i : Arrow C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : HasLiftingProperty i (Arrow.mk f))
    (hg : HasLiftingProperty i (Arrow.mk g)) : HasLiftingProperty i (Arrow.mk (f ≫ g)) :=
  { sq_has_lift := fun sq1 =>
      -- construct a square i ⟶ f
      let sq2 : i ⟶ Arrow.mk f := ⟨sq1.left, Arrow.lift (Arrow.squareToSnd sq1)⟩
      -- show that the lift of this square is a lift of i with respect to g ∘ f
      ⟨⟨⟨(Arrow.lift sq2 : _ ⟶ _), by
            simp ⟩⟩⟩ }

/-- The objects of the subcategory `right_lifting_subcategory` are the ones in the
underlying category. -/
def RightLiftingSubcat (R : Type u) :=
  R

instance RightLiftingSubcat.inhabited (R : Type u) [Inhabited R] :
    Inhabited (RightLiftingSubcat R) where default := (default : R)

/-- The objects of the subcategory `right_lifting_subcategory` are the ones in the
underlying category. -/
def RightLiftingSubcat.x {R : Type u} (x : RightLiftingSubcat R) : R :=
  x

theorem id_has_right_lifting_property' {F : D → Arrow C} (X : C) : ∀ i : D, HasLiftingProperty (F i) (Arrow.mk (𝟙 X)) :=
  fun i => id_has_right_lifting_property (F i)

theorem has_right_lifting_property_comp' {F : D → Arrow C} {f : X ⟶ Y}
    (hf : ∀ i : D, HasLiftingProperty (F i) (Arrow.mk f)) {g : Y ⟶ Z}
    (hg : ∀ i : D, HasLiftingProperty (F i) (Arrow.mk g)) : ∀ i : D, HasLiftingProperty (F i) (Arrow.mk (f ≫ g)) :=
  fun i => has_right_lifting_property_comp (hf i) (hg i)

/-- Given a set of arrows in C, indexed by `F : D → arrow C`,
we construct the (non-full) subcategory of `C`
spanned by those morphisms that have the right lifting property relative to all maps
of the form `F i`, where `i` is any element in `D`. -/
def rightLiftingSubcategory (F : D → Arrow C) : Category (RightLiftingSubcat C) where
  Hom := fun X Y => { p : X ⟶ Y // ∀ {i : D}, HasLiftingProperty (F i) (Arrow.mk p) }
  id := fun X => ⟨𝟙 X, id_has_right_lifting_property' X⟩
  comp := fun X Y Z f g => ⟨f.val ≫ g.val, has_right_lifting_property_comp' f.property g.property⟩

end CategoryTheory

