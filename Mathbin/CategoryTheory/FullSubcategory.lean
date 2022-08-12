/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import Mathbin.CategoryTheory.Functor.FullyFaithful

/-!
# Induced categories and full subcategories

Given a category `D` and a function `F : C → D `from a type `C` to the
objects of `D`, there is an essentially unique way to give `C` a
category structure such that `F` becomes a fully faithful functor,
namely by taking $$ Hom_C(X, Y) = Hom_D(FX, FY) $$. We call this the
category induced from `D` along `F`.

As a special case, if `C` is a subtype of `D`,
this produces the full subcategory of `D` on the objects belonging to `C`.
In general the induced category is equivalent to the full subcategory of `D` on the
image of `F`.

## Implementation notes

It looks odd to make `D` an explicit argument of `induced_category`,
when it is determined by the argument `F` anyways. The reason to make `D`
explicit is in order to control its syntactic form, so that instances
like `induced_category.has_forget₂` (elsewhere) refer to the correct
form of D. This is used to set up several algebraic categories like

  def CommMon : Type (u+1) := induced_category Mon (bundled.map @comm_monoid.to_monoid)
  -- not `induced_category (bundled monoid) (bundled.map @comm_monoid.to_monoid)`,
  -- even though `Mon = bundled monoid`!
-/


namespace CategoryTheory

universe v v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v} D]

variable (F : C → D)

include F

/-- `induced_category D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint has_inhabited_instance unused_arguments]
def InducedCategory : Type u₁ :=
  C

variable {D}

instance InducedCategory.hasCoeToSort {α : Sort _} [CoeSort D α] : CoeSort (InducedCategory D F) α :=
  ⟨fun c => ↥(F c)⟩

instance InducedCategory.category : Category.{v} (InducedCategory D F) where
  Hom := fun X Y => F X ⟶ F Y
  id := fun X => 𝟙 (F X)
  comp := fun _ _ _ f g => f ≫ g

/-- The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps]
def inducedFunctor : InducedCategory D F ⥤ D where
  obj := F
  map := fun x y f => f

instance InducedCategory.full : Full (inducedFunctor F) where preimage := fun x y f => f

instance InducedCategory.faithful : Faithful (inducedFunctor F) where

end Induced

section FullSubcategory

-- A full subcategory is the special case of an induced category with F = subtype.val.
variable {C : Type u₁} [Category.{v} C]

variable (Z : C → Prop)

/-- The category structure on a subtype; morphisms just ignore the property.

See <https://stacks.math.columbia.edu/tag/001D>. We do not define 'strictly full' subcategories.
-/
instance fullSubcategory : Category.{v} { X : C // Z X } :=
  InducedCategory.category Subtype.val

/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def fullSubcategoryInclusion : { X : C // Z X } ⥤ C :=
  inducedFunctor Subtype.val

@[simp]
theorem fullSubcategoryInclusion.obj {X} : (fullSubcategoryInclusion Z).obj X = X.val :=
  rfl

@[simp]
theorem fullSubcategoryInclusion.map {X Y} {f : X ⟶ Y} : (fullSubcategoryInclusion Z).map f = f :=
  rfl

instance fullSubcategory.full : Full (fullSubcategoryInclusion Z) :=
  InducedCategory.full Subtype.val

instance fullSubcategory.faithful : Faithful (fullSubcategoryInclusion Z) :=
  InducedCategory.faithful Subtype.val

variable {Z} {Z' : C → Prop}

/-- An implication of predicates `Z → Z'` induces a functor between full subcategories. -/
@[simps]
def fullSubcategory.map (h : ∀ ⦃X⦄, Z X → Z' X) : { X // Z X } ⥤ { X // Z' X } where
  obj := fun X => ⟨X.1, h X.2⟩
  map := fun X Y f => f

instance (h : ∀ ⦃X⦄, Z X → Z' X) : Full (fullSubcategory.map h) where preimage := fun X Y f => f

instance (h : ∀ ⦃X⦄, Z X → Z' X) : Faithful (fullSubcategory.map h) where

@[simp]
theorem fullSubcategory.map_inclusion (h : ∀ ⦃X⦄, Z X → Z' X) :
    fullSubcategory.map h ⋙ fullSubcategoryInclusion Z' = fullSubcategoryInclusion Z :=
  rfl

section lift

variable {D : Type u₂} [Category.{v₂} D] (P Q : D → Prop)

/-- A functor which maps objects to objects satisfying a certain property induces a lift through
    the full subcategory of objects satisfying that property. -/
@[simps]
def fullSubcategory.lift (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) : C ⥤ { X // P X } where
  obj := fun X => ⟨F.obj X, hF X⟩
  map := fun X Y f => F.map f

/-- Composing the lift of a functor through a full subcategory with the inclusion yields the
    original functor. Unfortunately, this is not true by definition, so we only get a natural
    isomorphism, but it is pointwise definitionally true, see
    `full_subcategory.inclusion_obj_lift_obj` and `full_subcategory.inclusion_map_lift_map`. -/
def fullSubcategory.liftCompInclusion (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) :
    fullSubcategory.lift P F hF ⋙ fullSubcategoryInclusion P ≅ F :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      simp )

@[simp]
theorem fullSubcategory.inclusion_obj_lift_obj (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) {X : C} :
    (fullSubcategoryInclusion P).obj ((fullSubcategory.lift P F hF).obj X) = F.obj X :=
  rfl

theorem fullSubcategory.inclusion_map_lift_map (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) {X Y : C} (f : X ⟶ Y) :
    (fullSubcategoryInclusion P).map ((fullSubcategory.lift P F hF).map f) = F.map f :=
  rfl

instance (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) [Faithful F] : Faithful (fullSubcategory.lift P F hF) :=
  Faithful.of_comp_iso (fullSubcategory.liftCompInclusion P F hF)

instance (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) [Full F] : Full (fullSubcategory.lift P F hF) :=
  Full.ofCompFaithfulIso (fullSubcategory.liftCompInclusion P F hF)

@[simp]
theorem fullSubcategory.lift_comp_map (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) (h : ∀ ⦃X⦄, P X → Q X) :
    fullSubcategory.lift P F hF ⋙ fullSubcategory.map h = fullSubcategory.lift Q F fun X => h (hF X) :=
  rfl

end lift

end FullSubcategory

end CategoryTheory

