/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.CategoryTheory.SingleObj
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Pi.Basic
import Mathbin.CategoryTheory.Limits.IsLimit

/-!
# Category of groupoids

This file contains the definition of the category `Groupoid` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : Groupoid ⥤ Type`
and `forget_to_Cat : Groupoid ⥤ Cat`.

## Implementation notes

Though `Groupoid` is not a concrete category, we use `bundled` to define
its carrier type.
-/


universe v u

namespace CategoryTheory

/-- Category of groupoids -/
-- intended to be used with explicit universe parameters
@[nolint check_univs]
def Groupoidₓ :=
  Bundled Groupoid.{v, u}

namespace Groupoid

instance : Inhabited Groupoidₓ :=
  ⟨Bundled.of (SingleObj PUnit)⟩

instance str (C : Groupoidₓ.{v, u}) : Groupoid.{v, u} C.α :=
  C.str

instance : CoeSort Groupoidₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `Groupoid` from the underlying type and the typeclass. -/
def of (C : Type u) [Groupoid.{v} C] : Groupoidₓ.{v, u} :=
  Bundled.of C

@[simp]
theorem coe_of (C : Type u) [Groupoid C] : (of C : Type u) = C :=
  rfl

/-- Category structure on `Groupoid` -/
instance category : LargeCategory.{max v u} Groupoidₓ.{v, u} where
  Hom := fun C D => C ⥤ D
  id := fun C => 𝟭 C
  comp := fun C D E F G => F ⋙ G
  id_comp' := fun C D F => by
    cases F <;> rfl
  comp_id' := fun C D F => by
    cases F <;> rfl
  assoc' := by
    intros <;> rfl

/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Groupoid.{v, u} ⥤ Type u where
  obj := Bundled.α
  map := fun C D F => F.obj

/-- Forgetting functor to `Cat` -/
def forgetToCat : Groupoid.{v, u} ⥤ Cat.{v, u} where
  obj := fun C => Cat.of C
  map := fun C D => id

instance forgetToCatFull : Full forgetToCat where Preimage := fun C D => id

instance forget_to_Cat_faithful : Faithful forgetToCat where

/-- Convert arrows in the category of groupoids to functors,
which sometimes helps in applying simp lemmas -/
theorem hom_to_functor {C D E : Groupoidₓ.{v, u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g :=
  rfl

/-- Converts identity in the category of groupoids to the functor identity -/
theorem id_to_functor {C : Groupoidₓ.{v, u}} : 𝟭 C = 𝟙 C :=
  rfl

section Products

attribute [local tidy] tactic.discrete_cases

/-- Construct the product over an indexed family of groupoids, as a fan. -/
def piLimitFan ⦃J : Type u⦄ (F : J → Groupoidₓ.{u, u}) : Limits.Fan F :=
  Limits.Fan.mk (@of (∀ j : J, F j) _) fun j => CategoryTheory.pi.eval _ j

/-- The product fan over an indexed family of groupoids, is a limit cone. -/
def piLimitFanIsLimit ⦃J : Type u⦄ (F : J → Groupoidₓ.{u, u}) : Limits.IsLimit (piLimitFan F) :=
  Limits.mkFanLimit (piLimitFan F) (fun s => Functor.pi' fun j => s.proj j)
    (by
      intros
      dunfold pi_limit_fan
      simp [← hom_to_functor])
    (by
      intro s m w
      apply functor.pi_ext
      intro j
      specialize w j
      simpa)

instance has_pi : Limits.HasProducts Groupoidₓ.{u, u} :=
  Limits.has_products_of_limit_fans piLimitFan piLimitFanIsLimit

/-- The product of a family of groupoids is isomorphic
to the product object in the category of Groupoids -/
noncomputable def piIsoPi (J : Type u) (f : J → Groupoidₓ.{u, u}) : @of (∀ j, f j) _ ≅ ∏ f :=
  Limits.IsLimit.conePointUniqueUpToIso (piLimitFanIsLimit f) (Limits.limit.isLimit (Discrete.functor f))

@[simp]
theorem pi_iso_pi_hom_π (J : Type u) (f : J → Groupoidₓ.{u, u}) (j : J) :
    (piIsoPi J f).Hom ≫ Limits.Pi.π f j = CategoryTheory.pi.eval _ j := by
  simp [← pi_iso_pi]
  rfl

end Products

end Groupoid

end CategoryTheory

