/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Pi.Basic
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# Limits in the category of indexed families of objects.

Given a functor `F : J ⥤ Π i, C i` into a category of indexed families,
1. we can assemble a collection of cones over `F ⋙ pi.eval C i` into a cone over `F`
2. if all those cones are limit cones, the assembled cone is a limit cone, and
3. if we have limits for each of `F ⋙ pi.eval C i`, we can produce a
   `has_limit F` instance
-/


open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.pi

universe v₁ v₂ u₁ u₂

variable {I : Type v₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]

variable {J : Type v₁} [SmallCategory J]

variable {F : J ⥤ ∀ i, C i}

/-- A cone over `F : J ⥤ Π i, C i` has as its components cones over each of the `F ⋙ pi.eval C i`.
-/
def coneCompEval (c : Cone F) (i : I) : Cone (F ⋙ pi.eval C i) where
  x := c.x i
  π := { app := fun j => c.π.app j i, naturality' := fun j j' f => congr_fun (c.π.naturality f) i }

/-- A cocone over `F : J ⥤ Π i, C i` has as its components cocones over each of the `F ⋙ pi.eval C i`.
-/
def coconeCompEval (c : Cocone F) (i : I) : Cocone (F ⋙ pi.eval C i) where
  x := c.x i
  ι := { app := fun j => c.ι.app j i, naturality' := fun j j' f => congr_fun (c.ι.naturality f) i }

/-- Given a family of cones over the `F ⋙ pi.eval C i`, we can assemble these together as a `cone F`.
-/
def coneOfConeCompEval (c : ∀ i, Cone (F ⋙ pi.eval C i)) : Cone F where
  x := fun i => (c i).x
  π :=
    { app := fun j i => (c i).π.app j,
      naturality' := fun j j' f => by
        ext i
        exact (c i).π.naturality f }

/-- Given a family of cocones over the `F ⋙ pi.eval C i`,
we can assemble these together as a `cocone F`.
-/
def coconeOfCoconeCompEval (c : ∀ i, Cocone (F ⋙ pi.eval C i)) : Cocone F where
  x := fun i => (c i).x
  ι :=
    { app := fun j i => (c i).ι.app j,
      naturality' := fun j j' f => by
        ext i
        exact (c i).ι.naturality f }

/-- Given a family of limit cones over the `F ⋙ pi.eval C i`,
assembling them together as a `cone F` produces a limit cone.
-/
def coneOfConeEvalIsLimit {c : ∀ i, Cone (F ⋙ pi.eval C i)} (P : ∀ i, IsLimit (c i)) :
    IsLimit (coneOfConeCompEval c) where
  lift := fun s i => (P i).lift (coneCompEval s i)
  fac' := fun s j => by
    ext i
    exact (P i).fac (cone_comp_eval s i) j
  uniq' := fun s m w => by
    ext i
    exact (P i).uniq (cone_comp_eval s i) (m i) fun j => congr_fun (w j) i

/-- Given a family of colimit cocones over the `F ⋙ pi.eval C i`,
assembling them together as a `cocone F` produces a colimit cocone.
-/
def coconeOfCoconeEvalIsColimit {c : ∀ i, Cocone (F ⋙ pi.eval C i)} (P : ∀ i, IsColimit (c i)) :
    IsColimit (coconeOfCoconeCompEval c) where
  desc := fun s i => (P i).desc (coconeCompEval s i)
  fac' := fun s j => by
    ext i
    exact (P i).fac (cocone_comp_eval s i) j
  uniq' := fun s m w => by
    ext i
    exact (P i).uniq (cocone_comp_eval s i) (m i) fun j => congr_fun (w j) i

section

variable [∀ i, HasLimit (F ⋙ pi.eval C i)]

/-- If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and we have limits for each of the `F ⋙ pi.eval C i`,
then `F` has a limit.
-/
theorem has_limit_of_has_limit_comp_eval : HasLimit F :=
  HasLimit.mk
    { Cone := coneOfConeCompEval fun i => Limit.cone _, IsLimit := coneOfConeEvalIsLimit fun i => limit.isLimit _ }

end

section

variable [∀ i, HasColimit (F ⋙ pi.eval C i)]

/-- If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and colimits exist for each of the `F ⋙ pi.eval C i`,
there is a colimit for `F`.
-/
theorem has_colimit_of_has_colimit_comp_eval : HasColimit F :=
  HasColimit.mk
    { Cocone := coconeOfCoconeCompEval fun i => Colimit.cocone _,
      IsColimit := coconeOfCoconeEvalIsColimit fun i => colimit.isColimit _ }

end

/-!
As an example, we can use this to construct particular shapes of limits
in a category of indexed families.

With the addition of
`import category_theory.limits.shapes.types`
we can use:
```
local attribute [instance] has_limit_of_has_limit_comp_eval
example : has_binary_products (I → Type v₁) := ⟨by apply_instance⟩
```
-/


end CategoryTheory.pi

