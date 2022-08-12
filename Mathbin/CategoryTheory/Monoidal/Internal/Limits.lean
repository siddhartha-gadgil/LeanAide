/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.Internal.FunctorCategory
import Mathbin.CategoryTheory.Monoidal.Limits
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Limits of monoid objects.

If `C` has limits, so does `Mon_ C`, and the forgetful functor preserves these limits.

(This could potentially replace many individual constructions for concrete categories,
in particular `Mon`, `SemiRing`, `Ring`, and `Algebra R`.)
-/


open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Monoidal

universe v u

noncomputable section

namespace Mon_

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C] [HasLimits C] [MonoidalCategory.{v} C]

/-- We construct the (candidate) limit of a functor `F : J ⥤ Mon_ C`
by interpreting it as a functor `Mon_ (J ⥤ C)`,
and noting that taking limits is a lax monoidal functor,
and hence sends monoid objects to monoid objects.
-/
@[simps]
def limit (F : J ⥤ Mon_ C) : Mon_ C :=
  limLax.mapMon.obj (MonFunctorCategoryEquivalence.inverse.obj F)

/-- Implementation of `Mon_.has_limits`: a limiting cone over a functor `F : J ⥤ Mon_ C`.
-/
@[simps]
def limitCone (F : J ⥤ Mon_ C) : Cone F where
  x := limit F
  π :=
    { app := fun j => { Hom := limit.π (F ⋙ Mon_.forget C) j },
      naturality' := fun j j' f => by
        ext
        exact (limit.cone (F ⋙ Mon_.forget C)).π.naturality f }

/-- The image of the proposed limit cone for `F : J ⥤ Mon_ C` under the forgetful functor
`forget C : Mon_ C ⥤ C` is isomorphic to the limit cone of `F ⋙ forget C`.
-/
def forgetMapConeLimitConeIso (F : J ⥤ Mon_ C) : (forget C).mapCone (limitCone F) ≅ Limit.cone (F ⋙ forget C) :=
  Cones.ext (Iso.refl _) fun j => by
    tidy

/-- Implementation of `Mon_.has_limits`:
the proposed cone over a functor `F : J ⥤ Mon_ C` is a limit cone.
-/
@[simps]
def limitConeIsLimit (F : J ⥤ Mon_ C) : IsLimit (limitCone F) where
  lift := fun s =>
    { Hom := limit.lift (F ⋙ Mon_.forget C) ((Mon_.forget C).mapCone s),
      mul_hom' := by
        ext
        dsimp'
        simp
        dsimp'
        slice_rhs 1 2 => rw [← monoidal_category.tensor_comp, limit.lift_π]dsimp }
  fac' := fun s h => by
    ext
    simp
  uniq' := fun s m w => by
    ext
    dsimp'
    simp only [← Mon_.forget_map, ← limit.lift_π, ← functor.map_cone_π_app]
    exact congr_arg Mon_.Hom.hom (w j)

instance has_limits :
    HasLimits
      (Mon_
        C) where HasLimitsOfShape := fun J 𝒥 =>
    { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } }

instance forgetPreservesLimits :
    PreservesLimits
      (Mon_.forget
        C) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F : J ⥤ Mon_ C =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (is_limit.of_iso_limit (limit.is_limit (F ⋙ Mon_.forget C)) (forget_map_cone_limit_cone_iso F).symm) }

end Mon_

