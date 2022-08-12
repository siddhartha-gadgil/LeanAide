/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Topology.Sheaves.SheafCondition.Sites
import Mathbin.CategoryTheory.Sites.Limits
import Mathbin.CategoryTheory.Adjunction.Default
import Mathbin.CategoryTheory.Limits.FunctorCategory

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type v} [SmallCategory J]

namespace Top

instance [HasLimits C] (X : Top) : HasLimits (Presheaf C X) :=
  limits.functor_category_has_limits_of_size.{v, v}

instance [HasColimits C] (X : Top) : HasColimitsOfSize.{v} (Presheaf C X) :=
  limits.functor_category_has_colimits_of_size

instance [HasLimits C] (X : Top) : CreatesLimits (Sheaf.forget C X) :=
  (@createsLimitsOfNatIso _ _ (Presheaf.sheafSpacesEquivSheafSitesInverseForget C X))
    (@CategoryTheory.compCreatesLimits _ _ _ _ _ _
      Sheaf.CategoryTheory.SheafToPresheaf.CategoryTheory.createsLimits.{u, v, v})

instance [HasLimits C] (X : Top) : HasLimitsOfSize.{v} (Sheaf.{v} C X) :=
  has_limits_of_has_limits_creates_limits (Sheaf.forget C X)

theorem is_sheaf_of_is_limit [HasLimits C] {X : Top} (F : J ⥤ Presheaf.{v} C X) (H : ∀ j, (F.obj j).IsSheaf)
    {c : Cone F} (hc : IsLimit c) : c.x.IsSheaf := by
  let F' : J ⥤ sheaf C X := { obj := fun j => ⟨F.obj j, H j⟩, map := F.map }
  let e : F' ⋙ sheaf.forget C X ≅ F :=
    nat_iso.of_components (fun _ => iso.refl _)
      (by
        tidy)
  exact
    presheaf.is_sheaf_of_iso ((is_limit_of_preserves (sheaf.forget C X) (limit.is_limit F')).conePointsIsoOfNatIso hc e)
      (limit F').2

theorem limit_is_sheaf [HasLimits C] {X : Top} (F : J ⥤ Presheaf.{v} C X) (H : ∀ j, (F.obj j).IsSheaf) :
    (limit F).IsSheaf :=
  is_sheaf_of_is_limit F H (limit.isLimit F)

end Top

