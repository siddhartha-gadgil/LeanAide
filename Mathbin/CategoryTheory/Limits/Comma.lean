/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Creates
import Mathbin.CategoryTheory.Limits.Unit
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.StructuredArrow
import Mathbin.CategoryTheory.Arrow

/-!
# Limits and colimits in comma categories

We build limits in the comma category `comma L R` provided that the two source categories have
limits and `R` preserves them.
This is used to construct limits in the arrow category, structured arrow category and under
category, and show that the appropriate forgetful functors create limits.

The duals of all the above are also given.
-/


namespace CategoryTheory

open Category Limits

universe v u₁ u₂ u₃

variable {J : Type v} [SmallCategory J]

variable {A : Type u₁} [Category.{v} A]

variable {B : Type u₂} [Category.{v} B]

variable {T : Type u₃} [Category.{v} T]

namespace Comma

variable {L : A ⥤ T} {R : B ⥤ T}

variable (F : J ⥤ Comma L R)

/-- (Implementation). An auxiliary cone which is useful in order to construct limits
in the comma category. -/
@[simps]
def limitAuxiliaryCone (c₁ : Cone (F ⋙ fst L R)) : Cone ((F ⋙ snd L R) ⋙ R) :=
  (Cones.postcompose (whiskerLeft F (Comma.natTrans L R) : _)).obj (L.mapCone c₁)

/-- If `R` preserves the appropriate limit, then given a cone for `F ⋙ fst L R : J ⥤ L` and a
limit cone for `F ⋙ snd L R : J ⥤ R` we can build a cone for `F` which will turn out to be a limit
cone.
-/
@[simps]
def coneOfPreserves [PreservesLimit (F ⋙ snd L R) R] (c₁ : Cone (F ⋙ fst L R)) {c₂ : Cone (F ⋙ snd L R)}
    (t₂ : IsLimit c₂) : Cone F where
  x := { left := c₁.x, right := c₂.x, Hom := (isLimitOfPreserves R t₂).lift (limitAuxiliaryCone _ c₁) }
  π :=
    { app := fun j =>
        { left := c₁.π.app j, right := c₂.π.app j,
          w' := ((isLimitOfPreserves R t₂).fac (limitAuxiliaryCone F c₁) j).symm },
      naturality' := fun j₁ j₂ t => by
        ext <;> dsimp' <;> simp [c₁.w t, c₂.w t] }

/-- Provided that `R` preserves the appropriate limit, then the cone in `cone_of_preserves` is a
limit. -/
def coneOfPreservesIsLimit [PreservesLimit (F ⋙ snd L R) R] {c₁ : Cone (F ⋙ fst L R)} (t₁ : IsLimit c₁)
    {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) : IsLimit (coneOfPreserves F c₁ t₂) where
  lift := fun s =>
    { left := t₁.lift ((fst L R).mapCone s), right := t₂.lift ((snd L R).mapCone s),
      w' :=
        (isLimitOfPreserves R t₂).hom_ext fun j => by
          rw [cone_of_preserves_X_hom, assoc, assoc, (is_limit_of_preserves R t₂).fac, limit_auxiliary_cone_π_app, ←
            L.map_comp_assoc, t₁.fac, R.map_cone_π_app, ← R.map_comp, t₂.fac]
          exact (s.π.app j).w }
  uniq' := fun s m w =>
    CommaMorphism.ext _ _
      (t₁.uniq ((fst L R).mapCone s) _ fun j => by
        simp [w])
      (t₂.uniq ((snd L R).mapCone s) _ fun j => by
        simp [w])

/-- (Implementation). An auxiliary cocone which is useful in order to construct colimits
in the comma category. -/
@[simps]
def colimitAuxiliaryCocone (c₂ : Cocone (F ⋙ snd L R)) : Cocone ((F ⋙ fst L R) ⋙ L) :=
  (Cocones.precompose (whiskerLeft F (Comma.natTrans L R) : _)).obj (R.mapCocone c₂)

/-- If `L` preserves the appropriate colimit, then given a colimit cocone for `F ⋙ fst L R : J ⥤ L` and
a cocone for `F ⋙ snd L R : J ⥤ R` we can build a cocone for `F` which will turn out to be a
colimit cocone.
-/
@[simps]
def coconeOfPreserves [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)} (t₁ : IsColimit c₁)
    (c₂ : Cocone (F ⋙ snd L R)) : Cocone F where
  x := { left := c₁.x, right := c₂.x, Hom := (isColimitOfPreserves L t₁).desc (colimitAuxiliaryCocone _ c₂) }
  ι :=
    { app := fun j =>
        { left := c₁.ι.app j, right := c₂.ι.app j,
          w' := (isColimitOfPreserves L t₁).fac (colimitAuxiliaryCocone _ c₂) j },
      naturality' := fun j₁ j₂ t => by
        ext <;> dsimp' <;> simp [c₁.w t, c₂.w t] }

/-- Provided that `L` preserves the appropriate colimit, then the cocone in `cocone_of_preserves` is
a colimit. -/
def coconeOfPreservesIsColimit [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)} (t₁ : IsColimit c₁)
    {c₂ : Cocone (F ⋙ snd L R)} (t₂ : IsColimit c₂) : IsColimit (coconeOfPreserves F t₁ c₂) where
  desc := fun s =>
    { left := t₁.desc ((fst L R).mapCocone s), right := t₂.desc ((snd L R).mapCocone s),
      w' :=
        (isColimitOfPreserves L t₁).hom_ext fun j => by
          rw [cocone_of_preserves_X_hom, (is_colimit_of_preserves L t₁).fac_assoc, colimit_auxiliary_cocone_ι_app,
            assoc, ← R.map_comp, t₂.fac, L.map_cocone_ι_app, ← L.map_comp_assoc, t₁.fac]
          exact (s.ι.app j).w }
  uniq' := fun s m w =>
    CommaMorphism.ext _ _
      (t₁.uniq ((fst L R).mapCocone s) _
        (by
          simp [w]))
      (t₂.uniq ((snd L R).mapCocone s) _
        (by
          simp [w]))

instance has_limit (F : J ⥤ Comma L R) [HasLimit (F ⋙ fst L R)] [HasLimit (F ⋙ snd L R)]
    [PreservesLimit (F ⋙ snd L R) R] : HasLimit F :=
  HasLimit.mk ⟨_, coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)⟩

instance has_limits_of_shape [HasLimitsOfShape J A] [HasLimitsOfShape J B] [PreservesLimitsOfShape J R] :
    HasLimitsOfShape J (Comma L R) where

instance has_limits [HasLimits A] [HasLimits B] [PreservesLimits R] : HasLimits (Comma L R) :=
  ⟨inferInstance⟩

instance has_colimit (F : J ⥤ Comma L R) [HasColimit (F ⋙ fst L R)] [HasColimit (F ⋙ snd L R)]
    [PreservesColimit (F ⋙ fst L R) L] : HasColimit F :=
  HasColimit.mk ⟨_, coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _)⟩

instance has_colimits_of_shape [HasColimitsOfShape J A] [HasColimitsOfShape J B] [PreservesColimitsOfShape J L] :
    HasColimitsOfShape J (Comma L R) where

instance has_colimits [HasColimits A] [HasColimits B] [PreservesColimits L] : HasColimits (Comma L R) :=
  ⟨inferInstance⟩

end Comma

namespace Arrow

instance has_limit (F : J ⥤ Arrow T) [i₁ : HasLimit (F ⋙ left_func)] [i₂ : HasLimit (F ⋙ right_func)] : HasLimit F :=
  @Comma.has_limit _ _ _ _ _ i₁ i₂ _

instance has_limits_of_shape [HasLimitsOfShape J T] : HasLimitsOfShape J (Arrow T) where

instance has_limits [HasLimits T] : HasLimits (Arrow T) :=
  ⟨inferInstance⟩

instance has_colimit (F : J ⥤ Arrow T) [i₁ : HasColimit (F ⋙ left_func)] [i₂ : HasColimit (F ⋙ right_func)] :
    HasColimit F :=
  @Comma.has_colimit _ _ _ _ _ i₁ i₂ _

instance has_colimits_of_shape [HasColimitsOfShape J T] : HasColimitsOfShape J (Arrow T) where

instance has_colimits [HasColimits T] : HasColimits (Arrow T) :=
  ⟨inferInstance⟩

end Arrow

namespace StructuredArrow

variable {X : T} {G : A ⥤ T} (F : J ⥤ StructuredArrow X G)

instance has_limit [i₁ : HasLimit (F ⋙ proj X G)] [i₂ : PreservesLimit (F ⋙ proj X G) G] : HasLimit F :=
  @Comma.has_limit _ _ _ _ _ _ i₁ i₂

instance has_limits_of_shape [HasLimitsOfShape J A] [PreservesLimitsOfShape J G] :
    HasLimitsOfShape J (StructuredArrow X G) where

instance has_limits [HasLimits A] [PreservesLimits G] : HasLimits (StructuredArrow X G) :=
  ⟨inferInstance⟩

noncomputable instance createsLimit [i : PreservesLimit (F ⋙ proj X G) G] : CreatesLimit F (proj X G) :=
  creates_limit_of_reflects_iso fun c t =>
    { liftedCone := @Comma.coneOfPreserves _ _ _ _ _ i punitCone t,
      makesLimit := Comma.coneOfPreservesIsLimit _ punitConeIsLimit _,
      validLift := (Cones.ext (Iso.refl _)) fun j => (id_comp _).symm }

noncomputable instance createsLimitsOfShape [PreservesLimitsOfShape J G] : CreatesLimitsOfShape J (proj X G) where

noncomputable instance createsLimits [PreservesLimits G] : CreatesLimits (proj X G : _) :=
  ⟨⟩

end StructuredArrow

namespace CostructuredArrow

variable {G : A ⥤ T} {X : T} (F : J ⥤ CostructuredArrow G X)

instance has_colimit [i₁ : HasColimit (F ⋙ proj G X)] [i₂ : PreservesColimit (F ⋙ proj G X) G] : HasColimit F :=
  @Comma.has_colimit _ _ _ _ _ i₁ _ i₂

instance has_colimits_of_shape [HasColimitsOfShape J A] [PreservesColimitsOfShape J G] :
    HasColimitsOfShape J (CostructuredArrow G X) where

instance has_colimits [HasColimits A] [PreservesColimits G] : HasColimits (CostructuredArrow G X) :=
  ⟨inferInstance⟩

noncomputable instance createsColimit [i : PreservesColimit (F ⋙ proj G X) G] : CreatesColimit F (proj G X) :=
  creates_colimit_of_reflects_iso fun c t =>
    { liftedCocone := @Comma.coconeOfPreserves _ _ _ _ _ i t punitCocone,
      makesColimit := Comma.coconeOfPreservesIsColimit _ _ punitCoconeIsColimit,
      validLift := (Cocones.ext (Iso.refl _)) fun j => comp_id _ }

noncomputable instance createsColimitsOfShape [PreservesColimitsOfShape J G] : CreatesColimitsOfShape J (proj G X) where

noncomputable instance createsColimits [PreservesColimits G] : CreatesColimits (proj G X : _) :=
  ⟨⟩

end CostructuredArrow

end CategoryTheory

