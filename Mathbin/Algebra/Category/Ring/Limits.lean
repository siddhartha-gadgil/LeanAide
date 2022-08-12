/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Ring.Pi
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.Algebra.Category.Group.Limits
import Mathbin.RingTheory.Subring.Basic

/-!
# The category of (commutative) rings has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


-- We use the following trick a lot of times in this file.
library_note "change elaboration strategy with `by apply`"/--
Some definitions may be extremely slow to elaborate, when the target type to be constructed
is complicated and when the type of the term given in the definition is also complicated and does
not obviously match the target type. In this case, instead of just giving the term, prefixing it
with `by apply` may speed up things considerably as the types are not elaborated in the same order.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

noncomputable section

namespace SemiRing

variable {J : Type v} [SmallCategory J]

instance semiringObj (F : J ⥤ SemiRing.{max v u}) (j) : Semiringₓ ((F ⋙ forget SemiRing).obj j) := by
  change Semiringₓ (F.obj j)
  infer_instance

/-- The flat sections of a functor into `SemiRing` form a subsemiring of all sections.
-/
def sectionsSubsemiring (F : J ⥤ SemiRing.{max v u}) : Subsemiring (∀ j, F.obj j) :=
  { AddMon.sectionsAddSubmonoid (F ⋙ forget₂ SemiRing AddCommMon.{max v u} ⋙ forget₂ AddCommMon AddMon.{max v u}),
    Mon.sectionsSubmonoid (F ⋙ forget₂ SemiRing Mon.{max v u}) with Carrier := (F ⋙ forget SemiRing).sections }

instance limitSemiring (F : J ⥤ SemiRing.{max v u}) : Semiringₓ (Types.limitCone (F ⋙ forget SemiRing.{max v u})).x :=
  (sectionsSubsemiring F).toSemiring

/-- `limit.π (F ⋙ forget SemiRing) j` as a `ring_hom`. -/
def limitπRingHom (F : J ⥤ SemiRing.{max v u}) (j) :
    (Types.limitCone (F ⋙ forget SemiRing)).x →+* (F ⋙ forget SemiRing).obj j :=
  { AddMon.limitπAddMonoidHom (F ⋙ forget₂ SemiRing AddCommMon.{max v u} ⋙ forget₂ AddCommMon AddMon.{max v u}) j,
    Mon.limitπMonoidHom (F ⋙ forget₂ SemiRing Mon.{max v u}) j with
    toFun := (Types.limitCone (F ⋙ forget SemiRing)).π.app j }

namespace HasLimits

/-- Construction of a limit cone in `SemiRing`.
(Internal use only; use the limits API.)
-/
-- The next two definitions are used in the construction of `has_limits SemiRing`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
def limitCone (F : J ⥤ SemiRing.{max v u}) : Cone F where
  x := SemiRing.of (Types.limitCone (F ⋙ forget _)).x
  π :=
    { app := limitπRingHom F,
      naturality' := fun j j' f => RingHom.coe_inj ((Types.limitCone (F ⋙ forget _)).π.naturality f) }

/-- Witness that the limit cone in `SemiRing` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit (F : J ⥤ SemiRing.{max v u}) : IsLimit (limitCone F) := by
  refine'
      is_limit.of_faithful (forget SemiRing) (types.limit_cone_is_limit _) (fun s => ⟨_, _, _, _, _⟩) fun s => rfl <;>
    tidy

end HasLimits

open HasLimits

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
/-- The category of rings has all limits. -/
irreducible_def has_limits_of_size : HasLimitsOfSize.{v} SemiRing.{max v u} :=
  { HasLimitsOfShape := fun J 𝒥 =>
      { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } } }

instance has_limits : HasLimits SemiRing.{u} :=
  SemiRing.has_limits_of_size.{u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommMonPreservesLimitsAux (F : J ⥤ SemiRing.{max v u}) :
    IsLimit ((forget₂ SemiRing AddCommMon).mapCone (limitCone F)) := by
  apply AddCommMon.limitConeIsLimit (F ⋙ forget₂ SemiRing AddCommMon.{max v u})

/-- The forgetful functor from semirings to additive commutative monoids preserves all limits.
-/
instance forget₂AddCommMonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ SemiRing
        AddCommMon.{max v
            u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (forget₂_AddCommMon_preserves_limits_aux F) }

instance forget₂AddCommMonPreservesLimits : PreservesLimits (forget₂ SemiRing AddCommMon.{u}) :=
  SemiRing.forget₂AddCommMonPreservesLimitsOfSize.{u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂MonPreservesLimitsAux (F : J ⥤ SemiRing.{max v u}) :
    IsLimit ((forget₂ SemiRing Mon).mapCone (limitCone F)) := by
  apply Mon.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRing Mon.{max v u})

/-- The forgetful functor from semirings to monoids preserves all limits.
-/
instance forget₂MonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ SemiRing
        Mon.{max v
            u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (forget₂_Mon_preserves_limits_aux F) }

instance forget₂MonPreservesLimits : PreservesLimits (forget₂ SemiRing Mon.{u}) :=
  SemiRing.forget₂MonPreservesLimitsOfSize.{u, u}

/-- The forgetful functor from semirings to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget
        SemiRing.{max v
            u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget _)) }

instance forgetPreservesLimits : PreservesLimits (forget SemiRing.{u}) :=
  SemiRing.forgetPreservesLimitsOfSize.{u, u}

end SemiRing

namespace CommSemiRing

variable {J : Type v} [SmallCategory J]

instance commSemiringObj (F : J ⥤ CommSemiRing.{max v u}) (j) : CommSemiringₓ ((F ⋙ forget CommSemiRing).obj j) := by
  change CommSemiringₓ (F.obj j)
  infer_instance

instance limitCommSemiring (F : J ⥤ CommSemiRing.{max v u}) :
    CommSemiringₓ (Types.limitCone (F ⋙ forget CommSemiRing.{max v u})).x :=
  @Subsemiring.toCommSemiring (∀ j, F.obj j) _
    (SemiRing.sectionsSubsemiring (F ⋙ forget₂ CommSemiRing SemiRing.{max v u}))

/-- We show that the forgetful functor `CommSemiRing ⥤ SemiRing` creates limits.

All we need to do is notice that the limit point has a `comm_semiring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommSemiRing.{max v u}) : CreatesLimit F (forget₂ CommSemiRing SemiRing.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { x := CommSemiRing.of (Types.limitCone (F ⋙ forget _)).x,
          π :=
            { app := by
                apply SemiRing.limitπRingHom (F ⋙ forget₂ CommSemiRing SemiRing.{max v u}),
              naturality' :=
                (SemiRing.HasLimits.limitCone (F ⋙ forget₂ CommSemiRing SemiRing.{max v u})).π.naturality } },
      validLift := by
        apply is_limit.unique_up_to_iso (SemiRing.HasLimits.limitConeIsLimit _) t,
      makesLimit :=
        IsLimit.ofFaithful (forget₂ CommSemiRing SemiRing.{max v u})
          (by
            apply SemiRing.HasLimits.limitConeIsLimit _)
          (fun s => (SemiRing.HasLimits.limitConeIsLimit _).lift ((forget₂ _ SemiRing).mapCone s)) fun s => rfl }

/-- A choice of limit cone for a functor into `CommSemiRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ CommSemiRing.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRing SemiRing.{max v u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ CommSemiRing.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
/-- The category of rings has all limits. -/
irreducible_def has_limits_of_size : HasLimitsOfSize.{v, v} CommSemiRing.{max v u} :=
  { HasLimitsOfShape := fun J 𝒥 =>
      { HasLimit := fun F => has_limit_of_created F (forget₂ CommSemiRing SemiRing.{max v u}) } }

instance has_limits : HasLimits CommSemiRing.{u} :=
  CommSemiRing.has_limits_of_size.{u, u}

/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ CommSemiRing
        SemiRing.{max v u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F => by
        infer_instance }

instance forget₂SemiRingPreservesLimits : PreservesLimits (forget₂ CommSemiRing SemiRing.{u}) :=
  CommSemiRing.forget₂SemiRingPreservesLimitsOfSize.{u, u}

/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget
        CommSemiRing.{max v
            u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F => limits.comp_preserves_limit (forget₂ CommSemiRing SemiRing) (forget SemiRing) }

instance forgetPreservesLimits : PreservesLimits (forget CommSemiRing.{u}) :=
  CommSemiRing.forgetPreservesLimitsOfSize.{u, u}

end CommSemiRing

namespace Ringₓₓ

variable {J : Type v} [SmallCategory J]

instance ringObj (F : J ⥤ Ringₓₓ.{max v u}) (j) : Ringₓ ((F ⋙ forget Ringₓₓ).obj j) := by
  change Ringₓ (F.obj j)
  infer_instance

/-- The flat sections of a functor into `Ring` form a subring of all sections.
-/
def sectionsSubring (F : J ⥤ Ringₓₓ.{max v u}) : Subring (∀ j, F.obj j) :=
  { AddGroupₓₓ.sectionsAddSubgroup
      (F ⋙ forget₂ Ringₓₓ AddCommGroupₓₓ.{max v u} ⋙ forget₂ AddCommGroupₓₓ AddGroupₓₓ.{max v u}),
    SemiRing.sectionsSubsemiring (F ⋙ forget₂ Ringₓₓ SemiRing.{max v u}) with Carrier := (F ⋙ forget Ringₓₓ).sections }

instance limitRing (F : J ⥤ Ringₓₓ.{max v u}) : Ringₓ (Types.limitCone (F ⋙ forget Ringₓₓ.{max v u})).x :=
  (sectionsSubring F).toRing

/-- We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ Ringₓₓ.{max v u}) : CreatesLimit F (forget₂ Ringₓₓ SemiRing.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { x := Ringₓₓ.of (Types.limitCone (F ⋙ forget _)).x,
          π :=
            { app := by
                apply SemiRing.limitπRingHom (F ⋙ forget₂ Ringₓₓ SemiRing.{max v u}),
              naturality' := (SemiRing.HasLimits.limitCone (F ⋙ forget₂ Ringₓₓ SemiRing.{max v u})).π.naturality } },
      validLift := by
        apply is_limit.unique_up_to_iso (SemiRing.HasLimits.limitConeIsLimit _) t,
      makesLimit :=
        IsLimit.ofFaithful (forget₂ Ringₓₓ SemiRing.{max v u})
          (by
            apply SemiRing.HasLimits.limitConeIsLimit _)
          (fun s => _) fun s => rfl }

/-- A choice of limit cone for a functor into `Ring`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ Ringₓₓ.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ Ringₓₓ SemiRing.{max v u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ Ringₓₓ.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
/-- The category of rings has all limits. -/
irreducible_def has_limits_of_size : HasLimitsOfSize.{v, v} Ringₓₓ.{max v u} :=
  { HasLimitsOfShape := fun J 𝒥 => { HasLimit := fun F => has_limit_of_created F (forget₂ Ringₓₓ SemiRing.{max v u}) } }

instance has_limits : HasLimits Ringₓₓ.{u} :=
  Ringₓₓ.has_limits_of_size.{u, u}

/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ Ringₓₓ SemiRing.{max v u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F => by
        infer_instance }

instance forget₂SemiRingPreservesLimits : PreservesLimits (forget₂ Ringₓₓ SemiRing.{u}) :=
  Ringₓₓ.forget₂SemiRingPreservesLimitsOfSize.{u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroupPreservesLimitsAux (F : J ⥤ Ringₓₓ.{max v u}) :
    IsLimit ((forget₂ Ringₓₓ AddCommGroupₓₓ).mapCone (limitCone F)) := by
  apply AddCommGroupₓₓ.limitConeIsLimit (F ⋙ forget₂ Ringₓₓ AddCommGroupₓₓ.{max v u})

/-- The forgetful functor from rings to additive commutative groups preserves all limits.
-/
instance forget₂AddCommGroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ Ringₓₓ
        AddCommGroupₓₓ.{max v
            u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (forget₂_AddCommGroup_preserves_limits_aux F) }

instance forget₂AddCommGroupPreservesLimits : PreservesLimits (forget₂ Ringₓₓ AddCommGroupₓₓ.{u}) :=
  Ringₓₓ.forget₂AddCommGroupPreservesLimitsOfSize.{u, u}

/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget
        Ringₓₓ.{max v
            u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F => limits.comp_preserves_limit (forget₂ Ringₓₓ SemiRing) (forget SemiRing.{max v u}) }

instance forgetPreservesLimits : PreservesLimits (forget Ringₓₓ.{u}) :=
  Ringₓₓ.forgetPreservesLimitsOfSize.{u, u}

end Ringₓₓ

namespace CommRingₓₓ

variable {J : Type v} [SmallCategory J]

instance commRingObj (F : J ⥤ CommRingₓₓ.{max v u}) (j) : CommRingₓ ((F ⋙ forget CommRingₓₓ).obj j) := by
  change CommRingₓ (F.obj j)
  infer_instance

instance limitCommRing (F : J ⥤ CommRingₓₓ.{max v u}) :
    CommRingₓ (Types.limitCone (F ⋙ forget CommRingₓₓ.{max v u})).x :=
  @Subring.toCommRing (∀ j, F.obj j) _ (Ringₓₓ.sectionsSubring (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{max v u}))

/-- We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `comm_ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommRingₓₓ.{max v u}) : CreatesLimit F (forget₂ CommRingₓₓ Ringₓₓ.{max v u}) :=
  /-
    A terse solution here would be
    ```
    creates_limit_of_fully_faithful_of_iso (CommRing.of (limit (F ⋙ forget _))) (iso.refl _)
    ```
    but it seems this would introduce additional identity morphisms in `limit.π`.
    -/
    createsLimitOfReflectsIso
    fun c' t =>
    { liftedCone :=
        { x := CommRingₓₓ.of (Types.limitCone (F ⋙ forget _)).x,
          π :=
            { app := by
                apply
                  SemiRing.limitπRingHom (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{max v u} ⋙ forget₂ Ringₓₓ SemiRing.{max v u}),
              naturality' :=
                (SemiRing.HasLimits.limitCone
                      (F ⋙ forget₂ _ Ringₓₓ.{max v u} ⋙ forget₂ _ SemiRing.{max v u})).π.naturality } },
      validLift := by
        apply is_limit.unique_up_to_iso (Ringₓₓ.limitConeIsLimit _) t,
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ Ringₓₓ.{max v u})
          (by
            apply Ringₓₓ.limitConeIsLimit (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{max v u}))
          (fun s => (Ringₓₓ.limitConeIsLimit _).lift ((forget₂ _ Ringₓₓ.{max v u}).mapCone s)) fun s => rfl }

/-- A choice of limit cone for a functor into `CommRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ CommRingₓₓ.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{max v u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ CommRingₓₓ.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
/-- The category of commutative rings has all limits. -/
irreducible_def has_limits_of_size : HasLimitsOfSize.{v, v} CommRingₓₓ.{max v u} :=
  { HasLimitsOfShape := fun J 𝒥 =>
      { HasLimit := fun F => has_limit_of_created F (forget₂ CommRingₓₓ Ringₓₓ.{max v u}) } }

instance has_limits : HasLimits CommRingₓₓ.{u} :=
  CommRingₓₓ.has_limits_of_size.{u, u}

/-- The forgetful functor from commutative rings to rings preserves all limits.
(That is, the underlying rings could have been computed instead as limits in the category of rings.)
-/
instance forget₂RingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ CommRingₓₓ Ringₓₓ.{max v u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F => by
        infer_instance }

instance forget₂RingPreservesLimits : PreservesLimits (forget₂ CommRingₓₓ Ringₓₓ.{u}) :=
  CommRingₓₓ.forget₂RingPreservesLimitsOfSize.{u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂CommSemiRingPreservesLimitsAux (F : J ⥤ CommRingₓₓ.{max v u}) :
    IsLimit ((forget₂ CommRingₓₓ CommSemiRing).mapCone (limitCone F)) := by
  apply CommSemiRing.limitConeIsLimit (F ⋙ forget₂ CommRingₓₓ CommSemiRing.{max v u})

/-- The forgetful functor from commutative rings to commutative semirings preserves all limits.
(That is, the underlying commutative semirings could have been computed instead as limits
in the category of commutative semirings.)
-/
instance forget₂CommSemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ CommRingₓₓ
        CommSemiRing.{max v
            u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (forget₂_CommSemiRing_preserves_limits_aux F) }

instance forget₂CommSemiRingPreservesLimits : PreservesLimits (forget₂ CommRingₓₓ CommSemiRing.{u}) :=
  CommRingₓₓ.forget₂CommSemiRingPreservesLimitsOfSize.{u, u}

/-- The forgetful functor from commutative rings to types preserves all limits.
(That is, the underlying types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget
        CommRingₓₓ.{max v
            u}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F => limits.comp_preserves_limit (forget₂ CommRingₓₓ Ringₓₓ) (forget Ringₓₓ) }

instance forgetPreservesLimits : PreservesLimits (forget CommRingₓₓ.{u}) :=
  CommRingₓₓ.forgetPreservesLimitsOfSize.{u, u}

end CommRingₓₓ

