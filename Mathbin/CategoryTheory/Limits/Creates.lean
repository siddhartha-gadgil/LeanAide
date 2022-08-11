/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Creating (co)limits

We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.
-/


open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

universe w' w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

section Creates

variable {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

/-- Define the lift of a cone: For a cone `c` for `K ⋙ F`, give a cone for `K`
which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of limits:
every limit cone has a lift.

Note this definition is really only useful when `c` is a limit already.
-/
structure LiftableCone (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) where
  liftedCone : Cone K
  validLift : F.mapCone lifted_cone ≅ c

/-- Define the lift of a cocone: For a cocone `c` for `K ⋙ F`, give a cocone for
`K` which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of colimits:
every limit cocone has a lift.

Note this definition is really only useful when `c` is a colimit already.
-/
structure LiftableCocone (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) where
  liftedCocone : Cocone K
  validLift : F.mapCocone lifted_cocone ≅ c

/-- Definition 3.3.1 of [Riehl].
We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cone is
a limit - see `creates_limit_of_reflects_iso`.
-/
class CreatesLimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsLimit K F where
  lifts : ∀ c, IsLimit c → LiftableCone K F c

/-- `F` creates limits of shape `J` if `F` creates the limit of any diagram
`K : J ⥤ C`.
-/
class CreatesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesLimit : ∀ {K : J ⥤ C}, CreatesLimit K F := by
    run_tac
      tactic.apply_instance

/-- `F` creates limits if it creates limits of shape `J` for any `J`. -/
-- This should be used with explicit universe variables.
@[nolint check_univs]
class CreatesLimitsOfSize (F : C ⥤ D) where
  CreatesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesLimitsOfShape J F := by
    run_tac
      tactic.apply_instance

/-- `F` creates small limits if it creates limits of shape `J` for any small `J`. -/
abbrev CreatesLimits (F : C ⥤ D) :=
  CreatesLimitsOfSize.{v₂, v₂} F

/-- Dual of definition 3.3.1 of [Riehl].
We say that `F` creates colimits of `K` if, given any limit cocone `c` for
`K ⋙ F` (i.e. below) we can lift it to a cocone "above", and further that `F`
reflects limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cocone is
a limit - see `creates_limit_of_reflects_iso`.
-/
class CreatesColimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsColimit K F where
  lifts : ∀ c, IsColimit c → LiftableCocone K F c

/-- `F` creates colimits of shape `J` if `F` creates the colimit of any diagram
`K : J ⥤ C`.
-/
class CreatesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesColimit : ∀ {K : J ⥤ C}, CreatesColimit K F := by
    run_tac
      tactic.apply_instance

/-- `F` creates colimits if it creates colimits of shape `J` for any small `J`. -/
-- This should be used with explicit universe variables.
@[nolint check_univs]
class CreatesColimitsOfSize (F : C ⥤ D) where
  CreatesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesColimitsOfShape J F := by
    run_tac
      tactic.apply_instance

/-- `F` creates small colimits if it creates colimits of shape `J` for any small `J`. -/
abbrev CreatesColimits (F : C ⥤ D) :=
  CreatesColimitsOfSize.{v₂, v₂} F

attribute [instance]
  creates_limits_of_shape.creates_limit creates_limits_of_size.creates_limits_of_shape creates_colimits_of_shape.creates_colimit creates_colimits_of_size.creates_colimits_of_shape

/-- `lift_limit t` is the cone for `K` given by lifting the limit `t` for `K ⋙ F`. -/
-- see Note [lower instance priority]
-- Interface to the `creates_limit` class.
def liftLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) : Cone K :=
  (CreatesLimit.lifts c t).liftedCone

/-- The lifted cone has an image isomorphic to the original cone. -/
def liftedLimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) :
    F.mapCone (liftLimit t) ≅ c :=
  (CreatesLimit.lifts c t).validLift

/-- The lifted cone is a limit. -/
def liftedLimitIsLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) :
    IsLimit (liftLimit t) :=
  ReflectsLimit.reflects (IsLimit.ofIsoLimit t (liftedLimitMapsToOriginal t).symm)

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem has_limit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K :=
  HasLimit.mk { Cone := liftLimit (limit.isLimit (K ⋙ F)), IsLimit := liftedLimitIsLimit _ }

/-- If `F` creates limits of shape `J`, and `D` has limits of shape `J`, then
`C` has limits of shape `J`.
-/
theorem has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape (F : C ⥤ D) [HasLimitsOfShape J D]
    [CreatesLimitsOfShape J F] : HasLimitsOfShape J C :=
  ⟨fun G => has_limit_of_created G F⟩

/-- If `F` creates limits, and `D` has all limits, then `C` has all limits. -/
theorem has_limits_of_has_limits_creates_limits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D]
    [CreatesLimitsOfSize.{w, w'} F] : HasLimitsOfSize.{w, w'} C :=
  ⟨fun J I => has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape F⟩

/-- `lift_colimit t` is the cocone for `K` given by lifting the colimit `t` for `K ⋙ F`. -/
-- Interface to the `creates_colimit` class.
def liftColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)} (t : IsColimit c) : Cocone K :=
  (CreatesColimit.lifts c t).liftedCocone

/-- The lifted cocone has an image isomorphic to the original cocone. -/
def liftedColimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)} (t : IsColimit c) :
    F.mapCocone (liftColimit t) ≅ c :=
  (CreatesColimit.lifts c t).validLift

/-- The lifted cocone is a colimit. -/
def liftedColimitIsColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)} (t : IsColimit c) :
    IsColimit (liftColimit t) :=
  ReflectsColimit.reflects (IsColimit.ofIsoColimit t (liftedColimitMapsToOriginal t).symm)

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem has_colimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] : HasColimit K :=
  HasColimit.mk { Cocone := liftColimit (colimit.isColimit (K ⋙ F)), IsColimit := liftedColimitIsColimit _ }

/-- If `F` creates colimits of shape `J`, and `D` has colimits of shape `J`, then
`C` has colimits of shape `J`.
-/
theorem has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape (F : C ⥤ D) [HasColimitsOfShape J D]
    [CreatesColimitsOfShape J F] : HasColimitsOfShape J C :=
  ⟨fun G => has_colimit_of_created G F⟩

/-- If `F` creates colimits, and `D` has all colimits, then `C` has all colimits. -/
theorem has_colimits_of_has_colimits_creates_colimits (F : C ⥤ D) [HasColimitsOfSize.{w, w'} D]
    [CreatesColimitsOfSize.{w, w'} F] : HasColimitsOfSize.{w, w'} C :=
  ⟨fun J I => has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape F⟩

instance (priority := 10) reflectsLimitsOfShapeOfCreatesLimitsOfShape (F : C ⥤ D) [CreatesLimitsOfShape J F] :
    ReflectsLimitsOfShape J F where

instance (priority := 10) reflectsLimitsOfCreatesLimits (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F where

instance (priority := 10) reflectsColimitsOfShapeOfCreatesColimitsOfShape (F : C ⥤ D) [CreatesColimitsOfShape J F] :
    ReflectsColimitsOfShape J F where

instance (priority := 10) reflectsColimitsOfCreatesColimits (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F where

/-- A helper to show a functor creates limits. In particular, if we can show
that for any limit cone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates limits.
Usually, `F` creating limits says that _any_ lift of `c` is a limit, but
here we only need to show that our particular lift of `c` is a limit.
-/
structure LiftsToLimit (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) (t : IsLimit c) extends LiftableCone K F c where
  makesLimit : IsLimit lifted_cone

/-- A helper to show a functor creates colimits. In particular, if we can show
that for any limit cocone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates colimits.
Usually, `F` creating colimits says that _any_ lift of `c` is a colimit, but
here we only need to show that our particular lift of `c` is a colimit.
-/
structure LiftsToColimit (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) (t : IsColimit c) extends
  LiftableCocone K F c where
  makesColimit : IsColimit lifted_cocone

/-- If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
In particular here we don't need to assume that F reflects limits.
-/
def createsLimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [ReflectsIsomorphisms F] (h : ∀ c t, LiftsToLimit K F c t) :
    CreatesLimit K F where
  lifts := fun c t => (h c t).toLiftableCone
  toReflectsLimit :=
    { reflects := fun (d : Cone K) (hd : IsLimit (F.mapCone d)) => by
        let d' : cone K := (h (F.map_cone d) hd).toLiftableCone.liftedCone
        let i : F.map_cone d' ≅ F.map_cone d := (h (F.map_cone d) hd).toLiftableCone.validLift
        let hd' : is_limit d' := (h (F.map_cone d) hd).makesLimit
        let f : d ⟶ d' := hd'.lift_cone_morphism d
        have : (cones.functoriality K F).map f = i.inv := (hd.of_iso_limit i.symm).uniq_cone_morphism
        have : is_iso ((cones.functoriality K F).map f) := by
          rw [this]
          infer_instance
        have : is_iso f := is_iso_of_reflects_iso f (cones.functoriality K F)
        exact is_limit.of_iso_limit hd' (as_iso f).symm }

/-- When `F` is fully faithful, and `has_limit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to exhibit a lift of the chosen limit cone for `K ⋙ F`.
-/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
def createsLimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F] [HasLimit (K ⋙ F)] (c : Cone K)
    (i : F.mapCone c ≅ Limit.cone (K ⋙ F)) : CreatesLimit K F :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c, validLift := i.trans (IsLimit.uniqueUpToIso (limit.isLimit _) t),
      makesLimit :=
        IsLimit.ofFaithful F (IsLimit.ofIsoLimit (limit.isLimit _) i.symm) (fun s => F.preimage _) fun s =>
          F.image_preimage _ }

/-- When `F` is fully faithful, and `has_limit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to show that the chosen limit point is in the essential image of `F`.
-/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
def createsLimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F] [HasLimit (K ⋙ F)] (X : C)
    (i : F.obj X ≅ limit (K ⋙ F)) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift
    ({ x,
      π :=
        { app := fun j => F.preimage (i.Hom ≫ limit.π (K ⋙ F) j),
          naturality' := fun Y Z f =>
            F.map_injective
              (by
                dsimp'
                simp
                erw [limit.w (K ⋙ F)]) } } :
      Cone K)
    (by
      fapply cones.ext
      exact i
      tidy)

/-- `F` preserves the limit of `K` if it creates the limit and `K ⋙ F` has the limit. -/
-- see Note [lower instance priority]
instance (priority := 100) preservesLimitOfCreatesLimitAndHasLimit (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F]
    [HasLimit (K ⋙ F)] :
    PreservesLimit K
      F where preserves := fun c t =>
    IsLimit.ofIsoLimit (limit.isLimit _)
      ((liftedLimitMapsToOriginal (limit.isLimit _)).symm ≪≫
        (Cones.functoriality K F).mapIso ((liftedLimitIsLimit (limit.isLimit _)).uniqueUpToIso t))

/-- `F` preserves the limit of shape `J` if it creates these limits and `D` has them. -/
-- see Note [lower instance priority]
instance (priority := 100) preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape (F : C ⥤ D)
    [CreatesLimitsOfShape J F] [HasLimitsOfShape J D] : PreservesLimitsOfShape J F where

/-- `F` preserves limits if it creates limits and `D` has limits. -/
-- see Note [lower instance priority]
instance (priority := 100) preservesLimitsOfCreatesLimitsAndHasLimits (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F]
    [HasLimitsOfSize.{w, w'} D] : PreservesLimitsOfSize.{w, w'} F where

/-- If `F` reflects isomorphisms and we can lift any colimit cocone to a colimit cocone,
then `F` creates colimits.
In particular here we don't need to assume that F reflects colimits.
-/
def createsColimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [ReflectsIsomorphisms F] (h : ∀ c t, LiftsToColimit K F c t) :
    CreatesColimit K F where
  lifts := fun c t => (h c t).toLiftableCocone
  toReflectsColimit :=
    { reflects := fun (d : Cocone K) (hd : IsColimit (F.mapCocone d)) => by
        let d' : cocone K := (h (F.map_cocone d) hd).toLiftableCocone.liftedCocone
        let i : F.map_cocone d' ≅ F.map_cocone d := (h (F.map_cocone d) hd).toLiftableCocone.validLift
        let hd' : is_colimit d' := (h (F.map_cocone d) hd).makesColimit
        let f : d' ⟶ d := hd'.desc_cocone_morphism d
        have : (cocones.functoriality K F).map f = i.hom := (hd.of_iso_colimit i.symm).uniq_cocone_morphism
        have : is_iso ((cocones.functoriality K F).map f) := by
          rw [this]
          infer_instance
        have := is_iso_of_reflects_iso f (cocones.functoriality K F)
        exact is_colimit.of_iso_colimit hd' (as_iso f) }

/-- When `F` is fully faithful, and `has_colimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to exhibit a lift of the chosen colimit cocone for `K ⋙ F`.
-/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
def createsColimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F] [HasColimit (K ⋙ F)]
    (c : Cocone K) (i : F.mapCocone c ≅ Colimit.cocone (K ⋙ F)) : CreatesColimit K F :=
  createsColimitOfReflectsIso fun c' t =>
    { liftedCocone := c, validLift := i.trans (IsColimit.uniqueUpToIso (colimit.isColimit _) t),
      makesColimit :=
        IsColimit.ofFaithful F (IsColimit.ofIsoColimit (colimit.isColimit _) i.symm) (fun s => F.preimage _) fun s =>
          F.image_preimage _ }

/-- When `F` is fully faithful, and `has_colimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to show that the chosen colimit point is in the essential image of `F`.
-/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
def createsColimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F] [HasColimit (K ⋙ F)] (X : C)
    (i : F.obj X ≅ colimit (K ⋙ F)) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift
    ({ x,
      ι :=
        { app := fun j => F.preimage (colimit.ι (K ⋙ F) j ≫ i.inv : _),
          naturality' := fun Y Z f =>
            F.map_injective
              (by
                erw [category.comp_id]
                simp only [← functor.map_comp, ← functor.image_preimage]
                erw [colimit.w_assoc (K ⋙ F)]) } } :
      Cocone K)
    (by
      fapply cocones.ext
      exact i
      tidy)

/-- `F` preserves the colimit of `K` if it creates the colimit and `K ⋙ F` has the colimit. -/
-- see Note [lower instance priority]
instance (priority := 100) preservesColimitOfCreatesColimitAndHasColimit (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F]
    [HasColimit (K ⋙ F)] :
    PreservesColimit K
      F where preserves := fun c t =>
    IsColimit.ofIsoColimit (colimit.isColimit _)
      ((liftedColimitMapsToOriginal (colimit.isColimit _)).symm ≪≫
        (Cocones.functoriality K F).mapIso ((liftedColimitIsColimit (colimit.isColimit _)).uniqueUpToIso t))

/-- `F` preserves the colimit of shape `J` if it creates these colimits and `D` has them. -/
-- see Note [lower instance priority]
instance (priority := 100) preservesColimitOfShapeOfCreatesColimitsOfShapeAndHasColimitsOfShape (F : C ⥤ D)
    [CreatesColimitsOfShape J F] [HasColimitsOfShape J D] : PreservesColimitsOfShape J F where

/-- `F` preserves limits if it creates limits and `D` has limits. -/
-- see Note [lower instance priority]
instance (priority := 100) preservesColimitsOfCreatesColimitsAndHasColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] [HasColimitsOfSize.{w, w'} D] : PreservesColimitsOfSize.{w, w'} F where

/-- Transfer creation of limits along a natural isomorphism in the diagram. -/
def createsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesLimit K₁ F] : CreatesLimit K₂ F :=
  { reflectsLimitOfIsoDiagram F h with
    lifts := fun c t =>
      let t' := (IsLimit.postcomposeInvEquiv (isoWhiskerRight h F : _) c).symm t
      { liftedCone := (Cones.postcompose h.Hom).obj (liftLimit t'),
        validLift :=
          F.mapConePostcompose ≪≫
            (Cones.postcompose (isoWhiskerRight h F).Hom).mapIso (liftedLimitMapsToOriginal t') ≪≫
              Cones.ext (Iso.refl _) fun j => by
                dsimp'
                rw [category.assoc, ← F.map_comp]
                simp } }

/-- If `F` creates the limit of `K` and `F ≅ G`, then `G` creates the limit of `K`. -/
def createsLimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimit K F] : CreatesLimit K G where
  lifts := fun c t =>
    { liftedCone := liftLimit ((IsLimit.postcomposeInvEquiv (isoWhiskerLeft K h : _) c).symm t),
      validLift := by
        refine' (is_limit.map_cone_equiv h _).uniqueUpToIso t
        apply is_limit.of_iso_limit _ (lifted_limit_maps_to_original _).symm
        apply (is_limit.postcompose_inv_equiv _ _).symm t }
  toReflectsLimit := reflectsLimitOfNatIso _ h

/-- If `F` creates limits of shape `J` and `F ≅ G`, then `G` creates limits of shape `J`. -/
def createsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfShape J F] :
    CreatesLimitsOfShape J G where CreatesLimit := fun K => createsLimitOfNatIso h

/-- If `F` creates limits and `F ≅ G`, then `G` creates limits. -/
def createsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} G where CreatesLimitsOfShape := fun J 𝒥₁ => creates_limits_of_shape_of_nat_iso h

/-- Transfer creation of colimits along a natural isomorphism in the diagram. -/
def createsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesColimit K₁ F] : CreatesColimit K₂ F :=
  { reflectsColimitOfIsoDiagram F h with
    lifts := fun c t =>
      let t' := (IsColimit.precomposeHomEquiv (isoWhiskerRight h F : _) c).symm t
      { liftedCocone := (Cocones.precompose h.inv).obj (liftColimit t'),
        validLift :=
          F.mapCoconePrecompose ≪≫
            (Cocones.precompose (isoWhiskerRight h F).inv).mapIso (liftedColimitMapsToOriginal t') ≪≫
              Cocones.ext (Iso.refl _) fun j => by
                dsimp'
                rw [← F.map_comp_assoc]
                simp } }

/-- If `F` creates the colimit of `K` and `F ≅ G`, then `G` creates the colimit of `K`. -/
def createsColimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimit K F] : CreatesColimit K G where
  lifts := fun c t =>
    { liftedCocone := liftColimit ((IsColimit.precomposeHomEquiv (isoWhiskerLeft K h : _) c).symm t),
      validLift := by
        refine' (is_colimit.map_cocone_equiv h _).uniqueUpToIso t
        apply is_colimit.of_iso_colimit _ (lifted_colimit_maps_to_original _).symm
        apply (is_colimit.precompose_hom_equiv _ _).symm t }
  toReflectsColimit := reflectsColimitOfNatIso _ h

/-- If `F` creates colimits of shape `J` and `F ≅ G`, then `G` creates colimits of shape `J`. -/
def createsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfShape J F] :
    CreatesColimitsOfShape J G where CreatesColimit := fun K => createsColimitOfNatIso h

/-- If `F` creates colimits and `F ≅ G`, then `G` creates colimits. -/
def createsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} G where CreatesColimitsOfShape := fun J 𝒥₁ => creates_colimits_of_shape_of_nat_iso h

/-- If F creates the limit of K, any cone lifts to a limit. -/
-- For the inhabited linter later.
def liftsToLimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F)) (t : IsLimit c) :
    LiftsToLimit K F c t where
  liftedCone := liftLimit t
  validLift := liftedLimitMapsToOriginal t
  makesLimit := liftedLimitIsLimit t

/-- If F creates the colimit of K, any cocone lifts to a colimit. -/
-- For the inhabited linter later.
def liftsToColimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F)) (t : IsColimit c) :
    LiftsToColimit K F c t where
  liftedCocone := liftColimit t
  validLift := liftedColimitMapsToOriginal t
  makesColimit := liftedColimitIsColimit t

/-- Any cone lifts through the identity functor. -/
def idLiftsCone (c : Cone (K ⋙ 𝟭 C)) : LiftableCone K (𝟭 C) c where
  liftedCone := { x := c.x, π := c.π ≫ K.rightUnitor.Hom }
  validLift :=
    Cones.ext (Iso.refl _)
      (by
        tidy)

/-- The identity functor creates all limits. -/
instance idCreatesLimits :
    CreatesLimitsOfSize.{w, w'}
      (𝟭
        C) where CreatesLimitsOfShape := fun J 𝒥 => { CreatesLimit := fun F => { lifts := fun c t => id_lifts_cone c } }

/-- Any cocone lifts through the identity functor. -/
def idLiftsCocone (c : Cocone (K ⋙ 𝟭 C)) : LiftableCocone K (𝟭 C) c where
  liftedCocone := { x := c.x, ι := K.rightUnitor.inv ≫ c.ι }
  validLift :=
    Cocones.ext (Iso.refl _)
      (by
        tidy)

/-- The identity functor creates all colimits. -/
instance idCreatesColimits :
    CreatesColimitsOfSize.{w, w'}
      (𝟭
        C) where CreatesColimitsOfShape := fun J 𝒥 =>
    { CreatesColimit := fun F => { lifts := fun c t => id_lifts_cocone c } }

/-- Satisfy the inhabited linter -/
instance inhabitedLiftableCone (c : Cone (K ⋙ 𝟭 C)) : Inhabited (LiftableCone K (𝟭 C) c) :=
  ⟨idLiftsCone c⟩

instance inhabitedLiftableCocone (c : Cocone (K ⋙ 𝟭 C)) : Inhabited (LiftableCocone K (𝟭 C) c) :=
  ⟨idLiftsCocone c⟩

/-- Satisfy the inhabited linter -/
instance inhabitedLiftsToLimit (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F)) (t : IsLimit c) :
    Inhabited (LiftsToLimit _ _ _ t) :=
  ⟨liftsToLimitOfCreates K F c t⟩

instance inhabitedLiftsToColimit (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F)) (t : IsColimit c) :
    Inhabited (LiftsToColimit _ _ _ t) :=
  ⟨liftsToColimitOfCreates K F c t⟩

section Comp

variable {E : Type u₃} [ℰ : Category.{v₃} E]

variable (F : C ⥤ D) (G : D ⥤ E)

instance compCreatesLimit [CreatesLimit K F] [CreatesLimit (K ⋙ F) G] :
    CreatesLimit K
      (F ⋙
        G) where lifts := fun c t =>
    { liftedCone := liftLimit (liftedLimitIsLimit t),
      validLift :=
        (Cones.functoriality (K ⋙ F) G).mapIso (liftedLimitMapsToOriginal (liftedLimitIsLimit t)) ≪≫
          liftedLimitMapsToOriginal t }

instance compCreatesLimitsOfShape [CreatesLimitsOfShape J F] [CreatesLimitsOfShape J G] :
    CreatesLimitsOfShape J (F ⋙ G) where CreatesLimit := inferInstance

instance compCreatesLimits [CreatesLimitsOfSize.{w, w'} F] [CreatesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (F ⋙ G) where CreatesLimitsOfShape := inferInstance

instance compCreatesColimit [CreatesColimit K F] [CreatesColimit (K ⋙ F) G] :
    CreatesColimit K
      (F ⋙
        G) where lifts := fun c t =>
    { liftedCocone := liftColimit (liftedColimitIsColimit t),
      validLift :=
        (Cocones.functoriality (K ⋙ F) G).mapIso (liftedColimitMapsToOriginal (liftedColimitIsColimit t)) ≪≫
          liftedColimitMapsToOriginal t }

instance compCreatesColimitsOfShape [CreatesColimitsOfShape J F] [CreatesColimitsOfShape J G] :
    CreatesColimitsOfShape J (F ⋙ G) where CreatesColimit := inferInstance

instance compCreatesColimits [CreatesColimitsOfSize.{w, w'} F] [CreatesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (F ⋙ G) where CreatesColimitsOfShape := inferInstance

end Comp

end Creates

end CategoryTheory

