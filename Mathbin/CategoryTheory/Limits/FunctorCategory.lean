/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Limits.Preserves.Limits

/-!
# (Co)limits in functor categories.

We show that if `D` has limits, then the functor category `C ⥤ D` also has limits
(`category_theory.limits.functor_category_has_limits`),
and the evaluation functors preserve limits
(`category_theory.limits.evaluation_preserves_limits`)
(and similarly for colimits).

We also show that `F : D ⥤ K ⥤ C` preserves (co)limits if it does so for each `k : K`
(`category_theory.limits.preserves_limits_of_evaluation` and
`category_theory.limits.preserves_colimits_of_evaluation`).
-/


open CategoryTheory CategoryTheory.Category

-- morphism levels before object levels. See note [category_theory universes].
universe v₁ v₂ u₁ u₂ v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

@[simp, reassoc]
theorem limit.lift_π_app (H : J ⥤ K ⥤ C) [HasLimit H] (c : Cone H) (j : J) (k : K) :
    (limit.lift H c).app k ≫ (limit.π H j).app k = (c.π.app j).app k :=
  congr_app (limit.lift_π c j) k

@[simp, reassoc]
theorem colimit.ι_desc_app (H : J ⥤ K ⥤ C) [HasColimit H] (c : Cocone H) (j : J) (k : K) :
    (colimit.ι H j).app k ≫ (colimit.desc H c).app k = (c.ι.app j).app k :=
  congr_app (colimit.ι_desc c j) k

/-- The evaluation functors jointly reflect limits: that is, to show a cone is a limit of `F`
it suffices to show that each evaluation cone is a limit. In other words, to prove a cone is
limiting you can show it's pointwise limiting.
-/
def evaluationJointlyReflectsLimits {F : J ⥤ K ⥤ C} (c : Cone F)
    (t : ∀ k : K, IsLimit (((evaluation K C).obj k).mapCone c)) : IsLimit c where
  lift := fun s =>
    { app := fun k => (t k).lift ⟨s.x.obj k, whiskerRight s.π ((evaluation K C).obj k)⟩,
      naturality' := fun X Y f =>
        (t Y).hom_ext fun j => by
          rw [assoc, (t Y).fac _ j]
          simpa using ((t X).fac_assoc ⟨s.X.obj X, whisker_right s.π ((evaluation K C).obj X)⟩ j _).symm }
  fac' := fun s j => NatTrans.ext _ _ <| funext fun k => (t k).fac _ j
  uniq' := fun s m w =>
    NatTrans.ext _ _ <|
      funext fun x =>
        (t x).hom_ext fun j =>
          (congr_app (w j) x).trans ((t x).fac ⟨s.x.obj _, whiskerRight s.π ((evaluation K C).obj _)⟩ j).symm

/-- Given a functor `F` and a collection of limit cones for each diagram `X ↦ F X k`, we can stitch
them together to give a cone for the diagram `F`.
`combined_is_limit` shows that the new cone is limiting, and `eval_combined` shows it is
(essentially) made up of the original cones.
-/
@[simps]
def combineCones (F : J ⥤ K ⥤ C) (c : ∀ k : K, LimitCone (F.flip.obj k)) : Cone F where
  x :=
    { obj := fun k => (c k).Cone.x, map := fun k₁ k₂ f => (c k₂).IsLimit.lift ⟨_, (c k₁).Cone.π ≫ F.flip.map f⟩,
      map_id' := fun k =>
        (c k).IsLimit.hom_ext fun j => by
          dsimp'
          simp ,
      map_comp' := fun k₁ k₂ k₃ f₁ f₂ =>
        (c k₃).IsLimit.hom_ext fun j => by
          simp }
  π :=
    { app := fun j => { app := fun k => (c k).Cone.π.app j },
      naturality' := fun j₁ j₂ g => NatTrans.ext _ _ <| funext fun k => (c k).Cone.π.naturality g }

/-- The stitched together cones each project down to the original given cones (up to iso). -/
def evaluateCombinedCones (F : J ⥤ K ⥤ C) (c : ∀ k : K, LimitCone (F.flip.obj k)) (k : K) :
    ((evaluation K C).obj k).mapCone (combineCones F c) ≅ (c k).Cone :=
  Cones.ext (Iso.refl _)
    (by
      tidy)

/-- Stitching together limiting cones gives a limiting cone. -/
def combinedIsLimit (F : J ⥤ K ⥤ C) (c : ∀ k : K, LimitCone (F.flip.obj k)) : IsLimit (combineCones F c) :=
  evaluationJointlyReflectsLimits _ fun k => (c k).IsLimit.ofIsoLimit (evaluateCombinedCones F c k).symm

/-- The evaluation functors jointly reflect colimits: that is, to show a cocone is a colimit of `F`
it suffices to show that each evaluation cocone is a colimit. In other words, to prove a cocone is
colimiting you can show it's pointwise colimiting.
-/
def evaluationJointlyReflectsColimits {F : J ⥤ K ⥤ C} (c : Cocone F)
    (t : ∀ k : K, IsColimit (((evaluation K C).obj k).mapCocone c)) : IsColimit c where
  desc := fun s =>
    { app := fun k => (t k).desc ⟨s.x.obj k, whiskerRight s.ι ((evaluation K C).obj k)⟩,
      naturality' := fun X Y f =>
        (t X).hom_ext fun j => by
          rw [(t X).fac_assoc _ j]
          erw [← (c.ι.app j).naturality_assoc f]
          erw [(t Y).fac ⟨s.X.obj _, whisker_right s.ι _⟩ j]
          dsimp'
          simp }
  fac' := fun s j => NatTrans.ext _ _ <| funext fun k => (t k).fac _ j
  uniq' := fun s m w =>
    NatTrans.ext _ _ <|
      funext fun x =>
        (t x).hom_ext fun j =>
          (congr_app (w j) x).trans ((t x).fac ⟨s.x.obj _, whiskerRight s.ι ((evaluation K C).obj _)⟩ j).symm

/-- Given a functor `F` and a collection of colimit cocones for each diagram `X ↦ F X k`, we can stitch
them together to give a cocone for the diagram `F`.
`combined_is_colimit` shows that the new cocone is colimiting, and `eval_combined` shows it is
(essentially) made up of the original cocones.
-/
@[simps]
def combineCocones (F : J ⥤ K ⥤ C) (c : ∀ k : K, ColimitCocone (F.flip.obj k)) : Cocone F where
  x :=
    { obj := fun k => (c k).Cocone.x, map := fun k₁ k₂ f => (c k₁).IsColimit.desc ⟨_, F.flip.map f ≫ (c k₂).Cocone.ι⟩,
      map_id' := fun k =>
        (c k).IsColimit.hom_ext fun j => by
          dsimp'
          simp ,
      map_comp' := fun k₁ k₂ k₃ f₁ f₂ =>
        (c k₁).IsColimit.hom_ext fun j => by
          simp }
  ι :=
    { app := fun j => { app := fun k => (c k).Cocone.ι.app j },
      naturality' := fun j₁ j₂ g => NatTrans.ext _ _ <| funext fun k => (c k).Cocone.ι.naturality g }

/-- The stitched together cocones each project down to the original given cocones (up to iso). -/
def evaluateCombinedCocones (F : J ⥤ K ⥤ C) (c : ∀ k : K, ColimitCocone (F.flip.obj k)) (k : K) :
    ((evaluation K C).obj k).mapCocone (combineCocones F c) ≅ (c k).Cocone :=
  Cocones.ext (Iso.refl _)
    (by
      tidy)

/-- Stitching together colimiting cocones gives a colimiting cocone. -/
def combinedIsColimit (F : J ⥤ K ⥤ C) (c : ∀ k : K, ColimitCocone (F.flip.obj k)) : IsColimit (combineCocones F c) :=
  evaluationJointlyReflectsColimits _ fun k => (c k).IsColimit.ofIsoColimit (evaluateCombinedCocones F c k).symm

noncomputable section

instance functor_category_has_limits_of_shape [HasLimitsOfShape J C] :
    HasLimitsOfShape J
      (K ⥤
        C) where HasLimit := fun F =>
    HasLimit.mk { Cone := combineCones F fun k => getLimitCone _, IsLimit := combinedIsLimit _ _ }

instance functor_category_has_colimits_of_shape [HasColimitsOfShape J C] :
    HasColimitsOfShape J
      (K ⥤
        C) where HasColimit := fun F =>
    HasColimit.mk { Cocone := combineCocones _ fun k => getColimitCocone _, IsColimit := combinedIsColimit _ _ }

instance functor_category_has_limits_of_size [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfSize.{v₁, u₁} (K ⥤ C) :=
  ⟨inferInstance⟩

instance functor_category_has_colimits_of_size [HasColimitsOfSize.{v₁, u₁} C] : HasColimitsOfSize.{v₁, u₁} (K ⥤ C) :=
  ⟨inferInstance⟩

instance evaluationPreservesLimitsOfShape [HasLimitsOfShape J C] (k : K) :
    PreservesLimitsOfShape J
      ((evaluation K C).obj
        k) where PreservesLimit := fun F =>
    preservesLimitOfPreservesLimitCone (combinedIsLimit _ _) <|
      IsLimit.ofIsoLimit (limit.isLimit _) (evaluateCombinedCones F _ k).symm

/-- If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a limit,
then the evaluation of that limit at `k` is the limit of the evaluations of `F.obj j` at `k`.
-/
def limitObjIsoLimitCompEvaluation [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (k : K) :
    (limit F).obj k ≅ limit (F ⋙ (evaluation K C).obj k) :=
  preservesLimitIso ((evaluation K C).obj k) F

@[simp, reassoc]
theorem limit_obj_iso_limit_comp_evaluation_hom_π [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) :
    (limitObjIsoLimitCompEvaluation F k).Hom ≫ limit.π (F ⋙ (evaluation K C).obj k) j = (limit.π F j).app k := by
  dsimp' [← limit_obj_iso_limit_comp_evaluation]
  simp

@[simp, reassoc]
theorem limit_obj_iso_limit_comp_evaluation_inv_π_app [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) :
    (limitObjIsoLimitCompEvaluation F k).inv ≫ (limit.π F j).app k = limit.π (F ⋙ (evaluation K C).obj k) j := by
  dsimp' [← limit_obj_iso_limit_comp_evaluation]
  rw [iso.inv_comp_eq]
  simp

@[simp, reassoc]
theorem limit_map_limit_obj_iso_limit_comp_evaluation_hom [HasLimitsOfShape J C] {i j : K} (F : J ⥤ K ⥤ C) (f : i ⟶ j) :
    (limit F).map f ≫ (limitObjIsoLimitCompEvaluation _ _).Hom =
      (limitObjIsoLimitCompEvaluation _ _).Hom ≫ limMap (whiskerLeft _ ((evaluation _ _).map f)) :=
  by
  ext
  dsimp'
  simp

@[simp, reassoc]
theorem limit_obj_iso_limit_comp_evaluation_inv_limit_map [HasLimitsOfShape J C] {i j : K} (F : J ⥤ K ⥤ C) (f : i ⟶ j) :
    (limitObjIsoLimitCompEvaluation _ _).inv ≫ (limit F).map f =
      limMap (whiskerLeft _ ((evaluation _ _).map f)) ≫ (limitObjIsoLimitCompEvaluation _ _).inv :=
  by
  rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, limit_map_limit_obj_iso_limit_comp_evaluation_hom]

@[ext]
theorem limit_obj_ext {H : J ⥤ K ⥤ C} [HasLimitsOfShape J C] {k : K} {W : C} {f g : W ⟶ (limit H).obj k}
    (w : ∀ j, f ≫ (Limits.limit.π H j).app k = g ≫ (Limits.limit.π H j).app k) : f = g := by
  apply (cancel_mono (limit_obj_iso_limit_comp_evaluation H k).Hom).1
  ext
  simpa using w j

instance evaluationPreservesColimitsOfShape [HasColimitsOfShape J C] (k : K) :
    PreservesColimitsOfShape J
      ((evaluation K C).obj
        k) where PreservesColimit := fun F =>
    preservesColimitOfPreservesColimitCocone (combinedIsColimit _ _) <|
      IsColimit.ofIsoColimit (colimit.isColimit _) (evaluateCombinedCocones F _ k).symm

/-- If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a colimit,
then the evaluation of that colimit at `k` is the colimit of the evaluations of `F.obj j` at `k`.
-/
def colimitObjIsoColimitCompEvaluation [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (k : K) :
    (colimit F).obj k ≅ colimit (F ⋙ (evaluation K C).obj k) :=
  preservesColimitIso ((evaluation K C).obj k) F

@[simp, reassoc]
theorem colimit_obj_iso_colimit_comp_evaluation_ι_inv [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) :
    colimit.ι (F ⋙ (evaluation K C).obj k) j ≫ (colimitObjIsoColimitCompEvaluation F k).inv = (colimit.ι F j).app k :=
  by
  dsimp' [← colimit_obj_iso_colimit_comp_evaluation]
  simp

@[simp, reassoc]
theorem colimit_obj_iso_colimit_comp_evaluation_ι_app_hom [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) :
    (colimit.ι F j).app k ≫ (colimitObjIsoColimitCompEvaluation F k).Hom = colimit.ι (F ⋙ (evaluation K C).obj k) j :=
  by
  dsimp' [← colimit_obj_iso_colimit_comp_evaluation]
  rw [← iso.eq_comp_inv]
  simp

@[simp, reassoc]
theorem colimit_obj_iso_colimit_comp_evaluation_inv_colimit_map [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) {i j : K}
    (f : i ⟶ j) :
    (colimitObjIsoColimitCompEvaluation _ _).inv ≫ (colimit F).map f =
      colimMap (whiskerLeft _ ((evaluation _ _).map f)) ≫ (colimitObjIsoColimitCompEvaluation _ _).inv :=
  by
  ext
  dsimp'
  simp

@[simp, reassoc]
theorem colimit_map_colimit_obj_iso_colimit_comp_evaluation_hom [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) {i j : K}
    (f : i ⟶ j) :
    (colimit F).map f ≫ (colimitObjIsoColimitCompEvaluation _ _).Hom =
      (colimitObjIsoColimitCompEvaluation _ _).Hom ≫ colimMap (whiskerLeft _ ((evaluation _ _).map f)) :=
  by
  rw [← iso.inv_comp_eq, ← category.assoc, ← iso.eq_comp_inv, colimit_obj_iso_colimit_comp_evaluation_inv_colimit_map]

@[ext]
theorem colimit_obj_ext {H : J ⥤ K ⥤ C} [HasColimitsOfShape J C] {k : K} {W : C} {f g : (colimit H).obj k ⟶ W}
    (w : ∀ j, (colimit.ι H j).app k ≫ f = (colimit.ι H j).app k ≫ g) : f = g := by
  apply (cancel_epi (colimit_obj_iso_colimit_comp_evaluation H k).inv).1
  ext
  simpa using w j

instance evaluationPreservesLimits [HasLimits C] (k : K) :
    PreservesLimits ((evaluation K C).obj k) where PreservesLimitsOfShape := fun J 𝒥 => by
    skip <;> infer_instance

/-- `F : D ⥤ K ⥤ C` preserves the limit of some `G : J ⥤ D` if it does for each `k : K`. -/
def preservesLimitOfEvaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D)
    (H : ∀ k : K, PreservesLimit G (F ⋙ (evaluation K C).obj k : D ⥤ C)) : PreservesLimit G F :=
  ⟨fun c hc => by
    apply evaluation_jointly_reflects_limits
    intro X
    have := H X
    change is_limit ((F ⋙ (evaluation K C).obj X).mapCone c)
    exact preserves_limit.preserves hc⟩

/-- `F : D ⥤ K ⥤ C` preserves limits of shape `J` if it does for each `k : K`. -/
def preservesLimitsOfShapeOfEvaluation (F : D ⥤ K ⥤ C) (J : Type _) [Category J]
    (H : ∀ k : K, PreservesLimitsOfShape J (F ⋙ (evaluation K C).obj k)) : PreservesLimitsOfShape J F :=
  ⟨fun G => preservesLimitOfEvaluation F G fun k => PreservesLimitsOfShape.preservesLimit⟩

/-- `F : D ⥤ K ⥤ C` preserves all limits if it does for each `k : K`. -/
def preservesLimitsOfEvaluation.{w', w} (F : D ⥤ K ⥤ C)
    (H : ∀ k : K, PreservesLimitsOfSize.{w', w} (F ⋙ (evaluation K C).obj k)) : PreservesLimitsOfSize.{w', w} F :=
  ⟨fun L hL => preserves_limits_of_shape_of_evaluation F L fun k => preserves_limits_of_size.preserves_limits_of_shape⟩

instance evaluationPreservesColimits [HasColimits C] (k : K) :
    PreservesColimits ((evaluation K C).obj k) where PreservesColimitsOfShape := fun J 𝒥 => by
    skip <;> infer_instance

/-- `F : D ⥤ K ⥤ C` preserves the colimit of some `G : J ⥤ D` if it does for each `k : K`. -/
def preservesColimitOfEvaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D)
    (H : ∀ k, PreservesColimit G (F ⋙ (evaluation K C).obj k)) : PreservesColimit G F :=
  ⟨fun c hc => by
    apply evaluation_jointly_reflects_colimits
    intro X
    have := H X
    change is_colimit ((F ⋙ (evaluation K C).obj X).mapCocone c)
    exact preserves_colimit.preserves hc⟩

/-- `F : D ⥤ K ⥤ C` preserves all colimits of shape `J` if it does for each `k : K`. -/
def preservesColimitsOfShapeOfEvaluation (F : D ⥤ K ⥤ C) (J : Type _) [Category J]
    (H : ∀ k : K, PreservesColimitsOfShape J (F ⋙ (evaluation K C).obj k)) : PreservesColimitsOfShape J F :=
  ⟨fun G => preservesColimitOfEvaluation F G fun k => PreservesColimitsOfShape.preservesColimit⟩

/-- `F : D ⥤ K ⥤ C` preserves all colimits if it does for each `k : K`. -/
def preservesColimitsOfEvaluation.{w', w} (F : D ⥤ K ⥤ C)
    (H : ∀ k : K, PreservesColimitsOfSize.{w', w} (F ⋙ (evaluation K C).obj k)) : PreservesColimitsOfSize.{w', w} F :=
  ⟨fun L hL =>
    preserves_colimits_of_shape_of_evaluation F L fun k => preserves_colimits_of_size.preserves_colimits_of_shape⟩

open CategoryTheory.prod

/-- The limit of a diagram `F : J ⥤ K ⥤ C` is isomorphic to the functor given by
the individual limits on objects. -/
@[simps]
def limitIsoFlipCompLim [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) : limit F ≅ F.flip ⋙ lim :=
  NatIso.ofComponents (limitObjIsoLimitCompEvaluation F) <| by
    tidy

/-- A variant of `limit_iso_flip_comp_lim` where the arguemnts of `F` are flipped. -/
@[simps]
def limitFlipIsoCompLim [HasLimitsOfShape J C] (F : K ⥤ J ⥤ C) : limit F.flip ≅ F ⋙ lim :=
  (NatIso.ofComponents fun k =>
      limitObjIsoLimitCompEvaluation F.flip k ≪≫ HasLimit.isoOfNatIso (flipCompEvaluation _ _)) <|
    by
    tidy

/-- For a functor `G : J ⥤ K ⥤ C`, its limit `K ⥤ C` is given by `(G' : K ⥤ J ⥤ C) ⋙ lim`.
Note that this does not require `K` to be small.
-/
@[simps]
def limitIsoSwapCompLim [HasLimitsOfShape J C] (G : J ⥤ K ⥤ C) : limit G ≅ curry.obj (swap K J ⋙ uncurry.obj G) ⋙ lim :=
  limitIsoFlipCompLim G ≪≫ isoWhiskerRight (flipIsoCurrySwapUncurry _) _

/-- The colimit of a diagram `F : J ⥤ K ⥤ C` is isomorphic to the functor given by
the individual colimits on objects. -/
@[simps]
def colimitIsoFlipCompColim [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) : colimit F ≅ F.flip ⋙ colim :=
  NatIso.ofComponents (colimitObjIsoColimitCompEvaluation F) <| by
    tidy

/-- A variant of `colimit_iso_flip_comp_colim` where the arguemnts of `F` are flipped. -/
@[simps]
def colimitFlipIsoCompColim [HasColimitsOfShape J C] (F : K ⥤ J ⥤ C) : colimit F.flip ≅ F ⋙ colim :=
  (NatIso.ofComponents fun k =>
      colimitObjIsoColimitCompEvaluation _ _ ≪≫ HasColimit.isoOfNatIso (flipCompEvaluation _ _)) <|
    by
    tidy

/-- For a functor `G : J ⥤ K ⥤ C`, its colimit `K ⥤ C` is given by `(G' : K ⥤ J ⥤ C) ⋙ colim`.
Note that this does not require `K` to be small.
-/
@[simps]
def colimitIsoSwapCompColim [HasColimitsOfShape J C] (G : J ⥤ K ⥤ C) :
    colimit G ≅ curry.obj (swap K J ⋙ uncurry.obj G) ⋙ colim :=
  colimitIsoFlipCompColim G ≪≫ isoWhiskerRight (flipIsoCurrySwapUncurry _) _

end CategoryTheory.Limits

