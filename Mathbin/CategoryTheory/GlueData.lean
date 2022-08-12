/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.Tactic.Elementwise
import Mathbin.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathbin.CategoryTheory.Limits.Constructions.EpiMono
import Mathbin.CategoryTheory.Limits.Preserves.Limits
import Mathbin.CategoryTheory.Limits.Shapes.Types

/-!
# Gluing data

We define `glue_data` as a family of data needed to glue topological spaces, schemes, etc. We
provide the API to realize it as a multispan diagram, and also states lemmas about its
interaction with a functor that preserves certain pullbacks.

-/


noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u₁ u₂

variable (C : Type u₁) [Category.{v} C] {C' : Type u₂} [Category.{v} C']

/-- A gluing datum consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
4. A monomorphism `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. The pullback for `f i j` and `f i k` exists.
9. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
10. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.
-/
@[nolint has_inhabited_instance]
structure GlueData where
  J : Type v
  U : J → C
  V : J × J → C
  f : ∀ i j, V (i, j) ⟶ U i
  f_mono : ∀ i j, Mono (f i j) := by
    run_tac
      tactic.apply_instance
  f_has_pullback : ∀ i j k, HasPullback (f i j) (f i k) := by
    run_tac
      tactic.apply_instance
  f_id : ∀ i, IsIso (f i i) := by
    run_tac
      tactic.apply_instance
  t : ∀ i j, V (i, j) ⟶ V (j, i)
  t_id : ∀ i, t i i = 𝟙 _
  t' : ∀ i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
  t_fac : ∀ i j k, t' i j k ≫ pullback.snd = pullback.fst ≫ t i j
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

attribute [simp] glue_data.t_id

attribute [instance] glue_data.f_id glue_data.f_mono glue_data.f_has_pullback

attribute [reassoc] glue_data.t_fac glue_data.cocycle

namespace GlueData

variable {C} (D : GlueData C)

@[simp]
theorem t'_iij (i j : D.J) : D.t' i i j = (pullbackSymmetry _ _).Hom := by
  have eq₁ := D.t_fac i i j
  have eq₂ := (is_iso.eq_comp_inv (D.f i i)).mpr (@pullback.condition _ _ _ _ _ _ (D.f i j) _)
  rw [D.t_id, category.comp_id, eq₂] at eq₁
  have eq₃ := (is_iso.eq_comp_inv (D.f i i)).mp eq₁
  rw [category.assoc, ← pullback.condition, ← category.assoc] at eq₃
  exact mono.right_cancellation _ _ ((mono.right_cancellation _ _ eq₃).trans (pullback_symmetry_hom_comp_fst _ _).symm)

theorem t'_jii (i j : D.J) : D.t' j i i = pullback.fst ≫ D.t j i ≫ inv pullback.snd := by
  rw [← category.assoc, ← D.t_fac]
  simp

theorem t'_iji (i j : D.J) : D.t' i j i = pullback.fst ≫ D.t i j ≫ inv pullback.snd := by
  rw [← category.assoc, ← D.t_fac]
  simp

@[simp, reassoc, elementwise]
theorem t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙 _ := by
  have eq : (pullback_symmetry (D.f i i) (D.f i j)).Hom = pullback.snd ≫ inv pullback.fst := by
    simp
  have := D.cocycle i j i
  rw [D.t'_iij, D.t'_jii, D.t'_iji, fst_eq_snd_of_mono_eq, Eq] at this
  simp only [← category.assoc, ← is_iso.inv_hom_id_assoc] at this
  rw [← is_iso.eq_inv_comp, ← category.assoc, is_iso.comp_inv_eq] at this
  simpa using this

theorem t'_inv (i j k : D.J) :
    D.t' i j k ≫ (pullbackSymmetry _ _).Hom ≫ D.t' j i k ≫ (pullbackSymmetry _ _).Hom = 𝟙 _ := by
  rw [← cancel_mono (pullback.fst : pullback (D.f i j) (D.f i k) ⟶ _)]
  simp [← t_fac, ← t_fac_assoc]

instance t_is_iso (i j : D.J) : IsIso (D.t i j) :=
  ⟨⟨D.t j i, D.t_inv _ _, D.t_inv _ _⟩⟩

instance t'_is_iso (i j k : D.J) : IsIso (D.t' i j k) :=
  ⟨⟨D.t' j k i ≫ D.t' k i j, D.cocycle _ _ _, by
      simpa using D.cocycle _ _ _⟩⟩

@[reassoc]
theorem t'_comp_eq_pullback_symmetry (i j k : D.J) :
    D.t' j k i ≫ D.t' k i j = (pullbackSymmetry _ _).Hom ≫ D.t' j i k ≫ (pullbackSymmetry _ _).Hom := by
  trans inv (D.t' i j k)
  · exact is_iso.eq_inv_of_hom_inv_id (D.cocycle _ _ _)
    
  · rw [← cancel_mono (pullback.fst : pullback (D.f i j) (D.f i k) ⟶ _)]
    simp [← t_fac, ← t_fac_assoc]
    

/-- (Implementation) The disjoint union of `U i`. -/
def sigmaOpens [HasCoproduct D.U] : C :=
  ∐ D.U

/-- (Implementation) The diagram to take colimit of. -/
def diagram : MultispanIndex C where
  L := D.J × D.J
  R := D.J
  fstFrom := Prod.fst
  sndFrom := Prod.snd
  left := D.V
  right := D.U
  fst := fun ⟨i, j⟩ => D.f i j
  snd := fun ⟨i, j⟩ => D.t i j ≫ D.f j i

@[simp]
theorem diagram_L : D.diagram.L = (D.J × D.J) :=
  rfl

@[simp]
theorem diagram_R : D.diagram.R = D.J :=
  rfl

@[simp]
theorem diagram_fst_from (i j : D.J) : D.diagram.fstFrom ⟨i, j⟩ = i :=
  rfl

@[simp]
theorem diagram_snd_from (i j : D.J) : D.diagram.sndFrom ⟨i, j⟩ = j :=
  rfl

@[simp]
theorem diagram_fst (i j : D.J) : D.diagram.fst ⟨i, j⟩ = D.f i j :=
  rfl

@[simp]
theorem diagram_snd (i j : D.J) : D.diagram.snd ⟨i, j⟩ = D.t i j ≫ D.f j i :=
  rfl

@[simp]
theorem diagram_left : D.diagram.left = D.V :=
  rfl

@[simp]
theorem diagram_right : D.diagram.right = D.U :=
  rfl

section

variable [HasMulticoequalizer D.diagram]

/-- The glued object given a family of gluing data. -/
def glued : C :=
  multicoequalizer D.diagram

/-- The map `D.U i ⟶ D.glued` for each `i`. -/
def ι (i : D.J) : D.U i ⟶ D.glued :=
  multicoequalizer.π D.diagram i

@[simp, elementwise]
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
  (Category.assoc _ _ _).symm.trans (multicoequalizer.condition D.diagram ⟨i, j⟩).symm

/-- The pullback cone spanned by `V i j ⟶ U i` and `V i j ⟶ U j`.
This will often be a pullback diagram. -/
def vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j) :=
  PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i)
    (by
      simp )

variable [HasColimits C]

/-- The projection `∐ D.U ⟶ D.glued` given by the colimit. -/
def π : D.sigmaOpens ⟶ D.glued :=
  multicoequalizer.sigmaπ D.diagram

instance π_epi : Epi D.π := by
  unfold π
  infer_instance

end

theorem types_π_surjective (D : GlueData (Type _)) : Function.Surjective D.π :=
  (epi_iff_surjective _).mp inferInstance

theorem types_ι_jointly_surjective (D : GlueData (Type _)) (x : D.glued) : ∃ (i : _)(y : D.U i), D.ι i y = x := by
  delta' CategoryTheory.GlueData.ι
  simp_rw [← multicoequalizer.ι_sigma_π D.diagram]
  rcases D.types_π_surjective x with ⟨x', rfl⟩
  have := colimit.iso_colimit_cocone (types.coproduct_colimit_cocone _)
  rw [←
    show (colimit.iso_colimit_cocone (types.coproduct_colimit_cocone _)).inv _ = x' from
      concrete_category.congr_hom (colimit.iso_colimit_cocone (types.coproduct_colimit_cocone _)).hom_inv_id x']
  rcases(colimit.iso_colimit_cocone (types.coproduct_colimit_cocone _)).Hom x' with ⟨i, y⟩
  exact
    ⟨i, y, by
      simpa [multicoequalizer.ι_sigma_π, -multicoequalizer.ι_sigma_π] ⟩

variable (F : C ⥤ C') [H : ∀ i j k, PreservesLimit (cospan (D.f i j) (D.f i k)) F]

include H

instance (i j k : D.J) : HasPullback (F.map (D.f i j)) (F.map (D.f i k)) :=
  ⟨⟨⟨_, isLimitOfHasPullbackOfPreservesLimit F (D.f i j) (D.f i k)⟩⟩⟩

/-- A functor that preserves the pullbacks of `f i j` and `f i k` can map a family of glue data. -/
@[simps]
def mapGlueData : GlueData C' where
  J := D.J
  U := fun i => F.obj (D.U i)
  V := fun i => F.obj (D.V i)
  f := fun i j => F.map (D.f i j)
  f_mono := fun i j => preserves_mono_of_preserves_limit _ _
  f_id := fun i => inferInstance
  t := fun i j => F.map (D.t i j)
  t_id := fun i => by
    rw [D.t_id i]
    simp
  t' := fun i j k =>
    (PreservesPullback.iso F (D.f i j) (D.f i k)).inv ≫
      F.map (D.t' i j k) ≫ (PreservesPullback.iso F (D.f j k) (D.f j i)).Hom
  t_fac := fun i j k => by
    simpa [← iso.inv_comp_eq] using congr_arg (fun f => F.map f) (D.t_fac i j k)
  cocycle := fun i j k => by
    simp only [← category.assoc, ← iso.hom_inv_id_assoc, functor.map_comp_assoc, ← D.cocycle, ← iso.inv_hom_id, ←
      CategoryTheory.Functor.map_id, ← category.id_comp]

/-- The diagram of the image of a `glue_data` under a functor `F` is naturally isomorphic to the
original diagram of the `glue_data` via `F`.
-/
def diagramIso : D.diagram.multispan ⋙ F ≅ (D.mapGlueData F).diagram.multispan :=
  NatIso.ofComponents
    (fun x =>
      match x with
      | walking_multispan.left a => Iso.refl _
      | walking_multispan.right b => Iso.refl _)
    (by
      rintro (⟨_, _⟩ | _) _ (_ | _ | _)
      · erw [category.comp_id, category.id_comp, Functor.map_id]
        rfl
        
      · erw [category.comp_id, category.id_comp]
        rfl
        
      · erw [category.comp_id, category.id_comp, functor.map_comp]
        rfl
        
      · erw [category.comp_id, category.id_comp, Functor.map_id]
        rfl
        )

@[simp]
theorem diagram_iso_app_left (i : D.J × D.J) : (D.diagramIso F).app (WalkingMultispan.left i) = Iso.refl _ :=
  rfl

@[simp]
theorem diagram_iso_app_right (i : D.J) : (D.diagramIso F).app (WalkingMultispan.right i) = Iso.refl _ :=
  rfl

@[simp]
theorem diagram_iso_hom_app_left (i : D.J × D.J) : (D.diagramIso F).Hom.app (WalkingMultispan.left i) = 𝟙 _ :=
  rfl

@[simp]
theorem diagram_iso_hom_app_right (i : D.J) : (D.diagramIso F).Hom.app (WalkingMultispan.right i) = 𝟙 _ :=
  rfl

@[simp]
theorem diagram_iso_inv_app_left (i : D.J × D.J) : (D.diagramIso F).inv.app (WalkingMultispan.left i) = 𝟙 _ :=
  rfl

@[simp]
theorem diagram_iso_inv_app_right (i : D.J) : (D.diagramIso F).inv.app (WalkingMultispan.right i) = 𝟙 _ :=
  rfl

variable [HasMulticoequalizer D.diagram] [PreservesColimit D.diagram.multispan F]

omit H

theorem has_colimit_multispan_comp : HasColimit (D.diagram.multispan ⋙ F) :=
  ⟨⟨⟨_, PreservesColimit.preserves (colimit.isColimit _)⟩⟩⟩

include H

attribute [local instance] has_colimit_multispan_comp

theorem has_colimit_map_glue_data_diagram : HasMulticoequalizer (D.mapGlueData F).diagram :=
  has_colimit_of_iso (D.diagramIso F).symm

attribute [local instance] has_colimit_map_glue_data_diagram

/-- If `F` preserves the gluing, we obtain an iso between the glued objects. -/
def gluedIso : F.obj D.glued ≅ (D.mapGlueData F).glued :=
  preservesColimitIso F D.diagram.multispan ≪≫ Limits.HasColimit.isoOfNatIso (D.diagramIso F)

@[simp, reassoc]
theorem ι_glued_iso_hom (i : D.J) : F.map (D.ι i) ≫ (D.gluedIso F).Hom = (D.mapGlueData F).ι i := by
  erw [ι_preserves_colimits_iso_hom_assoc]
  rw [has_colimit.iso_of_nat_iso_ι_hom]
  erw [category.id_comp]
  rfl

@[simp, reassoc]
theorem ι_glued_iso_inv (i : D.J) : (D.mapGlueData F).ι i ≫ (D.gluedIso F).inv = F.map (D.ι i) := by
  rw [iso.comp_inv_eq, ι_glued_iso_hom]

/-- If `F` preserves the gluing, and reflects the pullback of `U i ⟶ glued` and `U j ⟶ glued`,
then `F` reflects the fact that `V_pullback_cone` is a pullback. -/
def vPullbackConeIsLimitOfMap (i j : D.J) [ReflectsLimit (cospan (D.ι i) (D.ι j)) F]
    (hc : IsLimit ((D.mapGlueData F).vPullbackCone i j)) : IsLimit (D.vPullbackCone i j) := by
  apply is_limit_of_reflects F
  apply (is_limit_map_cone_pullback_cone_equiv _ _).symm _
  let e : cospan (F.map (D.ι i)) (F.map (D.ι j)) ≅ cospan ((D.map_glue_data F).ι i) ((D.map_glue_data F).ι j)
  exact
    nat_iso.of_components
      (fun x => by
        cases x
        exacts[D.glued_iso F, iso.refl _])
      (by
        rintro (_ | _) (_ | _) (_ | _ | _) <;> simp )
  apply is_limit.postcompose_hom_equiv e _ _
  apply hc.of_iso_limit
  refine' cones.ext (iso.refl _) _
  · rintro (_ | _ | _)
    change _ = _ ≫ (_ ≫ _) ≫ _
    all_goals
      change _ = 𝟙 _ ≫ _ ≫ _
      simpa
    

omit H

/-- If there is a forgetful functor into `Type` that preserves enough (co)limits, then `D.ι` will
be jointly surjective. -/
theorem ι_jointly_surjective (F : C ⥤ Type v) [PreservesColimit D.diagram.multispan F]
    [∀ i j k : D.J, PreservesLimit (cospan (D.f i j) (D.f i k)) F] (x : F.obj D.glued) :
    ∃ (i : _)(y : F.obj (D.U i)), F.map (D.ι i) y = x := by
  let e := D.glued_iso F
  obtain ⟨i, y, eq⟩ := (D.map_glue_data F).types_ι_jointly_surjective (e.hom x)
  replace eq := congr_arg e.inv Eq
  change ((D.map_glue_data F).ι i ≫ e.inv) y = (e.hom ≫ e.inv) x at eq
  rw [e.hom_inv_id, D.ι_glued_iso_inv] at eq
  exact ⟨i, y, Eq⟩

end GlueData

end CategoryTheory

