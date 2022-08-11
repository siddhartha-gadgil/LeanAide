/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace
import Mathbin.Topology.Category.Top.Limits
import Mathbin.Topology.Sheaves.Limits
import Mathbin.CategoryTheory.Limits.ConcreteCategory

/-!
# `PresheafedSpace C` has colimits.

If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `Top` preserves these colimits.

When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheaved spaces.

Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.

Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)

The limit of this diagram then constitutes the colimit presheaf.
-/


noncomputable section

universe v' u' v u

open CategoryTheory

open Top

open Top.Presheaf

open TopologicalSpace

open Opposite

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Functor

variable {J : Type u'} [Category.{v'} J]

variable {C : Type u} [Category.{v} C]

namespace AlgebraicGeometry

namespace PresheafedSpace

attribute [local simp] eq_to_hom_map

@[simp]
theorem map_id_c_app (F : J ⥤ PresheafedSpace.{v} C) (j) (U) :
    (F.map (𝟙 j)).c.app (op U) =
      (Pushforward.id (F.obj j).Presheaf).inv.app (op U) ≫
        (pushforwardEq
                (by
                  simp
                  rfl)
                (F.obj j).Presheaf).Hom.app
          (op U) :=
  by
  cases U
  dsimp'
  simp [← PresheafedSpace.congr_app (F.map_id j)]
  rfl

@[simp]
theorem map_comp_c_app (F : J ⥤ PresheafedSpace.{v} C) {j₁ j₂ j₃} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (U) :
    (F.map (f ≫ g)).c.app (op U) =
      (F.map g).c.app (op U) ≫
        (pushforwardMap (F.map g).base (F.map f).c).app (op U) ≫
          (Pushforward.comp (F.obj j₁).Presheaf (F.map f).base (F.map g).base).inv.app (op U) ≫
            (pushforwardEq
                    (by
                      rw [F.map_comp]
                      rfl)
                    _).Hom.app
              _ :=
  by
  cases U
  dsimp'
  simp only [← PresheafedSpace.congr_app (F.map_comp f g)]
  dsimp'
  simp
  dsimp'
  simp

/-- Given a diagram of `PresheafedSpace C`s, its colimit is computed by pushing the sheaves onto
the colimit of the underlying spaces, and taking componentwise limit.
This is the componentwise diagram for an open set `U` of the colimit of the underlying spaces.
-/
-- See note [dsimp, simp]
@[simps]
def componentwiseDiagram (F : J ⥤ PresheafedSpace.{v} C) [HasColimit F] (U : Opens (Limits.colimit F).Carrier) :
    Jᵒᵖ ⥤ C where
  obj := fun j => (F.obj (unop j)).Presheaf.obj (op ((Opens.map (colimit.ι F (unop j)).base).obj U))
  map := fun j k f =>
    (F.map f.unop).c.app _ ≫
      (F.obj (unop k)).Presheaf.map
        (eqToHom
          (by
            rw [← colimit.w F f.unop, comp_base]
            rfl))
  map_comp' := fun i j k f g => by
    cases U
    dsimp'
    simp_rw [map_comp_c_app, category.assoc]
    congr 1
    rw [Top.Presheaf.Pushforward.comp_inv_app, Top.Presheaf.pushforward_eq_hom_app,
      CategoryTheory.NatTrans.naturality_assoc, Top.Presheaf.pushforward_map_app]
    congr 1
    rw [category.id_comp, ← (F.obj (unop k)).Presheaf.map_comp]
    erw [← (F.obj (unop k)).Presheaf.map_comp]
    congr

variable [HasColimitsOfShape J Top.{v}]

/-- Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topological spaces,
obtaining a diagram in `(presheaf C X)ᵒᵖ`.
-/
@[simps]
def pushforwardDiagramToColimit (F : J ⥤ PresheafedSpace.{v} C) :
    J ⥤ (Presheaf C (colimit (F ⋙ PresheafedSpace.forget C)))ᵒᵖ where
  obj := fun j => op (colimit.ι (F ⋙ PresheafedSpace.forget C) j _* (F.obj j).Presheaf)
  map := fun j j' f =>
    (pushforwardMap (colimit.ι (F ⋙ PresheafedSpace.forget C) j') (F.map f).c ≫
        (Pushforward.comp (F.obj j).Presheaf ((F ⋙ PresheafedSpace.forget C).map f)
              (colimit.ι (F ⋙ PresheafedSpace.forget C) j')).inv ≫
          (pushforwardEq (colimit.w (F ⋙ PresheafedSpace.forget C) f) (F.obj j).Presheaf).Hom).op
  map_id' := fun j => by
    apply (op_equiv _ _).Injective
    ext U
    induction U using Opposite.rec
    cases U
    dsimp'
    simp
    dsimp'
    simp
  map_comp' := fun j₁ j₂ j₃ f g => by
    apply (op_equiv _ _).Injective
    ext U
    dsimp'
    simp only [← map_comp_c_app, ← id.def, ← eq_to_hom_op, ← pushforward_map_app, ← eq_to_hom_map, ← assoc, ← id_comp, ←
      pushforward.comp_inv_app, ← pushforward_eq_hom_app]
    dsimp'
    simp only [← eq_to_hom_trans, ← id_comp]
    congr 1
    -- The key fact is `(F.map f).c.congr`,
    -- which allows us in rewrite in the argument of `(F.map f).c.app`.
    rw [(F.map f).c.congr]
    -- Now we pick up the pieces. First, we say what we want to replace that open set by:
    pick_goal 3
    refine' op ((opens.map (colimit.ι (F ⋙ PresheafedSpace.forget C) j₂)).obj (unop U))
    -- Now we show the open sets are equal.
    swap
    · apply unop_injective
      rw [← opens.map_comp_obj]
      congr
      exact colimit.w (F ⋙ PresheafedSpace.forget C) g
      
    -- Finally, the original goal is now easy:
    swap
    · simp
      rfl
      

variable [∀ X : Top.{v}, HasLimitsOfShape Jᵒᵖ (X.Presheaf C)]

/-- Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
def colimit (F : J ⥤ PresheafedSpace.{v} C) : PresheafedSpace C where
  Carrier := colimit (F ⋙ PresheafedSpace.forget C)
  Presheaf := limit (pushforwardDiagramToColimit F).leftOp

@[simp]
theorem colimit_carrier (F : J ⥤ PresheafedSpace.{v} C) :
    (colimit F).Carrier = Limits.colimit (F ⋙ PresheafedSpace.forget C) :=
  rfl

@[simp]
theorem colimit_presheaf (F : J ⥤ PresheafedSpace.{v} C) :
    (colimit F).Presheaf = limit (pushforwardDiagramToColimit F).leftOp :=
  rfl

/-- Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
@[simps]
def colimitCocone (F : J ⥤ PresheafedSpace.{v} C) : Cocone F where
  x := colimit F
  ι :=
    { app := fun j => { base := colimit.ι (F ⋙ PresheafedSpace.forget C) j, c := limit.π _ (op j) },
      naturality' := fun j j' f => by
        fapply PresheafedSpace.ext
        · ext x
          exact colimit.w_apply (F ⋙ PresheafedSpace.forget C) f x
          
        · ext U
          induction U using Opposite.rec
          cases U
          dsimp'
          simp only [← PresheafedSpace.id_c_app, ← eq_to_hom_op, ← eq_to_hom_map, ← assoc, ← pushforward.comp_inv_app]
          rw [← congr_arg nat_trans.app (limit.w (pushforward_diagram_to_colimit F).leftOp f.op)]
          dsimp'
          simp only [← eq_to_hom_op, ← eq_to_hom_map, ← assoc, ← id_comp, ← pushforward.comp_inv_app]
          congr
          dsimp'
          simp only [← id_comp]
          simpa
           }

variable [HasLimitsOfShape Jᵒᵖ C]

namespace ColimitCoconeIsColimit

/-- Auxiliary definition for `PresheafedSpace.colimit_cocone_is_colimit`.
-/
def descCApp (F : J ⥤ PresheafedSpace.{v} C) (s : Cocone F) (U : (Opens ↥s.x.Carrier)ᵒᵖ) :
    s.x.Presheaf.obj U ⟶
      (colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) _*
            limit (pushforwardDiagramToColimit F).leftOp).obj
        U :=
  by
  refine'
    limit.lift _ { x := s.X.presheaf.obj U, π := { app := fun j => _, naturality' := fun j j' f => _ } } ≫
      (limit_obj_iso_limit_comp_evaluation _ _).inv
  -- We still need to construct the `app` and `naturality'` fields omitted above.
  · refine' (s.ι.app (unop j)).c.app U ≫ (F.obj (unop j)).Presheaf.map (eq_to_hom _)
    dsimp'
    rw [← opens.map_comp_obj]
    simp
    
  · rw [PresheafedSpace.congr_app (s.w f.unop).symm U]
    dsimp'
    have w :=
      functor.congr_obj (congr_arg opens.map (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j)))
        (unop U)
    simp only [← opens.map_comp_obj_unop] at w
    replace w := congr_arg op w
    have w' := nat_trans.congr (F.map f.unop).c w
    rw [w']
    dsimp'
    simp
    dsimp'
    simp
    

theorem desc_c_naturality (F : J ⥤ PresheafedSpace.{v} C) (s : Cocone F) {U V : (Opens ↥s.x.Carrier)ᵒᵖ} (i : U ⟶ V) :
    s.x.Presheaf.map i ≫ descCApp F s V =
      descCApp F s U ≫ (colimit.desc (F ⋙ forget C) ((forget C).mapCocone s) _* (colimitCocone F).x.Presheaf).map i :=
  by
  dsimp' [← desc_c_app]
  ext
  simp only [← limit.lift_π, ← nat_trans.naturality, ← limit.lift_π_assoc, ← eq_to_hom_map, ← assoc, ←
    pushforward_obj_map, ← nat_trans.naturality_assoc, ← op_map, ← limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc,
    ← limit_obj_iso_limit_comp_evaluation_inv_π_app]
  dsimp'
  have w :=
    functor.congr_hom (congr_arg opens.map (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j))) i.unop
  simp only [← opens.map_comp_map] at w
  replace w := congr_arg Quiver.Hom.op w
  rw [w]
  dsimp'
  simp

/-- Auxiliary definition for `PresheafedSpace.colimit_cocone_is_colimit`.
-/
def desc (F : J ⥤ PresheafedSpace.{v} C) (s : Cocone F) : colimit F ⟶ s.x where
  base := colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s)
  c := { app := fun U => descCApp F s U, naturality' := fun U V i => desc_c_naturality F s i }

theorem desc_fac (F : J ⥤ PresheafedSpace.{v} C) (s : Cocone F) (j : J) :
    (colimitCocone F).ι.app j ≫ desc F s = s.ι.app j := by
  fapply PresheafedSpace.ext
  · simp [← desc]
    
  · ext
    dsimp' [← desc, ← desc_c_app]
    simpa
    

end ColimitCoconeIsColimit

open ColimitCoconeIsColimit

/-- Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
def colimitCoconeIsColimit (F : J ⥤ PresheafedSpace.{v} C) : IsColimit (colimitCocone F) where
  desc := fun s => desc F s
  fac' := fun s => desc_fac F s
  uniq' := fun s m w => by
    -- We need to use the identity on the continuous maps twice, so we prepare that first:
    have t : m.base = colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) := by
      apply CategoryTheory.Limits.colimit.hom_ext
      intro j
      apply ContinuousMap.ext
      intro x
      dsimp'
      simp only [← colimit.ι_desc_apply, ← map_cocone_ι_app]
      rw [← w j]
      simp
    fapply PresheafedSpace.ext
    -- could `ext` please not reorder goals?
    · exact t
      
    · ext U j
      dsimp' [← desc, ← desc_c_app]
      simp only [← limit.lift_π, ← eq_to_hom_op, ← eq_to_hom_map, ← assoc, ←
        limit_obj_iso_limit_comp_evaluation_inv_π_app]
      rw [PresheafedSpace.congr_app (w (unop j)).symm U]
      dsimp'
      have w := congr_arg op (functor.congr_obj (congr_arg opens.map t) (unop U))
      rw [nat_trans.congr (limit.π (pushforward_diagram_to_colimit F).leftOp j) w]
      simp
      

instance :
    HasColimitsOfShape J
      (PresheafedSpace.{v}
        C) where HasColimit := fun F =>
    HasColimit.mk { Cocone := colimitCocone F, IsColimit := colimitCoconeIsColimit F }

instance :
    PreservesColimitsOfShape J
      (PresheafedSpace.forget
        C) where PreservesColimit := fun F =>
    preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit F)
      (by
        apply is_colimit.of_iso_colimit (colimit.is_colimit _)
        fapply cocones.ext
        · rfl
          
        · intro j
          dsimp'
          simp
          )

/-- When `C` has limits, the category of presheaved spaces with values in `C` itself has colimits.
-/
instance [HasLimits C] :
    HasColimits
      (PresheafedSpace.{v}
        C) where HasColimitsOfShape := fun J 𝒥 =>
    { HasColimit := fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_cocone_is_colimit F } }

/-- The underlying topological space of a colimit of presheaved spaces is
the colimit of the underlying topological spaces.
-/
instance forgetPreservesColimits [HasLimits C] :
    PreservesColimits
      (PresheafedSpace.forget
        C) where PreservesColimitsOfShape := fun J 𝒥 =>
    { PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
          (by
            apply is_colimit.of_iso_colimit (colimit.is_colimit _)
            fapply cocones.ext
            · rfl
              
            · intro j
              dsimp'
              simp
              ) }

/-- The components of the colimit of a diagram of `PresheafedSpace C` is obtained
via taking componentwise limits.
-/
def colimitPresheafObjIsoComponentwiseLimit (F : J ⥤ PresheafedSpace.{v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).Carrier) :
    (Limits.colimit F).Presheaf.obj (op U) ≅ limit (componentwiseDiagram F U) := by
  refine' ((sheaf_iso_of_iso (colimit.iso_colimit_cocone ⟨_, colimit_cocone_is_colimit F⟩).symm).app (op U)).trans _
  refine' (limit_obj_iso_limit_comp_evaluation _ _).trans (limits.lim.map_iso _)
  fapply nat_iso.of_components
  · intro X
    refine' (F.obj (unop X)).Presheaf.mapIso (eq_to_iso _)
    dsimp' only [← functor.op, ← unop_op, ← opens.map]
    congr 2
    rw [Set.preimage_preimage]
    simp_rw [← comp_app]
    congr 2
    exact ι_preserves_colimits_iso_inv (forget C) F (unop X)
    
  · intro X Y f
    change ((F.map f.unop).c.app _ ≫ _ ≫ _) ≫ (F.obj (unop Y)).Presheaf.map _ = _ ≫ _
    rw [Top.Presheaf.Pushforward.comp_inv_app]
    erw [category.id_comp]
    rw [category.assoc]
    erw [← (F.obj (unop Y)).Presheaf.map_comp, (F.map f.unop).c.naturality_assoc, ← (F.obj (unop Y)).Presheaf.map_comp]
    congr
    

@[simp]
theorem colimit_presheaf_obj_iso_componentwise_limit_inv_ι_app (F : J ⥤ PresheafedSpace.{v} C)
    (U : Opens (Limits.colimit F).Carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).inv ≫ (colimit.ι F j).c.app (op U) = limit.π _ (op j) := by
  delta' colimit_presheaf_obj_iso_componentwise_limit
  rw [iso.trans_inv, iso.trans_inv, iso.app_inv, sheaf_iso_of_iso_inv, pushforward_to_of_iso_app,
    congr_app (iso.symm_inv _)]
  simp_rw [category.assoc]
  rw [← functor.map_comp_assoc, nat_trans.naturality]
  erw [← comp_c_app_assoc]
  rw [congr_app (colimit.iso_colimit_cocone_ι_hom _ _)]
  simp_rw [category.assoc]
  erw [limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc, lim_map_π_assoc]
  convert category.comp_id _
  erw [← (F.obj j).Presheaf.map_id]
  iterate 2 
    erw [← (F.obj j).Presheaf.map_comp]
  congr

@[simp]
theorem colimit_presheaf_obj_iso_componentwise_limit_hom_π (F : J ⥤ PresheafedSpace.{v} C)
    (U : Opens (Limits.colimit F).Carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).Hom ≫ limit.π _ (op j) = (colimit.ι F j).c.app (op U) := by
  rw [← iso.eq_inv_comp, colimit_presheaf_obj_iso_componentwise_limit_inv_ι_app]

end PresheafedSpace

end AlgebraicGeometry

