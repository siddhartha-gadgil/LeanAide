/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace.HasColimits
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathbin.Topology.Sheaves.Functors
import Mathbin.AlgebraicGeometry.Scheme
import Mathbin.CategoryTheory.Limits.Shapes.StrictInitial
import Mathbin.Algebra.Category.Ring.Instances

/-!
# Open immersions of structured spaces

We say that a morphism of presheafed spaces `f : X ⟶ Y` is an open immersions if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Abbreviations are also provided for `SheafedSpace`, `LocallyRingedSpace` and `Scheme`.

## Main definitions

* `algebraic_geometry.PresheafedSpace.is_open_immersion`: the `Prop`-valued typeclass asserting
  that a PresheafedSpace hom `f` is an open_immersion.
* `algebraic_geometry.is_open_immersion`: the `Prop`-valued typeclass asserting
  that a Scheme morphism `f` is an open_immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.lift`: Any morphism whose range is
  contained in an open immersion factors though the open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace`: If `f : X ⟶ Y` is an
  open immersion of presheafed spaces, and `Y` is a sheafed space, then `X` is also a sheafed
  space. The morphism as morphisms of sheafed spaces is given by `to_SheafedSpace_hom`.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace`: If `f : X ⟶ Y` is
  an open immersion of presheafed spaces, and `Y` is a locally ringed space, then `X` is also a
  locally ringed space. The morphism as morphisms of locally ringed spaces is given by
  `to_LocallyRingedSpace_hom`.

## Main results

* `algebraic_geometry.PresheafedSpace.is_open_immersion.comp`: The composition of two open
  immersions is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso`: An iso is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso`:
  A surjective open immersion is an isomorphism.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left`: If `f` is an open
  immersion, then the pullback `(f, g)` exists (and the forgetful functor to `Top` preserves it).
* `algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left`: Open immersions
  are stable under pullbacks.
* `algebraic_geometry.SheafedSpace.is_open_immersion.of_stalk_iso` An (topological) open embedding
  between two sheafed spaces is an open immersion if all the stalk maps are isomorphisms.

-/


open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
class PresheafedSpace.IsOpenImmersion {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) : Prop where
  base_open : OpenEmbedding f.base
  c_iso : ∀ U : Opens X, IsIso (f.c.app (op (base_open.IsOpenMap.Functor.obj U)))

/-- A morphism of SheafedSpaces is an open immersion if it is an open immersion as a morphism
of PresheafedSpaces
-/
abbrev SheafedSpace.IsOpenImmersion [HasProducts.{v} C] {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsOpenImmersion f

/-- A morphism of LocallyRingedSpaces is an open immersion if it is an open immersion as a morphism
of SheafedSpaces
-/
abbrev LocallyRingedSpace.IsOpenImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Prop :=
  SheafedSpace.IsOpenImmersion f.1

/-- A morphism of Schemes is an open immersion if it is an open immersion as a morphism
of LocallyRingedSpaces
-/
abbrev IsOpenImmersion {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  LocallyRingedSpace.IsOpenImmersion f

namespace PresheafedSpace.IsOpenImmersion

open PresheafedSpace

-- mathport name: «expris_open_immersion»
local notation "is_open_immersion" => PresheafedSpace.IsOpenImmersion

attribute [instance] is_open_immersion.c_iso

section

variable {X Y : PresheafedSpace.{v} C} {f : X ⟶ Y} (H : is_open_immersion f)

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev openFunctor :=
  H.base_open.IsOpenMap.Functor

/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps]
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
  PresheafedSpace.isoOfComponents (Iso.refl _)
    (by
      symm
      fapply nat_iso.of_components
      intro U
      refine' as_iso (f.c.app (op (H.open_functor.obj (unop U)))) ≪≫ X.presheaf.map_iso (eq_to_iso _)
      · induction U using Opposite.rec
        cases U
        dsimp' only [← IsOpenMap.functor, ← functor.op, ← opens.map]
        congr 2
        erw [Set.preimage_image_eq _ H.base_open.inj]
        rfl
        
      · intro U V i
        simp only [← CategoryTheory.eqToIso.hom, ← Top.Presheaf.pushforward_obj_map, ← category.assoc, ← functor.op_map,
          ← iso.trans_hom, ← as_iso_hom, ← functor.map_iso_hom, X.presheaf.map_comp]
        erw [f.c.naturality_assoc, ← X.presheaf.map_comp]
        congr
        )

@[simp]
theorem iso_restrict_hom_of_restrict : H.isoRestrict.Hom ≫ Y.ofRestrict _ = f := by
  ext
  · simp only [← comp_c_app, ← iso_restrict_hom_c_app, ← nat_trans.comp_app, ← eq_to_hom_refl, ← of_restrict_c_app, ←
      category.assoc, ← whisker_right_id']
    erw [category.comp_id, f.c.naturality_assoc, ← X.presheaf.map_comp]
    trans f.c.app x ≫ X.presheaf.map (𝟙 _)
    · congr
      
    · erw [X.presheaf.map_id, category.comp_id]
      
    
  · simp
    

@[simp]
theorem iso_restrict_inv_of_restrict : H.isoRestrict.inv ≫ f = Y.ofRestrict _ := by
  rw [iso.inv_comp_eq]
  simp

instance mono [H : is_open_immersion f] : Mono f := by
  rw [← H.iso_restrict_hom_of_restrict]
  apply mono_comp

/-- The composition of two open immersions is an open immersion. -/
instance comp {Z : PresheafedSpace C} (f : X ⟶ Y) [hf : is_open_immersion f] (g : Y ⟶ Z) [hg : is_open_immersion g] :
    is_open_immersion (f ≫ g) where
  base_open := hg.base_open.comp hf.base_open
  c_iso := fun U => by
    generalize_proofs h
    dsimp' only [← AlgebraicGeometry.PresheafedSpace.comp_c_app, ← unop_op, ← functor.op, ← comp_base, ←
      Top.Presheaf.pushforward_obj_obj, ← opens.map_comp_obj]
    apply is_iso.comp_is_iso with { instances := false }
    swap
    · have : (opens.map g.base).obj (h.functor.obj U) = hf.open_functor.obj U := by
        dsimp' only [← opens.map, ← IsOpenMap.functor, ← PresheafedSpace.comp_base]
        congr 1
        rw [coe_comp, ← Set.image_image, Set.preimage_image_eq _ hg.base_open.inj]
      rw [this]
      infer_instance
      
    · have : h.functor.obj U = hg.open_functor.obj (hf.open_functor.obj U) := by
        dsimp' only [← IsOpenMap.functor]
        congr 1
        rw [comp_base, coe_comp, ← Set.image_image]
        congr
      rw [this]
      infer_instance
      

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable def invApp (U : Opens X) : X.Presheaf.obj (op U) ⟶ Y.Presheaf.obj (op (H.openFunctor.obj U)) :=
  X.Presheaf.map
      (eqToHom
        (by
          simp [← opens.map, ← Set.preimage_image_eq _ H.base_open.inj])) ≫
    inv (f.c.app (op (H.openFunctor.obj U)))

@[simp, reassoc]
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.Presheaf.map i ≫ H.inv_app (unop V) = H.inv_app (unop U) ≫ Y.Presheaf.map (H.openFunctor.op.map i) := by
  simp only [← inv_app, category.assoc]
  rw [is_iso.comp_inv_eq]
  simp only [← category.assoc, ← f.c.naturality, ← is_iso.inv_hom_id_assoc, X.presheaf.map_comp]
  erw [← X.presheaf.map_comp]
  congr

instance (U : Opens X) : IsIso (H.inv_app U) := by
  delta' inv_app
  infer_instance

theorem inv_inv_app (U : Opens X) :
    inv (H.inv_app U) =
      f.c.app (op (H.openFunctor.obj U)) ≫
        X.Presheaf.map
          (eqToHom
            (by
              simp [← opens.map, ← Set.preimage_image_eq _ H.base_open.inj])) :=
  by
  rw [← cancel_epi (H.inv_app U)]
  rw [is_iso.hom_inv_id]
  delta' inv_app
  simp [functor.map_comp]

@[simp, reassoc, elementwise]
theorem inv_app_app (U : Opens X) :
    H.inv_app U ≫ f.c.app (op (H.openFunctor.obj U)) =
      X.Presheaf.map
        (eqToHom
          (by
            simp [← opens.map, ← Set.preimage_image_eq _ H.base_open.inj])) :=
  by
  rw [inv_app, category.assoc, is_iso.inv_hom_id, category.comp_id]

@[simp, reassoc]
theorem app_inv_app (U : Opens Y) :
    f.c.app (op U) ≫ H.inv_app ((Opens.map f.base).obj U) =
      Y.Presheaf.map
        ((homOfLe (Set.image_preimage_subset f.base U)).op :
          op U ⟶ op (H.openFunctor.obj ((Opens.map f.base).obj U))) :=
  by
  erw [← category.assoc]
  rw [is_iso.comp_inv_eq, f.c.naturality]
  congr

/-- A variant of `app_inv_app` that gives an `eq_to_hom` instead of `hom_of_le`. -/
@[reassoc]
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.Range f.base) :
    f.c.app (op U) ≫ H.inv_app ((Opens.map f.base).obj U) =
      Y.Presheaf.map
        (eqToHom
            (by
              apply LE.le.antisymm
              · exact Set.image_preimage_subset f.base U.1
                
              · change U ⊆ _
                refine' LE.le.trans_eq _ (@Set.image_preimage_eq_inter_range _ _ f.base U.1).symm
                exact set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩
                )).op :=
  by
  erw [← category.assoc]
  rw [is_iso.comp_inv_eq, f.c.naturality]
  congr

/-- An isomorphism is an open immersion. -/
instance of_iso {X Y : PresheafedSpace.{v} C} (H : X ≅ Y) : is_open_immersion H.Hom where
  base_open := (Top.homeoOfIso ((forget C).mapIso H)).OpenEmbedding
  c_iso := fun _ => inferInstance

instance (priority := 100) of_is_iso {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) [IsIso f] : is_open_immersion f :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.of_iso (asIso f)

instance of_restrict {X : Top} (Y : PresheafedSpace C) {f : X ⟶ Y.Carrier} (hf : OpenEmbedding f) :
    is_open_immersion (Y.ofRestrict hf) where
  base_open := hf
  c_iso := fun U => by
    dsimp'
    have : (opens.map f).obj (hf.is_open_map.functor.obj U) = U := by
      cases U
      dsimp' only [← opens.map, ← IsOpenMap.functor]
      congr 1
      rw [Set.preimage_image_eq _ hf.inj]
      rfl
    convert show is_iso (Y.presheaf.map (𝟙 _)) from inferInstance
    · apply Subsingleton.helimₓ
      rw [this]
      
    · rw [Y.presheaf.map_id]
      infer_instance
      

@[elementwise, simp]
theorem of_restrict_inv_app {C : Type _} [Category C] (X : PresheafedSpace C) {Y : Top} {f : Y ⟶ Top.of X.Carrier}
    (h : OpenEmbedding f) (U : Opens (X.restrict h).Carrier) :
    (PresheafedSpace.IsOpenImmersion.of_restrict X h).inv_app U = 𝟙 _ := by
  delta' PresheafedSpace.is_open_immersion.inv_app
  rw [is_iso.comp_inv_eq, category.id_comp]
  change X.presheaf.map _ = X.presheaf.map _
  congr

/-- An open immersion is an iso if the underlying continuous map is epi. -/
theorem to_iso (f : X ⟶ Y) [h : is_open_immersion f] [h' : Epi f.base] : IsIso f := by
  apply is_iso_of_components with { instances := false }
  · let this : X ≃ₜ Y :=
      (Homeomorph.ofEmbedding _ h.base_open.to_embedding).trans
        { toFun := Subtype.val,
          invFun := fun x =>
            ⟨x, by
              rw [set.range_iff_surjective.mpr ((Top.epi_iff_surjective _).mp h')]
              trivial⟩,
          left_inv := fun ⟨_, _⟩ => rfl, right_inv := fun _ => rfl }
    convert is_iso.of_iso (Top.isoOfHomeo this)
    · ext
      rfl
      
    
  · apply nat_iso.is_iso_of_is_iso_app with { instances := false }
    intro U
    have : U = op (h.open_functor.obj ((opens.map f.base).obj (unop U))) := by
      induction U using Opposite.rec
      cases U
      dsimp' only [← functor.op, ← opens.map]
      congr
      exact (Set.image_preimage_eq _ ((Top.epi_iff_surjective _).mp h')).symm
    convert @is_open_immersion.c_iso _ h ((opens.map f.base).obj (unop U))
    

instance stalk_iso [HasColimits C] [H : is_open_immersion f] (x : X) : IsIso (stalkMap f x) := by
  rw [← H.iso_restrict_hom_of_restrict]
  rw [PresheafedSpace.stalk_map.comp]
  infer_instance

end

section Pullback

noncomputable section

variable {X Y Z : PresheafedSpace.{v} C} (f : X ⟶ Z) [hf : is_open_immersion f] (g : Y ⟶ Z)

include hf

/-- (Implementation.) The projection map when constructing the pullback along an open immersion.
-/
def pullbackConeOfLeftFst : Y.restrict (Top.snd_open_embedding_of_left_open_embedding hf.base_open g.base) ⟶ X where
  base := pullback.fst
  c :=
    { app := fun U =>
        hf.inv_app (unop U) ≫
          g.c.app (op (hf.base_open.IsOpenMap.Functor.obj (unop U))) ≫
            Y.Presheaf.map
              (eqToHom
                (by
                  simp only [← IsOpenMap.functor, ← Subtype.mk_eq_mk, ← unop_op, ← op_inj_iff, ← opens.map, ←
                    Subtype.coe_mk, ← functor.op_obj, ← Subtype.val_eq_coe]
                  apply LE.le.antisymm
                  · rintro _ ⟨_, h₁, h₂⟩
                    use (Top.pullbackIsoProdSubtype _ _).inv ⟨⟨_, _⟩, h₂⟩
                    simpa using h₁
                    
                  · rintro _ ⟨x, h₁, rfl⟩
                    exact ⟨_, h₁, concrete_category.congr_hom pullback.condition x⟩
                    )),
      naturality' := by
        intro U V i
        induction U using Opposite.rec
        induction V using Opposite.rec
        simp only [← Quiver.Hom.unop_op, ← Top.Presheaf.pushforward_obj_map, ← category.assoc, ←
          nat_trans.naturality_assoc, ← functor.op_map, ← inv_naturality_assoc, Y.presheaf.map_comp]
        erw [← Y.presheaf.map_comp]
        congr }

theorem pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.ofRestrict _ ≫ g := by
  ext U
  · induction U using Opposite.rec
    dsimp' only [← comp_c_app, ← nat_trans.comp_app, ← unop_op, ← whisker_right_app, ← pullback_cone_of_left_fst]
    simp only [← Quiver.Hom.unop_op, ← Top.Presheaf.pushforward_obj_map, ← app_inv_app_assoc, ← eq_to_hom_app, ←
      eq_to_hom_unop, ← category.assoc, ← nat_trans.naturality_assoc, ← functor.op_map]
    erw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
    congr
    
  · simpa using pullback.condition
    

/-- We construct the pullback along an open immersion via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
def pullbackConeOfLeft : PullbackCone f g :=
  PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.ofRestrict _) (pullback_cone_of_left_condition f g)

variable (s : PullbackCone f g)

/-- (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-/
def pullbackConeOfLeftLift : s.x ⟶ (pullbackConeOfLeft f g).x where
  base := pullback.lift s.fst.base s.snd.base (congr_arg (fun x => PresheafedSpace.Hom.base x) s.condition)
  c :=
    { app := fun U =>
        s.snd.c.app _ ≫
          s.x.Presheaf.map
            (eqToHom
              (by
                dsimp' only [← opens.map, ← IsOpenMap.functor, ← functor.op]
                congr 2
                let s' : pullback_cone f.base g.base := pullback_cone.mk s.fst.base s.snd.base _
                have : _ = s.snd.base := limit.lift_π s' walking_cospan.right
                conv_lhs => erw [← this]rw [coe_comp]erw [← Set.preimage_preimage]
                erw [Set.preimage_image_eq _ (Top.snd_open_embedding_of_left_open_embedding hf.base_open g.base).inj]
                simp )),
      naturality' := fun U V i => by
        erw [s.snd.c.naturality_assoc]
        rw [category.assoc]
        erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp]
        congr }

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullback_cone_of_left_lift_fst : pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).fst = s.fst := by
  ext x
  · induction x using Opposite.rec
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _
    simp_rw [category.assoc]
    erw [← s.X.presheaf.map_comp]
    erw [s.snd.c.naturality_assoc]
    have := congr_app s.condition (op (hf.open_functor.obj x))
    dsimp' only [← comp_c_app, ← unop_op]  at this
    rw [← is_iso.comp_inv_eq] at this
    reassoc! this
    erw [← this, hf.inv_app_app_assoc, s.fst.c.naturality_assoc]
    simpa [← eq_to_hom_map]
    
  · change pullback.lift _ _ _ ≫ pullback.fst = _
    simp
    

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullback_cone_of_left_lift_snd : pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).snd = s.snd := by
  ext x
  · change (_ ≫ _ ≫ _) ≫ _ = _
    simp_rw [category.assoc]
    erw [s.snd.c.naturality_assoc]
    erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp]
    trans s.snd.c.app x ≫ s.X.presheaf.map (𝟙 _)
    · congr
      
    · rw [s.X.presheaf.map_id]
      erw [category.comp_id]
      
    
  · change pullback.lift _ _ _ ≫ pullback.snd = _
    simp
    

instance pullback_cone_snd_is_open_immersion : is_open_immersion (pullbackConeOfLeft f g).snd := by
  erw [CategoryTheory.Limits.PullbackCone.mk_snd]
  infer_instance

/-- The constructed pullback cone is indeed the pullback. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) := by
  apply pullback_cone.is_limit_aux'
  intro s
  use pullback_cone_of_left_lift f g s
  use pullback_cone_of_left_lift_fst f g s
  use pullback_cone_of_left_lift_snd f g s
  intro m h₁ h₂
  rw [← cancel_mono (pullback_cone_of_left f g).snd]
  exact h₂.trans (pullback_cone_of_left_lift_snd f g s).symm

instance has_pullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

instance has_pullback_of_right : HasPullback g f :=
  has_pullback_symmetry f g

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left : is_open_immersion (pullback.snd : pullback f g ⟶ _) := by
  delta' pullback.snd
  rw [← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right]
  infer_instance

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right : is_open_immersion (pullback.fst : pullback g f ⟶ _) := by
  rw [← pullback_symmetry_hom_comp_snd]
  infer_instance

instance pullback_to_base_is_open_immersion [is_open_immersion g] :
    is_open_immersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) walking_cospan.hom.inl, cospan_map_inl]
  infer_instance

instance forgetPreservesLimitsOfLeft : PreservesLimit (cospan f g) (forget C) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (is_limit.postcompose_hom_equiv (diagramIsoCospan.{v} _) _).toFun
      refine' (is_limit.equiv_iso_limit _).toFun (limit.is_limit (cospan f.base g.base))
      fapply cones.ext
      exact iso.refl _
      change ∀ j, _ = 𝟙 _ ≫ _ ≫ _
      simp_rw [category.id_comp]
      rintro (_ | _ | _) <;> symm
      · erw [category.comp_id]
        exact limit.w (cospan f.base g.base) walking_cospan.hom.inl
        
      · exact category.comp_id _
        
      · exact category.comp_id _
        )

instance forgetPreservesLimitsOfRight : PreservesLimit (cospan g f) (forget C) :=
  preservesPullbackSymmetry (forget C) f g

theorem pullback_snd_is_iso_of_range_subset (H : Set.Range g.base ⊆ Set.Range f.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) := by
  have := Top.snd_iso_of_left_embedding_range_subset hf.base_open.to_embedding g.base H
  have : is_iso (pullback.snd : pullback f g ⟶ _).base := by
    delta' pullback.snd
    rw [← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right]
    change is_iso (_ ≫ pullback.snd)
    infer_instance
  apply to_iso

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H : Set.Range g.base ⊆ Set.Range f.base) : Y ⟶ X := by
  have := pullback_snd_is_iso_of_range_subset f g H
  exact inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst

@[simp, reassoc]
theorem lift_fac (H : Set.Range g.base ⊆ Set.Range f.base) : lift f g H ≫ f = g := by
  erw [category.assoc]
  rw [is_iso.inv_comp_eq]
  exact pullback.condition

theorem lift_uniq (H : Set.Range g.base ⊆ Set.Range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) : l = lift f g H := by
  rw [← cancel_mono f, hl, lift_fac]

/-- Two open immersions with equal range is isomorphic. -/
@[simps]
def isoOfRangeEq [is_open_immersion g] (e : Set.Range f.base = Set.Range g.base) : X ≅ Y where
  Hom := lift g f (le_of_eqₓ e)
  inv := lift f g (le_of_eqₓ e.symm)
  hom_inv_id' := by
    rw [← cancel_mono f]
    simp
  inv_hom_id' := by
    rw [← cancel_mono g]
    simp

end Pullback

open CategoryTheory.Limits.WalkingCospan

section ToSheafedSpace

variable [HasProducts.{v} C] {X : PresheafedSpace.{v} C} (Y : SheafedSpace C)

variable (f : X ⟶ Y.toPresheafedSpace) [H : is_open_immersion f]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
def toSheafedSpace : SheafedSpace C where
  IsSheaf := by
    apply Top.Presheaf.is_sheaf_of_iso (sheaf_iso_of_iso H.iso_restrict.symm).symm
    apply Top.Sheaf.pushforward_sheaf_of_sheaf
    exact (Y.restrict H.base_open).IsSheaf
  toPresheafedSpace := X

@[simp]
theorem to_SheafedSpace_to_PresheafedSpace : (toSheafedSpace Y f).toPresheafedSpace = X :=
  rfl

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a SheafedSpace, we can
upgrade it into a morphism of SheafedSpaces.
-/
def toSheafedSpaceHom : toSheafedSpace Y f ⟶ Y :=
  f

@[simp]
theorem to_SheafedSpace_hom_base : (toSheafedSpaceHom Y f).base = f.base :=
  rfl

@[simp]
theorem to_SheafedSpace_hom_c : (toSheafedSpaceHom Y f).c = f.c :=
  rfl

instance to_SheafedSpace_is_open_immersion : SheafedSpace.IsOpenImmersion (toSheafedSpaceHom Y f) :=
  H

omit H

@[simp]
theorem SheafedSpace_to_SheafedSpace {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) [is_open_immersion f] :
    toSheafedSpace Y f = X := by
  cases X
  rfl

end ToSheafedSpace

section ToLocallyRingedSpace

variable {X : PresheafedSpace.{u} CommRingₓₓ.{u}} (Y : LocallyRingedSpace.{u})

variable (f : X ⟶ Y.toPresheafedSpace) [H : is_open_immersion f]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a LocallyRingedSpace, then so is `X`. -/
def toLocallyRingedSpace : LocallyRingedSpace where
  toSheafedSpace := toSheafedSpace Y.toSheafedSpace f
  LocalRing := fun x => by
    have : LocalRing (Y.to_SheafedSpace.to_PresheafedSpace.stalk (f.base x)) := Y.local_ring _
    exact (as_iso (stalk_map f x)).commRingIsoToRingEquiv.LocalRing

@[simp]
theorem to_LocallyRingedSpace_to_SheafedSpace : (toLocallyRingedSpace Y f).toSheafedSpace = toSheafedSpace Y.1 f :=
  rfl

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a LocallyRingedSpace, we can
upgrade it into a morphism of LocallyRingedSpace.
-/
def toLocallyRingedSpaceHom : toLocallyRingedSpace Y f ⟶ Y :=
  ⟨f, fun x => inferInstance⟩

@[simp]
theorem to_LocallyRingedSpace_hom_val : (toLocallyRingedSpaceHom Y f).val = f :=
  rfl

instance to_LocallyRingedSpace_is_open_immersion : LocallyRingedSpace.IsOpenImmersion (toLocallyRingedSpaceHom Y f) :=
  H

omit H

@[simp]
theorem LocallyRingedSpace_to_LocallyRingedSpace {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] :
    @toLocallyRingedSpace X.toPresheafedSpace Y (@coe (@coeToLift (@coeBaseₓ coeSubtype)) f)
        (show is_open_immersion f.val by
          infer_instance) =
      X :=
  by
  cases X
  delta' to_LocallyRingedSpace
  simp

end ToLocallyRingedSpace

theorem is_iso_of_subset {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) [H : PresheafedSpace.IsOpenImmersion f]
    (U : Opens Y.Carrier) (hU : (U : Set Y.Carrier) ⊆ Set.Range f.base) : IsIso (f.c.app <| op U) := by
  have : U = H.base_open.is_open_map.functor.obj ((opens.map f.base).obj U) := by
    ext1
    exact (set.inter_eq_left_iff_subset.mpr hU).symm.trans set.image_preimage_eq_inter_range.symm
  convert PresheafedSpace.is_open_immersion.c_iso ((opens.map f.base).obj U)

end PresheafedSpace.IsOpenImmersion

namespace SheafedSpace.IsOpenImmersion

variable [HasProducts.{v} C]

instance (priority := 100) of_is_iso {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) [IsIso f] :
    SheafedSpace.IsOpenImmersion f :=
  @PresheafedSpace.IsOpenImmersion.of_is_iso _ f (SheafedSpace.forgetToPresheafedSpace.map_is_iso _)

instance comp {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpenImmersion f]
    [SheafedSpace.IsOpenImmersion g] : SheafedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f g

section Pullback

variable {X Y Z : SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : SheafedSpace.IsOpenImmersion f]

include H

-- mathport name: «exprforget»
local notation "forget" => SheafedSpace.forgetToPresheafedSpace

open CategoryTheory.Limits.WalkingCospan

instance : Mono f :=
  forget.mono_of_mono_map
    (show @Mono (PresheafedSpace C) _ _ _ f by
      infer_instance)

instance forget_map_is_open_immersion : PresheafedSpace.IsOpenImmersion (forget.map f) :=
  ⟨H.base_open, H.c_iso⟩

instance has_limit_cospan_forget_of_left : HasLimit (cospan f g ⋙ forget) := by
  apply has_limit_of_iso (diagramIsoCospan.{v} _).symm
  change has_limit (cospan (forget.map f) (forget.map g))
  infer_instance

instance has_limit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map f) (forget.map g)) from inferInstance

instance has_limit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  apply has_limit_of_iso (diagramIsoCospan.{v} _).symm
  change has_limit (cospan (forget.map g) (forget.map f))
  infer_instance

instance has_limit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map g) (forget.map f)) from inferInstance

instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y (@pullback.snd (PresheafedSpace C) _ _ _ _ f g _))
    (eqToIso
        (show pullback _ _ = pullback _ _ by
          congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y (@pullback.fst (PresheafedSpace C) _ _ _ _ g f _))
    (eqToIso
        (show pullback _ _ = pullback _ _ by
          congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

instance sheafedSpaceForgetPreservesOfLeft : PreservesLimit (cospan f g) (SheafedSpace.forget C) :=
  @Limits.compPreservesLimit _ _ _ _ forget (PresheafedSpace.forget C) _
    (by
      apply preserves_limit_of_iso_diagram _ (diagramIsoCospan.{v} _).symm with { instances := true }
      dsimp'
      infer_instance)

instance sheafedSpaceForgetPreservesOfRight : PreservesLimit (cospan g f) (SheafedSpace.forget C) :=
  preservesPullbackSymmetry _ _ _

instance SheafedSpace_has_pullback_of_left : HasPullback f g :=
  has_limit_of_created (cospan f g) forget

instance SheafedSpace_has_pullback_of_right : HasPullback g f :=
  has_limit_of_created (cospan g f) forget

/-- Open immersions are stable under base-change. -/
instance SheafedSpace_pullback_snd_of_left : SheafedSpace.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) := by
  delta' pullback.snd
  have : _ = limit.π (cospan f g) right := preserves_limits_iso_hom_π forget (cospan f g) right
  rw [← this]
  have := has_limit.iso_of_nat_iso_hom_π (diagramIsoCospan.{v} (cospan f g ⋙ forget)) right
  erw [category.comp_id] at this
  rw [← this]
  dsimp'
  infer_instance

instance SheafedSpace_pullback_fst_of_right : SheafedSpace.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) := by
  delta' pullback.fst
  have : _ = limit.π (cospan g f) left := preserves_limits_iso_hom_π forget (cospan g f) left
  rw [← this]
  have := has_limit.iso_of_nat_iso_hom_π (diagramIsoCospan.{v} (cospan g f ⋙ forget)) left
  erw [category.comp_id] at this
  rw [← this]
  dsimp'
  infer_instance

instance SheafedSpace_pullback_to_base_is_open_immersion [SheafedSpace.IsOpenImmersion g] :
    SheafedSpace.IsOpenImmersion (limit.π (cospan f g) one : pullback f g ⟶ Z) := by
  rw [← limit.w (cospan f g) hom.inl, cospan_map_inl]
  infer_instance

end Pullback

section OfStalkIso

variable [HasLimits C] [HasColimits C] [ConcreteCategory.{v} C]

variable [ReflectsIsomorphisms (forget C)] [PreservesLimits (forget C)]

variable [PreservesFilteredColimits (forget C)]

/-- Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered colimits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
theorem of_stalk_iso {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : OpenEmbedding f.base)
    [H : ∀ x : X, IsIso (PresheafedSpace.stalkMap f x)] : SheafedSpace.IsOpenImmersion f :=
  { base_open := hf,
    c_iso := fun U => by
      apply
        Top.Presheaf.app_is_iso_of_stalk_functor_map_iso
          (show Y.sheaf ⟶ (Top.Sheaf.pushforward f.base).obj X.sheaf from f.c) with
        { instances := false }
      rintro ⟨_, y, hy, rfl⟩
      specialize H y
      delta' PresheafedSpace.stalk_map  at H
      have H' := Top.Presheaf.stalkPushforward.stalk_pushforward_iso_of_open_embedding C hf X.presheaf y
      have := @is_iso.comp_is_iso _ H (@is_iso.inv_is_iso _ H')
      rw [category.assoc, is_iso.hom_inv_id, category.comp_id] at this
      exact this }

end OfStalkIso

section Prod

variable [HasLimits C] {ι : Type v} (F : Discrete ι ⥤ SheafedSpace C) [HasColimit F] (i : Discrete ι)

theorem sigma_ι_open_embedding : OpenEmbedding (colimit.ι F i).base := by
  rw [← show _ = (colimit.ι F i).base from ι_preserves_colimits_iso_inv (SheafedSpace.forget C) F i]
  have : _ = _ ≫ colimit.ι (discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ discrete.mk)) i :=
    has_colimit.iso_of_nat_iso_ι_hom discrete.nat_iso_functor i
  rw [← iso.eq_comp_inv] at this
  rw [this]
  have : colimit.ι _ _ ≫ _ = _ := Top.sigma_iso_sigma_hom_ι.{v, v} ((F ⋙ SheafedSpace.forget C).obj ∘ discrete.mk) i.as
  rw [← iso.eq_comp_inv] at this
  cases i
  rw [this]
  simp_rw [← category.assoc, Top.open_embedding_iff_comp_is_iso, Top.open_embedding_iff_is_iso_comp]
  dsimp'
  exact open_embedding_sigma_mk

theorem image_preimage_is_empty (j : Discrete ι) (h : i ≠ j) (U : Opens (F.obj i)) :
    (Opens.map (colimit.ι (F ⋙ SheafedSpace.forget_to_PresheafedSpace) j).base).obj
        ((Opens.map (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
          ((sigma_ι_open_embedding F i).IsOpenMap.Functor.obj U)) =
      ∅ :=
  by
  ext
  apply iff_false_intro
  rintro ⟨y, hy, eq⟩
  replace eq :=
    concrete_category.congr_arg
      (preserves_colimit_iso (SheafedSpace.forget C) F ≪≫
          has_colimit.iso_of_nat_iso discrete.nat_iso_functor ≪≫ Top.sigmaIsoSigma.{v} _).Hom
      Eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← Top.comp_app, ← PresheafedSpace.comp_base] at eq
  rw [ι_preserves_colimits_iso_inv] at eq
  change ((SheafedSpace.forget C).map (colimit.ι F i) ≫ _) y = ((SheafedSpace.forget C).map (colimit.ι F j) ≫ _) x at eq
  cases i
  cases j
  rw [ι_preserves_colimits_iso_hom_assoc, ι_preserves_colimits_iso_hom_assoc, has_colimit.iso_of_nat_iso_ι_hom_assoc,
    has_colimit.iso_of_nat_iso_ι_hom_assoc, Top.sigma_iso_sigma_hom_ι.{v}, Top.sigma_iso_sigma_hom_ι.{v}] at eq
  exact h (congr_arg discrete.mk (congr_arg Sigma.fst Eq))

instance sigma_ι_is_open_immersion [HasStrictTerminalObjects C] : SheafedSpace.IsOpenImmersion (colimit.ι F i) where
  base_open := sigma_ι_open_embedding F i
  c_iso := fun U => by
    have e : colimit.ι F i = _ := (ι_preserves_colimits_iso_inv SheafedSpace.forget_to_PresheafedSpace F i).symm
    have H :
      OpenEmbedding
        (colimit.ι (F ⋙ SheafedSpace.forget_to_PresheafedSpace) i ≫
            (preserves_colimit_iso SheafedSpace.forget_to_PresheafedSpace F).inv).base :=
      e ▸ sigma_ι_open_embedding F i
    suffices
      is_iso
        ((colimit.ι (F ⋙ SheafedSpace.forget_to_PresheafedSpace) i ≫
                (preserves_colimit_iso SheafedSpace.forget_to_PresheafedSpace F).inv).c.app
          (op (H.is_open_map.functor.obj U)))
      by
      convert this
    rw [PresheafedSpace.comp_c_app, ← PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π]
    suffices
      is_iso
        (limit.π
          (PresheafedSpace.componentwise_diagram (F ⋙ SheafedSpace.forget_to_PresheafedSpace)
            ((opens.map (preserves_colimit_iso SheafedSpace.forget_to_PresheafedSpace F).inv.base).obj
              (unop <| op <| H.is_open_map.functor.obj U)))
          (op i))
      by
      skip
      infer_instance
    apply limit_π_is_iso_of_is_strict_terminal
    intro j hj
    induction j using Opposite.rec
    dsimp'
    convert (F.obj j).Sheaf.isTerminalOfEmpty
    convert image_preimage_is_empty F i j (fun h => hj (congr_arg op h.symm)) U
    exact (congr_arg PresheafedSpace.hom.base e).symm

end Prod

end SheafedSpace.IsOpenImmersion

namespace LocallyRingedSpace.IsOpenImmersion

section Pullback

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : LocallyRingedSpace.IsOpenImmersion f]

instance (priority := 100) of_is_iso [IsIso g] : LocallyRingedSpace.IsOpenImmersion g :=
  @PresheafedSpace.IsOpenImmersion.of_is_iso _ g.1
    ⟨⟨(inv g).1, by
        erw [← LocallyRingedSpace.comp_val]
        rw [is_iso.hom_inv_id]
        erw [← LocallyRingedSpace.comp_val]
        rw [is_iso.inv_hom_id]
        constructor <;> simpa⟩⟩

include H

instance comp (g : Z ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g] : LocallyRingedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f.1 g.1

instance mono : Mono f :=
  LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map
    (show Mono f.1 by
      infer_instance)

instance : SheafedSpace.IsOpenImmersion (LocallyRingedSpace.forgetToSheafedSpace.map f) :=
  H

/-- An explicit pullback cone over `cospan f g` if `f` is an open immersion. -/
def pullbackConeOfLeft : PullbackCone f g := by
  refine' pullback_cone.mk _ (Y.of_restrict (Top.snd_open_embedding_of_left_open_embedding H.base_open g.1.base)) _
  · use PresheafedSpace.is_open_immersion.pullback_cone_of_left_fst f.1 g.1
    intro x
    have :=
      PresheafedSpace.stalk_map.congr_hom _ _
        (PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition f.1 g.1) x
    rw [PresheafedSpace.stalk_map.comp, PresheafedSpace.stalk_map.comp] at this
    rw [← is_iso.eq_inv_comp] at this
    rw [this]
    infer_instance
    
  · exact Subtype.eq (PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition _ _)
    

instance : LocallyRingedSpace.IsOpenImmersion (pullbackConeOfLeft f g).snd :=
  show PresheafedSpace.IsOpenImmersion (Y.toPresheafedSpace.ofRestrict _) by
    infer_instance

/-- The constructed `pullback_cone_of_left` is indeed limiting. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  (PullbackCone.isLimitAux' _) fun s => by
    use
      PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift f.1 g.1
        (pullback_cone.mk s.fst.1 s.snd.1 (congr_arg Subtype.val s.condition))
    · intro x
      have :=
        PresheafedSpace.stalk_map.congr_hom _ _
          (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1
            (pullback_cone.mk s.fst.1 s.snd.1 (congr_arg Subtype.val s.condition)))
          x
      change _ = _ ≫ PresheafedSpace.stalk_map s.snd.1 x at this
      rw [PresheafedSpace.stalk_map.comp, ← is_iso.eq_inv_comp] at this
      rw [this]
      infer_instance
      
    constructor
    exact Subtype.eq (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_fst f.1 g.1 _)
    constructor
    exact Subtype.eq (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1 _)
    intro m h₁ h₂
    rw [← cancel_mono (pullback_cone_of_left f g).snd]
    exact
      h₂.trans
        (Subtype.eq
          (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1
              (pullback_cone.mk s.fst.1 s.snd.1 (congr_arg Subtype.val s.condition))).symm)

instance has_pullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

instance has_pullback_of_right : HasPullback g f :=
  has_pullback_symmetry f g

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left : LocallyRingedSpace.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) := by
  delta' pullback.snd
  rw [← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right]
  infer_instance

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right : LocallyRingedSpace.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) := by
  rw [← pullback_symmetry_hom_comp_snd]
  infer_instance

instance pullback_to_base_is_open_immersion [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) walking_cospan.hom.inl, cospan_map_inl]
  infer_instance

instance forgetPreservesPullbackOfLeft : PreservesLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (is_limit_map_cone_pullback_cone_equiv _ _).symm.toFun
      apply is_limit_of_is_limit_pullback_cone_map SheafedSpace.forget_to_PresheafedSpace
      exact PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit f.1 g.1)

instance forgetToPresheafedSpacePreservesPullbackOfLeft :
    PreservesLimit (cospan f g) (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (is_limit_map_cone_pullback_cone_equiv _ _).symm.toFun
      exact PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit f.1 g.1)

instance forget_to_PresheafedSpace_preserves_open_immersion :
    PresheafedSpace.IsOpenImmersion
      ((LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace).map f) :=
  H

instance forgetToTopPreservesPullbackOfLeft :
    PreservesLimit (cospan f g) (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _) := by
  change
    preserves_limit _
      ((LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) ⋙ PresheafedSpace.forget _)
  apply limits.comp_preserves_limit with { instances := false }
  infer_instance
  apply preserves_limit_of_iso_diagram _ (diagramIsoCospan.{u} _).symm
  dsimp' [← SheafedSpace.forget_to_PresheafedSpace, -Subtype.val_eq_coe]
  infer_instance

instance forgetReflectsPullbackOfLeft : ReflectsLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _

instance forgetPreservesPullbackOfRight : PreservesLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesPullbackSymmetry _ _ _

instance forgetToPresheafedSpacePreservesPullbackOfRight :
    PreservesLimit (cospan g f) (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) :=
  preservesPullbackSymmetry _ _ _

instance forgetReflectsPullbackOfRight : ReflectsLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _

instance forgetToPresheafedSpaceReflectsPullbackOfLeft :
    ReflectsLimit (cospan f g) (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _

instance forgetToPresheafedSpaceReflectsPullbackOfRight :
    ReflectsLimit (cospan g f) (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _

theorem pullback_snd_is_iso_of_range_subset (H' : Set.Range g.1.base ⊆ Set.Range f.1.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) := by
  apply reflects_isomorphisms.reflects LocallyRingedSpace.forget_to_SheafedSpace with { instances := false }
  apply reflects_isomorphisms.reflects SheafedSpace.forget_to_PresheafedSpace with { instances := false }
  erw [←
    preserves_pullback.iso_hom_snd (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace)
      f g]
  have := PresheafedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset _ _ H'
  infer_instance
  infer_instance

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.Range g.1.base ⊆ Set.Range f.1.base) : Y ⟶ X := by
  have := pullback_snd_is_iso_of_range_subset f g H'
  exact inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst

@[simp, reassoc]
theorem lift_fac (H' : Set.Range g.1.base ⊆ Set.Range f.1.base) : lift f g H' ≫ f = g := by
  erw [category.assoc]
  rw [is_iso.inv_comp_eq]
  exact pullback.condition

theorem lift_uniq (H' : Set.Range g.1.base ⊆ Set.Range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) : l = lift f g H' := by
  rw [← cancel_mono f, hl, lift_fac]

theorem lift_range (H' : Set.Range g.1.base ⊆ Set.Range f.1.base) :
    Set.Range (lift f g H').1.base = f.1.base ⁻¹' Set.Range g.1.base := by
  have := pullback_snd_is_iso_of_range_subset f g H'
  dsimp' only [← lift]
  have : _ = (pullback.fst : pullback f g ⟶ _).val.base :=
    preserves_pullback.iso_hom_fst (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _) f g
  rw [LocallyRingedSpace.comp_val, SheafedSpace.comp_base, ← this, ← category.assoc, coe_comp]
  rw [Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ, Top.pullback_fst_range]
  ext
  constructor
  · rintro ⟨y, eq⟩
    exact ⟨y, Eq.symm⟩
    
  · rintro ⟨y, eq⟩
    exact ⟨y, Eq.symm⟩
    
  · rw [← Top.epi_iff_surjective]
    rw
      [show (inv (pullback.snd : pullback f g ⟶ _)).val.base = _ from
        (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _).map_inv _]
    infer_instance
    

end Pullback

/-- An open immersion is isomorphic to the induced open subscheme on its image. -/
def isoRestrict {X Y : LocallyRingedSpace} {f : X ⟶ Y} (H : LocallyRingedSpace.IsOpenImmersion f) :
    X ≅ Y.restrict H.base_open := by
  apply LocallyRingedSpace.iso_of_SheafedSpace_iso
  refine' SheafedSpace.forget_to_PresheafedSpace.preimage_iso _
  exact H.iso_restrict

/-- To show that a locally ringed space is a scheme, it suffices to show that it has a jointly
surjective family of open immersions from affine schemes. -/
protected def scheme (X : LocallyRingedSpace)
    (h :
      ∀ x : X,
        ∃ (R : CommRingₓₓ)(f : Spec.toLocallyRingedSpace.obj (op R) ⟶ X),
          (x ∈ Set.Range f.1.base : _) ∧ LocallyRingedSpace.IsOpenImmersion f) :
    Scheme where
  toLocallyRingedSpace := X
  local_affine := by
    intro x
    obtain ⟨R, f, h₁, h₂⟩ := h x
    refine' ⟨⟨⟨_, h₂.base_open.open_range⟩, h₁⟩, R, ⟨_⟩⟩
    apply LocallyRingedSpace.iso_of_SheafedSpace_iso
    refine' SheafedSpace.forget_to_PresheafedSpace.preimage_iso _
    skip
    apply PresheafedSpace.is_open_immersion.iso_of_range_eq (PresheafedSpace.of_restrict _ _) f.1
    · exact Subtype.range_coe_subtype
      
    · infer_instance
      

end LocallyRingedSpace.IsOpenImmersion

theorem IsOpenImmersion.open_range {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] : IsOpen (Set.Range f.1.base) :=
  H.base_open.open_range

section OpenCover

namespace Scheme

/-- An open cover of `X` consists of a family of open immersions into `X`,
and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.

This is merely a coverage in the Zariski pretopology, and it would be optimal
if we could reuse the existing API about pretopologies, However, the definitions of sieves and
grothendieck topologies uses `Prop`s, so that the actual open sets and immersions are hard to
obtain. Also, since such a coverage in the pretopology usually contains a proper class of
immersions, it is quite hard to glue them, reason about finite covers, etc.
-/
-- TODO: provide API to and from a presieve.
structure OpenCover (X : Scheme.{u}) where
  J : Type v
  obj : ∀ j : J, Scheme
  map : ∀ j : J, obj j ⟶ X
  f : X.Carrier → J
  Covers : ∀ x, x ∈ Set.Range (map (f x)).1.base
  IsOpen : ∀ x, IsOpenImmersion (map x) := by
    run_tac
      tactic.apply_instance

attribute [instance] open_cover.is_open

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)

variable [∀ x, HasPullback (𝒰.map x ≫ f) g]

/-- The affine cover of a scheme. -/
def affineCover (X : Scheme) : OpenCover X where
  J := X.Carrier
  obj := fun x => spec.obj <| Opposite.op (X.local_affine x).some_spec.some
  map := fun x => ((X.local_affine x).some_spec.some_spec.some.inv ≫ X.toLocallyRingedSpace.ofRestrict _ : _)
  f := fun x => x
  IsOpen := fun x => by
    apply PresheafedSpace.is_open_immersion.comp with { instances := false }
    infer_instance
    apply PresheafedSpace.is_open_immersion.of_restrict
  Covers := by
    intro x
    erw [coe_comp]
    rw [Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ]
    erw [Subtype.range_coe_subtype]
    exact (X.local_affine x).some.2
    rw [← Top.epi_iff_surjective]
    change epi ((SheafedSpace.forget _).map (LocallyRingedSpace.forget_to_SheafedSpace.map _))
    infer_instance

instance : Inhabited X.OpenCover :=
  ⟨X.affineCover⟩

/-- Given an open cover `{ Uᵢ }` of `X`, and for each `Uᵢ` an open cover, we may combine these
open covers to form an open cover of `X`.  -/
@[simps J obj map]
def OpenCover.bind (f : ∀ x : 𝒰.J, OpenCover (𝒰.obj x)) : OpenCover X where
  J := Σi : 𝒰.J, (f i).J
  obj := fun x => (f x.1).obj x.2
  map := fun x => (f x.1).map x.2 ≫ 𝒰.map x.1
  f := fun x => ⟨_, (f _).f (𝒰.Covers x).some⟩
  Covers := fun x => by
    let y := (𝒰.covers x).some
    have hy : (𝒰.map (𝒰.f x)).val.base y = x := (𝒰.covers x).some_spec
    rcases(f (𝒰.f x)).Covers y with ⟨z, hz⟩
    change x ∈ Set.Range ((f (𝒰.f x)).map ((f (𝒰.f x)).f y) ≫ 𝒰.map (𝒰.f x)).1.base
    use z
    erw [comp_apply]
    rw [hz, hy]

/-- An isomorphism `X ⟶ Y` is an open cover of `Y`. -/
@[simps J obj map]
def openCoverOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : OpenCover Y where
  J := PUnit.{v + 1}
  obj := fun _ => X
  map := fun _ => f
  f := fun _ => PUnit.unit
  Covers := fun x => by
    rw [set.range_iff_surjective.mpr]
    · trivial
      
    rw [← Top.epi_iff_surjective]
    infer_instance

/-- We construct an open cover from another, by providing the needed fields and showing that the
provided fields are isomorphic with the original open cover. -/
@[simps J obj map]
def OpenCover.copy {X : Scheme} (𝒰 : OpenCover X) (J : Type _) (obj : J → Scheme) (map : ∀ i, obj i ⟶ X) (e₁ : J ≃ 𝒰.J)
    (e₂ : ∀ i, obj i ≅ 𝒰.obj (e₁ i)) (e₂ : ∀ i, map i = (e₂ i).Hom ≫ 𝒰.map (e₁ i)) : OpenCover X :=
  { J, obj, map, f := fun x => e₁.symm (𝒰.f x),
    Covers := fun x => by
      rw [e₂, Scheme.comp_val_base, coe_comp, Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ,
        e₁.right_inverse_symm]
      · exact 𝒰.covers x
        
      · rw [← Top.epi_iff_surjective]
        infer_instance
        ,
    IsOpen := fun i => by
      rw [e₂]
      infer_instance }

/-- The pushforward of an open cover along an isomorphism. -/
@[simps J obj map]
def OpenCover.pushforwardIso {X Y : Scheme} (𝒰 : OpenCover X) (f : X ⟶ Y) [IsIso f] : OpenCover Y :=
  ((openCoverOfIsIso f).bind fun _ => 𝒰).copy 𝒰.J _ _
    ((Equivₓ.punitProd _).symm.trans (Equivₓ.sigmaEquivProd PUnit 𝒰.J).symm) (fun _ => Iso.refl _) fun _ =>
    (Category.id_comp _).symm

/-- Adding an open immersion into an open cover gives another open cover. -/
@[simps]
def OpenCover.add {X : Scheme} (𝒰 : X.OpenCover) {Y : Scheme} (f : Y ⟶ X) [IsOpenImmersion f] : X.OpenCover where
  J := Option 𝒰.J
  obj := fun i => Option.rec Y 𝒰.obj i
  map := fun i => Option.rec f 𝒰.map i
  f := fun x => some (𝒰.f x)
  Covers := 𝒰.Covers
  IsOpen := by
    rintro (_ | _) <;> dsimp' <;> infer_instance

-- Related result : `open_cover.pullback_cover`, where we pullback an open cover on `X` along a
-- morphism `W ⟶ X`. This is provided at the end of the file since it needs some more results
-- about open immersion (which in turn needs the open cover API).
attribute [local reducible] CommRingₓₓ.of CommRingₓₓ.ofHom

instance val_base_is_iso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.1.base :=
  Scheme.forgetToTop.map_is_iso f

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
instance basic_open_is_open_immersion {R : CommRingₓₓ} (f : R) :
    AlgebraicGeometry.IsOpenImmersion (Scheme.spec.map (CommRingₓₓ.ofHom (algebraMap R (Localization.Away f))).op) := by
  apply SheafedSpace.is_open_immersion.of_stalk_iso with { instances := false }
  any_goals {
  }
  any_goals {
  }
  exact (PrimeSpectrum.localization_away_open_embedding (Localization.Away f) f : _)
  intro x
  exact Spec_map_localization_is_iso R (Submonoid.powers f) x

/-- The basic open sets form an affine open cover of `Spec R`. -/
def affineBasisCoverOfAffine (R : CommRingₓₓ) : OpenCover (spec.obj (Opposite.op R)) where
  J := R
  obj := fun r => spec.obj (Opposite.op <| CommRingₓₓ.of <| Localization.Away r)
  map := fun r => spec.map (Quiver.Hom.op (algebraMap R (Localization.Away r) : _))
  f := fun x => 1
  Covers := fun r => by
    rw [set.range_iff_surjective.mpr ((Top.epi_iff_surjective _).mp _)]
    · exact trivialₓ
      
    · infer_instance
      
  IsOpen := fun x => AlgebraicGeometry.Scheme.basic_open_is_open_immersion x

/-- We may bind the basic open sets of an open affine cover to form a affine cover that is also
a basis. -/
def affineBasisCover (X : Scheme) : OpenCover X :=
  X.affineCover.bind fun x => affineBasisCoverOfAffine _

/-- The coordinate ring of a component in the `affine_basis_cover`. -/
def affineBasisCoverRing (X : Scheme) (i : X.affineBasisCover.J) : CommRingₓₓ :=
  CommRingₓₓ.of <| @Localization.Away (X.local_affine i.1).some_spec.some _ i.2

theorem affine_basis_cover_obj (X : Scheme) (i : X.affineBasisCover.J) :
    X.affineBasisCover.obj i = spec.obj (op <| X.affineBasisCoverRing i) :=
  rfl

theorem affine_basis_cover_map_range (X : Scheme) (x : X.Carrier) (r : (X.local_affine x).some_spec.some) :
    Set.Range (X.affineBasisCover.map ⟨x, r⟩).1.base = (X.affineCover.map x).1.base '' (PrimeSpectrum.basicOpen r).1 :=
  by
  erw [coe_comp, Set.range_comp]
  congr
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r : _)

theorem affine_basis_cover_is_basis (X : Scheme) :
    TopologicalSpace.IsTopologicalBasis
      { x : Set X.Carrier | ∃ a : X.affineBasisCover.J, x = Set.Range (X.affineBasisCover.map a).1.base } :=
  by
  apply TopologicalSpace.is_topological_basis_of_open_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact is_open_immersion.open_range (X.affine_basis_cover.map a)
    
  · rintro a U haU hU
    rcases X.affine_cover.covers a with ⟨x, e⟩
    let U' := (X.affine_cover.map (X.affine_cover.f a)).1.base ⁻¹' U
    have hxU' : x ∈ U' := by
      rw [← e] at haU
      exact haU
    rcases prime_spectrum.is_basis_basic_opens.exists_subset_of_mem_open hxU'
        ((X.affine_cover.map (X.affine_cover.f a)).1.base.continuous_to_fun.is_open_preimage _ hU) with
      ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxV, hVU⟩
    refine' ⟨_, ⟨⟨_, s⟩, rfl⟩, _, _⟩ <;> erw [affine_basis_cover_map_range]
    · exact ⟨x, hxV, e⟩
      
    · rw [Set.image_subset_iff]
      exact hVU
      
    

/-- Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
@[simps obj map]
def OpenCover.finiteSubcover {X : Scheme} (𝒰 : OpenCover X) [H : CompactSpace X.Carrier] : OpenCover X := by
  have :=
    @CompactSpace.elim_nhds_subcover _ H (fun x : X.carrier => Set.Range (𝒰.map (𝒰.f x)).1.base) fun x =>
      (is_open_immersion.open_range (𝒰.map (𝒰.f x))).mem_nhds (𝒰.covers x)
  let t := this.some
  have h : ∀ x : X.carrier, ∃ y : t, x ∈ Set.Range (𝒰.map (𝒰.f y)).1.base := by
    intro x
    have h' : x ∈ (⊤ : Set X.carrier) := trivialₓ
    rw [← Classical.some_spec this, Set.mem_Union] at h'
    rcases h' with ⟨y, _, ⟨hy, rfl⟩, hy'⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  exact
    { J := t, obj := fun x => 𝒰.obj (𝒰.f x.1), map := fun x => 𝒰.map (𝒰.f x.1), f := fun x => (h x).some,
      Covers := fun x => (h x).some_spec }

instance [H : CompactSpace X.Carrier] : Fintype 𝒰.finiteSubcover.J := by
  delta' open_cover.finite_subcover
  infer_instance

end Scheme

end OpenCover

namespace PresheafedSpace.IsOpenImmersion

section ToScheme

variable {X : PresheafedSpace.{u} CommRingₓₓ.{u}} (Y : Scheme.{u})

variable (f : X ⟶ Y.toPresheafedSpace) [H : PresheafedSpace.IsOpenImmersion f]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a scheme, then so is `X`. -/
def toScheme : Scheme := by
  apply LocallyRingedSpace.is_open_immersion.Scheme (to_LocallyRingedSpace _ f)
  intro x
  obtain ⟨_, ⟨i, rfl⟩, hx, hi⟩ :=
    Y.affine_basis_cover_is_basis.exists_subset_of_mem_open (Set.mem_range_self x) H.base_open.open_range
  use Y.affine_basis_cover_ring i
  use LocallyRingedSpace.is_open_immersion.lift (to_LocallyRingedSpace_hom _ f) _ hi
  constructor
  · rw [LocallyRingedSpace.is_open_immersion.lift_range]
    exact hx
    
  · delta' LocallyRingedSpace.is_open_immersion.lift
    infer_instance
    

@[simp]
theorem to_Scheme_to_LocallyRingedSpace : (toScheme Y f).toLocallyRingedSpace = toLocallyRingedSpace Y.1 f :=
  rfl

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a Scheme, we can
upgrade it into a morphism of Schemes.
-/
def toSchemeHom : toScheme Y f ⟶ Y :=
  toLocallyRingedSpaceHom _ f

@[simp]
theorem to_Scheme_hom_val : (toSchemeHom Y f).val = f :=
  rfl

instance to_Scheme_hom_is_open_immersion : IsOpenImmersion (toSchemeHom Y f) :=
  H

omit H

theorem Scheme_eq_of_LocallyRingedSpace_eq {X Y : Scheme} (H : X.toLocallyRingedSpace = Y.toLocallyRingedSpace) :
    X = Y := by
  cases X
  cases Y
  congr
  exact H

theorem Scheme_to_Scheme {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : toScheme Y f.1 = X := by
  apply Scheme_eq_of_LocallyRingedSpace_eq
  exact LocallyRingedSpace_to_LocallyRingedSpace f

end ToScheme

end PresheafedSpace.IsOpenImmersion

/-- The restriction of a Scheme along an open embedding. -/
@[simps]
def Scheme.restrict {U : Top} (X : Scheme) {f : U ⟶ Top.of X.Carrier} (h : OpenEmbedding f) : Scheme :=
  { PresheafedSpace.IsOpenImmersion.toScheme X (X.toPresheafedSpace.ofRestrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }

/-- The canonical map from the restriction to the supspace. -/
@[simps]
def Scheme.ofRestrict {U : Top} (X : Scheme) {f : U ⟶ Top.of X.Carrier} (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  X.toLocallyRingedSpace.ofRestrict h

instance IsOpenImmersion.of_restrict {U : Top} (X : Scheme) {f : U ⟶ Top.of X.Carrier} (h : OpenEmbedding f) :
    IsOpenImmersion (X.ofRestrict h) :=
  show PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.ofRestrict h) by
    infer_instance

namespace IsOpenImmersion

variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : IsOpenImmersion f]

instance (priority := 100) of_is_iso [IsIso g] : IsOpenImmersion g :=
  @LocallyRingedSpace.IsOpenImmersion.of_is_iso _
    (show IsIso ((inducedFunctor _).map g) by
      infer_instance)

/-- A open immersion induces an isomorphism from the domain onto the image -/
def isoRestrict : X ≅ (Z.restrict H.base_open : _) :=
  ⟨H.isoRestrict.Hom, H.isoRestrict.inv, H.isoRestrict.hom_inv_id, H.isoRestrict.inv_hom_id⟩

include H

-- mathport name: «exprforget»
local notation "forget" => Scheme.forgetToLocallyRingedSpace

instance mono : Mono f :=
  (inducedFunctor _).mono_of_mono_map
    (show @Mono LocallyRingedSpace _ _ _ f by
      infer_instance)

instance forget_map_is_open_immersion : LocallyRingedSpace.IsOpenImmersion (forget.map f) :=
  ⟨H.base_open, H.c_iso⟩

instance has_limit_cospan_forget_of_left : HasLimit (cospan f g ⋙ Scheme.forget_to_LocallyRingedSpace) := by
  apply has_limit_of_iso (diagramIsoCospan.{u} _).symm
  change has_limit (cospan (forget.map f) (forget.map g))
  infer_instance

open CategoryTheory.Limits.WalkingCospan

instance has_limit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map f) (forget.map g)) from inferInstance

instance has_limit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  apply has_limit_of_iso (diagramIsoCospan.{u} _).symm
  change has_limit (cospan (forget.map g) (forget.map f))
  infer_instance

instance has_limit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map g) (forget.map f)) from inferInstance

instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (@pullback.snd LocallyRingedSpace _ _ _ _ f g _).1)
    (eqToIso
        (by
          simp ) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (@pullback.fst LocallyRingedSpace _ _ _ _ g f _).1)
    (eqToIso
        (by
          simp ) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

instance forgetPreservesOfLeft : PreservesLimit (cospan f g) forget :=
  CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit _ _

instance forgetPreservesOfRight : PreservesLimit (cospan g f) forget :=
  preservesPullbackSymmetry _ _ _

instance has_pullback_of_left : HasPullback f g :=
  has_limit_of_created (cospan f g) forget

instance has_pullback_of_right : HasPullback g f :=
  has_limit_of_created (cospan g f) forget

instance pullback_snd_of_left : IsOpenImmersion (pullback.snd : pullback f g ⟶ _) := by
  have := preserves_pullback.iso_hom_snd forget f g
  dsimp' only [← Scheme.forget_to_LocallyRingedSpace, ← induced_functor_map]  at this
  rw [← this]
  change LocallyRingedSpace.is_open_immersion _
  infer_instance

instance pullback_fst_of_right : IsOpenImmersion (pullback.fst : pullback g f ⟶ _) := by
  rw [← pullback_symmetry_hom_comp_snd]
  infer_instance

instance pullback_to_base [IsOpenImmersion g] : IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) walking_cospan.hom.inl]
  change is_open_immersion (_ ≫ f)
  infer_instance

instance forgetToTopPreservesOfLeft : PreservesLimit (cospan f g) Scheme.forgetToTop := by
  apply limits.comp_preserves_limit with { instances := false }
  infer_instance
  apply preserves_limit_of_iso_diagram _ (diagramIsoCospan.{u} _).symm
  dsimp' [← LocallyRingedSpace.forget_to_Top]
  infer_instance

instance forgetToTopPreservesOfRight : PreservesLimit (cospan g f) Scheme.forgetToTop :=
  preservesPullbackSymmetry _ _ _

theorem range_pullback_snd_of_left :
    Set.Range (pullback.snd : pullback f g ⟶ Y).1.base =
      (Opens.map g.1.base).obj ⟨Set.Range f.1.base, H.base_open.open_range⟩ :=
  by
  rw [← show _ = (pullback.snd : pullback f g ⟶ _).1.base from preserves_pullback.iso_hom_snd Scheme.forget_to_Top f g,
    coe_comp, Set.range_comp, set.range_iff_surjective.mpr, ←
    @Set.preimage_univ _ _ (pullback.fst : pullback f.1.base g.1.base ⟶ _), Top.pullback_snd_image_fst_preimage,
    Set.image_univ]
  rfl
  rw [← Top.epi_iff_surjective]
  infer_instance

theorem range_pullback_fst_of_right :
    Set.Range (pullback.fst : pullback g f ⟶ Y).1.base =
      (Opens.map g.1.base).obj ⟨Set.Range f.1.base, H.base_open.open_range⟩ :=
  by
  rw [← show _ = (pullback.fst : pullback g f ⟶ _).1.base from preserves_pullback.iso_hom_fst Scheme.forget_to_Top g f,
    coe_comp, Set.range_comp, set.range_iff_surjective.mpr, ←
    @Set.preimage_univ _ _ (pullback.snd : pullback g.1.base f.1.base ⟶ _), Top.pullback_fst_image_snd_preimage,
    Set.image_univ]
  rfl
  rw [← Top.epi_iff_surjective]
  infer_instance

theorem range_pullback_to_base_of_left :
    Set.Range (pullback.fst ≫ f : pullback f g ⟶ Z).1.base = Set.Range f.1.base ∩ Set.Range g.1.base := by
  rw [pullback.condition, Scheme.comp_val_base, coe_comp, Set.range_comp, range_pullback_snd_of_left, opens.map_obj,
    Subtype.coe_mk, Set.image_preimage_eq_inter_range, Set.inter_comm]

theorem range_pullback_to_base_of_right :
    Set.Range (pullback.fst ≫ g : pullback g f ⟶ Z).1.base = Set.Range g.1.base ∩ Set.Range f.1.base := by
  rw [Scheme.comp_val_base, coe_comp, Set.range_comp, range_pullback_fst_of_right, opens.map_obj, Subtype.coe_mk,
    Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.Range g.1.base ⊆ Set.Range f.1.base) : Y ⟶ X :=
  LocallyRingedSpace.IsOpenImmersion.lift f g H'

@[simp, reassoc]
theorem lift_fac (H' : Set.Range g.1.base ⊆ Set.Range f.1.base) : lift f g H' ≫ f = g :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac f g H'

theorem lift_uniq (H' : Set.Range g.1.base ⊆ Set.Range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) : l = lift f g H' :=
  LocallyRingedSpace.IsOpenImmersion.lift_uniq f g H' l hl

/-- Two open immersions with equal range are isomorphic. -/
@[simps]
def isoOfRangeEq [IsOpenImmersion g] (e : Set.Range f.1.base = Set.Range g.1.base) : X ≅ Y where
  Hom := lift g f (le_of_eqₓ e)
  inv := lift f g (le_of_eqₓ e.symm)
  hom_inv_id' := by
    rw [← cancel_mono f]
    simp
  inv_hom_id' := by
    rw [← cancel_mono g]
    simp

theorem image_basic_open {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] {U : Opens X.Carrier}
    (r : X.Presheaf.obj (op U)) : H.base_open.IsOpenMap.Functor.obj (X.basicOpen r) = Y.basicOpen (H.inv_app U r) := by
  have e := Scheme.preimage_basic_open f (H.inv_app U r)
  rw [PresheafedSpace.is_open_immersion.inv_app_app_apply, Scheme.basic_open_res, opens.inter_eq, inf_eq_right.mpr _] at
    e
  rw [← e]
  ext1
  refine' set.image_preimage_eq_inter_range.trans _
  erw [Set.inter_eq_left_iff_subset]
  refine' Set.Subset.trans (Scheme.basic_open_subset _ _) (Set.image_subset_range _ _)
  refine' le_transₓ (Scheme.basic_open_subset _ _) (le_of_eqₓ _)
  ext1
  exact (Set.preimage_image_eq _ H.base_open.inj).symm

end IsOpenImmersion

/-- The functor taking open subsets of `X` to open subschemes of `X`. -/
@[simps obj_left obj_hom mapLeft]
def Scheme.restrictFunctor (X : Scheme) : Opens X.Carrier ⥤ Over X where
  obj := fun U => Over.mk (X.ofRestrict U.OpenEmbedding)
  map := fun U V i =>
    Over.homMk
      (IsOpenImmersion.lift (X.ofRestrict _) (X.ofRestrict _)
        (by
          change Set.Range coe ⊆ Set.Range coe
          simp_rw [Subtype.range_coe]
          exact i.le))
      (IsOpenImmersion.lift_fac _ _ _)
  map_id' := fun U => by
    ext1
    dsimp' only [← over.hom_mk_left, ← over.id_left]
    rw [← cancel_mono (X.of_restrict U.open_embedding), category.id_comp, is_open_immersion.lift_fac]
  map_comp' := fun U V W i j => by
    ext1
    dsimp' only [← over.hom_mk_left, ← over.comp_left]
    rw [← cancel_mono (X.of_restrict W.open_embedding), category.assoc]
    iterate 3 
      rw [is_open_immersion.lift_fac]

/-- The restriction of an isomorphism onto an open set. -/
noncomputable abbrev Scheme.restrictMapIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Opens Y.Carrier) :
    X.restrict ((Opens.map f.1.base).obj U).OpenEmbedding ≅ Y.restrict U.OpenEmbedding := by
  refine' is_open_immersion.iso_of_range_eq (X.of_restrict _ ≫ f) (Y.of_restrict _) _
  dsimp' [← opens.inclusion]
  rw [coe_comp, Set.range_comp]
  dsimp'
  rw [Subtype.range_coe, Subtype.range_coe]
  refine' @Set.image_preimage_eq _ _ f.1.base U.1 _
  rw [← Top.epi_iff_surjective]
  infer_instance

/-- Given an open cover on `X`, we may pull them back along a morphism `W ⟶ X` to obtain
an open cover of `W`. -/
@[simps]
def Scheme.OpenCover.pullbackCover {X : Scheme} (𝒰 : X.OpenCover) {W : Scheme} (f : W ⟶ X) : W.OpenCover where
  J := 𝒰.J
  obj := fun x => pullback f (𝒰.map x)
  map := fun x => pullback.fst
  f := fun x => 𝒰.f (f.1.base x)
  Covers := fun x => by
    rw [←
      show _ = (pullback.fst : pullback f (𝒰.map (𝒰.f (f.1.base x))) ⟶ _).1.base from
        preserves_pullback.iso_hom_fst Scheme.forget_to_Top f (𝒰.map (𝒰.f (f.1.base x)))]
    rw [coe_comp, Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ, Top.pullback_fst_range]
    obtain ⟨y, h⟩ := 𝒰.covers (f.1.base x)
    exact ⟨y, h.symm⟩
    · rw [← Top.epi_iff_surjective]
      infer_instance
      

/-- Given open covers `{ Uᵢ }` and `{ Uⱼ }`, we may form the open cover `{ Uᵢ ∩ Uⱼ }`. -/
def Scheme.OpenCover.inter {X : Scheme.{u}} (𝒰₁ : Scheme.OpenCover.{v₁} X) (𝒰₂ : Scheme.OpenCover.{v₂} X) :
    X.OpenCover where
  J := 𝒰₁.J × 𝒰₂.J
  obj := fun ij => pullback (𝒰₁.map ij.1) (𝒰₂.map ij.2)
  map := fun ij => pullback.fst ≫ 𝒰₁.map ij.1
  f := fun x => ⟨𝒰₁.f x, 𝒰₂.f x⟩
  Covers := fun x => by
    rw [is_open_immersion.range_pullback_to_base_of_left]
    exact ⟨𝒰₁.covers x, 𝒰₂.covers x⟩

section MorphismRestrict

/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
def pullbackRestrictIsoRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.Carrier) :
    pullback f (Y.ofRestrict U.OpenEmbedding) ≅ X.restrict ((Opens.map f.1.base).obj U).OpenEmbedding := by
  refine' is_open_immersion.iso_of_range_eq pullback.fst (X.of_restrict _) _
  rw [is_open_immersion.range_pullback_fst_of_right]
  dsimp' [← opens.inclusion]
  rw [Subtype.range_coe, Subtype.range_coe]
  rfl

@[simp, reassoc]
theorem pullback_restrict_iso_restrict_inv_fst {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.Carrier) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst = X.ofRestrict _ := by
  delta' pullback_restrict_iso_restrict
  simp

@[simp, reassoc]
theorem pullback_restrict_iso_restrict_hom_restrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.Carrier) :
    (pullbackRestrictIsoRestrict f U).Hom ≫ X.ofRestrict _ = pullback.fst := by
  delta' pullback_restrict_iso_restrict
  simp

/-- The restriction of a morphism `X ⟶ Y` onto `X |_{f ⁻¹ U} ⟶ Y |_ U`. -/
def morphismRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.Carrier) :
    X.restrict ((Opens.map f.1.base).obj U).OpenEmbedding ⟶ Y.restrict U.OpenEmbedding :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd

-- mathport name: «expr ∣_ »
infixl:80 " ∣_ " => morphismRestrict

@[simp, reassoc]
theorem pullback_restrict_iso_restrict_hom_morphism_restrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.Carrier) :
    (pullbackRestrictIsoRestrict f U).Hom ≫ f ∣_ U = pullback.snd :=
  Iso.hom_inv_id_assoc _ _

@[simp, reassoc]
theorem morphism_restrict_ι {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.Carrier) :
    (f ∣_ U) ≫ Y.ofRestrict U.OpenEmbedding = X.ofRestrict _ ≫ f := by
  delta' morphism_restrict
  rw [category.assoc, pullback.condition.symm, pullback_restrict_iso_restrict_inv_fst_assoc]

theorem morphism_restrict_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z.Carrier) :
    (f ≫ g) ∣_ U = ((f ∣_ (Opens.map g.val.base).obj U) ≫ g ∣_ U : _) := by
  delta' morphism_restrict
  rw [← pullback_right_pullback_fst_iso_inv_snd_snd]
  simp_rw [← category.assoc]
  congr 1
  rw [← cancel_mono pullback.fst]
  simp_rw [category.assoc]
  rw [pullback_restrict_iso_restrict_inv_fst, pullback_right_pullback_fst_iso_inv_snd_fst, ← pullback.condition,
    pullback_restrict_iso_restrict_inv_fst_assoc, pullback_restrict_iso_restrict_inv_fst_assoc]
  rfl
  infer_instance

instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Opens Y.Carrier) : IsIso (f ∣_ U) := by
  delta' morphism_restrict
  infer_instance

theorem morphism_restrict_base_coe {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.Carrier) (x) :
    @coe U Y.Carrier _ ((f ∣_ U).1.base x) = f.1.base x.1 :=
  congr_arg (fun f => PresheafedSpace.Hom.base (Subtype.val f) x) (morphism_restrict_ι f U)

theorem image_morphism_restrict_preimage {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.Carrier) (V : Opens U) :
    ((Opens.map f.val.base).obj U).OpenEmbedding.IsOpenMap.Functor.obj ((Opens.map (f ∣_ U).val.base).obj V) =
      (Opens.map f.val.base).obj (U.OpenEmbedding.IsOpenMap.Functor.obj V) :=
  by
  ext1
  ext x
  constructor
  · rintro ⟨⟨x, hx⟩, hx' : (f ∣_ U).1.base _ ∈ _, rfl⟩
    refine' ⟨⟨_, hx⟩, _, rfl⟩
    convert hx'
    ext1
    exact (morphism_restrict_base_coe f U ⟨x, hx⟩).symm
    
  · rintro ⟨⟨x, hx⟩, hx', rfl : x = _⟩
    refine' ⟨⟨_, hx⟩, (_ : (f ∣_ U).1.base ⟨x, hx⟩ ∈ V.1), rfl⟩
    convert hx'
    ext1
    exact morphism_restrict_base_coe f U ⟨x, hx⟩
    

theorem morphism_restrict_c_app {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.Carrier) (V : Opens U) :
    (f ∣_ U).1.c.app (op V) =
      f.1.c.app (op (U.OpenEmbedding.IsOpenMap.Functor.obj V)) ≫
        X.Presheaf.map (eqToHom (image_morphism_restrict_preimage f U V)).op :=
  by
  have := Scheme.congr_app (morphism_restrict_ι f U) (op (U.open_embedding.is_open_map.functor.obj V))
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app_assoc] at this
  have e : (opens.map U.inclusion).obj (U.open_embedding.is_open_map.functor.obj V) = V := by
    ext1
    exact Set.preimage_image_eq _ Subtype.coe_injective
  have : _ ≫ X.presheaf.map _ = _ := (((f ∣_ U).1.c.naturality (eq_to_hom e).op).symm.trans _).trans this
  swap
  · change Y.presheaf.map _ ≫ _ = Y.presheaf.map _ ≫ _
    congr
    
  rw [← is_iso.eq_comp_inv, ← functor.map_inv, category.assoc] at this
  rw [this]
  congr 1
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  congr 1

theorem Γ_map_morphism_restrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.Carrier) :
    Scheme.Γ.map (f ∣_ U).op =
      Y.Presheaf.map (eq_to_hom <| U.open_embedding_obj_top.symm).op ≫
        f.1.c.app (op U) ≫ X.Presheaf.map (eq_to_hom <| ((Opens.map f.val.base).obj U).open_embedding_obj_top).op :=
  by
  rw [Scheme.Γ_map_op, morphism_restrict_c_app f U ⊤, f.val.c.naturality_assoc]
  erw [← X.presheaf.map_comp]
  congr

end MorphismRestrict

end AlgebraicGeometry

