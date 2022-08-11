/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import Mathbin.Topology.Category.Top.EpiMono
import Mathbin.CategoryTheory.Limits.Preserves.Limits
import Mathbin.CategoryTheory.Category.Ulift
import Mathbin.CategoryTheory.Limits.Shapes.Types
import Mathbin.CategoryTheory.Limits.ConcreteCategory

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/


open TopologicalSpace

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe u v w

noncomputable section

namespace Top

variable {J : Type v} [SmallCategory J]

-- mathport name: «exprforget»
local notation "forget" => forget Top

/-- A choice of limit cone for a functor `F : J ⥤ Top`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limitCone (F : J ⥤ Top.{max v u}) : Cone F where
  x := Top.of { u : ∀ j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j =>
        { toFun := fun u => u.val j,
          continuous_to_fun :=
            show Continuous ((fun u : ∀ j : J, F.obj j => u j) ∘ Subtype.val) by
              continuity } }

/-- A choice of limit cone for a functor `F : J ⥤ Top` whose topology is defined as an
infimum of topologies infimum.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limitConeInfi (F : J ⥤ Top.{max v u}) : Cone F where
  x := ⟨(Types.limitCone (F ⋙ forget)).x, ⨅ j, (F.obj j).str.induced ((Types.limitCone (F ⋙ forget)).π.app j)⟩
  π :=
    { app := fun j => ⟨(Types.limitCone (F ⋙ forget)).π.app j, continuous_iff_le_induced.mpr (infi_le _ _)⟩,
      naturality' := fun j j' f => ContinuousMap.coe_injective ((Types.limitCone (F ⋙ forget)).π.naturality f) }

/-- The chosen cone `Top.limit_cone F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limitConeIsLimit (F : J ⥤ Top.{max v u}) : IsLimit (limitCone F) where
  lift := fun S =>
    { toFun := fun x =>
        ⟨fun j => S.π.app _ x, fun i j f => by
          dsimp'
          erw [← S.w f]
          rfl⟩ }
  uniq' := fun S m h => by
    ext : 3
    simpa [h]

/-- The chosen cone `Top.limit_cone_infi F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limitConeInfiIsLimit (F : J ⥤ Top.{max v u}) : IsLimit (limitConeInfi F) := by
  refine' is_limit.of_faithful forget (types.limit_cone_is_limit _) (fun s => ⟨_, _⟩) fun s => rfl
  exact
    continuous_iff_coinduced_le.mpr
      (le_infi fun j => coinduced_le_iff_le_induced.mp <| (continuous_iff_coinduced_le.mp (s.π.app j).Continuous : _))

instance Top_has_limits_of_size :
    HasLimitsOfSize.{v}
      Top.{max v
          u} where HasLimitsOfShape := fun J 𝒥 =>
    { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } }

instance Top_has_limits : HasLimits Top.{u} :=
  Top.Top_has_limits_of_size.{u, u}

instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget :
        Top.{max v u} ⥤
          Type
            max v
              u) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget)) }

instance forgetPreservesLimits : PreservesLimits (forget : Top.{u} ⥤ Type u) :=
  Top.forgetPreservesLimitsOfSize.{u, u}

/-- A choice of colimit cocone for a functor `F : J ⥤ Top`.
Generally you should just use `colimit.coone F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone`).
-/
def colimitCocone (F : J ⥤ Top.{max v u}) : Cocone F where
  x := ⟨(Types.colimitCocone (F ⋙ forget)).x, ⨆ j, (F.obj j).str.coinduced ((Types.colimitCocone (F ⋙ forget)).ι.app j)⟩
  ι :=
    { app := fun j => ⟨(Types.colimitCocone (F ⋙ forget)).ι.app j, continuous_iff_coinduced_le.mpr (le_supr _ j)⟩,
      naturality' := fun j j' f => ContinuousMap.coe_injective ((Types.colimitCocone (F ⋙ forget)).ι.naturality f) }

/-- The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.
Generally you should just use `colimit.is_colimit F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone_is_colimit`).
-/
def colimitCoconeIsColimit (F : J ⥤ Top.{max v u}) : IsColimit (colimitCocone F) := by
  refine' is_colimit.of_faithful forget (types.colimit_cocone_is_colimit _) (fun s => ⟨_, _⟩) fun s => rfl
  exact
    continuous_iff_le_induced.mpr
      (supr_le fun j => coinduced_le_iff_le_induced.mp <| (continuous_iff_coinduced_le.mp (s.ι.app j).Continuous : _))

instance Top_has_colimits_of_size :
    HasColimitsOfSize.{v}
      Top.{max v
          u} where HasColimitsOfShape := fun J 𝒥 =>
    { HasColimit := fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_cocone_is_colimit F } }

instance Top_has_colimits : HasColimits Top.{u} :=
  Top.Top_has_colimits_of_size.{u, u}

instance forgetPreservesColimitsOfSize :
    PreservesColimitsOfSize.{v, v}
      (forget :
        Top.{max v u} ⥤
          Type
            max v
              u) where PreservesColimitsOfShape := fun J 𝒥 =>
    { PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
          (types.colimit_cocone_is_colimit (F ⋙ forget)) }

instance forgetPreservesColimits : PreservesColimits (forget : Top.{u} ⥤ Type u) :=
  Top.forgetPreservesColimitsOfSize.{u, u}

/-- The projection from the product as a bundled continous map. -/
abbrev piπ {ι : Type v} (α : ι → Top.{max v u}) (i : ι) : Top.of (∀ i, α i) ⟶ α i :=
  ⟨fun f => f i, continuous_apply i⟩

/-- The explicit fan of a family of topological spaces given by the pi type. -/
@[simps x π_app]
def piFan {ι : Type v} (α : ι → Top.{max v u}) : Fan α :=
  Fan.mk (Top.of (∀ i, α i)) (piπ α)

/-- The constructed fan is indeed a limit -/
def piFanIsLimit {ι : Type v} (α : ι → Top.{max v u}) : IsLimit (piFan α) where
  lift := fun S => { toFun := fun s i => S.π.app ⟨i⟩ s }
  uniq' := by
    intro S m h
    ext x i
    simp [h ⟨i⟩]
  fac' := fun s j => by
    cases j
    tidy

/-- The product is homeomorphic to the product of the underlying spaces,
equipped with the product topology.
-/
def piIsoPi {ι : Type v} (α : ι → Top.{max v u}) : ∏ α ≅ Top.of (∀ i, α i) :=
  (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit α)

@[simp, reassoc]
theorem pi_iso_pi_inv_π {ι : Type v} (α : ι → Top.{max v u}) (i : ι) : (piIsoPi α).inv ≫ Pi.π α i = piπ α i := by
  simp [← pi_iso_pi]

@[simp]
theorem pi_iso_pi_inv_π_apply {ι : Type v} (α : ι → Top.{max v u}) (i : ι) (x : ∀ i, α i) :
    (Pi.π α i : _) ((piIsoPi α).inv x) = x i :=
  ConcreteCategory.congr_hom (pi_iso_pi_inv_π α i) x

@[simp]
theorem pi_iso_pi_hom_apply {ι : Type v} (α : ι → Top.{max v u}) (i : ι) (x : ∏ α) :
    (piIsoPi α).Hom x i = (Pi.π α i : _) x := by
  have := pi_iso_pi_inv_π α i
  rw [iso.inv_comp_eq] at this
  exact concrete_category.congr_hom this x

/-- The inclusion to the coproduct as a bundled continous map. -/
abbrev sigmaι {ι : Type v} (α : ι → Top.{max v u}) (i : ι) : α i ⟶ Top.of (Σi, α i) :=
  ⟨Sigma.mk i⟩

/-- The explicit cofan of a family of topological spaces given by the sigma type. -/
@[simps x ι_app]
def sigmaCofan {ι : Type v} (α : ι → Top.{max v u}) : Cofan α :=
  Cofan.mk (Top.of (Σi, α i)) (sigmaι α)

/-- The constructed cofan is indeed a colimit -/
def sigmaCofanIsColimit {ι : Type v} (α : ι → Top.{max v u}) : IsColimit (sigmaCofan α) where
  desc := fun S =>
    { toFun := fun s => S.ι.app ⟨s.1⟩ s.2,
      continuous_to_fun := by
        continuity
        dsimp' only
        continuity }
  uniq' := by
    intro S m h
    ext ⟨i, x⟩
    simp [h ⟨i⟩]
  fac' := fun s j => by
    cases j
    tidy

/-- The coproduct is homeomorphic to the disjoint union of the topological spaces.
-/
def sigmaIsoSigma {ι : Type v} (α : ι → Top.{max v u}) : ∐ α ≅ Top.of (Σi, α i) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit α)

@[simp, reassoc]
theorem sigma_iso_sigma_hom_ι {ι : Type v} (α : ι → Top.{max v u}) (i : ι) :
    Sigma.ι α i ≫ (sigmaIsoSigma α).Hom = sigmaι α i := by
  simp [← sigma_iso_sigma]

@[simp]
theorem sigma_iso_sigma_hom_ι_apply {ι : Type v} (α : ι → Top.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).Hom ((Sigma.ι α i : _) x) = Sigma.mk i x :=
  ConcreteCategory.congr_hom (sigma_iso_sigma_hom_ι α i) x

@[simp]
theorem sigma_iso_sigma_inv_apply {ι : Type v} (α : ι → Top.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).inv ⟨i, x⟩ = (Sigma.ι α i : _) x := by
  rw [← sigma_iso_sigma_hom_ι_apply, ← comp_app]
  simp

theorem induced_of_is_limit {F : J ⥤ Top.{max v u}} (C : Cone F) (hC : IsLimit C) :
    C.x.TopologicalSpace = ⨅ j, (F.obj j).TopologicalSpace.induced (C.π.app j) := by
  let homeo := homeo_of_iso (hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit F))
  refine' homeo.inducing.induced.trans _
  change induced homeo (⨅ j : J, _) = _
  simpa [← induced_infi, ← induced_compose]

theorem limit_topology (F : J ⥤ Top.{max v u}) :
    (limit F).TopologicalSpace = ⨅ j, (F.obj j).TopologicalSpace.induced (limit.π F j) :=
  induced_of_is_limit _ (limit.isLimit F)

section Prod

/-- The first projection from the product. -/
abbrev prodFst {X Y : Top.{u}} : Top.of (X × Y) ⟶ X :=
  ⟨Prod.fst⟩

/-- The second projection from the product. -/
abbrev prodSnd {X Y : Top.{u}} : Top.of (X × Y) ⟶ Y :=
  ⟨Prod.snd⟩

/-- The explicit binary cofan of `X, Y` given by `X × Y`. -/
def prodBinaryFan (X Y : Top.{u}) : BinaryFan X Y :=
  BinaryFan.mk prodFst prodSnd

/-- The constructed binary fan is indeed a limit -/
def prodBinaryFanIsLimit (X Y : Top.{u}) : IsLimit (prodBinaryFan X Y) where
  lift := fun S : BinaryFan X Y => { toFun := fun s => (S.fst s, S.snd s) }
  fac' := by
    rintro S (_ | _)
    tidy
  uniq' := by
    intro S m h
    ext x
    · specialize h ⟨walking_pair.left⟩
      apply_fun fun e => e x  at h
      exact h
      
    · specialize h ⟨walking_pair.right⟩
      apply_fun fun e => e x  at h
      exact h
      

/-- The homeomorphism between `X ⨯ Y` and the set-theoretic product of `X` and `Y`,
equipped with the product topology.
-/
def prodIsoProd (X Y : Top.{u}) : X ⨯ Y ≅ Top.of (X × Y) :=
  (limit.isLimit _).conePointUniqueUpToIso (prodBinaryFanIsLimit X Y)

@[simp, reassoc]
theorem prod_iso_prod_hom_fst (X Y : Top.{u}) : (prodIsoProd X Y).Hom ≫ prod_fst = limits.prod.fst := by
  simpa [iso.eq_inv_comp, ← prod_iso_prod]

@[simp, reassoc]
theorem prod_iso_prod_hom_snd (X Y : Top.{u}) : (prodIsoProd X Y).Hom ≫ prod_snd = limits.prod.snd := by
  simpa [iso.eq_inv_comp, ← prod_iso_prod]

@[simp]
theorem prod_iso_prod_hom_apply {X Y : Top.{u}} (x : X ⨯ Y) :
    (prodIsoProd X Y).Hom x = ((Limits.prod.fst : X ⨯ Y ⟶ _) x, (Limits.prod.snd : X ⨯ Y ⟶ _) x) := by
  ext
  · exact concrete_category.congr_hom (prod_iso_prod_hom_fst X Y) x
    
  · exact concrete_category.congr_hom (prod_iso_prod_hom_snd X Y) x
    

@[simp, reassoc, elementwise]
theorem prod_iso_prod_inv_fst (X Y : Top.{u}) : (prodIsoProd X Y).inv ≫ limits.prod.fst = prod_fst := by
  simp [← iso.inv_comp_eq]

@[simp, reassoc, elementwise]
theorem prod_iso_prod_inv_snd (X Y : Top.{u}) : (prodIsoProd X Y).inv ≫ limits.prod.snd = prod_snd := by
  simp [← iso.inv_comp_eq]

theorem prod_topology {X Y : Top} :
    (X ⨯ Y).TopologicalSpace =
      induced (Limits.prod.fst : X ⨯ Y ⟶ _)
          X.TopologicalSpace⊓induced (Limits.prod.snd : X ⨯ Y ⟶ _) Y.TopologicalSpace :=
  by
  let homeo := homeo_of_iso (prod_iso_prod X Y)
  refine' homeo.inducing.induced.trans _
  change induced homeo (_⊓_) = _
  simpa [← induced_compose]

theorem range_prod_map {W X Y Z : Top.{u}} (f : W ⟶ Y) (g : X ⟶ Z) :
    Set.Range (Limits.prod.map f g) =
      (Limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' Set.Range f ∩ (Limits.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' Set.Range g :=
  by
  ext
  constructor
  · rintro ⟨y, rfl⟩
    simp only [← Set.mem_preimage, ← Set.mem_range, ← Set.mem_inter_eq, comp_apply]
    simp only [← limits.prod.map_fst, ← limits.prod.map_snd, ← exists_apply_eq_applyₓ, ← comp_apply, ← and_selfₓ]
    
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    use (prod_iso_prod W X).inv (x₁, x₂)
    apply concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · simp only [comp_apply, ← category.assoc]
      erw [limits.prod.map_fst]
      simp [← hx₁]
      
    · simp only [comp_apply, ← category.assoc]
      erw [limits.prod.map_snd]
      simp [← hx₂]
      
    

theorem inducing_prod_map {W X Y Z : Top} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Inducing f) (hg : Inducing g) :
    Inducing (Limits.prod.map f g) := by
  constructor
  simp only [← prod_topology, ← induced_compose, coe_comp, ← limits.prod.map_fst, ← limits.prod.map_snd, ← induced_inf]
  simp only [← coe_comp]
  rw [← @induced_compose _ _ _ _ _ f, ← @induced_compose _ _ _ _ _ g, ← hf.induced, ← hg.induced]

theorem embedding_prod_map {W X Y Z : Top} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Embedding f) (hg : Embedding g) :
    Embedding (Limits.prod.map f g) :=
  ⟨inducing_prod_map hf.to_inducing hg.to_inducing, by
    have := (Top.mono_iff_injective _).mpr hf.inj
    have := (Top.mono_iff_injective _).mpr hg.inj
    exact (Top.mono_iff_injective _).mp inferInstance⟩

end Prod

section Pullback

variable {X Y Z : Top.{u}}

/-- The first projection from the pullback. -/
abbrev pullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) : Top.of { p : X × Y // f p.1 = g p.2 } ⟶ X :=
  ⟨Prod.fst ∘ Subtype.val⟩

/-- The second projection from the pullback. -/
abbrev pullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) : Top.of { p : X × Y // f p.1 = g p.2 } ⟶ Y :=
  ⟨Prod.snd ∘ Subtype.val⟩

/-- The explicit pullback cone of `X, Y` given by `{ p : X × Y // f p.1 = g p.2 }`. -/
def pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g)
    (by
      ext ⟨x, h⟩
      simp [← h])

/-- The constructed cone is a limit. -/
def pullbackConeIsLimit (f : X ⟶ Z) (g : Y ⟶ Z) : IsLimit (pullbackCone f g) :=
  PullbackCone.isLimitAux' _
    (by
      intro s
      constructor
      swap
      exact
        { toFun := fun x =>
            ⟨⟨s.fst x, s.snd x⟩, by
              simpa using concrete_category.congr_hom s.condition x⟩ }
      refine' ⟨_, _, _⟩
      · ext
        delta' pullback_cone
        simp
        
      · ext
        delta' pullback_cone
        simp
        
      · intro m h₁ h₂
        ext x
        · simpa using concrete_category.congr_hom h₁ x
          
        · simpa using concrete_category.congr_hom h₂ x
          
        )

/-- The pullback of two maps can be identified as a subspace of `X × Y`. -/
def pullbackIsoProdSubtype (f : X ⟶ Z) (g : Y ⟶ Z) : pullback f g ≅ Top.of { p : X × Y // f p.1 = g p.2 } :=
  (limit.isLimit _).conePointUniqueUpToIso (pullbackConeIsLimit f g)

@[simp, reassoc]
theorem pullback_iso_prod_subtype_inv_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.fst = pullbackFst f g := by
  simpa [← pullback_iso_prod_subtype]

@[simp]
theorem pullback_iso_prod_subtype_inv_fst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) :
    (pullback.fst : pullback f g ⟶ _) ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).fst :=
  ConcreteCategory.congr_hom (pullback_iso_prod_subtype_inv_fst f g) x

@[simp, reassoc]
theorem pullback_iso_prod_subtype_inv_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.snd = pullbackSnd f g := by
  simpa [← pullback_iso_prod_subtype]

@[simp]
theorem pullback_iso_prod_subtype_inv_snd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) :
    (pullback.snd : pullback f g ⟶ _) ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).snd :=
  ConcreteCategory.congr_hom (pullback_iso_prod_subtype_inv_snd f g) x

theorem pullback_iso_prod_subtype_hom_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).Hom ≫ pullbackFst f g = pullback.fst := by
  rw [← iso.eq_inv_comp, pullback_iso_prod_subtype_inv_fst]

theorem pullback_iso_prod_subtype_hom_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).Hom ≫ pullbackSnd f g = pullback.snd := by
  rw [← iso.eq_inv_comp, pullback_iso_prod_subtype_inv_snd]

@[simp]
theorem pullback_iso_prod_subtype_hom_apply {f : X ⟶ Z} {g : Y ⟶ Z} (x : pullback f g) :
    (pullbackIsoProdSubtype f g).Hom x =
      ⟨⟨(pullback.fst : pullback f g ⟶ _) x, (pullback.snd : pullback f g ⟶ _) x⟩, by
        simpa using concrete_category.congr_hom pullback.condition x⟩ :=
  by
  ext
  exacts[concrete_category.congr_hom (pullback_iso_prod_subtype_hom_fst f g) x,
    concrete_category.congr_hom (pullback_iso_prod_subtype_hom_snd f g) x]

theorem pullback_topology {X Y Z : Top.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g).TopologicalSpace =
      induced (pullback.fst : pullback f g ⟶ _)
          X.TopologicalSpace⊓induced (pullback.snd : pullback f g ⟶ _) Y.TopologicalSpace :=
  by
  let homeo := homeo_of_iso (pullback_iso_prod_subtype f g)
  refine' homeo.inducing.induced.trans _
  change induced homeo (induced _ (_⊓_)) = _
  simpa [← induced_compose]

theorem range_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.Range (prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) =
      { x | (limits.prod.fst ≫ f) x = (limits.prod.snd ≫ g) x } :=
  by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp only [comp_apply, ← Set.mem_set_of_eq]
    congr 1
    simp [← pullback.condition]
    
  · intro h
    use (pullback_iso_prod_subtype f g).inv ⟨⟨_, _⟩, h⟩
    apply concrete.limit_ext
    rintro ⟨⟨⟩⟩ <;> simp
    

theorem inducing_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Inducing ⇑(prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
  ⟨by
    simp [← prod_topology, ← pullback_topology, ← induced_compose, coe_comp]⟩

theorem embedding_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Embedding ⇑(prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
  ⟨inducing_pullback_to_prod f g, (Top.mono_iff_injective _).mp inferInstance⟩

/-- If the map `S ⟶ T` is mono, then there is a description of the image of `W ×ₛ X ⟶ Y ×ₜ Z`. -/
theorem range_pullback_map {W X Y Z S T : Top} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) (i₁ : W ⟶ Y)
    (i₂ : X ⟶ Z) (i₃ : S ⟶ T) [H₃ : Mono i₃] (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    Set.Range (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) =
      (pullback.fst : pullback g₁ g₂ ⟶ _) ⁻¹' Set.Range i₁ ∩ (pullback.snd : pullback g₁ g₂ ⟶ _) ⁻¹' Set.Range i₂ :=
  by
  ext
  constructor
  · rintro ⟨y, rfl⟩
    simp
    
  rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  have : f₁ x₁ = f₂ x₂ := by
    apply (Top.mono_iff_injective _).mp H₃
    simp only [comp_apply, ← eq₁, ← eq₂]
    simp only [← comp_apply, ← hx₁, ← hx₂]
    simp only [comp_apply, ← pullback.condition]
  use (pullback_iso_prod_subtype f₁ f₂).inv ⟨⟨x₁, x₂⟩, this⟩
  apply concrete.limit_ext
  rintro (_ | _ | _)
  · simp only [← Top.comp_app, ← limit.lift_π_apply, ← category.assoc, ← pullback_cone.mk_π_app_one, ← hx₁, ←
      pullback_iso_prod_subtype_inv_fst_apply, ← Subtype.coe_mk]
    simp only [comp_apply]
    congr
    apply limit.w _ walking_cospan.hom.inl
    
  · simp [← hx₁]
    
  · simp [← hx₂]
    

theorem pullback_fst_range {X Y S : Top} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.Range (pullback.fst : pullback f g ⟶ _) = { x : X | ∃ y : Y, f x = g y } := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    use (pullback.snd : pullback f g ⟶ _) y
    exact concrete_category.congr_hom pullback.condition y
    
  · rintro ⟨y, eq⟩
    use (Top.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, Eq⟩
    simp
    

theorem pullback_snd_range {X Y S : Top} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.Range (pullback.snd : pullback f g ⟶ _) = { y : Y | ∃ x : X, f x = g y } := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    use (pullback.fst : pullback f g ⟶ _) x
    exact concrete_category.congr_hom pullback.condition x
    
  · rintro ⟨x, eq⟩
    use (Top.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, Eq⟩
    simp
    

/-- If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are embeddings,
then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an embedding.

  W  ⟶  Y
    ↘      ↘
      S  ⟶  T
    ↗      ↗
  X  ⟶  Z
-/
theorem pullback_map_embedding_of_embeddings {W X Y Z S T : Top} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
    {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : Embedding i₁) (H₂ : Embedding i₂) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : Embedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine'
    embedding_of_embedding_compose (ContinuousMap.continuous_to_fun _)
      (show Continuous (prod.lift pullback.fst pullback.snd : pullback g₁ g₂ ⟶ Y ⨯ Z) from
        ContinuousMap.continuous_to_fun _)
      _
  suffices Embedding (prod.lift pullback.fst pullback.snd ≫ limits.prod.map i₁ i₂ : pullback f₁ f₂ ⟶ _) by
    simpa [coe_comp] using this
  rw [coe_comp]
  refine' Embedding.comp (embedding_prod_map H₁ H₂) (embedding_pullback_to_prod _ _)

/-- If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are open embeddings, and `S ⟶ T`
is mono, then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an open embedding.
  W  ⟶  Y
    ↘      ↘
      S  ⟶  T
    ↗       ↗
  X  ⟶  Z
-/
theorem pullback_map_open_embedding_of_open_embeddings {W X Y Z S T : Top} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : OpenEmbedding i₁) (H₂ : OpenEmbedding i₂) (i₃ : S ⟶ T) [H₃ : Mono i₃]
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : OpenEmbedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
  by
  constructor
  · apply pullback_map_embedding_of_embeddings f₁ f₂ g₁ g₂ H₁.to_embedding H₂.to_embedding i₃ eq₁ eq₂
    
  · rw [range_pullback_map]
    apply IsOpen.inter <;> apply Continuous.is_open_preimage
    continuity
    exacts[H₁.open_range, H₂.open_range]
    

theorem snd_embedding_of_left_embedding {X Y S : Top} {f : X ⟶ S} (H : Embedding f) (g : Y ⟶ S) :
    Embedding ⇑(pullback.snd : pullback f g ⟶ Y) := by
  convert
    (homeo_of_iso (as_iso (pullback.snd : pullback (𝟙 S) g ⟶ _))).Embedding.comp
      (pullback_map_embedding_of_embeddings f g (𝟙 _) g H (homeo_of_iso (iso.refl _)).Embedding (𝟙 _) rfl
        (by
          simp ))
  erw [← coe_comp]
  simp

theorem fst_embedding_of_right_embedding {X Y S : Top} (f : X ⟶ S) {g : Y ⟶ S} (H : Embedding g) :
    Embedding ⇑(pullback.fst : pullback f g ⟶ X) := by
  convert
    (homeo_of_iso (as_iso (pullback.fst : pullback f (𝟙 S) ⟶ _))).Embedding.comp
      (pullback_map_embedding_of_embeddings f g f (𝟙 _) (homeo_of_iso (iso.refl _)).Embedding H (𝟙 _) rfl
        (by
          simp ))
  erw [← coe_comp]
  simp

theorem embedding_of_pullback_embeddings {X Y S : Top} {f : X ⟶ S} {g : Y ⟶ S} (H₁ : Embedding f) (H₂ : Embedding g) :
    Embedding (limit.π (cospan f g) WalkingCospan.one) := by
  convert H₂.comp (snd_embedding_of_left_embedding H₁ g)
  erw [← coe_comp]
  congr
  exact (limit.w _ walking_cospan.hom.inr).symm

theorem snd_open_embedding_of_left_open_embedding {X Y S : Top} {f : X ⟶ S} (H : OpenEmbedding f) (g : Y ⟶ S) :
    OpenEmbedding ⇑(pullback.snd : pullback f g ⟶ Y) := by
  convert
    (homeo_of_iso (as_iso (pullback.snd : pullback (𝟙 S) g ⟶ _))).OpenEmbedding.comp
      (pullback_map_open_embedding_of_open_embeddings f g (𝟙 _) g H (homeo_of_iso (iso.refl _)).OpenEmbedding (𝟙 _) rfl
        (by
          simp ))
  erw [← coe_comp]
  simp

theorem fst_open_embedding_of_right_open_embedding {X Y S : Top} (f : X ⟶ S) {g : Y ⟶ S} (H : OpenEmbedding g) :
    OpenEmbedding ⇑(pullback.fst : pullback f g ⟶ X) := by
  convert
    (homeo_of_iso (as_iso (pullback.fst : pullback f (𝟙 S) ⟶ _))).OpenEmbedding.comp
      (pullback_map_open_embedding_of_open_embeddings f g f (𝟙 _) (homeo_of_iso (iso.refl _)).OpenEmbedding H (𝟙 _) rfl
        (by
          simp ))
  erw [← coe_comp]
  simp

/-- If `X ⟶ S`, `Y ⟶ S` are open embeddings, then so is `X ×ₛ Y ⟶ S`. -/
theorem open_embedding_of_pullback_open_embeddings {X Y S : Top} {f : X ⟶ S} {g : Y ⟶ S} (H₁ : OpenEmbedding f)
    (H₂ : OpenEmbedding g) : OpenEmbedding (limit.π (cospan f g) WalkingCospan.one) := by
  convert H₂.comp (snd_open_embedding_of_left_open_embedding H₁ g)
  erw [← coe_comp]
  congr
  exact (limit.w _ walking_cospan.hom.inr).symm

theorem fst_iso_of_right_embedding_range_subset {X Y S : Top} (f : X ⟶ S) {g : Y ⟶ S} (hg : Embedding g)
    (H : Set.Range f ⊆ Set.Range g) : IsIso (pullback.fst : pullback f g ⟶ X) := by
  let this : (pullback f g : Top) ≃ₜ X :=
    (Homeomorph.ofEmbedding _ (fst_embedding_of_right_embedding f hg)).trans
      { toFun := coe,
        invFun := fun x =>
          ⟨x, by
            rw [pullback_fst_range]
            exact ⟨_, (H (Set.mem_range_self x)).some_spec.symm⟩⟩,
        left_inv := fun ⟨_, _⟩ => rfl, right_inv := fun x => rfl }
  convert is_iso.of_iso (iso_of_homeo this)
  ext
  rfl

theorem snd_iso_of_left_embedding_range_subset {X Y S : Top} {f : X ⟶ S} (hf : Embedding f) (g : Y ⟶ S)
    (H : Set.Range g ⊆ Set.Range f) : IsIso (pullback.snd : pullback f g ⟶ Y) := by
  let this : (pullback f g : Top) ≃ₜ Y :=
    (Homeomorph.ofEmbedding _ (snd_embedding_of_left_embedding hf g)).trans
      { toFun := coe,
        invFun := fun x =>
          ⟨x, by
            rw [pullback_snd_range]
            exact ⟨_, (H (Set.mem_range_self x)).some_spec⟩⟩,
        left_inv := fun ⟨_, _⟩ => rfl, right_inv := fun x => rfl }
  convert is_iso.of_iso (iso_of_homeo this)
  ext
  rfl

theorem pullback_snd_image_fst_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set X) :
    (pullback.snd : pullback f g ⟶ _) '' ((pullback.fst : pullback f g ⟶ _) ⁻¹' U) = g ⁻¹' (f '' U) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(pullback.fst : pullback f g ⟶ _) y, hy, concrete_category.congr_hom pullback.condition y⟩
    
  · rintro ⟨y, hy, eq⟩
    exact
      ⟨(Top.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, Eq⟩, by
        simpa, by
        simp ⟩
    

theorem pullback_fst_image_snd_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set Y) :
    (pullback.fst : pullback f g ⟶ _) '' ((pullback.snd : pullback f g ⟶ _) ⁻¹' U) = f ⁻¹' (g '' U) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(pullback.snd : pullback f g ⟶ _) y, hy, (concrete_category.congr_hom pullback.condition y).symm⟩
    
  · rintro ⟨y, hy, eq⟩
    exact
      ⟨(Top.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, Eq.symm⟩, by
        simpa, by
        simp ⟩
    

end Pullback

--TODO: Add analogous constructions for `coprod` and `pushout`.
theorem coinduced_of_is_colimit {F : J ⥤ Top.{max v u}} (c : Cocone F) (hc : IsColimit c) :
    c.x.TopologicalSpace = ⨆ j, (F.obj j).TopologicalSpace.coinduced (c.ι.app j) := by
  let homeo := homeo_of_iso (hc.cocone_point_unique_up_to_iso (colimit_cocone_is_colimit F))
  ext
  refine' homeo.symm.is_open_preimage.symm.trans (Iff.trans _ is_open_supr_iff.symm)
  exact is_open_supr_iff

theorem colimit_topology (F : J ⥤ Top.{max v u}) :
    (colimit F).TopologicalSpace = ⨆ j, (F.obj j).TopologicalSpace.coinduced (colimit.ι F j) :=
  coinduced_of_is_colimit _ (colimit.isColimit F)

theorem colimit_is_open_iff (F : J ⥤ Top.{max v u}) (U : Set ((colimit F : _) : Type max v u)) :
    IsOpen U ↔ ∀ j, IsOpen (colimit.ι F j ⁻¹' U) := by
  conv_lhs => rw [colimit_topology F]
  exact is_open_supr_iff

theorem coequalizer_is_open_iff (F : walking_parallel_pair ⥤ Top.{u}) (U : Set ((colimit F : _) : Type u)) :
    IsOpen U ↔ IsOpen (colimit.ι F WalkingParallelPair.one ⁻¹' U) := by
  rw [colimit_is_open_iff.{u}]
  constructor
  · intro H
    exact H _
    
  · intro H j
    cases j
    · rw [← colimit.w F walking_parallel_pair_hom.left]
      exact (F.map walking_parallel_pair_hom.left).continuous_to_fun.is_open_preimage _ H
      
    · exact H
      
    

end Top

namespace Top

section CofilteredLimit

variable {J : Type v} [SmallCategory J] [IsCofiltered J] (F : J ⥤ Top.{max v u}) (C : Cone F) (hC : IsLimit C)

include hC

/-- Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem is_topological_basis_cofiltered_limit (T : ∀ j, Set (Set (F.obj j))) (hT : ∀ j, IsTopologicalBasis (T j))
    (univ : ∀ i : J, Set.Univ ∈ T i) (inter : ∀ (i) (U1 U2 : Set (F.obj i)), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
    (compat : ∀ (i j : J) (f : i ⟶ j) (V : Set (F.obj j)) (hV : V ∈ T j), F.map f ⁻¹' V ∈ T i) :
    IsTopologicalBasis { U : Set C.x | ∃ (j : _)(V : Set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V } := by
  classical
  -- The limit cone for `F` whose topology is defined as an infimum.
  let D := limit_cone_infi F
  -- The isomorphism between the cone point of `C` and the cone point of `D`.
  let E : C.X ≅ D.X := hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit _)
  have hE : Inducing E.hom := (Top.homeoOfIso E).Inducing
  -- Reduce to the assertion of the theorem with `D` instead of `C`.
  suffices is_topological_basis { U : Set D.X | ∃ (j : _)(V : Set (F.obj j)), V ∈ T j ∧ U = D.π.app j ⁻¹' V } by
    convert this.inducing hE
    ext U0
    constructor
    · rintro ⟨j, V, hV, rfl⟩
      refine' ⟨D.π.app j ⁻¹' V, ⟨j, V, hV, rfl⟩, rfl⟩
      
    · rintro ⟨W, ⟨j, V, hV, rfl⟩, rfl⟩
      refine' ⟨j, V, hV, rfl⟩
      
  -- Using `D`, we can apply the characterization of the topological basis of a
  -- topology defined as an infimum...
  convert is_topological_basis_infi hT fun j (x : D.X) => D.π.app j x
  ext U0
  constructor
  · rintro ⟨j, V, hV, rfl⟩
    let U : ∀ i, Set (F.obj i) := fun i =>
      if h : i = j then by
        rw [h]
        exact V
      else Set.Univ
    refine' ⟨U, {j}, _, _⟩
    · rintro i h
      rw [Finset.mem_singleton] at h
      dsimp' [← U]
      rw [dif_pos h]
      subst h
      exact hV
      
    · dsimp' [← U]
      simp
      
    
  · rintro ⟨U, G, h1, h2⟩
    obtain ⟨j, hj⟩ := is_cofiltered.inf_objs_exists G
    let g : ∀ (e) (he : e ∈ G), j ⟶ e := fun _ he => (hj he).some
    let Vs : J → Set (F.obj j) := fun e => if h : e ∈ G then F.map (g e h) ⁻¹' U e else Set.Univ
    let V : Set (F.obj j) := ⋂ (e : J) (he : e ∈ G), Vs e
    refine' ⟨j, V, _, _⟩
    · -- An intermediate claim used to apply induction along `G : finset J` later on.
      have :
        ∀ (S : Set (Set (F.obj j))) (E : Finset J) (P : J → Set (F.obj j)) (univ : Set.Univ ∈ S)
          (inter : ∀ A B : Set (F.obj j), A ∈ S → B ∈ S → A ∩ B ∈ S) (cond : ∀ (e : J) (he : e ∈ E), P e ∈ S),
          (⋂ (e) (he : e ∈ E), P e) ∈ S :=
        by
        intro S E
        apply E.induction_on
        · intro P he hh
          simpa
          
        · intro a E ha hh1 hh2 hh3 hh4 hh5
          rw [Finset.set_bInter_insert]
          refine' hh4 _ _ (hh5 _ (Finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 _)
          intro e he
          exact hh5 e (Finset.mem_insert_of_mem he)
          
      -- use the intermediate claim to finish off the goal using `univ` and `inter`.
      refine' this _ _ _ (univ _) (inter _) _
      intro e he
      dsimp' [← Vs]
      rw [dif_pos he]
      exact compat j e (g e he) (U e) (h1 e he)
      
    · -- conclude...
      rw [h2]
      dsimp' [← V]
      rw [Set.preimage_Inter]
      congr 1
      ext1 e
      rw [Set.preimage_Inter]
      congr 1
      ext1 he
      dsimp' [← Vs]
      rw [dif_pos he, ← Set.preimage_comp]
      congr 1
      change _ = ⇑(D.π.app j ≫ F.map (g e he))
      rw [D.w]
      
    

end CofilteredLimit

section TopologicalKonig

/-!
## Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

We give this in a more general form, which is that cofiltered limits
of nonempty compact Hausdorff spaces are nonempty
(`nonempty_limit_cone_of_compact_t2_cofiltered_system`).

This also applies to inverse limits, where `{J : Type u} [preorder J] [is_directed J (≤)]` and
`F : Jᵒᵖ ⥤ Top`.

The theorem is specialized to nonempty finite types (which are compact Hausdorff with the
discrete topology) in `nonempty_sections_of_fintype_cofiltered_system` and
`nonempty_sections_of_fintype_inverse_system`.

(See <https://stacks.math.columbia.edu/tag/086J> for the Set version.)
-/


variable {J : Type u} [SmallCategory J]

variable (F : J ⥤ Top.{u})

private abbrev finite_diagram_arrow {J : Type u} [SmallCategory J] (G : Finset J) :=
  Σ'(X Y : J)(mX : X ∈ G)(mY : Y ∈ G), X ⟶ Y

private abbrev finite_diagram (J : Type u) [SmallCategory J] :=
  ΣG : Finset J, Finset (FiniteDiagramArrow G)

/-- Partial sections of a cofiltered limit are sections when restricted to
a finite subset of objects and morphisms of `J`.
-/
def PartialSections {J : Type u} [SmallCategory J] (F : J ⥤ Top.{u}) {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : Set (∀ j, F.obj j) :=
  { u | ∀ {f : FiniteDiagramArrow G} (hf : f ∈ H), F.map f.2.2.2.2 (u f.1) = u f.2.1 }

theorem PartialSections.nonempty [IsCofiltered J] [h : ∀ j : J, Nonempty (F.obj j)] {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : (PartialSections F H).Nonempty := by
  classical
  use fun j : J =>
    if hj : j ∈ G then F.map (is_cofiltered.inf_to G H hj) (h (is_cofiltered.inf G H)).some else (h _).some
  rintro ⟨X, Y, hX, hY, f⟩ hf
  dsimp' only
  rwa [dif_pos hX, dif_pos hY, ← comp_app, ← F.map_comp, @is_cofiltered.inf_to_commutes _ _ _ G H]

theorem PartialSections.directed : Directed Superset fun G : FiniteDiagram J => PartialSections F G.2 := by
  classical
  intro A B
  let ιA : finite_diagram_arrow A.1 → finite_diagram_arrow (A.1⊔B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1, Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
  let ιB : finite_diagram_arrow B.1 → finite_diagram_arrow (A.1⊔B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_right _ f.2.2.1, Finset.mem_union_right _ f.2.2.2.1, f.2.2.2.2⟩
  refine' ⟨⟨A.1⊔B.1, A.2.Image ιA⊔B.2.Image ιB⟩, _, _⟩
  · rintro u hu f hf
    have : ιA f ∈ A.2.Image ιA⊔B.2.Image ιB := by
      apply Finset.mem_union_left
      rw [Finset.mem_image]
      refine' ⟨f, hf, rfl⟩
    exact hu this
    
  · rintro u hu f hf
    have : ιB f ∈ A.2.Image ιA⊔B.2.Image ιB := by
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine' ⟨f, hf, rfl⟩
    exact hu this
    

theorem PartialSections.closed [∀ j : J, T2Space (F.obj j)] {G : Finset J} (H : Finset (FiniteDiagramArrow G)) :
    IsClosed (PartialSections F H) := by
  have :
    partial_sections F H = ⋂ (f : finite_diagram_arrow G) (hf : f ∈ H), { u | F.map f.2.2.2.2 (u f.1) = u f.2.1 } := by
    ext1
    simp only [← Set.mem_Inter, ← Set.mem_set_of_eq]
    rfl
  rw [this]
  apply is_closed_bInter
  intro f hf
  apply is_closed_eq
  continuity

/-- Cofiltered limits of nonempty compact Hausdorff spaces are nonempty topological spaces.
--/
theorem nonempty_limit_cone_of_compact_t2_cofiltered_system [IsCofiltered J] [∀ j : J, Nonempty (F.obj j)]
    [∀ j : J, CompactSpace (F.obj j)] [∀ j : J, T2Space (F.obj j)] : Nonempty (Top.limitCone.{u} F).x := by
  classical
  obtain ⟨u, hu⟩ :=
    IsCompact.nonempty_Inter_of_directed_nonempty_compact_closed (fun G => partial_sections F _)
      (partial_sections.directed F) (fun G => partial_sections.nonempty F _)
      (fun G => IsClosed.is_compact (partial_sections.closed F _)) fun G => partial_sections.closed F _
  use u
  intro X Y f
  let G : finite_diagram J :=
    ⟨{X, Y},
      {⟨X, Y, by
          simp only [← true_orₓ, ← eq_self_iff_true, ← Finset.mem_insert], by
          simp only [← eq_self_iff_true, ← or_trueₓ, ← Finset.mem_insert, ← Finset.mem_singleton], f⟩}⟩
  exact hu _ ⟨G, rfl⟩ (Finset.mem_singleton_self _)

end TopologicalKonig

end Top

section FintypeKonig

/-- This bootstraps `nonempty_sections_of_fintype_inverse_system`. In this version,
the `F` functor is between categories of the same universe, and it is an easy
corollary to `Top.nonempty_limit_cone_of_compact_t2_inverse_system`. -/
theorem NonemptySectionsOfFintypeCofilteredSystem.init {J : Type u} [SmallCategory J] [IsCofiltered J] (F : J ⥤ Type u)
    [hf : ∀ j : J, Fintype (F.obj j)] [hne : ∀ j : J, Nonempty (F.obj j)] : F.sections.Nonempty := by
  let F' : J ⥤ Top := F ⋙ Top.discrete
  have : ∀ j : J, Fintype (F'.obj j) := hf
  have : ∀ j : J, Nonempty (F'.obj j) := hne
  obtain ⟨⟨u, hu⟩⟩ := Top.nonempty_limit_cone_of_compact_t2_cofiltered_system F'
  exact ⟨u, fun _ _ f => hu f⟩

/-- The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_inverse_system` for a specialization to inverse limits. -/
theorem nonempty_sections_of_fintype_cofiltered_system {J : Type u} [Category.{w} J] [IsCofiltered J] (F : J ⥤ Type v)
    [∀ j : J, Fintype (F.obj j)] [∀ j : J, Nonempty (F.obj j)] : F.sections.Nonempty := by
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type max w v u := AsSmall.{max w v} J
  let down : J' ⥤ J := as_small.down
  let F' : J' ⥤ Type max u v w := down ⋙ F ⋙ ulift_functor.{max u w, v}
  have : ∀ i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (down.obj i))⟩⟩
  have : ∀ i, Fintype (F'.obj i) := fun i => Fintype.ofEquiv (F.obj (down.obj i)) equiv.ulift.symm
  -- Step 2: apply the bootstrap theorem
  obtain ⟨u, hu⟩ := NonemptySectionsOfFintypeCofilteredSystem.init F'
  -- Step 3: interpret the results
  use fun j => (u ⟨j⟩).down
  intro j j' f
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ULift.up f)
  simp only [← as_small.down, ← functor.comp_map, ← ulift_functor_map, ← functor.op_map] at h
  simp_rw [← h]
  rfl

/-- The inverse limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_cofiltered_system` for a generalization to cofiltered limits.
That version applies in almost all cases, and the only difference is that this version
allows `J` to be empty.

This may be regarded as a generalization of Kőnig's lemma.
To specialize: given a locally finite connected graph, take `Jᵒᵖ` to be `ℕ` and
`F j` to be length-`j` paths that start from an arbitrary fixed vertex.
Elements of `F.sections` can be read off as infinite rays in the graph. -/
theorem nonempty_sections_of_fintype_inverse_system {J : Type u} [Preorderₓ J] [IsDirected J (· ≤ ·)] (F : Jᵒᵖ ⥤ Type v)
    [∀ j : Jᵒᵖ, Fintype (F.obj j)] [∀ j : Jᵒᵖ, Nonempty (F.obj j)] : F.sections.Nonempty := by
  cases is_empty_or_nonempty J
  · have : IsEmpty Jᵒᵖ := ⟨fun j => isEmptyElim j.unop⟩
    -- TODO: this should be a global instance
    exact ⟨isEmptyElim, isEmptyElim⟩
    
  · exact nonempty_sections_of_fintype_cofiltered_system _
    

end FintypeKonig

