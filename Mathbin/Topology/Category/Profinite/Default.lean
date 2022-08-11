/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne
-/
import Mathbin.Topology.Category.CompHaus.Default
import Mathbin.Topology.Connected
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.LocallyConstant.Basic
import Mathbin.CategoryTheory.Adjunction.Reflective
import Mathbin.CategoryTheory.Monad.Limits
import Mathbin.CategoryTheory.Limits.Constructions.EpiMono
import Mathbin.CategoryTheory.Fintype

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `Top`. The fully faithful functor
is called `Profinite_to_Top`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

0. Link to category of projective limits of finite discrete sets.
1. finite coproducts
2. Clausen/Scholze topology on the category `Profinite`.

## Tags

profinite

-/


universe u

open CategoryTheory

/-- The type of profinite topological spaces. -/
structure Profinite where
  toCompHaus : CompHaus
  [IsTotallyDisconnected : TotallyDisconnectedSpace to_CompHaus]

namespace Profinite

/-- Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] : Profinite :=
  ⟨⟨⟨X⟩⟩⟩

instance : Inhabited Profinite :=
  ⟨Profinite.of Pempty⟩

instance category : Category Profinite :=
  InducedCategory.category toCompHaus

instance concreteCategory : ConcreteCategory Profinite :=
  InducedCategory.concreteCategory _

instance hasForget₂ : HasForget₂ Profinite Top :=
  InducedCategory.hasForget₂ _

instance : CoeSort Profinite (Type _) :=
  ⟨fun X => X.toCompHaus⟩

instance {X : Profinite} : TotallyDisconnectedSpace X :=
  X.IsTotallyDisconnected

-- We check that we automatically infer that Profinite sets are compact and Hausdorff.
example {X : Profinite} : CompactSpace X :=
  inferInstance

example {X : Profinite} : T2Space X :=
  inferInstance

@[simp]
theorem coe_to_CompHaus {X : Profinite} : (X.toCompHaus : Type _) = X :=
  rfl

@[simp]
theorem coe_id (X : Profinite) : (𝟙 X : X → X) = id :=
  rfl

@[simp]
theorem coe_comp {X Y Z : Profinite} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  rfl

end Profinite

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
@[simps]
def profiniteToCompHaus : Profinite ⥤ CompHaus :=
  inducedFunctor _ deriving Full, Faithful

/-- The fully faithful embedding of `Profinite` in `Top`. This is definitionally the same as the
obvious composite. -/
@[simps]
def Profinite.toTop : Profinite ⥤ Top :=
  forget₂ _ _ deriving Full, Faithful

@[simp]
theorem Profinite.to_CompHaus_to_Top : profiniteToCompHaus ⋙ compHausToTop = Profinite.toTop :=
  rfl

section Profinite

/-- (Implementation) The object part of the connected_components functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components.
See: https://stacks.math.columbia.edu/tag/0900
-/
-- Without explicit universe annotations here, Lean introduces two universe variables and
-- unhelpfully defines a function `CompHaus.{max u₁ u₂} → Profinite.{max u₁ u₂}`.
def CompHaus.toProfiniteObj (X : CompHaus.{u}) : Profinite.{u} where
  toCompHaus :=
    { toTop := Top.of (ConnectedComponents X), IsCompact := Quotientₓ.compact_space,
      is_hausdorff := ConnectedComponents.t2 }
  IsTotallyDisconnected := ConnectedComponents.totally_disconnected_space

/-- (Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
def Profinite.toCompHausEquivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
    (CompHaus.toProfiniteObj X ⟶ Y) ≃ (X ⟶ profiniteToCompHaus.obj Y) where
  toFun := fun f => f.comp ⟨Quotientₓ.mk', continuous_quotient_mk⟩
  invFun := fun g =>
    { toFun := Continuous.connectedComponentsLift g.2,
      continuous_to_fun := Continuous.connected_components_lift_continuous g.2 }
  left_inv := fun f => ContinuousMap.ext <| ConnectedComponents.surjective_coe.forall.2 fun a => rfl
  right_inv := fun f => ContinuousMap.ext fun x => rfl

/-- The connected_components functor from compact Hausdorff spaces to profinite spaces,
left adjoint to the inclusion functor.
-/
def CompHaus.toProfinite : CompHaus ⥤ Profinite :=
  Adjunction.leftAdjointOfEquiv Profinite.toCompHausEquivalence fun _ _ _ _ _ => rfl

theorem CompHaus.to_Profinite_obj' (X : CompHaus) : ↥(CompHaus.toProfinite.obj X) = ConnectedComponents X :=
  rfl

/-- Finite types are given the discrete topology. -/
def Fintypeₓ.discreteTopology (A : Fintypeₓ) : TopologicalSpace A :=
  ⊥

section DiscreteTopology

attribute [local instance] Fintypeₓ.discreteTopology

/-- The natural functor from `Fintype` to `Profinite`, endowing a finite type with the
discrete topology. -/
@[simps]
def Fintypeₓ.toProfinite : Fintypeₓ ⥤ Profinite where
  obj := fun A => Profinite.of A
  map := fun _ _ f => ⟨f⟩

end DiscreteTopology

end Profinite

namespace Profinite

/-- An explicit limit cone for a functor `F : J ⥤ Profinite`, defined in terms of
`Top.limit_cone`. -/
-- TODO the following construction of limits could be generalised
-- to allow diagrams in lower universes.
def limitCone {J : Type u} [SmallCategory J] (F : J ⥤ Profinite.{u}) : Limits.Cone F where
  x :=
    { toCompHaus := (CompHaus.limitCone.{u, u} (F ⋙ profiniteToCompHaus)).x,
      IsTotallyDisconnected := by
        change TotallyDisconnectedSpace ↥{ u : ∀ j : J, F.obj j | _ }
        exact Subtype.totally_disconnected_space }
  π := { app := (CompHaus.limitCone.{u, u} (F ⋙ profiniteToCompHaus)).π.app }

/-- The limit cone `Profinite.limit_cone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type u} [SmallCategory J] (F : J ⥤ Profinite.{u}) : Limits.IsLimit (limitCone F) where
  lift := fun S => (CompHaus.limitConeIsLimit.{u, u} (F ⋙ profiniteToCompHaus)).lift (profiniteToCompHaus.mapCone S)
  uniq' := fun S m h => (CompHaus.limitConeIsLimit.{u, u} _).uniq (profiniteToCompHaus.mapCone S) _ h

/-- The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus -/
def toProfiniteAdjToCompHaus : CompHaus.toProfinite ⊣ profiniteToCompHaus :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The category of profinite sets is reflective in the category of compact hausdroff spaces -/
instance toCompHaus.reflective :
    Reflective profiniteToCompHaus where toIsRightAdjoint := ⟨CompHaus.toProfinite, Profinite.toProfiniteAdjToCompHaus⟩

noncomputable instance toCompHaus.createsLimits : CreatesLimits profiniteToCompHaus :=
  monadicCreatesLimits _

noncomputable instance toTop.reflective : Reflective Profinite.toTop :=
  Reflective.comp profiniteToCompHaus compHausToTop

noncomputable instance toTop.createsLimits : CreatesLimits Profinite.toTop :=
  monadicCreatesLimits _

instance has_limits : Limits.HasLimits Profinite :=
  has_limits_of_has_limits_creates_limits Profinite.toTop

instance has_colimits : Limits.HasColimits Profinite :=
  has_colimits_of_reflective profiniteToCompHaus

noncomputable instance forgetPreservesLimits : Limits.PreservesLimits (forget Profinite) := by
  apply limits.comp_preserves_limits Profinite.toTop (forget Top)

variable {X Y : Profinite.{u}} (f : X ⟶ Y)

/-- Any morphism of profinite spaces is a closed map. -/
theorem is_closed_map : IsClosedMap f :=
  CompHaus.is_closed_map _

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
theorem is_iso_of_bijective (bij : Function.Bijective f) : IsIso f := by
  have := CompHaus.is_iso_of_bijective (Profinite_to_CompHaus.map f) bij
  exact is_iso_of_fully_faithful profiniteToCompHaus _

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
noncomputable def isoOfBijective (bij : Function.Bijective f) : X ≅ Y := by
  let this := Profinite.is_iso_of_bijective f bij <;> exact as_iso f

instance forget_reflects_isomorphisms : ReflectsIsomorphisms (forget Profinite) :=
  ⟨by
    intro A B f hf <;> exact Profinite.is_iso_of_bijective _ ((is_iso_iff_bijective f).mp hf)⟩

/-- Construct an isomorphism from a homeomorphism. -/
@[simps Hom inv]
def isoOfHomeo (f : X ≃ₜ Y) : X ≅ Y where
  Hom := ⟨f, f.Continuous⟩
  inv := ⟨f.symm, f.symm.Continuous⟩
  hom_inv_id' := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id' := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.Hom
  invFun := f.inv
  left_inv := fun x => by
    change (f.hom ≫ f.inv) x = x
    rw [iso.hom_inv_id, coe_id, id.def]
  right_inv := fun x => by
    change (f.inv ≫ f.hom) x = x
    rw [iso.inv_hom_id, coe_id, id.def]
  continuous_to_fun := f.Hom.Continuous
  continuous_inv_fun := f.inv.Continuous

/-- The equivalence between isomorphisms in `Profinite` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext
    rfl

theorem epi_iff_surjective {X Y : Profinite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.Range f
    have hC : IsClosed C := (is_compact_range f.continuous).IsClosed
    let U := Cᶜ
    have hU : IsOpen U := is_open_compl_iff.mpr hC
    have hyU : y ∈ U := by
      refine' Set.mem_compl _
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ nhds y := hU.mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := is_topological_basis_clopen.mem_nhds_iff.mp hUy
    classical
    let this : TopologicalSpace (ULift.{u} <| Finₓ 2) := ⊥
    let Z := of (ULift.{u} <| Finₓ 2)
    let g : Y ⟶ Z := ⟨(LocallyConstant.ofClopen hV).map ULift.up, LocallyConstant.continuous _⟩
    let h : Y ⟶ Z := ⟨fun _ => ⟨1⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x
      dsimp' [← LocallyConstant.ofClopen]
      rw [if_neg]
      · rfl
        
      refine' mt (fun α => hVU α) _
      simp only [← Set.mem_range_self, ← not_true, ← not_false_iff, ← Set.mem_compl_eq]
    apply_fun fun e => (e y).down  at H
    dsimp' [← LocallyConstant.ofClopen]  at H
    rw [if_pos hyV] at H
    exact top_ne_bot H
    
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget Profinite).epi_of_epi_map
    

theorem mono_iff_injective {X Y : Profinite.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  constructor
  · intro h
    have : limits.preserves_limits profiniteToCompHaus := inferInstance
    have : mono (Profinite_to_CompHaus.map f) := inferInstance
    rwa [← CompHaus.mono_iff_injective]
    
  · rw [← CategoryTheory.mono_iff_injective]
    apply (forget Profinite).mono_of_mono_map
    

end Profinite

