/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Adjunction.Reflective
import Mathbin.Topology.Category.Top.Default
import Mathbin.Topology.StoneCech
import Mathbin.CategoryTheory.Monad.Limits
import Mathbin.Topology.UrysohnsLemma

/-!
# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `Top`.
The fully faithful functor `CompHaus ⥤ Top` is denoted `CompHaus_to_Top`.

**Note:** The file `topology/category/Compactum.lean` provides the equivalence between `Compactum`,
which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`Compactum_to_CompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `Compactum_to_CompHaus.is_equivalence`.
See `topology/category/Compactum.lean` for a more detailed discussion where these definitions are
introduced.

-/


universe v u

open CategoryTheory

/-- The type of Compact Hausdorff topological spaces. -/
structure CompHaus where
  toTop : Top
  [IsCompact : CompactSpace to_Top]
  [is_hausdorff : T2Space to_Top]

namespace CompHaus

instance : Inhabited CompHaus :=
  ⟨{ toTop := { α := Pempty } }⟩

instance : CoeSort CompHaus (Type _) :=
  ⟨fun X => X.toTop⟩

instance {X : CompHaus} : CompactSpace X :=
  X.IsCompact

instance {X : CompHaus} : T2Space X :=
  X.is_hausdorff

instance category : Category CompHaus :=
  InducedCategory.category toTop

instance concreteCategory : ConcreteCategory CompHaus :=
  InducedCategory.concreteCategory _

@[simp]
theorem coe_to_Top {X : CompHaus} : (X.toTop : Type _) = X :=
  rfl

variable (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- A constructor for objects of the category `CompHaus`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
def of : CompHaus where
  toTop := Top.of X
  IsCompact := ‹_›
  is_hausdorff := ‹_›

@[simp]
theorem coe_of : (CompHaus.of X : Type _) = X :=
  rfl

/-- Any continuous function on compact Hausdorff spaces is a closed map. -/
theorem is_closed_map {X Y : CompHaus.{u}} (f : X ⟶ Y) : IsClosedMap f := fun C hC =>
  (hC.IsCompact.Image f.Continuous).IsClosed

/-- Any continuous bijection of compact Hausdorff spaces is an isomorphism. -/
theorem is_iso_of_bijective {X Y : CompHaus.{u}} (f : X ⟶ Y) (bij : Function.Bijective f) : IsIso f := by
  let E := Equivₓ.ofBijective _ bij
  have hE : Continuous E.symm := by
    rw [continuous_iff_is_closed]
    intro S hS
    rw [← E.image_eq_preimage]
    exact IsClosedMap f S hS
  refine' ⟨⟨⟨E.symm, hE⟩, _, _⟩⟩
  · ext x
    apply E.symm_apply_apply
    
  · ext x
    apply E.apply_symm_apply
    

/-- Any continuous bijection of compact Hausdorff spaces induces an isomorphism. -/
noncomputable def isoOfBijective {X Y : CompHaus.{u}} (f : X ⟶ Y) (bij : Function.Bijective f) : X ≅ Y := by
  let this := is_iso_of_bijective _ bij <;> exact as_iso f

end CompHaus

/-- The fully faithful embedding of `CompHaus` in `Top`. -/
@[simps (config := { rhsMd := semireducible })]
def compHausToTop : CompHaus.{u} ⥤ Top.{u} :=
  inducedFunctor _ deriving Full, Faithful

instance CompHaus.forget_reflects_isomorphisms : ReflectsIsomorphisms (forget CompHaus.{u}) :=
  ⟨by
    intro A B f hf <;> exact CompHaus.is_iso_of_bijective _ ((is_iso_iff_bijective f).mp hf)⟩

/-- (Implementation) The object part of the compactification functor from topological spaces to
compact Hausdorff spaces.
-/
@[simps]
def stoneCechObj (X : Top) : CompHaus :=
  CompHaus.of (StoneCech X)

/-- (Implementation) The bijection of homsets to establish the reflective adjunction of compact
Hausdorff spaces in topological spaces.
-/
noncomputable def stoneCechEquivalence (X : Top.{u}) (Y : CompHaus.{u}) :
    (stoneCechObj X ⟶ Y) ≃ (X ⟶ compHausToTop.obj Y) where
  toFun := fun f => { toFun := f ∘ stoneCechUnit, continuous_to_fun := f.2.comp (@continuous_stone_cech_unit X _) }
  invFun := fun f => { toFun := stoneCechExtend f.2, continuous_to_fun := continuous_stone_cech_extend f.2 }
  left_inv := by
    rintro ⟨f : StoneCech X ⟶ Y, hf : Continuous f⟩
    ext (x : StoneCech X)
    refine' congr_fun _ x
    apply Continuous.ext_on dense_range_stone_cech_unit (continuous_stone_cech_extend _) hf
    rintro _ ⟨y, rfl⟩
    apply congr_fun (stone_cech_extend_extends (hf.comp _)) y
  right_inv := by
    rintro ⟨f : (X : Type _) ⟶ Y, hf : Continuous f⟩
    ext
    exact congr_fun (stone_cech_extend_extends hf) _

/-- The Stone-Cech compactification functor from topological spaces to compact Hausdorff spaces,
left adjoint to the inclusion functor.
-/
noncomputable def topToCompHaus : Top.{u} ⥤ CompHaus.{u} :=
  Adjunction.leftAdjointOfEquiv stoneCechEquivalence.{u} fun _ _ _ _ _ => rfl

theorem Top_to_CompHaus_obj (X : Top) : ↥(topToCompHaus.obj X) = StoneCech X :=
  rfl

/-- The category of compact Hausdorff spaces is reflective in the category of topological spaces.
-/
noncomputable instance compHausToTop.reflective :
    Reflective compHausToTop where toIsRightAdjoint := ⟨topToCompHaus, Adjunction.adjunctionOfEquivLeft _ _⟩

noncomputable instance compHausToTop.createsLimits : CreatesLimits compHausToTop :=
  monadicCreatesLimits _

instance CompHaus.has_limits : Limits.HasLimits CompHaus :=
  has_limits_of_has_limits_creates_limits compHausToTop

instance CompHaus.has_colimits : Limits.HasColimits CompHaus :=
  has_colimits_of_reflective compHausToTop

namespace CompHaus

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
/-- An explicit limit cone for a functor `F : J ⥤ CompHaus`, defined in terms of
`Top.limit_cone`. -/
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) : Limits.Cone F where
  x :=
    { toTop := (Top.limitCone (F ⋙ compHausToTop)).x,
      IsCompact := by
        show CompactSpace ↥{ u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j }
        rw [← is_compact_iff_compact_space]
        apply IsClosed.is_compact
        have :
          { u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j } =
            ⋂ (i : J) (j : J) (f : i ⟶ j), { u | F.map f (u i) = u j } :=
          by
          ext1
          simp only [← Set.mem_Inter, ← Set.mem_set_of_eq]
        rw [this]
        apply is_closed_Inter
        intro i
        apply is_closed_Inter
        intro j
        apply is_closed_Inter
        intro f
        apply is_closed_eq
        · exact (ContinuousMap.continuous (F.map f)).comp (continuous_apply i)
          
        · exact continuous_apply j
          ,
      is_hausdorff :=
        show T2Space ↥{ u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j } from inferInstance }
  π :=
    { app := fun j => (Top.limitCone (F ⋙ compHausToTop)).π.app j,
      naturality' := by
        intro _ _ _
        ext ⟨x, hx⟩
        simp only [← comp_apply, ← functor.const.obj_map, ← id_apply]
        exact (hx f).symm }

/-- The limit cone `CompHaus.limit_cone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) : Limits.IsLimit (limitCone F) where
  lift := fun S => (Top.limitConeIsLimit (F ⋙ compHausToTop)).lift (compHausToTop.mapCone S)
  uniq' := fun S m h => (Top.limitConeIsLimit _).uniq (compHausToTop.mapCone S) _ h

theorem epi_iff_surjective {X Y : CompHaus.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.Range f
    have hC : IsClosed C := (is_compact_range f.continuous).IsClosed
    let D := {y}
    have hD : IsClosed D := is_closed_singleton
    have hCD : Disjoint C D := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have : NormalSpace ↥Y.to_Top := normal_of_compact_t2
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_closed hC hD hCD
    have : CompactSpace (ULift.{u} <| Set.Icc (0 : ℝ) 1) := homeomorph.ulift.symm.compact_space
    have : T2Space (ULift.{u} <| Set.Icc (0 : ℝ) 1) := homeomorph.ulift.symm.t2_space
    let Z := of (ULift.{u} <| Set.Icc (0 : ℝ) 1)
    let g : Y ⟶ Z :=
      ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩, continuous_ulift_up.comp (continuous_subtype_mk (fun y' => hφ01 y') φ.continuous)⟩
    let h : Y ⟶ Z := ⟨fun _ => ⟨⟨0, set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x
      dsimp'
      simp only [← comp_apply, ← ContinuousMap.coe_mk, ← Subtype.coe_mk, ← hφ0 (Set.mem_range_self x), ← Pi.zero_apply]
    apply_fun fun e => (e y).down  at H
    dsimp'  at H
    simp only [← Subtype.mk_eq_mk, ← hφ1 (Set.mem_singleton y), ← Pi.one_apply] at H
    exact zero_ne_one H
    
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget CompHaus).epi_of_epi_map
    

theorem mono_iff_injective {X Y : CompHaus.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  constructor
  · intro hf x₁ x₂ h
    let g₁ : of PUnit ⟶ X := ⟨fun _ => x₁, continuous_of_discrete_topology⟩
    let g₂ : of PUnit ⟶ X := ⟨fun _ => x₂, continuous_of_discrete_topology⟩
    have : g₁ ≫ f = g₂ ≫ f := by
      ext
      exact h
    rw [cancel_mono] at this
    apply_fun fun e => e PUnit.unit  at this
    exact this
    
  · rw [← CategoryTheory.mono_iff_injective]
    apply (forget CompHaus).mono_of_mono_map
    

end CompHaus

