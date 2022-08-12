/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Topology.Sheaves.Presheaf
import Mathbin.CategoryTheory.Limits.Final
import Mathbin.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Another version of the sheaf condition.

Given a family of open sets `U : ι → opens X` we can form the subcategory
`{ V : opens X // ∃ i, V ≤ U i }`, which has `supr U` as a cocone.

The sheaf condition on a presheaf `F` is equivalent to
`F` sending the opposite of this cocone to a limit cone in `C`, for every `U`.

This condition is particularly nice when checking the sheaf condition
because we don't need to do any case bashing
(depending on whether we're looking at single or double intersections,
or equivalently whether we're looking at the first or second object in an equalizer diagram).

## References
* This is the definition Lurie uses in [Spectral Algebraic Geometry][LurieSAG].
-/


universe v u

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

open TopologicalSpace.Opens

namespace Top

variable {C : Type u} [Category.{v} C]

variable {X : Top.{v}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)

namespace Presheaf

namespace SheafCondition

/-- The category of open sets contained in some element of the cover.
-/
def OpensLeCover : Type v :=
  { V : Opens X // ∃ i, V ≤ U i }

instance [Inhabited ι] : Inhabited (OpensLeCover U) :=
  ⟨⟨⊥, default, bot_le⟩⟩

instance : Category (OpensLeCover U) :=
  CategoryTheory.fullSubcategory _

namespace OpensLeCover

variable {U}

/-- An arbitrarily chosen index such that `V ≤ U i`.
-/
def index (V : OpensLeCover U) : ι :=
  V.property.some

/-- The morphism from `V` to `U i` for some `i`.
-/
def homToIndex (V : OpensLeCover U) : V.val ⟶ U (index V) :=
  V.property.some_spec.Hom

end OpensLeCover

/-- `supr U` as a cocone over the opens sets contained in some element of the cover.

(In fact this is a colimit cocone.)
-/
def opensLeCoverCocone : Cocone (fullSubcategoryInclusion _ : OpensLeCover U ⥤ Opens X) where
  x := supr U
  ι := { app := fun V : OpensLeCover U => V.homToIndex ≫ Opens.leSupr U _ }

end SheafCondition

open SheafCondition

/-- An equivalent formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_opens_le_cover`).

A presheaf is a sheaf if `F` sends the cone `(opens_le_cover_cocone U).op` to a limit cone.
(Recall `opens_le_cover_cocone U`, has cone point `supr U`,
mapping down to any `V` which is contained in some `U i`.)
-/
def IsSheafOpensLeCover : Prop :=
  ∀ ⦃ι : Type v⦄ (U : ι → Opens X), Nonempty (IsLimit (F.mapCone (opensLeCoverCocone U).op))

namespace SheafCondition

open CategoryTheory.Pairwise

/-- Implementation detail:
the object level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
@[simp]
def pairwiseToOpensLeCoverObj : Pairwise ι → OpensLeCover U
  | single i => ⟨U i, ⟨i, le_rfl⟩⟩
  | pair i j => ⟨U i⊓U j, ⟨i, inf_le_left⟩⟩

open CategoryTheory.Pairwise.Hom

/-- Implementation detail:
the morphism level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
def pairwiseToOpensLeCoverMap :
    ∀ {V W : Pairwise ι}, (V ⟶ W) → (pairwiseToOpensLeCoverObj U V ⟶ pairwiseToOpensLeCoverObj U W)
  | _, _, id_single i => 𝟙 _
  | _, _, id_pair i j => 𝟙 _
  | _, _, left i j => homOfLe inf_le_left
  | _, _, right i j => homOfLe inf_le_right

/-- The category of single and double intersections of the `U i` maps into the category
of open sets below some `U i`.
-/
@[simps]
def pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U where
  obj := pairwiseToOpensLeCoverObj U
  map := fun V W i => pairwiseToOpensLeCoverMap U i

instance (V : OpensLeCover U) : Nonempty (StructuredArrow V (pairwiseToOpensLeCover U)) :=
  ⟨{ right := single V.index, Hom := V.homToIndex }⟩

/-- The diagram consisting of the `U i` and `U i ⊓ U j` is cofinal in the diagram
of all opens contained in some `U i`.
-/
-- This is a case bash: for each pair of types of objects in `pairwise ι`,
-- we have to explicitly construct a zigzag.
instance : Functor.Final (pairwiseToOpensLeCover U) :=
  ⟨fun V =>
    is_connected_of_zigzag fun A B => by
      rcases A with ⟨⟨⟨⟩⟩, ⟨i⟩ | ⟨i, j⟩, a⟩ <;> rcases B with ⟨⟨⟨⟩⟩, ⟨i'⟩ | ⟨i', j'⟩, b⟩ <;> dsimp'  at *
      · refine' ⟨[{ left := ⟨⟨⟩⟩, right := pair i i', Hom := (le_inf a.le b.le).Hom }, _], _, rfl⟩
        exact
          List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := left i i' }⟩)
            (List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := right i i' }⟩) List.Chain.nil)
        
      · refine'
          ⟨[{ left := ⟨⟨⟩⟩, right := pair i' i, Hom := (le_inf (b.le.trans inf_le_left) a.le).Hom },
              { left := ⟨⟨⟩⟩, right := single i', Hom := (b.le.trans inf_le_left).Hom }, _],
            _, rfl⟩
        exact
          List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := right i' i }⟩)
            (List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := left i' i }⟩)
              (List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := left i' j' }⟩) List.Chain.nil))
        
      · refine'
          ⟨[{ left := ⟨⟨⟩⟩, right := single i, Hom := (a.le.trans inf_le_left).Hom },
              { left := ⟨⟨⟩⟩, right := pair i i', Hom := (le_inf (a.le.trans inf_le_left) b.le).Hom }, _],
            _, rfl⟩
        exact
          List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := left i j }⟩)
            (List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := left i i' }⟩)
              (List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := right i i' }⟩) List.Chain.nil))
        
      · refine'
          ⟨[{ left := ⟨⟨⟩⟩, right := single i, Hom := (a.le.trans inf_le_left).Hom },
              { left := ⟨⟨⟩⟩, right := pair i i',
                Hom := (le_inf (a.le.trans inf_le_left) (b.le.trans inf_le_left)).Hom },
              { left := ⟨⟨⟩⟩, right := single i', Hom := (b.le.trans inf_le_left).Hom }, _],
            _, rfl⟩
        exact
          List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := left i j }⟩)
            (List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := left i i' }⟩)
              (List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := right i i' }⟩)
                (List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := left i' j' }⟩) List.Chain.nil)))
        ⟩

/-- The diagram in `opens X` indexed by pairwise intersections from `U` is isomorphic
(in fact, equal) to the diagram factored through `opens_le_cover U`.
-/
def pairwiseDiagramIso : Pairwise.diagram U ≅ pairwiseToOpensLeCover U ⋙ fullSubcategoryInclusion _ where
  Hom :=
    { app := by
        rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
  inv :=
    { app := by
        rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }

/-- The cocone `pairwise.cocone U` with cocone point `supr U` over `pairwise.diagram U` is isomorphic
to the cocone `opens_le_cover_cocone U` (with the same cocone point)
after appropriate whiskering and postcomposition.
-/
def pairwiseCoconeIso :
    (Pairwise.cocone U).op ≅
      (Cones.postcomposeEquivalence (NatIso.op (pairwiseDiagramIso U : _) : _)).Functor.obj
        ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op) :=
  Cones.ext (Iso.refl _)
    (by
      tidy)

end SheafCondition

open SheafCondition

/-- The sheaf condition
in terms of a limit diagram over all `{ V : opens X // ∃ i, V ≤ U i }`
is equivalent to the reformulation
in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
theorem is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections (F : Presheaf C X) :
    F.IsSheafOpensLeCover ↔ F.IsSheafPairwiseIntersections :=
  forall₂_congrₓ fun ι U =>
    Equivₓ.nonempty_congr <|
      calc
        IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
            IsLimit ((F.mapCone (opensLeCoverCocone U).op).whisker (pairwiseToOpensLeCover U).op) :=
          (Functor.Initial.isLimitWhiskerEquiv (pairwiseToOpensLeCover U).op _).symm
        _ ≃ IsLimit (F.mapCone ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op)) :=
          IsLimit.equivIsoLimit F.mapConeWhisker.symm
        _ ≃
            IsLimit
              ((Cones.postcomposeEquivalence _).Functor.obj
                (F.mapCone ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op))) :=
          (IsLimit.postcomposeHomEquiv _ _).symm
        _ ≃
            IsLimit
              (F.mapCone
                ((Cones.postcomposeEquivalence _).Functor.obj
                  ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op))) :=
          IsLimit.equivIsoLimit (Functor.mapConePostcomposeEquivalenceFunctor _).symm
        _ ≃ IsLimit (F.mapCone (Pairwise.cocone U).op) :=
          IsLimit.equivIsoLimit ((Cones.functoriality _ _).mapIso (pairwiseCoconeIso U : _).symm)
        

section

variable {Y : Opens X} (hY : Y = supr U)

/-- Given a family of opens `U` and an open `Y` equal to the union of opens in `U`, we may
    take the presieve on `Y` associated to `U` and the sieve generated by it, and form the
    full subcategory (subposet) of opens contained in `Y` (`over Y`) consisting of arrows
    in the sieve. This full subcategory is equivalent to `opens_le_cover U`, the (poset)
    category of opens contained in some `U i`. -/
@[simps]
def generateEquivalenceOpensLe :
    { f : Over Y // (Sieve.generate (PresieveOfCoveringAux U Y)).Arrows f.Hom } ≌ OpensLeCover U where
  Functor :=
    { obj := fun f =>
        ⟨f.1.left,
          let ⟨_, h, _, ⟨i, hY⟩, _⟩ := f.2
          ⟨i, hY ▸ h.le⟩⟩,
      map := fun _ _ g => g.left }
  inverse :=
    { obj := fun V =>
        ⟨Over.mk
            (hY.substr
                (let ⟨i, h⟩ := V.2
                h.trans (le_supr U i))).Hom,
          let ⟨i, h⟩ := V.2
          ⟨U i, h.Hom, (hY.substr (le_supr U i)).Hom, ⟨i, rfl⟩, rfl⟩⟩,
      map := fun _ _ g => Over.homMk g }
  unitIso :=
    eq_to_iso <|
      CategoryTheory.Functor.ext
        (by
          rintro ⟨⟨_, _⟩, _⟩
          dsimp'
          congr <;> ext)
        (by
          intros
          ext)
  counitIso :=
    eq_to_iso <|
      CategoryTheory.Functor.hext
        (by
          intro
          ext
          rfl)
        (by
          intros
          rfl)

/-- Given a family of opens `opens_le_cover_cocone U` is essentially the natural cocone
    associated to the sieve generated by the presieve associated to `U` with indexing
    category changed using the above equivalence. -/
@[simps]
def whiskerIsoMapGenerateCocone :
    Cone.whisker (generateEquivalenceOpensLe U hY).op.Functor (F.mapCone (opensLeCoverCocone U).op) ≅
      F.mapCone (Sieve.generate (PresieveOfCoveringAux U Y)).Arrows.Cocone.op where
  Hom :=
    { Hom := F.map (eqToHom (congr_arg op hY.symm)),
      w' := fun j => by
        erw [← F.map_comp]
        congr }
  inv :=
    { Hom := F.map (eqToHom (congr_arg op hY)),
      w' := fun j => by
        erw [← F.map_comp]
        congr }
  hom_inv_id' := by
    ext
    simp [← eq_to_hom_map]
  inv_hom_id' := by
    ext
    simp [← eq_to_hom_map]

/-- Given a presheaf `F` on the topological space `X` and a family of opens `U` of `X`,
    the natural cone associated to `F` and `U` used in the definition of
    `F.is_sheaf_opens_le_cover` is a limit cone iff the natural cone associated to `F`
    and the sieve generated by the presieve associated to `U` is a limit cone. -/
def isLimitOpensLeEquivGenerate₁ :
    IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
      IsLimit (F.mapCone (Sieve.generate (PresieveOfCoveringAux U Y)).Arrows.Cocone.op) :=
  (IsLimit.whiskerEquivalenceEquiv (generateEquivalenceOpensLe U hY).op).trans
    (IsLimit.equivIsoLimit (whiskerIsoMapGenerateCocone F U hY))

/-- Given a presheaf `F` on the topological space `X` and a presieve `R` whose generated sieve
    is covering for the associated Grothendieck topology (equivalently, the presieve is covering
    for the associated pretopology), the natural cone associated to `F` and the family of opens
    associated to `R` is a limit cone iff the natural cone associated to `F` and the generated
    sieve is a limit cone.
    Since only the existence of a 1-1 correspondence will be used, the exact definition does
    not matter, so tactics are used liberally. -/
def isLimitOpensLeEquivGenerate₂ (R : Presieve Y) (hR : Sieve.generate R ∈ Opens.grothendieckTopology X Y) :
    IsLimit (F.mapCone (opensLeCoverCocone (coveringOfPresieve Y R)).op) ≃
      IsLimit (F.mapCone (Sieve.generate R).Arrows.Cocone.op) :=
  by
  convert
      is_limit_opens_le_equiv_generate₁ F (covering_of_presieve Y R)
        (covering_of_presieve.supr_eq_of_mem_grothendieck Y R hR).symm using
      2 <;>
    rw [covering_presieve_eq_self R]

/-- A presheaf `(opens X)ᵒᵖ ⥤ C` on a topological space `X` is a sheaf on the site `opens X` iff
    it satisfies the `is_sheaf_opens_le_cover` sheaf condition. The latter is not the
    official definition of sheaves on spaces, but has the advantage that it does not
    require `has_products C`. -/
theorem is_sheaf_sites_iff_is_sheaf_opens_le_cover :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) F ↔ F.IsSheafOpensLeCover := by
  rw [presheaf.is_sheaf_iff_is_limit]
  constructor
  · intro h ι U
    rw [(is_limit_opens_le_equiv_generate₁ F U rfl).nonempty_congr]
    apply h
    apply presieve_of_covering.mem_grothendieck_topology
    
  · intro h Y S
    rw [← sieve.generate_sieve S]
    intro hS
    rw [← (is_limit_opens_le_equiv_generate₂ F S hS).nonempty_congr]
    apply h
    

end

variable [HasProducts.{v} C]

/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over all `{ V : opens X // ∃ i, V ≤ U i }`.
-/
theorem is_sheaf_iff_is_sheaf_opens_le_cover (F : Presheaf C X) : F.IsSheaf ↔ F.IsSheafOpensLeCover :=
  Iff.trans (is_sheaf_iff_is_sheaf_pairwise_intersections F)
    (is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections F).symm

end Presheaf

end Top

