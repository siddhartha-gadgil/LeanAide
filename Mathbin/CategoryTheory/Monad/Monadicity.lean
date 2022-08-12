/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.Reflexive
import Mathbin.CategoryTheory.Monad.Coequalizer
import Mathbin.CategoryTheory.Monad.Limits

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a right adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers`
* `G` creates `G`-split coequalizers, see
  `category_theory.monad.monadic_of_creates_G_split_coequalizers`
  (The converse of this is also shown, see
   `category_theory.monad.creates_G_split_coequalizers_of_monadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms`

## Tags

Beck, monadicity, descent

## TODO

Dualise to show comonadicity theorems.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Monadₓ

open Limits

noncomputable section

-- Hide the implementation details in this namespace.
namespace MonadicityInternal

section

-- We use these parameters and notations to simplify the statements of internal constructions
-- here.
parameter {C : Type u₁}{D : Type u₂}

parameter [Category.{v₁} C][Category.{v₁} D]

parameter {G : D ⥤ C}[IsRightAdjoint G]

-- mathport name: «exprF»
-- An unfortunate consequence of the local notation is that it is only recognised if there is an
-- extra space after the reference.
local notation "F" => leftAdjoint G

-- mathport name: «expradj»
local notation "adj" => Adjunction.ofRightAdjoint G

/-- The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
reflexive pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_reflexive (A : adj.toMonad.Algebra) : IsReflexivePair (F.map A.a) (adj.counit.app (F.obj A.a)) := by
  apply is_reflexive_pair.mk' (F.map (adj.Unit.app _)) _ _
  · rw [← F.map_comp, ← F.map_id]
    exact congr_arg (fun _ => F.map _) A.unit
    
  · rw [adj.left_triangle_components]
    rfl
    

/-- The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
`G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_G_split (A : adj.toMonad.Algebra) :
    G.IsSplitPair (F.map A.a) (adj.counit.app (F.obj A.a)) where splittable := ⟨_, _, ⟨beckSplitCoequalizer A⟩⟩

/-- The object function for the left adjoint to the comparison functor. -/
def comparisonLeftAdjointObj (A : adj.toMonad.Algebra) [HasCoequalizer (F.map A.a) (adj.counit.app _)] : D :=
  coequalizer (F.map A.a) (adj.counit.app _)

/-- We have a bijection of homsets which will be used to construct the left adjoint to the comparison
functor.
-/
@[simps]
def comparisonLeftAdjointHomEquiv (A : adj.toMonad.Algebra) (B : D)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] :
    (comparison_left_adjoint_obj A ⟶ B) ≃ (A ⟶ (comparison adj).obj B) :=
  calc
    (comparison_left_adjoint_obj A ⟶ B) ≃ { f : F.obj A.a ⟶ B // _ } := Cofork.IsColimit.homIso (colimit.isColimit _) B
    _ ≃ { g : A.a ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g } := by
      refine' (adj.homEquiv _ _).subtypeEquiv _
      intro f
      rw [← (adj.homEquiv _ _).Injective.eq_iff, adjunction.hom_equiv_naturality_left, adj.hom_equiv_unit,
        adj.hom_equiv_unit, G.map_comp]
      dsimp'
      rw [adj.right_triangle_components_assoc, ← G.map_comp, F.map_comp, category.assoc, adj.counit_naturality,
        adj.left_triangle_components_assoc]
      apply eq_comm
    _ ≃ (A ⟶ (comparison adj).obj B) :=
      { toFun := fun g => { f := _, h' := g.Prop }, invFun := fun f => ⟨f.f, f.h⟩,
        left_inv := fun g => by
          ext
          rfl,
        right_inv := fun f => by
          ext
          rfl }
    

/-- Construct the adjunction to the comparison functor.
-/
def leftAdjointComparison [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] :
    adj.toMonad.Algebra ⥤ D := by
  refine'
    @adjunction.left_adjoint_of_equiv _ _ _ _ (comparison adj) (fun A => comparison_left_adjoint_obj A) (fun A B => _) _
  · apply comparison_left_adjoint_hom_equiv
    
  · intro A B B' g h
    ext1
    dsimp' [← comparison_left_adjoint_hom_equiv]
    rw [← adj.hom_equiv_naturality_right, category.assoc]
    

/-- Provided we have the appropriate coequalizers, we have an adjunction to the comparison functor.
-/
@[simps counit]
def comparisonAdjunction [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] :
    left_adjoint_comparison ⊣ comparison adj :=
  Adjunction.adjunctionOfEquivLeft _ _

theorem comparison_adjunction_unit_f_aux
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] (A : adj.toMonad.Algebra) :
    (comparison_adjunction.Unit.app A).f =
      adj.homEquiv A.a _ (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.a))) :=
  congr_arg (adj.homEquiv _ _) (Category.comp_id _)

/-- This is a cofork which is helpful for establishing monadicity: the morphism from the Beck
coequalizer to this cofork is the unit for the adjunction on the comparison functor.
-/
@[simps x]
def unitCofork (A : adj.toMonad.Algebra) [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] :
    Cofork (G.map (F.map A.a)) (G.map (adj.counit.app (F.obj A.a))) :=
  Cofork.ofπ (G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.a))))
    (by
      change _ = G.map _ ≫ _
      rw [← G.map_comp, coequalizer.condition, G.map_comp])

@[simp]
theorem unit_cofork_π (A : adj.toMonad.Algebra) [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] :
    (unit_cofork A).π = G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.a))) :=
  rfl

theorem comparison_adjunction_unit_f
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] (A : adj.toMonad.Algebra) :
    (comparison_adjunction.Unit.app A).f = (beckCoequalizer A).desc (unit_cofork A) := by
  apply limits.cofork.is_colimit.hom_ext (beck_coequalizer A)
  rw [cofork.is_colimit.π_desc]
  dsimp' only [← beck_cofork_π, ← unit_cofork_π]
  rw [comparison_adjunction_unit_f_aux, ← adj.hom_equiv_naturality_left A.a, coequalizer.condition,
    adj.hom_equiv_naturality_right, adj.hom_equiv_unit, category.assoc]
  apply adj.right_triangle_components_assoc

/-- The cofork which describes the counit of the adjunction: the morphism from the coequalizer of
this pair to this morphism is the counit.
-/
@[simps]
def counitCofork (B : D) : Cofork (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B))) :=
  Cofork.ofπ (adj.counit.app B) (adj.counit_naturality _)

/-- The unit cofork is a colimit provided `G` preserves it.  -/
def unitColimitOfPreservesCoequalizer (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))]
    [PreservesColimit (parallelPair (F.map A.a) (adj.counit.app (F.obj A.a))) G] : IsColimit (unit_cofork A) :=
  isColimitOfHasCoequalizerOfPreservesColimit G _ _

/-- The counit cofork is a colimit provided `G` reflects it. -/
def counitCoequalizerOfReflectsCoequalizer (B : D)
    [ReflectsColimit (parallelPair (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B)))) G] :
    IsColimit (counit_cofork B) :=
  isColimitOfIsColimitCoforkMap G _ (beckCoequalizer ((comparison adj).obj B))

theorem comparison_adjunction_counit_app
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] (B : D) :
    comparison_adjunction.counit.app B = colimit.desc _ (counit_cofork B) := by
  apply coequalizer.hom_ext
  change
    coequalizer.π _ _ ≫ coequalizer.desc ((adj.homEquiv _ B).symm (𝟙 _)) _ = coequalizer.π _ _ ≫ coequalizer.desc _ _
  simp

end

end MonadicityInternal

open CategoryTheory.Adjunction

open MonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable (G : D ⥤ C)

/-- If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" direction of Beck's
monadicity theorem, the converse is given in `monadic_of_creates_G_split_coequalizers`.
-/
def createsGSplitCoequalizersOfMonadic [MonadicRightAdjoint G] ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g] :
    CreatesColimit (parallelPair f g) G := by
  apply monadic_creates_colimit_of_preserves_colimit _ _
  infer_instance
  · apply preserves_colimit_of_iso_diagram _ (diagramIsoParallelPair.{v₁} _).symm
    dsimp'
    infer_instance
    
  · apply preserves_colimit_of_iso_diagram _ (diagramIsoParallelPair.{v₁} _).symm
    dsimp'
    infer_instance
    

variable [IsRightAdjoint G]

section BeckMonadicity

/-- To show `G` is a monadic right adjoint, we can show it preserves and reflects `G`-split
coequalizers, and `C` has them.
-/
def monadicOfHasPreservesReflectsGSplitCoequalizers [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G] : MonadicRightAdjoint G := by
  let L : (adjunction.of_right_adjoint G).toMonad.Algebra ⥤ D := left_adjoint_comparison
  let i : is_right_adjoint (comparison (of_right_adjoint G)) := ⟨_, comparison_adjunction⟩
  constructor
  let this :
    ∀ X : (of_right_adjoint G).toMonad.Algebra,
      is_iso ((of_right_adjoint (comparison (of_right_adjoint G))).Unit.app X) :=
    by
    intro X
    apply is_iso_of_reflects_iso _ (monad.forget (of_right_adjoint G).toMonad)
    · change is_iso (comparison_adjunction.unit.app X).f
      rw [comparison_adjunction_unit_f]
      change
        is_iso
          (is_colimit.cocone_point_unique_up_to_iso (beck_coequalizer X) (unit_colimit_of_preserves_coequalizer X)).Hom
      refine' is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso _ _)
      
  let this : ∀ Y : D, is_iso ((of_right_adjoint (comparison (of_right_adjoint G))).counit.app Y) := by
    intro Y
    change is_iso (comparison_adjunction.counit.app Y)
    rw [comparison_adjunction_counit_app]
    change is_iso (is_colimit.cocone_point_unique_up_to_iso _ _).Hom
    infer_instance
    apply counit_coequalizer_of_reflects_coequalizer _
    let this :
      G.is_split_pair ((left_adjoint G).map (G.map ((adjunction.of_right_adjoint G).counit.app Y)))
        ((adjunction.of_right_adjoint G).counit.app ((left_adjoint G).obj (G.obj Y))) :=
      monadicity_internal.main_pair_G_split ((comparison (adjunction.of_right_adjoint G)).obj Y)
    infer_instance
  exact adjunction.is_right_adjoint_to_is_equivalence

/-- Beck's monadicity theorem. If `G` has a right adjoint and creates coequalizers of `G`-split pairs,
then it is monadic.
This is the converse of `creates_G_split_of_monadic`.
-/
def monadicOfCreatesGSplitCoequalizers
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G] : MonadicRightAdjoint G := by
  let this : ∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], has_colimit (parallel_pair f g ⋙ G) := by
    intro A B f g i
    apply has_colimit_of_iso (diagramIsoParallelPair.{v₁} _)
    change has_coequalizer (G.map f) (G.map g)
    infer_instance
  apply monadic_of_has_preserves_reflects_G_split_coequalizers _
  · infer_instance
    
  · intro A B f g i
    apply has_colimit_of_created (parallel_pair f g) G
    
  · intro A B f g i
    infer_instance
    
  · intro A B f g i
    infer_instance
    

/-- An alternate version of Beck's monadicity theorem. If `G` reflects isomorphisms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, then it is monadic.
-/
def monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms [ReflectsIsomorphisms G]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G] : MonadicRightAdjoint G := by
  apply monadic_of_has_preserves_reflects_G_split_coequalizers _
  · infer_instance
    
  · assumption
    
  · assumption
    
  · intro A B f g i
    apply reflects_colimit_of_reflects_isomorphisms
    

end BeckMonadicity

section ReflexiveMonadicity

variable [HasReflexiveCoequalizers D] [ReflectsIsomorphisms G]

variable [∀ ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesColimit (parallelPair f g) G]

/-- Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
def monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms : MonadicRightAdjoint G := by
  let L : (adjunction.of_right_adjoint G).toMonad.Algebra ⥤ D := left_adjoint_comparison
  let i : is_right_adjoint (comparison (adjunction.of_right_adjoint G)) := ⟨_, comparison_adjunction⟩
  constructor
  let this :
    ∀ X : (adjunction.of_right_adjoint G).toMonad.Algebra,
      is_iso ((adjunction.of_right_adjoint (comparison (adjunction.of_right_adjoint G))).Unit.app X) :=
    by
    intro X
    apply is_iso_of_reflects_iso _ (monad.forget (adjunction.of_right_adjoint G).toMonad)
    · change is_iso (comparison_adjunction.unit.app X).f
      rw [comparison_adjunction_unit_f]
      change
        is_iso
          (is_colimit.cocone_point_unique_up_to_iso (beck_coequalizer X) (unit_colimit_of_preserves_coequalizer X)).Hom
      apply is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso _ _)
      
  let this : ∀ Y : D, is_iso ((of_right_adjoint (comparison (adjunction.of_right_adjoint G))).counit.app Y) := by
    intro Y
    change is_iso (comparison_adjunction.counit.app Y)
    rw [comparison_adjunction_counit_app]
    change is_iso (is_colimit.cocone_point_unique_up_to_iso _ _).Hom
    infer_instance
    apply counit_coequalizer_of_reflects_coequalizer _
    apply reflects_colimit_of_reflects_isomorphisms
  exact adjunction.is_right_adjoint_to_is_equivalence

end ReflexiveMonadicity

end Monadₓ

end CategoryTheory

