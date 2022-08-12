/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.IsConnected
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Connected limits

A connected limit is a limit whose shape is a connected category.

We give examples of connected categories, and prove that the functor given
by `(X × -)` preserves any connected limit. That is, any limit of shape `J`
where `J` is a connected category is preserved by the functor `(X × -)`.
-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

section Examples

instance wide_pullback_shape_connected (J : Type v₁) : IsConnected (WidePullbackShape J) := by
  apply is_connected.of_induct
  introv hp t
  cases j
  · exact hp
    
  · rwa [t (wide_pullback_shape.hom.term j)]
    

instance wide_pushout_shape_connected (J : Type v₁) : IsConnected (WidePushoutShape J) := by
  apply is_connected.of_induct
  introv hp t
  cases j
  · exact hp
    
  · rwa [← t (wide_pushout_shape.hom.init j)]
    

instance parallelPairInhabited : Inhabited WalkingParallelPair :=
  ⟨WalkingParallelPair.one⟩

instance parallel_pair_connected : IsConnected WalkingParallelPair := by
  apply is_connected.of_induct
  introv _ t
  cases j
  · rwa [t walking_parallel_pair_hom.left]
    
  · assumption
    

end Examples

attribute [local tidy] tactic.case_bash

variable {C : Type u₂} [Category.{v₂} C]

variable [HasBinaryProducts C]

variable {J : Type v₂} [SmallCategory J]

namespace ProdPreservesConnectedLimits

/-- (Impl). The obvious natural transformation from (X × K -) to K. -/
@[simps]
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ K where app := fun Y => Limits.prod.snd

/-- (Impl). The obvious natural transformation from (X × K -) to X -/
@[simps]
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ (Functor.const J).obj X where app := fun Y => Limits.prod.fst

/-- (Impl).
Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simps]
def forgetCone {X : C} {K : J ⥤ C} (s : Cone (K ⋙ prod.functor.obj X)) : Cone K where
  x := s.x
  π := s.π ≫ γ₂ X

end ProdPreservesConnectedLimits

open ProdPreservesConnectedLimits

/-- The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limits - that is,
`(X × -)` does not preserve products or terminal object, eg `(X ⨯ A) ⨯ (X ⨯ B)` is not isomorphic to
`X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
noncomputable def prodPreservesConnectedLimits [IsConnected J] (X : C) :
    PreservesLimitsOfShape J
      (prod.functor.obj
        X) where PreservesLimit := fun K =>
    { preserves := fun c l =>
        { lift := fun s => prod.lift (s.π.app (Classical.arbitrary _) ≫ limits.prod.fst) (l.lift (forgetCone s)),
          fac' := fun s j => by
            apply prod.hom_ext
            · erw [assoc, lim_map_π, comp_id, limit.lift_π]
              exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
              
            · simp [l.fac (forget_cone s) j]
              ,
          uniq' := fun s m L => by
            apply prod.hom_ext
            · erw [limit.lift_π, ← L (Classical.arbitrary J), assoc, lim_map_π, comp_id]
              rfl
              
            · rw [limit.lift_π]
              apply l.uniq (forget_cone s)
              intro j
              simp [L j]
               } }

end CategoryTheory

