/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.FinCategory
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.Data.Fintype.Basic

/-!
# Categories with finite limits.

A typeclass for categories with all finite (co)limits.
-/


universe w' w v' u' v u

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/-- A category has all finite limits if every functor `J ⥤ C` with a `fin_category J`
instance and `J : Type` has a limit.

This is often called 'finitely complete'.
-/
-- We can't just made this an `abbreviation`
-- because of https://github.com/leanprover-community/lean/issues/429
class HasFiniteLimits : Prop where
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasLimitsOfShape J 𝒥 C _

instance (priority := 100) has_limits_of_shape_of_has_finite_limits (J : Type w) [SmallCategory J] [FinCategory J]
    [HasFiniteLimits C] : HasLimitsOfShape J C := by
  apply has_limits_of_shape_of_equivalence (fin_category.equiv_as_type J)
  apply has_finite_limits.out

instance (priority := 100) has_finite_limits_of_has_limits_of_size [HasLimitsOfSize.{v', u'} C] : HasFiniteLimits C :=
  ⟨fun J hJ hJ' => by
    have := has_limits_of_size_shrink.{0, 0} C
    exact has_limits_of_shape_of_equivalence (fin_category.equiv_as_type J)⟩

/-- If `C` has all limits, it has finite limits. -/
instance (priority := 100) has_finite_limits_of_has_limits [HasLimits C] : HasFiniteLimits C :=
  inferInstance

/-- We can always derive `has_finite_limits C` by providing limits at an
arbitrary universe. -/
theorem has_finite_limits_of_has_finite_limits_of_size
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (hJ : @FinCategory J 𝒥), by
        skip
        exact has_limits_of_shape J C) :
    HasFiniteLimits C :=
  ⟨fun J hJ hhJ => by
    skip
    let this : Category.{w, w} (UliftHom.{w} (ULift.{w, 0} J)) := by
      apply UliftHom.category.{0}
      exact CategoryTheory.uliftCategory J
    have := h (UliftHom.{w} (ULift.{w} J)) CategoryTheory.finCategoryUlift
    exact has_limits_of_shape_of_equivalence (UliftHomUliftCategory.equiv.{w, w} J).symm⟩

/-- A category has all finite colimits if every functor `J ⥤ C` with a `fin_category J`
instance and `J : Type` has a colimit.

This is often called 'finitely cocomplete'.
-/
class HasFiniteColimits : Prop where
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasColimitsOfShape J 𝒥 C _

instance (priority := 100) has_colimits_of_shape_of_has_finite_colimits (J : Type w) [SmallCategory J] [FinCategory J]
    [HasFiniteColimits C] : HasColimitsOfShape J C := by
  apply has_colimits_of_shape_of_equivalence (fin_category.equiv_as_type J)
  apply has_finite_colimits.out

instance (priority := 100) has_finite_colimits_of_has_colimits_of_size [HasColimitsOfSize.{v', u'} C] :
    HasFiniteColimits C :=
  ⟨fun J hJ hJ' => by
    have := has_colimits_of_size_shrink.{0, 0} C
    exact has_colimits_of_shape_of_equivalence (fin_category.equiv_as_type J)⟩

/-- We can always derive `has_finite_colimits C` by providing colimits at an
arbitrary universe. -/
theorem has_finite_colimits_of_has_finite_colimits_of_size
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (hJ : @FinCategory J 𝒥), by
        skip
        exact has_colimits_of_shape J C) :
    HasFiniteColimits C :=
  ⟨fun J hJ hhJ => by
    skip
    let this : Category.{w, w} (UliftHom.{w} (ULift.{w, 0} J)) := by
      apply UliftHom.category.{0}
      exact CategoryTheory.uliftCategory J
    have := h (UliftHom.{w} (ULift.{w} J)) CategoryTheory.finCategoryUlift
    exact has_colimits_of_shape_of_equivalence (UliftHomUliftCategory.equiv.{w, w} J).symm⟩

section

open WalkingParallelPair WalkingParallelPairHom

instance fintypeWalkingParallelPair : Fintype WalkingParallelPair where
  elems := [WalkingParallelPair.zero, WalkingParallelPair.one].toFinset
  complete := fun x => by
    cases x <;> simp

attribute [local tidy] tactic.case_bash

instance (j j' : WalkingParallelPair) : Fintype (WalkingParallelPairHom j j') where
  elems :=
    WalkingParallelPair.recOn j
      (WalkingParallelPair.recOn j' [WalkingParallelPairHom.id zero].toFinset [left, right].toFinset)
      (WalkingParallelPair.recOn j' ∅ [WalkingParallelPairHom.id one].toFinset)
  complete := by
    tidy

end

instance : FinCategory WalkingParallelPair where

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
example [HasFiniteLimits C] : HasEqualizers C := by
  infer_instance

/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
    coequalizers -/
example [HasFiniteColimits C] : HasCoequalizers C := by
  infer_instance

variable {J : Type v}

attribute [local tidy] tactic.case_bash

namespace WidePullbackShape

instance fintypeObj [Fintype J] : Fintype (WidePullbackShape J) := by
  rw [wide_pullback_shape]
  infer_instance

instance fintypeHom (j j' : WidePullbackShape J) : Fintype (j ⟶ j') where
  elems := by
    cases j'
    · cases j
      · exact {hom.id none}
        
      · exact {hom.term j}
        
      
    · by_cases' some j' = j
      · rw [h]
        exact {hom.id j}
        
      · exact ∅
        
      
  complete := by
    tidy

end WidePullbackShape

namespace WidePushoutShape

instance fintypeObj [Fintype J] : Fintype (WidePushoutShape J) := by
  rw [wide_pushout_shape]
  infer_instance

instance fintypeHom (j j' : WidePushoutShape J) : Fintype (j ⟶ j') where
  elems := by
    cases j
    · cases j'
      · exact {hom.id none}
        
      · exact {hom.init j'}
        
      
    · by_cases' some j = j'
      · rw [h]
        exact {hom.id j'}
        
      · exact ∅
        
      
  complete := by
    tidy

end WidePushoutShape

instance finCategoryWidePullback [Fintype J] :
    FinCategory (WidePullbackShape J) where fintypeHom := WidePullbackShape.fintypeHom

instance finCategoryWidePushout [Fintype J] :
    FinCategory (WidePushoutShape J) where fintypeHom := WidePushoutShape.fintypeHom

/-- `has_finite_wide_pullbacks` represents a choice of wide pullback
for every finite collection of morphisms
-/
-- We can't just made this an `abbreviation`
-- because of https://github.com/leanprover-community/lean/issues/429
class HasFiniteWidePullbacks : Prop where
  out (J : Type) [Fintype J] : HasLimitsOfShape (WidePullbackShape J) C

instance has_limits_of_shape_wide_pullback_shape (J : Type) [Fintype J] [HasFiniteWidePullbacks C] :
    HasLimitsOfShape (WidePullbackShape J) C := by
  have := @has_finite_wide_pullbacks.out C _ _ J
  infer_instance

/-- `has_finite_wide_pushouts` represents a choice of wide pushout
for every finite collection of morphisms
-/
class HasFiniteWidePushouts : Prop where
  out (J : Type) [Fintype J] : HasColimitsOfShape (WidePushoutShape J) C

instance has_colimits_of_shape_wide_pushout_shape (J : Type) [Fintype J] [HasFiniteWidePushouts C] :
    HasColimitsOfShape (WidePushoutShape J) C := by
  have := @has_finite_wide_pushouts.out C _ _ J
  infer_instance

/-- Finite wide pullbacks are finite limits, so if `C` has all finite limits,
it also has finite wide pullbacks
-/
theorem has_finite_wide_pullbacks_of_has_finite_limits [HasFiniteLimits C] : HasFiniteWidePullbacks C :=
  ⟨fun J _ => has_finite_limits.out _⟩

/-- Finite wide pushouts are finite colimits, so if `C` has all finite colimits,
it also has finite wide pushouts
-/
theorem has_finite_wide_pushouts_of_has_finite_limits [HasFiniteColimits C] : HasFiniteWidePushouts C :=
  ⟨fun J _ => has_finite_colimits.out _⟩

instance fintypeWalkingPair : Fintype WalkingPair where
  elems := {WalkingPair.left, WalkingPair.right}
  complete := fun x => by
    cases x <;> simp

/-- Pullbacks are finite limits, so if `C` has all finite limits, it also has all pullbacks -/
example [HasFiniteWidePullbacks C] : HasPullbacks C := by
  infer_instance

/-- Pushouts are finite colimits, so if `C` has all finite colimits, it also has all pushouts -/
example [HasFiniteWidePushouts C] : HasPushouts C := by
  infer_instance

end CategoryTheory.Limits

