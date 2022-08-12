/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.FinCategory

/-!
# Preservation of finite (co)limits.

These functors are also known as left exact (flat) or right exact functors when the categories
involved are abelian, or more generally, finitely (co)complete.

## Related results
* `category_theory.limits.preserves_finite_limits_of_preserves_equalizers_and_finite_products` :
  see `category_theory/limits/constructions/limits_of_products_and_equalizers.lean`. Also provides
  the dual version.
* `category_theory.limits.preserves_finite_limits_iff_flat` :
  see `category_theory/flat_functors.lean`.

-/


open CategoryTheory

namespace CategoryTheory.Limits

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

variable {J : Type w} [SmallCategory J] {K : J ⥤ C}

/-- A functor is said to preserve finite limits, if it preserves all limits of shape `J`,
where `J : Type` is a finite category.
-/
class PreservesFiniteLimits (F : C ⥤ D) where
  PreservesFiniteLimits : ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F := by
    run_tac
      tactic.apply_instance

attribute [instance] preserves_finite_limits.preserves_finite_limits

/-- Preserving finite limits also implies preserving limits over finite shapes in higher universes,
though through a noncomputable instance. -/
noncomputable instance (priority := 100) preservesLimitsOfShapeOfPreservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] (J : Type w) [SmallCategory J] [FinCategory J] : PreservesLimitsOfShape J F := by
  apply preserves_limits_of_shape_of_equiv (fin_category.equiv_as_type J)

noncomputable instance (priority := 100) PreservesLimits.preservesFiniteLimitsOfSize (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w₂} F] : PreservesFiniteLimits F :=
  ⟨fun J sJ fJ => by
    have := preserves_smallest_limits_of_preserves_limits F
    exact preserves_limits_of_shape_of_equiv (fin_category.equiv_as_type J) F⟩

noncomputable instance (priority := 120) PreservesLimits.preservesFiniteLimits (F : C ⥤ D) [PreservesLimits F] :
    PreservesFiniteLimits F :=
  PreservesLimits.preservesFiniteLimitsOfSize F

/-- We can always derive `preserves_finite_limits C` by showing that we are preserving limits at an
arbitrary universe. -/
def preservesFiniteLimitsOfPreservesFiniteLimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (hJ : @FinCategory J 𝒥), by
        skip
        exact preserves_limits_of_shape J F) :
    PreservesFiniteLimits F :=
  ⟨fun J hJ hhJ => by
    skip
    let this : Category.{w, w} (UliftHom.{w} (ULift.{w, 0} J)) := by
      apply UliftHom.category.{0}
      exact CategoryTheory.uliftCategory J
    have := h (UliftHom.{w} (ULift.{w} J)) CategoryTheory.finCategoryUlift
    exact preserves_limits_of_shape_of_equiv (UliftHomUliftCategory.equiv.{w, w} J).symm F⟩

instance idPreservesFiniteLimits : PreservesFiniteLimits (𝟭 C) where

/-- The composition of two left exact functors is left exact. -/
def compPreservesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F ⋙ G) :=
  ⟨fun _ _ _ => by
    skip
    infer_instance⟩

/-- A functor is said to preserve finite colimits, if it preserves all colimits of
shape `J`, where `J : Type` is a finite category.
-/
class PreservesFiniteColimits (F : C ⥤ D) where
  PreservesFiniteColimits : ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J F := by
    run_tac
      tactic.apply_instance

attribute [instance] preserves_finite_colimits.preserves_finite_colimits

/-- Preserving finite limits also implies preserving limits over finite shapes in higher universes,
though through a noncomputable instance. -/
noncomputable instance (priority := 100) preservesColimitsOfShapeOfPreservesFiniteColimits (F : C ⥤ D)
    [PreservesFiniteColimits F] (J : Type w) [SmallCategory J] [FinCategory J] : PreservesColimitsOfShape J F := by
  apply preserves_colimits_of_shape_of_equiv (fin_category.equiv_as_type J)

noncomputable instance (priority := 100) PreservesColimits.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w₂} F] : PreservesFiniteColimits F :=
  ⟨fun J sJ fJ => by
    have := preserves_smallest_colimits_of_preserves_colimits F
    exact preserves_colimits_of_shape_of_equiv (fin_category.equiv_as_type J) F⟩

/-- We can always derive `preserves_finite_limits C` by showing that we are preserving limits at an
arbitrary universe. -/
def preservesFiniteColimitsOfPreservesFiniteColimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (hJ : @FinCategory J 𝒥), by
        skip
        exact preserves_colimits_of_shape J F) :
    PreservesFiniteColimits F :=
  ⟨fun J hJ hhJ => by
    skip
    let this : Category.{w, w} (UliftHom.{w} (ULift.{w, 0} J)) := by
      apply UliftHom.category.{0}
      exact CategoryTheory.uliftCategory J
    have := h (UliftHom.{w} (ULift.{w} J)) CategoryTheory.finCategoryUlift
    exact preserves_colimits_of_shape_of_equiv (UliftHomUliftCategory.equiv.{w, w} J).symm F⟩

instance idPreservesFiniteColimits : PreservesFiniteColimits (𝟭 C) where

/-- The composition of two right exact functors is right exact. -/
def compPreservesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F] [PreservesFiniteColimits G] :
    PreservesFiniteColimits (F ⋙ G) :=
  ⟨fun _ _ _ => by
    skip
    infer_instance⟩

end CategoryTheory.Limits

