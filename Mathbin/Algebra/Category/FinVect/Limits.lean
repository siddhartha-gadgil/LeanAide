/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.FinVect
import Mathbin.Algebra.Category.Module.Limits
import Mathbin.Algebra.Category.Module.Products
import Mathbin.Algebra.Category.Module.EpiMono
import Mathbin.CategoryTheory.Limits.Creates
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# `forget₂ (FinVect K) (Module K)` creates all finite limits.

And hence `FinVect K` has all finite limits.

## Future work
After generalising `FinVect` to allow the ring and the module to live in different universes,
generalize this construction so we can take limits over smaller diagrams,
as is done for the other algebraic categories.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace FinVect

variable {J : Type} [SmallCategory J] [FinCategory J]

variable {k : Type v} [Field k]

instance {J : Type} [Fintype J] (Z : J → ModuleCat.{v} k) [∀ j, FiniteDimensional k (Z j)] :
    FiniteDimensional k (∏ fun j => Z j : ModuleCat.{v} k) := by
  have : FiniteDimensional k (ModuleCat.of k (∀ j, Z j)) := by
    dsimp'
    infer_instance
  exact
    FiniteDimensional.of_injective (ModuleCat.piIsoPi _).Hom
      ((ModuleCat.mono_iff_injective _).1
        (by
          infer_instance))

/-- Finite limits of finite finite dimensional vectors spaces are finite dimensional,
because we can realise them as subobjects of a finite product. -/
instance (F : J ⥤ FinVect k) :
    FiniteDimensional k (limit (F ⋙ forget₂ (FinVect k) (ModuleCat.{v} k)) : ModuleCat.{v} k) := by
  have : ∀ j, FiniteDimensional k ((F ⋙ forget₂ (FinVect k) (ModuleCat.{v} k)).obj j) := by
    intro j
    change FiniteDimensional k (F.obj j)
    infer_instance
  exact
    FiniteDimensional.of_injective (limit_subobject_product (F ⋙ forget₂ (FinVect k) (ModuleCat.{v} k)))
      ((ModuleCat.mono_iff_injective _).1
        (by
          infer_instance))

/-- The forgetful functor from `FinVect k` to `Module k` creates all finite limits. -/
def forget₂CreatesLimit (F : J ⥤ FinVect k) : CreatesLimit F (forget₂ (FinVect k) (ModuleCat.{v} k)) :=
  createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FinVect k) (ModuleCat.{v} k)) : ModuleCat.{v} k), by
      infer_instance⟩
    (Iso.refl _)

instance :
    CreatesLimitsOfShape J (forget₂ (FinVect k) (ModuleCat.{v} k)) where CreatesLimit := fun F => forget₂CreatesLimit F

instance :
    HasFiniteLimits
      (FinVect
        k) where out := fun J _ _ =>
    has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape (forget₂ (FinVect k) (ModuleCat.{v} k))

instance :
    PreservesFiniteLimits
      (forget₂ (FinVect k) (ModuleCat.{v} k)) where PreservesFiniteLimits := fun J _ _ => inferInstance

end FinVect

