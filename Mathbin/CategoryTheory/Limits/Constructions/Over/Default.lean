/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Connected
import Mathbin.CategoryTheory.Limits.Constructions.Over.Products
import Mathbin.CategoryTheory.Limits.Constructions.Over.Connected
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathbin.CategoryTheory.Limits.Constructions.Equalizers

/-!
# Limits in the over category

Declare instances for limits in the over category: If `C` has finite wide pullbacks, `over B` has
finite limits, and if `C` has arbitrary wide pullbacks then `over B` has limits.
-/


universe w v u

-- morphism levels before object levels. See note [category_theory universes].
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {X : C}

namespace CategoryTheory.Over

/-- Make sure we can derive pullbacks in `over B`. -/
instance {B : C} [HasPullbacks C] : HasPullbacks (Over B) := by
  let this : has_limits_of_shape (UliftHom.{v} (ULift.{v} walking_cospan)) C :=
    has_limits_of_shape_of_equivalence (UliftHomUliftCategory.equiv.{v} _)
  let this : category (UliftHom.{v} (ULift.{v} walking_cospan)) := inferInstance
  exact has_limits_of_shape_of_equivalence (UliftHomUliftCategory.equiv.{v, v} _).symm

/-- Make sure we can derive equalizers in `over B`. -/
instance {B : C} [HasEqualizers C] : HasEqualizers (Over B) := by
  let this : has_limits_of_shape (UliftHom.{v} (ULift.{v} walking_parallel_pair)) C :=
    has_limits_of_shape_of_equivalence (UliftHomUliftCategory.equiv.{v} _)
  let this : category (UliftHom.{v} (ULift.{v} walking_parallel_pair)) := inferInstance
  exact has_limits_of_shape_of_equivalence (UliftHomUliftCategory.equiv.{v, v} _).symm

instance has_finite_limits {B : C} [HasFiniteWidePullbacks C] : HasFiniteLimits (Over B) := by
  apply @finite_limits_from_equalizers_and_finite_products _ _ _ _
  · exact construct_products.over_finite_products_of_finite_wide_pullbacks
    
  · apply @has_equalizers_of_pullbacks_and_binary_products _ _ _ _
    · have : has_pullbacks C :=
        ⟨by
          infer_instance⟩
      exact construct_products.over_binary_product_of_pullback
      
    · infer_instance
      
    

instance has_limits {B : C} [HasWidePullbacks.{w} C] : HasLimitsOfSize.{w} (Over B) := by
  apply @limits_from_equalizers_and_products _ _ _ _
  · exact construct_products.over_products_of_wide_pullbacks
    
  · apply @has_equalizers_of_pullbacks_and_binary_products _ _ _ _
    · have : has_pullbacks C := ⟨inferInstance⟩
      exact construct_products.over_binary_product_of_pullback
      
    · infer_instance
      
    

end CategoryTheory.Over

