/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.EssentiallySmall

/-!
# Limits over essentially small indexing categories

If `C` has limits of size `w` and `J` is `w`-essentially small, then `C` has limits of shape `J`.

-/


universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable (J : Type u₂) [Category.{v₂} J] (C : Type u₁) [Category.{v₁} C]

theorem has_limits_of_shape_of_essentially_small [EssentiallySmall.{w₁} J] [HasLimitsOfSize.{w₁, w₁} C] :
    HasLimitsOfShape J C :=
  has_limits_of_shape_of_equivalence <| equivalence.symm <| equivSmallModel.{w₁} J

theorem has_colimits_of_shape_of_essentially_small [EssentiallySmall.{w₁} J] [HasColimitsOfSize.{w₁, w₁} C] :
    HasColimitsOfShape J C :=
  has_colimits_of_shape_of_equivalence <| equivalence.symm <| equivSmallModel.{w₁} J

theorem has_products_of_shape_of_small (β : Type w₁) [Small.{w₂} β] [HasProducts.{w₂} C] : HasProductsOfShape β C :=
  has_limits_of_shape_of_equivalence <| discrete.equivalence <| Equivₓ.symm <| equivShrink β

theorem has_coproducts_of_shape_of_small (β : Type w₁) [Small.{w₂} β] [HasCoproducts.{w₂} C] :
    HasCoproductsOfShape β C :=
  has_colimits_of_shape_of_equivalence <| discrete.equivalence <| Equivₓ.symm <| equivShrink β

end CategoryTheory.Limits

