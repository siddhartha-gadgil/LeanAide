/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Additive Categories

This file contains the definition of additive categories.

TODO: show that finite biproducts implies enriched over commutative monoids and what is missing
additionally to have additivity is that identities have additive inverses,
see https://ncatlab.org/nlab/show/biproduct#BiproductsImplyEnrichment
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory

variable (C : Type u) [Category C]

/-- A preadditive category `C` is called additive if it has all finite biproducts.
See <https://stacks.math.columbia.edu/tag/0104>.
-/
class AdditiveCategory extends Preadditive C, HasFiniteBiproducts C

end CategoryTheory

