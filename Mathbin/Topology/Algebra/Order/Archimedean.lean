/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Topology.Algebra.Order.Basic
import Mathbin.Algebra.Order.Archimedean

/-!
# Rational numbers are dense in a linear ordered archimedean field

In this file we prove that coercion from `ℚ` to a linear ordered archimedean field has dense range.
This lemma is in a separate file because `topology.algebra.order.basic` does not import
`algebra.order.archimedean`.
-/


variable {𝕜 : Type _} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜]

/-- Rational numbers are dense in a linear ordered archimedean field. -/
theorem Rat.dense_range_cast : DenseRange (coe : ℚ → 𝕜) :=
  dense_of_exists_between fun a b h => Set.exists_range_iff.2 <| exists_rat_btwn h

