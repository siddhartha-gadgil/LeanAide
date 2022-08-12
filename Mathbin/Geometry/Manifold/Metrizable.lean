/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Geometry.Manifold.SmoothManifoldWithCorners
import Mathbin.Topology.Paracompact
import Mathbin.Topology.MetricSpace.Metrizable

/-!
# Metrizability of a σ-compact manifold

In this file we show that a σ-compact Hausdorff topological manifold over a finite dimensional real
vector space is metrizable.
-/


open TopologicalSpace

/-- A σ-compact Hausdorff topological manifold over a finite dimensional real vector space is
metrizable. -/
theorem ManifoldWithCorners.metrizable_space {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type _} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
    [SigmaCompactSpace M] [T2Space M] : MetrizableSpace M := by
  have := I.locally_compact
  have := ChartedSpace.locally_compact H M
  have : NormalSpace M := normal_of_paracompact_t2
  have := I.second_countable_topology
  have := ChartedSpace.second_countable_of_sigma_compact H M
  exact metrizable_space_of_t3_second_countable M

