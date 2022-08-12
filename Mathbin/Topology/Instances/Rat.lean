/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Topology.MetricSpace.Basic
import Mathbin.Topology.Algebra.Order.Archimedean
import Mathbin.Topology.Instances.Int
import Mathbin.Topology.Instances.Nat
import Mathbin.Topology.Instances.Real

/-!
# Topology on the ratonal numbers

The structure of a metric space on `ℚ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Metric Set Filter

namespace Rat

instance : MetricSpace ℚ :=
  MetricSpace.induced coe Rat.cast_injective Real.metricSpace

theorem dist_eq (x y : ℚ) : dist x y = abs (x - y) :=
  rfl

@[norm_cast, simp]
theorem dist_cast (x y : ℚ) : dist (x : ℝ) y = dist x y :=
  rfl

theorem uniform_continuous_coe_real : UniformContinuous (coe : ℚ → ℝ) :=
  uniform_continuous_comap

theorem uniform_embedding_coe_real : UniformEmbedding (coe : ℚ → ℝ) :=
  uniform_embedding_comap Rat.cast_injective

theorem dense_embedding_coe_real : DenseEmbedding (coe : ℚ → ℝ) :=
  uniform_embedding_coe_real.DenseEmbedding Rat.dense_range_cast

theorem embedding_coe_real : Embedding (coe : ℚ → ℝ) :=
  dense_embedding_coe_real.toEmbedding

theorem continuous_coe_real : Continuous (coe : ℚ → ℝ) :=
  uniform_continuous_coe_real.Continuous

end Rat

@[norm_cast, simp]
theorem Nat.dist_cast_rat (x y : ℕ) : dist (x : ℚ) y = dist x y := by
  rw [← Nat.dist_cast_real, ← Rat.dist_cast] <;> congr 1 <;> norm_cast

theorem Nat.uniform_embedding_coe_rat : UniformEmbedding (coe : ℕ → ℚ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one <| by
    simpa using Nat.pairwise_one_le_dist

theorem Nat.closed_embedding_coe_rat : ClosedEmbedding (coe : ℕ → ℚ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one <| by
    simpa using Nat.pairwise_one_le_dist

@[norm_cast, simp]
theorem Int.dist_cast_rat (x y : ℤ) : dist (x : ℚ) y = dist x y := by
  rw [← Int.dist_cast_real, ← Rat.dist_cast] <;> congr 1 <;> norm_cast

theorem Int.uniform_embedding_coe_rat : UniformEmbedding (coe : ℤ → ℚ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one <| by
    simpa using Int.pairwise_one_le_dist

theorem Int.closed_embedding_coe_rat : ClosedEmbedding (coe : ℤ → ℚ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one <| by
    simpa using Int.pairwise_one_le_dist

instance : NoncompactSpace ℚ :=
  Int.closed_embedding_coe_rat.NoncompactSpace

-- TODO(Mario): Find a way to use rat_add_continuous_lemma
theorem Rat.uniform_continuous_add : UniformContinuous fun p : ℚ × ℚ => p.1 + p.2 :=
  Rat.uniform_embedding_coe_real.to_uniform_inducing.uniform_continuous_iff.2 <| by
    simp only [← (· ∘ ·), ← Rat.cast_add] <;>
      exact real.uniform_continuous_add.comp (rat.uniform_continuous_coe_real.prod_map Rat.uniform_continuous_coe_real)

theorem Rat.uniform_continuous_neg : UniformContinuous (@Neg.neg ℚ _) :=
  Metric.uniform_continuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun a b h => by
      rw [dist_comm] at h <;> simpa [← Rat.dist_eq] using h⟩

instance : UniformAddGroup ℚ :=
  UniformAddGroup.mk' Rat.uniform_continuous_add Rat.uniform_continuous_neg

instance : TopologicalAddGroup ℚ := by
  infer_instance

instance : OrderTopology ℚ :=
  induced_order_topology _ (fun x y => Rat.cast_lt) (@exists_rat_btwn _ _ _)

theorem Rat.uniform_continuous_abs : UniformContinuous (abs : ℚ → ℚ) :=
  Metric.uniform_continuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun a b h =>
      lt_of_le_of_ltₓ
        (by
          simpa [← Rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _)
        h⟩

theorem Rat.continuous_mul : Continuous fun p : ℚ × ℚ => p.1 * p.2 :=
  Rat.embedding_coe_real.continuous_iff.2 <| by
    simp [← (· ∘ ·)] <;> exact real.continuous_mul.comp (rat.continuous_coe_real.prod_map Rat.continuous_coe_real)

instance : TopologicalRing ℚ :=
  { Rat.topological_add_group with continuous_mul := Rat.continuous_mul }

theorem Rat.totally_bounded_Icc (a b : ℚ) : TotallyBounded (Icc a b) := by
  have := totally_bounded_preimage Rat.uniform_embedding_coe_real (totally_bounded_Icc a b)
  rwa [(Set.ext fun q => _ : Icc _ _ = _)]
  simp

