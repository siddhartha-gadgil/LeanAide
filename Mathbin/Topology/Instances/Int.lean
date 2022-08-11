/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Topology.MetricSpace.Basic
import Mathbin.Order.Filter.Archimedean

/-!
# Topology on the integers

The structure of a metric space on `ℤ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Metric Set Filter

namespace Int

instance : HasDist ℤ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℤ) : dist x y = abs (x - y) :=
  rfl

@[norm_cast, simp]
theorem dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y :=
  rfl

theorem pairwise_one_le_dist : Pairwise fun m n : ℤ => 1 ≤ dist m n := by
  intro m n hne
  rw [dist_eq]
  norm_cast
  rwa [← zero_addₓ (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]

theorem uniform_embedding_coe_real : UniformEmbedding (coe : ℤ → ℝ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

theorem closed_embedding_coe_real : ClosedEmbedding (coe : ℤ → ℝ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

instance : MetricSpace ℤ :=
  Int.uniform_embedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℤ) (r : ℝ) : coe ⁻¹' Ball (x : ℝ) r = Ball x r :=
  rfl

theorem preimage_closed_ball (x : ℤ) (r : ℝ) : coe ⁻¹' ClosedBall (x : ℝ) r = ClosedBall x r :=
  rfl

theorem ball_eq_Ioo (x : ℤ) (r : ℝ) : Ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉ := by
  rw [← preimage_ball, Real.ball_eq_Ioo, preimage_Ioo]

theorem closed_ball_eq_Icc (x : ℤ) (r : ℝ) : ClosedBall x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋ := by
  rw [← preimage_closed_ball, Real.closed_ball_eq_Icc, preimage_Icc]

instance : ProperSpace ℤ :=
  ⟨by
    intro x r
    rw [closed_ball_eq_Icc]
    exact (Set.finite_Icc _ _).IsCompact⟩

@[simp]
theorem cocompact_eq : cocompact ℤ = at_bot⊔at_top := by
  simp only [comap_dist_right_at_top_eq_cocompact (0 : ℤ), ← dist_eq, ← sub_zero, ← cast_zero, cast_abs,
    @comap_comap _ _ _ _ abs, ← Int.comap_coe_at_top, ← comap_abs_at_top]

@[simp]
theorem cofinite_eq : (cofinite : Filter ℤ) = at_bot⊔at_top := by
  rw [← cocompact_eq_cofinite, cocompact_eq]

end Int

