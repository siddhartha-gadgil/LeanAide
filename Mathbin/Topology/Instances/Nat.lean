/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Topology.Instances.Int

/-!
# Topology on the natural numbers

The structure of a metric space on `ℕ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Metric Set Filter

namespace Nat

noncomputable instance : HasDist ℕ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℕ) : dist x y = abs (x - y) :=
  rfl

theorem dist_coe_int (x y : ℕ) : dist (x : ℤ) (y : ℤ) = dist x y :=
  rfl

@[norm_cast, simp]
theorem dist_cast_real (x y : ℕ) : dist (x : ℝ) y = dist x y :=
  rfl

theorem pairwise_one_le_dist : Pairwise fun m n : ℕ => 1 ≤ dist m n := by
  intro m n hne
  rw [← dist_coe_int]
  apply Int.pairwise_one_le_dist
  exact_mod_cast hne

theorem uniform_embedding_coe_real : UniformEmbedding (coe : ℕ → ℝ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

theorem closed_embedding_coe_real : ClosedEmbedding (coe : ℕ → ℝ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

instance : MetricSpace ℕ :=
  Nat.uniform_embedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℕ) (r : ℝ) : coe ⁻¹' Ball (x : ℝ) r = Ball x r :=
  rfl

theorem preimage_closed_ball (x : ℕ) (r : ℝ) : coe ⁻¹' ClosedBall (x : ℝ) r = ClosedBall x r :=
  rfl

theorem closed_ball_eq_Icc (x : ℕ) (r : ℝ) : ClosedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊ := by
  rcases le_or_ltₓ 0 r with (hr | hr)
  · rw [← preimage_closed_ball, Real.closed_ball_eq_Icc, preimage_Icc]
    exact add_nonneg (cast_nonneg x) hr
    
  · rw [closed_ball_eq_empty.2 hr]
    apply (Icc_eq_empty _).symm
    rw [not_leₓ]
    calc ⌊(x : ℝ) + r⌋₊ ≤ ⌊(x : ℝ)⌋₊ := by
        apply floor_mono
        linarith _ < ⌈↑x - r⌉₊ := by
        rw [floor_coe, Nat.lt_ceil]
        linarith
    

instance : ProperSpace ℕ :=
  ⟨by
    intro x r
    rw [closed_ball_eq_Icc]
    exact (Set.finite_Icc _ _).IsCompact⟩

instance : NoncompactSpace ℕ :=
  noncompact_space_of_ne_bot <| by
    simp [← Filter.at_top_ne_bot]

end Nat

