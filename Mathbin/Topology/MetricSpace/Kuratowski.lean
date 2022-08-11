/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.NormedSpace.LpSpace
import Mathbin.Topology.Sets.Compacts

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℝ)`.
-/


noncomputable section

open Set Metric TopologicalSpace

open Ennreal

-- mathport name: «exprℓ_infty_ℝ»
local notation "ℓ_infty_ℝ" => lp (fun n : ℕ => ℝ) ∞

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace kuratowskiEmbedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℝ) -/


variable {f g : ℓ_infty_ℝ} {n : ℕ} {C : ℝ} [MetricSpace α] (x : ℕ → α) (a b : α)

/-- A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in `Kuratowski_embedding`,
without density assumptions. -/
def embeddingOfSubset : ℓ_infty_ℝ :=
  ⟨fun n => dist a (x n) - dist (x 0) (x n), by
    apply mem_ℓp_infty
    use dist a (x 0)
    rintro - ⟨n, rfl⟩
    exact abs_dist_sub_le _ _ _⟩

theorem embedding_of_subset_coe : embeddingOfSubset x a n = dist a (x n) - dist (x 0) (x n) :=
  rfl

/-- The embedding map is always a semi-contraction. -/
theorem embedding_of_subset_dist_le (a b : α) : dist (embeddingOfSubset x a) (embeddingOfSubset x b) ≤ dist a b := by
  refine' lp.norm_le_of_forall_le dist_nonneg fun n => _
  simp only [← lp.coe_fn_sub, ← Pi.sub_apply, ← embedding_of_subset_coe, ← Real.dist_eq]
  convert abs_dist_sub_le a b (x n) using 2
  ring

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- When the reference set is dense, the embedding map is an isometry on its image. -/
theorem embedding_of_subset_isometry (H : DenseRange x) : Isometry (embeddingOfSubset x) := by
  refine' isometry_emetric_iff_metric.2 fun a b => _
  refine' (embedding_of_subset_dist_le x a b).antisymm (le_of_forall_pos_le_add fun e epos => _)
  -- First step: find n with dist a (x n) < e
  rcases Metric.mem_closure_range_iff.1 (H a) (e / 2) (half_pos epos) with ⟨n, hn⟩
  -- Second step: use the norm control at index n to conclude
  have C : dist b (x n) - dist a (x n) = embedding_of_subset x b n - embedding_of_subset x a n := by
    simp only [← embedding_of_subset_coe, ← sub_sub_sub_cancel_right]
  have :=
    calc
      dist a b ≤ dist a (x n) + dist (x n) b := dist_triangle _ _ _
      _ = 2 * dist a (x n) + (dist b (x n) - dist a (x n)) := by
        simp [← dist_comm]
        ring
      _ ≤ 2 * dist a (x n) + abs (dist b (x n) - dist a (x n)) := by
        apply_rules [add_le_add_left, le_abs_self]
      _ ≤ 2 * (e / 2) + abs (embedding_of_subset x b n - embedding_of_subset x a n) := by
        rw [C]
        apply_rules [add_le_add, mul_le_mul_of_nonneg_left, hn.le, le_reflₓ]
        norm_num
      _ ≤ 2 * (e / 2) + dist (embedding_of_subset x b) (embedding_of_subset x a) := by
        have :
          abs (embedding_of_subset x b n - embedding_of_subset x a n) ≤
            dist (embedding_of_subset x b) (embedding_of_subset x a) :=
          by
          simpa [← dist_eq_norm] using
            lp.norm_apply_le_norm Ennreal.top_ne_zero (embedding_of_subset x b - embedding_of_subset x a) n
        nlinarith
      _ = dist (embedding_of_subset x b) (embedding_of_subset x a) + e := by
        ring
      
  simpa [← dist_comm] using this

/-- Every separable metric space embeds isometrically in `ℓ_infty_ℝ`. -/
theorem exists_isometric_embedding (α : Type u) [MetricSpace α] [SeparableSpace α] : ∃ f : α → ℓ_infty_ℝ, Isometry f :=
  by
  cases' (univ : Set α).eq_empty_or_nonempty with h h
  · use fun _ => 0
    intro x
    exact absurd h (nonempty.ne_empty ⟨x, mem_univ x⟩)
    
  · -- We construct a map x : ℕ → α with dense image
    rcases h with ⟨basepoint⟩
    have : Inhabited α := ⟨basepoint⟩
    have : ∃ s : Set α, s.Countable ∧ Dense s := exists_countable_dense α
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩
    rcases Set.countable_iff_exists_surjective.1 S_countable with ⟨x, x_range⟩
    -- Use embedding_of_subset to construct the desired isometry
    exact ⟨embedding_of_subset x, embedding_of_subset_isometry x (S_dense.mono x_range)⟩
    

end kuratowskiEmbedding

open TopologicalSpace kuratowskiEmbedding

/-- The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℝ)`. -/
def kuratowskiEmbedding (α : Type u) [MetricSpace α] [SeparableSpace α] : α → ℓ_infty_ℝ :=
  Classical.some (KuratowskiEmbedding.exists_isometric_embedding α)

/-- The Kuratowski embedding is an isometry. -/
protected theorem kuratowskiEmbedding.isometry (α : Type u) [MetricSpace α] [SeparableSpace α] :
    Isometry (kuratowskiEmbedding α) :=
  Classical.some_spec (exists_isometric_embedding α)

/-- Version of the Kuratowski embedding for nonempty compacts -/
def NonemptyCompacts.kuratowskiEmbedding (α : Type u) [MetricSpace α] [CompactSpace α] [Nonempty α] :
    NonemptyCompacts ℓ_infty_ℝ where
  Carrier := Range (kuratowskiEmbedding α)
  compact' := is_compact_range (kuratowskiEmbedding.isometry α).Continuous
  nonempty' := range_nonempty _

