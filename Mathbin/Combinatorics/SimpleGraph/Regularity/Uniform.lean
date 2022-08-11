/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Combinatorics.SimpleGraph.Density
import Mathbin.SetTheory.Ordinal.Basic

/-!
# Graph uniformity and uniform partitions

In this file we define uniformity of a pair of vertices in a graph and uniformity of a partition of
vertices of a graph. Both are also known as ε-regularity.

Finsets of vertices `s` and `t` are `ε`-uniform in a graph `G` if their edge density is at most
`ε`-far from the density of any big enough `s'` and `t'` where `s' ⊆ s`, `t' ⊆ t`.
The definition is pretty technical, but it amounts to the edges between `s` and `t` being "random"
The literature contains several definitions which are equivalent up to scaling `ε` by some constant
when the partition is equitable.

A partition `P` of the vertices is `ε`-uniform if the proportion of non `ε`-uniform pairs of parts
is less than `ε`.

## Main declarations

* `simple_graph.is_uniform`: Graph uniformity of a pair of finsets of vertices.
* `simple_graph.nonuniform_witness`: `G.nonuniform_witness ε s t` and `G.nonuniform_witness ε t s`
  together witness the non-uniformity of `s` and `t`.
* `finpartition.non_uniforms`: Non uniform pairs of parts of a partition.
* `finpartition.is_uniform`: Uniformity of a partition.
* `finpartition.nonuniform_witnesses`: For each non-uniform pair of parts of a partition, pick
  witnesses of non-uniformity and dump them all together.
-/


open Finset

variable {α 𝕜 : Type _} [LinearOrderedField 𝕜]

/-! ###  Graph uniformity -/


namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] (ε : 𝕜) {s t : Finset α} {a b : α}

/-- A pair of finsets of vertices is `ε`-uniform (aka `ε`-regular) iff their edge density is close
to the density of any big enough pair of subsets. Intuitively, the edges between them are
random-like. -/
def IsUniform (s t : Finset α) : Prop :=
  ∀ ⦃s'⦄,
    s' ⊆ s →
      ∀ ⦃t'⦄,
        t' ⊆ t →
          (s.card : 𝕜) * ε ≤ s'.card →
            (t.card : 𝕜) * ε ≤ t'.card → abs ((G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)) < ε

variable {G ε}

theorem IsUniform.mono {ε' : 𝕜} (h : ε ≤ ε') (hε : IsUniform G ε s t) : IsUniform G ε' s t := fun s' hs' t' ht' hs ht =>
  by
  refine' (hε hs' ht' (le_transₓ _ hs) (le_transₓ _ ht)).trans_le h <;>
    exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

theorem IsUniform.symm : Symmetric (IsUniform G ε) := fun s t h t' ht' s' hs' ht hs => by
  rw [edge_density_comm _ t', edge_density_comm _ t]
  exact h hs' ht' hs ht

variable (G)

theorem is_uniform_comm : IsUniform G ε s t ↔ IsUniform G ε t s :=
  ⟨fun h => h.symm, fun h => h.symm⟩

theorem is_uniform_singleton (hε : 0 < ε) : G.IsUniform ε {a} {b} := by
  intro s' hs' t' ht' hs ht
  rw [card_singleton, Nat.cast_oneₓ, one_mulₓ] at hs ht
  obtain rfl | rfl := Finset.subset_singleton_iff.1 hs'
  · replace hs : ε ≤ 0 := by
      simpa using hs
    exact (hε.not_le hs).elim
    
  obtain rfl | rfl := Finset.subset_singleton_iff.1 ht'
  · replace ht : ε ≤ 0 := by
      simpa using ht
    exact (hε.not_le ht).elim
    
  · rwa [sub_self, abs_zero]
    

theorem not_is_uniform_zero : ¬G.IsUniform (0 : 𝕜) s t := fun h =>
  (abs_nonneg _).not_lt <|
    h (empty_subset _) (empty_subset _)
      (by
        simp )
      (by
        simp )

theorem is_uniform_one : G.IsUniform (1 : 𝕜) s t := by
  intro s' hs' t' ht' hs ht
  rw [mul_oneₓ] at hs ht
  rw [eq_of_subset_of_card_le hs' (Nat.cast_le.1 hs), eq_of_subset_of_card_le ht' (Nat.cast_le.1 ht), sub_self,
    abs_zero]
  exact zero_lt_one

variable {G}

theorem not_is_uniform_iff :
    ¬G.IsUniform ε s t ↔
      ∃ s',
        s' ⊆ s ∧
          ∃ t',
            t' ⊆ t ∧
              ↑s.card * ε ≤ s'.card ∧ ↑t.card * ε ≤ t'.card ∧ ε ≤ abs (G.edgeDensity s' t' - G.edgeDensity s t) :=
  by
  unfold is_uniform
  simp only [← not_forall, ← not_ltₓ, ← exists_prop]

open Classical

variable (G)

/-- An arbitrary pair of subsets witnessing the non-uniformity of `(s, t)`. If `(s, t)` is uniform,
returns `(s, t)`. Witnesses for `(s, t)` and `(t, s)` don't necessarily match. See
`simple_graph.nonuniform_witness`. -/
noncomputable def nonuniformWitnesses (ε : 𝕜) (s t : Finset α) : Finset α × Finset α :=
  if h : ¬G.IsUniform ε s t then ((not_is_uniform_iff.1 h).some, (not_is_uniform_iff.1 h).some_spec.2.some) else (s, t)

theorem left_nonuniform_witnesses_subset (h : ¬G.IsUniform ε s t) : (G.nonuniformWitnesses ε s t).1 ⊆ s := by
  rw [nonuniform_witnesses, dif_pos h]
  exact (not_is_uniform_iff.1 h).some_spec.1

theorem left_nonuniform_witnesses_card (h : ¬G.IsUniform ε s t) :
    (s.card : 𝕜) * ε ≤ (G.nonuniformWitnesses ε s t).1.card := by
  rw [nonuniform_witnesses, dif_pos h]
  exact (not_is_uniform_iff.1 h).some_spec.2.some_spec.2.1

theorem right_nonuniform_witnesses_subset (h : ¬G.IsUniform ε s t) : (G.nonuniformWitnesses ε s t).2 ⊆ t := by
  rw [nonuniform_witnesses, dif_pos h]
  exact (not_is_uniform_iff.1 h).some_spec.2.some_spec.1

theorem right_nonuniform_witnesses_card (h : ¬G.IsUniform ε s t) :
    (t.card : 𝕜) * ε ≤ (G.nonuniformWitnesses ε s t).2.card := by
  rw [nonuniform_witnesses, dif_pos h]
  exact (not_is_uniform_iff.1 h).some_spec.2.some_spec.2.2.1

theorem nonuniform_witnesses_spec (h : ¬G.IsUniform ε s t) :
    ε ≤ abs (G.edgeDensity (G.nonuniformWitnesses ε s t).1 (G.nonuniformWitnesses ε s t).2 - G.edgeDensity s t) := by
  rw [nonuniform_witnesses, dif_pos h]
  exact (not_is_uniform_iff.1 h).some_spec.2.some_spec.2.2.2

/-- Arbitrary witness of non-uniformity. `G.nonuniform_witness ε s t` and
`G.nonuniform_witness ε t s` form a pair of subsets witnessing the non-uniformity of `(s, t)`. If
`(s, t)` is uniform, returns `s`. -/
noncomputable def nonuniformWitness (ε : 𝕜) (s t : Finset α) : Finset α :=
  if WellOrderingRel s t then (G.nonuniformWitnesses ε s t).1 else (G.nonuniformWitnesses ε t s).2

theorem nonuniform_witness_subset (h : ¬G.IsUniform ε s t) : G.nonuniformWitness ε s t ⊆ s := by
  unfold nonuniform_witness
  split_ifs
  · exact G.left_nonuniform_witnesses_subset h
    
  · exact G.right_nonuniform_witnesses_subset fun i => h i.symm
    

theorem nonuniform_witness_card_le (h : ¬G.IsUniform ε s t) : (s.card : 𝕜) * ε ≤ (G.nonuniformWitness ε s t).card := by
  unfold nonuniform_witness
  split_ifs
  · exact G.left_nonuniform_witnesses_card h
    
  · exact G.right_nonuniform_witnesses_card fun i => h i.symm
    

theorem nonuniform_witness_spec (h₁ : s ≠ t) (h₂ : ¬G.IsUniform ε s t) :
    ε ≤ abs (G.edgeDensity (G.nonuniformWitness ε s t) (G.nonuniformWitness ε t s) - G.edgeDensity s t) := by
  unfold nonuniform_witness
  rcases trichotomous_of WellOrderingRel s t with (lt | rfl | gt)
  · rw [if_pos lt, if_neg (asymm lt)]
    exact G.nonuniform_witnesses_spec h₂
    
  · cases h₁ rfl
    
  · rw [if_neg (asymm Gt), if_pos Gt, edge_density_comm, edge_density_comm _ s]
    apply G.nonuniform_witnesses_spec fun i => h₂ i.symm
    

end SimpleGraph

/-! ### Uniform partitions -/


variable [DecidableEq α] {A : Finset α} (P : Finpartition A) (G : SimpleGraph α) [DecidableRel G.Adj] {ε : 𝕜}

namespace Finpartition

open Classical

/-- The pairs of parts of a partition `P` which are not `ε`-uniform in a graph `G`. Note that we
dismiss the diagonal. We do not care whether `s` is `ε`-uniform with itself. -/
noncomputable def nonUniforms (ε : 𝕜) : Finset (Finset α × Finset α) :=
  P.parts.offDiag.filter fun uv => ¬G.IsUniform ε uv.1 uv.2

theorem mk_mem_non_uniforms_iff (u v : Finset α) (ε : 𝕜) :
    (u, v) ∈ P.nonUniforms G ε ↔ u ∈ P.parts ∧ v ∈ P.parts ∧ u ≠ v ∧ ¬G.IsUniform ε u v := by
  rw [non_uniforms, mem_filter, mem_off_diag, and_assoc, and_assoc]

theorem non_uniforms_mono {ε ε' : 𝕜} (h : ε ≤ ε') : P.nonUniforms G ε' ⊆ P.nonUniforms G ε :=
  (monotone_filter_right _) fun uv => mt <| SimpleGraph.IsUniform.mono h

theorem non_uniforms_bot (hε : 0 < ε) : (⊥ : Finpartition A).nonUniforms G ε = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  rintro ⟨u, v⟩
  simp only [← Finpartition.mk_mem_non_uniforms_iff, ← Finpartition.parts_bot, ← mem_map, ← not_and, ← not_not, ←
    exists_imp_distrib]
  rintro x hx rfl y hy rfl h
  exact G.is_uniform_singleton hε

/-- A finpartition of a graph's vertex set is `ε`-uniform (aka `ε`-regular) iff the proportion of
its pairs of parts that are not `ε`-uniform is at most `ε`. -/
def IsUniform (ε : 𝕜) : Prop :=
  ((P.nonUniforms G ε).card : 𝕜) ≤ (P.parts.card * (P.parts.card - 1) : ℕ) * ε

theorem bot_is_uniform (hε : 0 < ε) : (⊥ : Finpartition A).IsUniform G ε := by
  rw [Finpartition.IsUniform, Finpartition.card_bot, non_uniforms_bot _ hε, Finset.card_empty, Nat.cast_zeroₓ]
  exact mul_nonneg (Nat.cast_nonneg _) hε.le

theorem is_uniform_one : P.IsUniform G (1 : 𝕜) := by
  rw [is_uniform, mul_oneₓ, Nat.cast_le]
  refine' (card_filter_le _ _).trans _
  rw [off_diag_card, Nat.mul_sub_left_distrib, mul_oneₓ]

variable {P G}

theorem IsUniform.mono {ε ε' : 𝕜} (hP : P.IsUniform G ε) (h : ε ≤ ε') : P.IsUniform G ε' :=
  ((Nat.cast_le.2 <| card_le_of_subset <| P.non_uniforms_mono G h).trans hP).trans <|
    mul_le_mul_of_nonneg_left h <| Nat.cast_nonneg _

theorem is_uniform_of_empty (hP : P.parts = ∅) : P.IsUniform G ε := by
  simp [← is_uniform, ← hP, ← non_uniforms]

theorem nonempty_of_not_uniform (h : ¬P.IsUniform G ε) : P.parts.Nonempty :=
  nonempty_of_ne_empty fun h₁ => h <| is_uniform_of_empty h₁

variable (P G ε) (s : Finset α)

/-- A choice of witnesses of non-uniformity among the parts of a finpartition. -/
noncomputable def nonuniformWitnesses : Finset (Finset α) :=
  (P.parts.filter fun t => s ≠ t ∧ ¬G.IsUniform ε s t).Image (G.nonuniformWitness ε s)

variable {P G ε s} {t : Finset α}

theorem nonuniform_witness_mem_nonuniform_witnesses (h : ¬G.IsUniform ε s t) (ht : t ∈ P.parts) (hst : s ≠ t) :
    G.nonuniformWitness ε s t ∈ P.nonuniformWitnesses G ε s :=
  mem_image_of_mem _ <| mem_filter.2 ⟨ht, hst, h⟩

end Finpartition

