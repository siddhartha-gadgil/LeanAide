/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.NumberTheory.Liouville.Basic
import Mathbin.Topology.MetricSpace.Baire
import Mathbin.Topology.Instances.Irrational

/-!
# Density of Liouville numbers

In this file we prove that the set of Liouville numbers form a dense `Gδ` set. We also prove a
similar statement about irrational numbers.
-/


open Filter

open Filter Set Metric

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (a b)
theorem set_of_liouville_eq_Inter_Union :
    { x | Liouville x } = ⋂ n : ℕ, ⋃ (a : ℤ) (b : ℤ) (hb : 1 < b), Ball (a / b) (1 / b ^ n) \ {a / b} := by
  ext x
  simp only [← mem_Inter, ← mem_Union, ← Liouville, ← mem_set_of_eq, ← exists_prop, ← mem_diff, ← mem_singleton_iff, ←
    mem_ball, ← Real.dist_eq, ← and_comm]

theorem is_Gδ_set_of_liouville : IsGδ { x | Liouville x } := by
  rw [set_of_liouville_eq_Inter_Union]
  refine' is_Gδ_Inter fun n => IsOpen.is_Gδ _
  refine' is_open_Union fun a => is_open_Union fun b => is_open_Union fun hb => _
  exact is_open_ball.inter is_closed_singleton.is_open_compl

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (a b)
theorem set_of_liouville_eq_irrational_inter_Inter_Union :
    { x | Liouville x } = { x | Irrational x } ∩ ⋂ n : ℕ, ⋃ (a : ℤ) (b : ℤ) (hb : 1 < b), Ball (a / b) (1 / b ^ n) := by
  refine' subset.antisymm _ _
  · refine' subset_inter (fun x hx => hx.Irrational) _
    rw [set_of_liouville_eq_Inter_Union]
    exact Inter_mono fun n => Union₂_mono fun a b => Union_mono fun hb => diff_subset _ _
    
  · simp only [← inter_Inter, ← inter_Union, ← set_of_liouville_eq_Inter_Union]
    refine' Inter_mono fun n => Union₂_mono fun a b => Union_mono fun hb => _
    rw [inter_comm]
    refine' diff_subset_diff subset.rfl (singleton_subset_iff.2 ⟨a / b, _⟩)
    norm_cast
    

/-- The set of Liouville numbers is a residual set. -/
theorem eventually_residual_liouville : ∀ᶠ x in residual ℝ, Liouville x := by
  rw [Filter.Eventually, set_of_liouville_eq_irrational_inter_Inter_Union]
  refine' eventually_residual_irrational.and _
  refine' eventually_residual.2 ⟨_, _, rat.dense_embedding_coe_real.dense.mono _, subset.rfl⟩
  · exact
      is_Gδ_Inter fun n =>
        IsOpen.is_Gδ <| is_open_Union fun a => is_open_Union fun b => is_open_Union fun hb => is_open_ball
    
  · rintro _ ⟨r, rfl⟩
    simp only [← mem_Inter, ← mem_Union]
    refine' fun n => ⟨r.num * 2, r.denom * 2, _, _⟩
    · have := Int.coe_nat_le.2 r.pos
      rw [Int.coe_nat_one] at this
      linarith
      
    · convert mem_ball_self _ using 2
      · push_cast
        norm_cast
        norm_num
        
      · refine' one_div_pos.2 (pow_pos (Int.cast_pos.2 _) _)
        exact mul_pos (Int.coe_nat_pos.2 r.pos) zero_lt_two
        
      
    

/-- The set of Liouville numbers in dense. -/
theorem dense_liouville : Dense { x | Liouville x } :=
  dense_of_mem_residual eventually_residual_liouville

