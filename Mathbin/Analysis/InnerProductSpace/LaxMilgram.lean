/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Analysis.InnerProductSpace.Dual
import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Topology.MetricSpace.Antilipschitz

/-!
# The Lax-Milgram Theorem

We consider an Hilbert space `V` over `ℝ`
equipped with a bounded bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.

Recall that a bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ` is *coercive*
iff `∃ C, (0 < C) ∧ ∀ u, C * ∥u∥ * ∥u∥ ≤ B u u`.
Under the hypothesis that `B` is coercive
we prove the Lax-Milgram theorem:
that is, the map `inner_product_space.continuous_linear_map_of_bilin` from
`analysis.inner_product_space.dual` can be upgraded to a continuous equivalence
`is_coercive.continuous_linear_equiv_of_bilin : V ≃L[ℝ] V`.

## References

* We follow the notes of Peter Howard's Spring 2020 *M612: Partial Differential Equations* lecture,
  see[howard]

## Tags

dual, Lax-Milgram
-/


noncomputable section

open IsROrC LinearMap ContinuousLinearMap InnerProductSpace

open RealInnerProductSpace Nnreal

universe u

namespace IsCoercive

variable {V : Type u} [InnerProductSpace ℝ V] [CompleteSpace V]

variable {B : V →L[ℝ] V →L[ℝ] ℝ}

-- mathport name: «expr ♯»
local postfix:1024 "♯" => @continuousLinearMapOfBilin ℝ V _ _ _

theorem bounded_below (coercive : IsCoercive B) : ∃ C, 0 < C ∧ ∀ v, C * ∥v∥ ≤ ∥B♯ v∥ := by
  rcases coercive with ⟨C, C_ge_0, coercivity⟩
  refine' ⟨C, C_ge_0, _⟩
  intro v
  by_cases' h : 0 < ∥v∥
  · refine' (mul_le_mul_right h).mp _
    calc C * ∥v∥ * ∥v∥ ≤ B v v := coercivity v _ = ⟪B♯ v, v⟫_ℝ :=
        (continuous_linear_map_of_bilin_apply ℝ B v v).symm _ ≤ ∥B♯ v∥ * ∥v∥ := real_inner_le_norm (B♯ v) v
    
  · have : v = 0 := by
      simpa using h
    simp [← this]
    

theorem antilipschitz (coercive : IsCoercive B) : ∃ C : ℝ≥0 , 0 < C ∧ AntilipschitzWith C B♯ := by
  rcases coercive.bounded_below with ⟨C, C_pos, below_bound⟩
  refine' ⟨C⁻¹.toNnreal, real.to_nnreal_pos.mpr (inv_pos.mpr C_pos), _⟩
  refine' ContinuousLinearMap.antilipschitz_of_bound B♯ _
  simp_rw [Real.coe_to_nnreal', max_eq_left_of_ltₓ (inv_pos.mpr C_pos), ← inv_mul_le_iff (inv_pos.mpr C_pos)]
  simpa using below_bound

theorem ker_eq_bot (coercive : IsCoercive B) : B♯.ker = ⊥ := by
  rw [← ker_coe, LinearMap.ker_eq_bot]
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  exact antilipschitz.injective

theorem closed_range (coercive : IsCoercive B) : IsClosed (B♯.range : Set V) := by
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  exact antilipschitz.is_closed_range B♯.UniformContinuous

theorem range_eq_top (coercive : IsCoercive B) : B♯.range = ⊤ := by
  have := coercive.closed_range.complete_space_coe
  rw [← B♯.range.orthogonal_orthogonal]
  rw [Submodule.eq_top_iff']
  intro v w mem_w_orthogonal
  rcases coercive with ⟨C, C_pos, coercivity⟩
  obtain rfl : w = 0 := by
    rw [← norm_eq_zero, ← mul_self_eq_zero, ← mul_right_inj' C_pos.ne', mul_zero, ← mul_assoc]
    apply le_antisymmₓ
    · calc C * ∥w∥ * ∥w∥ ≤ B w w := coercivity w _ = ⟪B♯ w, w⟫_ℝ :=
          (continuous_linear_map_of_bilin_apply ℝ B w w).symm _ = 0 := mem_w_orthogonal _ ⟨w, rfl⟩
      
    · exact mul_nonneg (mul_nonneg C_pos.le (norm_nonneg w)) (norm_nonneg w)
      
  exact inner_zero_left

/-- The Lax-Milgram equivalence of a coercive bounded bilinear operator:
for all `v : V`, `continuous_linear_equiv_of_bilin B v` is the unique element `V`
such that `⟪continuous_linear_equiv_of_bilin B v, w⟫ = B v w`.
The Lax-Milgram theorem states that this is a continuous equivalence.
-/
def continuousLinearEquivOfBilin (coercive : IsCoercive B) : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.ofBijective B♯ coercive.ker_eq_bot coercive.range_eq_top

@[simp]
theorem continuous_linear_equiv_of_bilin_apply (coercive : IsCoercive B) (v w : V) :
    ⟪coercive.continuousLinearEquivOfBilin v, w⟫_ℝ = B v w :=
  continuous_linear_map_of_bilin_apply ℝ B v w

theorem unique_continuous_linear_equiv_of_bilin (coercive : IsCoercive B) {v f : V}
    (is_lax_milgram : ∀ w, ⟪f, w⟫_ℝ = B v w) : f = coercive.continuousLinearEquivOfBilin v :=
  unique_continuous_linear_map_of_bilin ℝ B is_lax_milgram

end IsCoercive

