/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.Normed.Group.AddTorsor
import Mathbin.LinearAlgebra.AffineSpace.Midpoint
import Mathbin.LinearAlgebra.AffineSpace.AffineSubspace
import Mathbin.Topology.Instances.RealVectorSpace

/-!
# Torsors of normed space actions.

This file contains lemmas about normed additive torsors over normed spaces.
-/


noncomputable section

open Nnreal TopologicalSpace

open Filter

variable {α V P : Type _} [SemiNormedGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]

variable {W Q : Type _} [NormedGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

section NormedSpace

variable {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]

open AffineMap

theorem AffineSubspace.is_closed_direction_iff (s : AffineSubspace 𝕜 Q) :
    IsClosed (s.direction : Set W) ↔ IsClosed (s : Set Q) := by
  rcases s.eq_bot_or_nonempty with (rfl | ⟨x, hx⟩)
  · simp [← is_closed_singleton]
    
  rw [← (Isometric.vaddConst x).toHomeomorph.symm.is_closed_image, AffineSubspace.coe_direction_eq_vsub_set_right hx]
  rfl

include V

@[simp]
theorem dist_center_homothety (p₁ p₂ : P) (c : 𝕜) : dist p₁ (homothety p₁ c p₂) = ∥c∥ * dist p₁ p₂ := by
  simp [← homothety_def, ← norm_smul, dist_eq_norm_vsub, ← dist_comm]

@[simp]
theorem dist_homothety_center (p₁ p₂ : P) (c : 𝕜) : dist (homothety p₁ c p₂) p₁ = ∥c∥ * dist p₁ p₂ := by
  rw [dist_comm, dist_center_homothety]

@[simp]
theorem dist_line_map_line_map (p₁ p₂ : P) (c₁ c₂ : 𝕜) :
    dist (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂ := by
  rw [dist_comm p₁ p₂]
  simp only [← line_map_apply, ← dist_eq_norm_vsub, ← vadd_vsub_vadd_cancel_right, sub_smul, ← norm_smul, ← vsub_eq_sub]

theorem lipschitz_with_line_map (p₁ p₂ : P) : LipschitzWith (nndist p₁ p₂) (lineMap p₁ p₂ : 𝕜 → P) :=
  LipschitzWith.of_dist_le_mul fun c₁ c₂ => ((dist_line_map_line_map p₁ p₂ c₁ c₂).trans (mul_comm _ _)).le

@[simp]
theorem dist_line_map_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap p₁ p₂ c) p₁ = ∥c∥ * dist p₁ p₂ := by
  simpa only [← line_map_apply_zero, ← dist_zero_right] using dist_line_map_line_map p₁ p₂ c 0

@[simp]
theorem dist_left_line_map (p₁ p₂ : P) (c : 𝕜) : dist p₁ (lineMap p₁ p₂ c) = ∥c∥ * dist p₁ p₂ :=
  (dist_comm _ _).trans (dist_line_map_left _ _ _)

@[simp]
theorem dist_line_map_right (p₁ p₂ : P) (c : 𝕜) : dist (lineMap p₁ p₂ c) p₂ = ∥1 - c∥ * dist p₁ p₂ := by
  simpa only [← line_map_apply_one, ← dist_eq_norm'] using dist_line_map_line_map p₁ p₂ c 1

@[simp]
theorem dist_right_line_map (p₁ p₂ : P) (c : 𝕜) : dist p₂ (lineMap p₁ p₂ c) = ∥1 - c∥ * dist p₁ p₂ :=
  (dist_comm _ _).trans (dist_line_map_right _ _ _)

@[simp]
theorem dist_homothety_self (p₁ p₂ : P) (c : 𝕜) : dist (homothety p₁ c p₂) p₂ = ∥1 - c∥ * dist p₁ p₂ := by
  rw [homothety_eq_line_map, dist_line_map_right]

@[simp]
theorem dist_self_homothety (p₁ p₂ : P) (c : 𝕜) : dist p₂ (homothety p₁ c p₂) = ∥1 - c∥ * dist p₁ p₂ := by
  rw [dist_comm, dist_homothety_self]

section invertibleTwo

variable [Invertible (2 : 𝕜)]

@[simp]
theorem dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜 p₁ p₂) = ∥(2 : 𝕜)∥⁻¹ * dist p₁ p₂ := by
  rw [midpoint, dist_comm, dist_line_map_left, inv_of_eq_inv, ← norm_inv]

@[simp]
theorem dist_midpoint_left (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₁ = ∥(2 : 𝕜)∥⁻¹ * dist p₁ p₂ := by
  rw [dist_comm, dist_left_midpoint]

@[simp]
theorem dist_midpoint_right (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₂ = ∥(2 : 𝕜)∥⁻¹ * dist p₁ p₂ := by
  rw [midpoint_comm, dist_midpoint_left, dist_comm]

@[simp]
theorem dist_right_midpoint (p₁ p₂ : P) : dist p₂ (midpoint 𝕜 p₁ p₂) = ∥(2 : 𝕜)∥⁻¹ * dist p₁ p₂ := by
  rw [dist_comm, dist_midpoint_right]

theorem dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
    dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / ∥(2 : 𝕜)∥ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint] <;>
    try
      infer_instance
  rw [midpoint_eq_smul_add, norm_smul, inv_of_eq_inv, norm_inv, ← div_eq_inv_mul]
  exact div_le_div_of_le_of_nonneg (norm_add_le _ _) (norm_nonneg _)

end invertibleTwo

omit V

include W

theorem antilipschitz_with_line_map {p₁ p₂ : Q} (h : p₁ ≠ p₂) :
    AntilipschitzWith (nndist p₁ p₂)⁻¹ (lineMap p₁ p₂ : 𝕜 → Q) :=
  AntilipschitzWith.of_le_mul_dist fun c₁ c₂ => by
    rw [dist_line_map_line_map, Nnreal.coe_inv, ← dist_nndist, mul_left_commₓ, inv_mul_cancel (dist_ne_zero.2 h),
      mul_oneₓ]

variable (𝕜)

theorem eventually_homothety_mem_of_mem_interior (x : Q) {s : Set Q} {y : Q} (hy : y ∈ Interior s) :
    ∀ᶠ δ in 𝓝 (1 : 𝕜), homothety x δ y ∈ s := by
  rw [(NormedGroup.nhds_basis_norm_lt (1 : 𝕜)).eventually_iff]
  cases' eq_or_ne y x with h h
  · use 1
    simp [← h.symm, ← interior_subset hy]
    
  have hxy : 0 < ∥y -ᵥ x∥ := by
    rwa [norm_pos_iff, vsub_ne_zero]
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := mem_interior.mp hy
  obtain ⟨ε, hε, hyε⟩ := metric.is_open_iff.mp hu₂ y hu₃
  refine' ⟨ε / ∥y -ᵥ x∥, div_pos hε hxy, fun δ (hδ : ∥δ - 1∥ < ε / ∥y -ᵥ x∥) => hu₁ (hyε _)⟩
  rw [lt_div_iff hxy, ← norm_smul, sub_smul, one_smul] at hδ
  rwa [homothety_apply, Metric.mem_ball, dist_eq_norm_vsub W, vadd_vsub_eq_sub_vsub]

theorem eventually_homothety_image_subset_of_finite_subset_interior (x : Q) {s : Set Q} {t : Set Q} (ht : t.Finite)
    (h : t ⊆ Interior s) : ∀ᶠ δ in 𝓝 (1 : 𝕜), homothety x δ '' t ⊆ s := by
  suffices ∀, ∀ y ∈ t, ∀, ∀ᶠ δ in 𝓝 (1 : 𝕜), homothety x δ y ∈ s by
    simp_rw [Set.image_subset_iff]
    exact (Filter.eventually_all_finite ht).mpr this
  intro y hy
  exact eventually_homothety_mem_of_mem_interior 𝕜 x (h hy)

end NormedSpace

variable [NormedSpace ℝ V] [NormedSpace ℝ W]

theorem dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
    dist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / 2 := by
  simpa using dist_midpoint_midpoint_le' p₁ p₂ p₃ p₄

include V W

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- A continuous map between two normed affine spaces is an affine map provided that
it sends midpoints to midpoints. -/
def AffineMap.ofMapMidpoint (f : P → Q) (h : ∀ x y, f (midpoint ℝ x y) = midpoint ℝ (f x) (f y)) (hfc : Continuous f) :
    P →ᵃ[ℝ] Q :=
  AffineMap.mk' f
    (↑((AddMonoidHom.ofMapMidpoint ℝ ℝ
            ((AffineEquiv.vaddConst ℝ (f <| Classical.arbitrary P)).symm ∘
              f ∘ AffineEquiv.vaddConst ℝ (Classical.arbitrary P))
            (by
              simp )
            fun x y => by
            simp [← h]).toRealLinearMap <|
        by
        apply_rules [Continuous.vadd, Continuous.vsub, continuous_const, hfc.comp, continuous_id]))
    (Classical.arbitrary P) fun p => by
    simp

