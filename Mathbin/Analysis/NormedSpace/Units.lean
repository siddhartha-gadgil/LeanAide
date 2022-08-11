/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.Analysis.SpecificLimits.Normed

/-!
# The group of units of a complete normed ring

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `one_sub`, `add` and `unit_of_nearby` state, in varying forms, that perturbations
of a unit are units.  The latter two are not stated in their optimal form; more precise versions
would use the spectral radius.

The first main result is `is_open`:  the group of units of a complete normed ring is an open subset
of the ring.

The function `inverse` (defined in `algebra.ring`), for a ring `R`, sends `a : R` to `a⁻¹` if `a` is
a unit and 0 if not.  The other major results of this file (notably `inverse_add`,
`inverse_add_norm` and `inverse_add_norm_diff_nth_order`) cover the asymptotic properties of
`inverse (x + t)` as `t → 0`.

-/


noncomputable section

open TopologicalSpace

variable {R : Type _} [NormedRing R] [CompleteSpace R]

namespace Units

/-- In a complete normed ring, a perturbation of `1` by an element `t` of distance less than `1`
from `1` is a unit.  Here we construct its `units` structure.  -/
@[simps coe]
def oneSub (t : R) (h : ∥t∥ < 1) : Rˣ where
  val := 1 - t
  inv := ∑' n : ℕ, t ^ n
  val_inv := mul_neg_geom_series t h
  inv_val := geom_series_mul_neg t h

/-- In a complete normed ring, a perturbation of a unit `x` by an element `t` of distance less than
`∥x⁻¹∥⁻¹` from `x` is a unit.  Here we construct its `units` structure. -/
@[simps coe]
def add (x : Rˣ) (t : R) (h : ∥t∥ < ∥(↑x⁻¹ : R)∥⁻¹) : Rˣ :=
  Units.copy
    (-- to make `coe_add` true definitionally, for convenience
      x *
      Units.oneSub (-(↑x⁻¹ * t))
        (by
          nontriviality R using ← zero_lt_one
          have hpos : 0 < ∥(↑x⁻¹ : R)∥ := Units.norm_pos x⁻¹
          calc ∥-(↑x⁻¹ * t)∥ = ∥↑x⁻¹ * t∥ := by
              rw [norm_neg]_ ≤ ∥(↑x⁻¹ : R)∥ * ∥t∥ := norm_mul_le ↑x⁻¹ _ _ < ∥(↑x⁻¹ : R)∥ * ∥(↑x⁻¹ : R)∥⁻¹ := by
              nlinarith only [h, hpos]_ = 1 := mul_inv_cancel (ne_of_gtₓ hpos)))
    (x + t)
    (by
      simp [← mul_addₓ])
    _ rfl

/-- In a complete normed ring, an element `y` of distance less than `∥x⁻¹∥⁻¹` from `x` is a unit.
Here we construct its `units` structure. -/
@[simps coe]
def unitOfNearby (x : Rˣ) (y : R) (h : ∥y - x∥ < ∥(↑x⁻¹ : R)∥⁻¹) : Rˣ :=
  Units.copy (x.add (y - x : R) h) y
    (by
      simp )
    _ rfl

/-- The group of units of a complete normed ring is an open subset of the ring. -/
protected theorem is_open : IsOpen { x : R | IsUnit x } := by
  nontriviality R
  apply metric.is_open_iff.mpr
  rintro x' ⟨x, rfl⟩
  refine' ⟨∥(↑x⁻¹ : R)∥⁻¹, _root_.inv_pos.mpr (Units.norm_pos x⁻¹), _⟩
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact (x.unit_of_nearby y hy).IsUnit

protected theorem nhds (x : Rˣ) : { x : R | IsUnit x } ∈ 𝓝 (x : R) :=
  IsOpen.mem_nhds Units.is_open x.IsUnit

end Units

namespace NormedRing

open Classical BigOperators

open Asymptotics Filter Metric Finset Ringₓ

theorem inverse_one_sub (t : R) (h : ∥t∥ < 1) : inverse (1 - t) = ↑(Units.oneSub t h)⁻¹ := by
  rw [← inverse_unit (Units.oneSub t h), Units.coe_one_sub]

/-- The formula `inverse (x + t) = inverse (1 + x⁻¹ * t) * x⁻¹` holds for `t` sufficiently small. -/
theorem inverse_add (x : Rˣ) : ∀ᶠ t in 𝓝 0, inverse ((x : R) + t) = inverse (1 + ↑x⁻¹ * t) * ↑x⁻¹ := by
  nontriviality R
  rw [eventually_iff, Metric.mem_nhds_iff]
  have hinv : 0 < ∥(↑x⁻¹ : R)∥⁻¹ := by
    cancel_denoms
  use ∥(↑x⁻¹ : R)∥⁻¹, hinv
  intro t ht
  simp only [← mem_ball, ← dist_zero_right] at ht
  have ht' : ∥-↑x⁻¹ * t∥ < 1 := by
    refine' lt_of_le_of_ltₓ (norm_mul_le _ _) _
    rw [norm_neg]
    refine' lt_of_lt_of_leₓ (mul_lt_mul_of_pos_left ht x⁻¹.norm_pos) _
    cancel_denoms
  have hright := inverse_one_sub (-↑x⁻¹ * t) ht'
  have hleft := inverse_unit (x.add t ht)
  simp only [← neg_mul, ← sub_neg_eq_add] at hright
  simp only [← Units.coe_add] at hleft
  simp [← hleft, ← hright, ← Units.add]

theorem inverse_one_sub_nth_order (n : ℕ) :
    ∀ᶠ t in 𝓝 0, inverse ((1 : R) - t) = (∑ i in range n, t ^ i) + t ^ n * inverse (1 - t) := by
  simp only [← eventually_iff, ← Metric.mem_nhds_iff]
  use 1, by
    norm_num
  intro t ht
  simp only [← mem_ball, ← dist_zero_right] at ht
  simp only [← inverse_one_sub t ht, ← Set.mem_set_of_eq]
  have h : 1 = ((range n).Sum fun i => t ^ i) * Units.oneSub t ht + t ^ n := by
    simp only [← Units.coe_one_sub]
    rw [geom_sum_mul_neg]
    simp
  rw [← one_mulₓ ↑(Units.oneSub t ht)⁻¹, h, add_mulₓ]
  congr
  · rw [mul_assoc, (Units.oneSub t ht).mul_inv]
    simp
    
  · simp only [← Units.coe_one_sub]
    rw [← add_mulₓ, geom_sum_mul_neg]
    simp
    

/-- The formula
`inverse (x + t) = (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹ + (- x⁻¹ * t) ^ n * inverse (x + t)`
holds for `t` sufficiently small. -/
theorem inverse_add_nth_order (x : Rˣ) (n : ℕ) :
    ∀ᶠ t in 𝓝 0, inverse ((x : R) + t) = (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹ + (-↑x⁻¹ * t) ^ n * inverse (x + t) :=
  by
  refine' (inverse_add x).mp _
  have hzero : tendsto (fun t : R => -↑x⁻¹ * t) (𝓝 0) (𝓝 0) := by
    convert ((mul_left_continuous (-(↑x⁻¹ : R))).Tendsto 0).comp tendsto_id
    simp
  refine' (hzero.eventually (inverse_one_sub_nth_order n)).mp (eventually_of_forall _)
  simp only [← neg_mul, ← sub_neg_eq_add]
  intro t h1 h2
  have h := congr_arg (fun a : R => a * ↑x⁻¹) h1
  dsimp'  at h
  convert h
  rw [add_mulₓ, mul_assoc]
  simp [← h2.symm]

theorem inverse_one_sub_norm : (fun t : R => inverse (1 - t)) =O[𝓝 0] (fun t => 1 : R → ℝ) := by
  simp only [← is_O, ← is_O_with, ← eventually_iff, ← Metric.mem_nhds_iff]
  refine'
    ⟨∥(1 : R)∥ + 1, (2 : ℝ)⁻¹, by
      norm_num, _⟩
  intro t ht
  simp only [← ball, ← dist_zero_right, ← Set.mem_set_of_eq] at ht
  have ht' : ∥t∥ < 1 := by
    have : (2 : ℝ)⁻¹ < 1 := by
      cancel_denoms
    linarith
  simp only [← inverse_one_sub t ht', ← norm_one, ← mul_oneₓ, ← Set.mem_set_of_eq]
  change ∥∑' n : ℕ, t ^ n∥ ≤ _
  have := NormedRing.tsum_geometric_of_norm_lt_1 t ht'
  have : (1 - ∥t∥)⁻¹ ≤ 2 := by
    rw [← inv_invₓ (2 : ℝ)]
    refine'
      inv_le_inv_of_le
        (by
          norm_num)
        _
    have : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by
      ring
    linarith
  linarith

/-- The function `λ t, inverse (x + t)` is O(1) as `t → 0`. -/
theorem inverse_add_norm (x : Rˣ) : (fun t : R => inverse (↑x + t)) =O[𝓝 0] fun t => (1 : ℝ) := by
  simp only [← is_O_iff, ← norm_one, ← mul_oneₓ]
  cases' is_O_iff.mp (@inverse_one_sub_norm R _ _) with C hC
  use C * ∥((x⁻¹ : Rˣ) : R)∥
  have hzero : tendsto (fun t => -(↑x⁻¹ : R) * t) (𝓝 0) (𝓝 0) := by
    convert ((mul_left_continuous (-↑x⁻¹ : R)).Tendsto 0).comp tendsto_id
    simp
  refine' (inverse_add x).mp ((hzero.eventually hC).mp (eventually_of_forall _))
  intro t bound iden
  rw [iden]
  simp at bound
  have hmul := norm_mul_le (inverse (1 + ↑x⁻¹ * t)) ↑x⁻¹
  nlinarith [norm_nonneg (↑x⁻¹ : R)]

/-- The function
`λ t, inverse (x + t) - (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹`
is `O(t ^ n)` as `t → 0`. -/
theorem inverse_add_norm_diff_nth_order (x : Rˣ) (n : ℕ) :
    (fun t : R => inverse (↑x + t) - (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹) =O[𝓝 (0 : R)] fun t => ∥t∥ ^ n := by
  by_cases' h : n = 0
  · simpa [← h] using inverse_add_norm x
    
  have hn : 0 < n := Nat.pos_of_ne_zeroₓ h
  simp [← is_O_iff]
  cases' is_O_iff.mp (inverse_add_norm x) with C hC
  use C * ∥(1 : ℝ)∥ * ∥(↑x⁻¹ : R)∥ ^ n
  have h :
    eventually_eq (𝓝 (0 : R)) (fun t => inverse (↑x + t) - (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹) fun t =>
      (-↑x⁻¹ * t) ^ n * inverse (x + t) :=
    by
    refine' (inverse_add_nth_order x n).mp (eventually_of_forall _)
    intro t ht
    convert congr_arg (fun a => a - (range n).Sum (pow (-↑x⁻¹ * t)) * ↑x⁻¹) ht
    simp
  refine' h.mp (hC.mp (eventually_of_forall _))
  intro t _ hLHS
  simp only [← neg_mul] at hLHS
  rw [hLHS]
  refine' le_transₓ (norm_mul_le _ _) _
  have h' : ∥-(↑x⁻¹ * t) ^ n∥ ≤ ∥(↑x⁻¹ : R)∥ ^ n * ∥t∥ ^ n := by
    calc ∥-(↑x⁻¹ * t) ^ n∥ ≤ ∥-(↑x⁻¹ * t)∥ ^ n := norm_pow_le' _ hn _ = ∥↑x⁻¹ * t∥ ^ n := by
        rw [norm_neg]_ ≤ (∥(↑x⁻¹ : R)∥ * ∥t∥) ^ n := _ _ = ∥(↑x⁻¹ : R)∥ ^ n * ∥t∥ ^ n := mul_powₓ _ _ n
    exact pow_le_pow_of_le_left (norm_nonneg _) (norm_mul_le (↑x⁻¹) t) n
  have h'' : 0 ≤ ∥(↑x⁻¹ : R)∥ ^ n * ∥t∥ ^ n := by
    refine' mul_nonneg _ _ <;> exact pow_nonneg (norm_nonneg _) n
  nlinarith [norm_nonneg (inverse (↑x + t))]

/-- The function `λ t, inverse (x + t) - x⁻¹` is `O(t)` as `t → 0`. -/
theorem inverse_add_norm_diff_first_order (x : Rˣ) : (fun t : R => inverse (↑x + t) - ↑x⁻¹) =O[𝓝 0] fun t => ∥t∥ := by
  simpa using inverse_add_norm_diff_nth_order x 1

/-- The function
`λ t, inverse (x + t) - x⁻¹ + x⁻¹ * t * x⁻¹`
is `O(t ^ 2)` as `t → 0`. -/
theorem inverse_add_norm_diff_second_order (x : Rˣ) :
    (fun t : R => inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =O[𝓝 0] fun t => ∥t∥ ^ 2 := by
  convert inverse_add_norm_diff_nth_order x 2
  ext t
  simp only [← range_succ, ← range_one, ← sum_insert, ← mem_singleton, ← sum_singleton, ← not_false_iff, ← one_ne_zero,
    ← pow_zeroₓ, ← add_mulₓ, ← pow_oneₓ, ← one_mulₓ, ← neg_mul, ← sub_add_eq_sub_sub_swap, ← sub_neg_eq_add]

/-- The function `inverse` is continuous at each unit of `R`. -/
theorem inverse_continuous_at (x : Rˣ) : ContinuousAt inverse (x : R) := by
  have h_is_o : (fun t : R => inverse (↑x + t) - ↑x⁻¹) =o[𝓝 0] (fun _ => 1 : R → ℝ) :=
    (inverse_add_norm_diff_first_order x).trans_is_o (is_o.norm_left <| is_o_id_const one_ne_zero)
  have h_lim : tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) := by
    refine' tendsto_zero_iff_norm_tendsto_zero.mpr _
    exact tendsto_iff_norm_tendsto_zero.mp tendsto_id
  rw [ContinuousAt, tendsto_iff_norm_tendsto_zero, inverse_unit]
  simpa [← (· ∘ ·)] using h_is_o.norm_left.tendsto_div_nhds_zero.comp h_lim

end NormedRing

namespace Units

open MulOpposite Filter NormedRing

/-- In a normed ring, the coercion from `Rˣ` (equipped with the induced topology from the
embedding in `R × R`) to `R` is an open map. -/
theorem is_open_map_coe : IsOpenMap (coe : Rˣ → R) := by
  rw [is_open_map_iff_nhds_le]
  intro x s
  rw [mem_map, mem_nhds_induced]
  rintro ⟨t, ht, hts⟩
  obtain ⟨u, hu, v, hv, huvt⟩ : ∃ u : Set R, u ∈ 𝓝 ↑x ∧ ∃ v : Set Rᵐᵒᵖ, v ∈ 𝓝 (op ↑x⁻¹) ∧ u ×ˢ v ⊆ t := by
    simpa [← embed_product, ← mem_nhds_prod_iff] using ht
  have : u ∩ op ∘ Ring.inverse ⁻¹' v ∩ Set.Range (coe : Rˣ → R) ∈ 𝓝 ↑x := by
    refine' inter_mem (inter_mem hu _) (Units.nhds x)
    refine' (continuous_op.continuous_at.comp (inverse_continuous_at x)).preimage_mem_nhds _
    simpa using hv
  refine' mem_of_superset this _
  rintro _ ⟨⟨huy, hvy⟩, ⟨y, rfl⟩⟩
  have : embed_product R y ∈ u ×ˢ v :=
    ⟨huy, by
      simpa using hvy⟩
  simpa using hts (huvt this)

/-- In a normed ring, the coercion from `Rˣ` (equipped with the induced topology from the
embedding in `R × R`) to `R` is an open embedding. -/
theorem open_embedding_coe : OpenEmbedding (coe : Rˣ → R) :=
  open_embedding_of_continuous_injective_open continuous_coe ext is_open_map_coe

end Units

