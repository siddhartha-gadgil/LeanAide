/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Analysis.NormedSpace.Ordered
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# A collection of specific asymptotic results

This file contains specific lemmas about asymptotics which don't have their place in the general
theory developped in `analysis.asymptotics.asymptotics`.
-/


open Filter Asymptotics

open TopologicalSpace

section NormedField

/-- If `f : 𝕜 → E` is bounded in a punctured neighborhood of `a`, then `f(x) = o((x - a)⁻¹)` as
`x → a`, `x ≠ a`. -/
theorem Filter.IsBoundedUnder.is_o_sub_self_inv {𝕜 E : Type _} [NormedField 𝕜] [HasNorm E] {a : 𝕜} {f : 𝕜 → E}
    (h : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) (norm ∘ f)) : f =o[𝓝[≠] a] fun x => (x - a)⁻¹ := by
  refine' (h.is_O_const (@one_ne_zero ℝ _ _)).trans_is_o (is_o_const_left.2 <| Or.inr _)
  simp only [← (· ∘ ·), ← norm_inv]
  exact (tendsto_norm_sub_self_punctured_nhds a).inv_tendsto_zero

end NormedField

section LinearOrderedField

variable {𝕜 : Type _} [LinearOrderedField 𝕜]

theorem pow_div_pow_eventually_eq_at_top {p q : ℕ} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[at_top] fun x => x ^ ((p : ℤ) - q) := by
  apply (eventually_gt_at_top (0 : 𝕜)).mono fun x hx => _
  simp [← zpow_sub₀ hx.ne']

theorem pow_div_pow_eventually_eq_at_bot {p q : ℕ} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[at_bot] fun x => x ^ ((p : ℤ) - q) := by
  apply (eventually_lt_at_bot (0 : 𝕜)).mono fun x hx => _
  simp [← zpow_sub₀ hx.ne]

theorem tendsto_zpow_at_top_at_top {n : ℤ} (hn : 0 < n) : Tendsto (fun x : 𝕜 => x ^ n) atTop atTop := by
  lift n to ℕ using hn.le
  simp only [← zpow_coe_nat]
  exact tendsto_pow_at_top (nat.cast_pos.mp hn).ne'

theorem tendsto_pow_div_pow_at_top_at_top {p q : ℕ} (hpq : q < p) : Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop atTop :=
  by
  rw [tendsto_congr' pow_div_pow_eventually_eq_at_top]
  apply tendsto_zpow_at_top_at_top
  linarith

theorem tendsto_pow_div_pow_at_top_zero [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q : ℕ} (hpq : p < q) :
    Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop (𝓝 0) := by
  rw [tendsto_congr' pow_div_pow_eventually_eq_at_top]
  apply tendsto_zpow_at_top_zero
  linarith

end LinearOrderedField

section NormedLinearOrderedField

variable {𝕜 : Type _} [NormedLinearOrderedField 𝕜]

theorem Asymptotics.is_o_pow_pow_at_top_of_lt [OrderTopology 𝕜] {p q : ℕ} (hpq : p < q) :
    (fun x : 𝕜 => x ^ p) =o[at_top] fun x => x ^ q := by
  refine' (is_o_iff_tendsto' _).mpr (tendsto_pow_div_pow_at_top_zero hpq)
  exact (eventually_gt_at_top 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim

theorem Asymptotics.IsO.trans_tendsto_norm_at_top {α : Type _} {u v : α → 𝕜} {l : Filter α} (huv : u =O[l] v)
    (hu : Tendsto (fun x => ∥u x∥) l atTop) : Tendsto (fun x => ∥v x∥) l atTop := by
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩
  rw [is_O_with] at hcuv
  convert tendsto.at_top_div_const hc (tendsto_at_top_mono' l hcuv hu)
  ext x
  rw [mul_div_cancel_left _ hc.ne.symm]

end NormedLinearOrderedField

section Real

open BigOperators

open Finset

theorem Asymptotics.IsOₓ.sum_range {α : Type _} [NormedGroup α] {f : ℕ → α} {g : ℕ → ℝ} (h : f =o[at_top] g)
    (hg : 0 ≤ g) (h'g : Tendsto (fun n => ∑ i in range n, g i) atTop atTop) :
    (fun n => ∑ i in range n, f i) =o[at_top] fun n => ∑ i in range n, g i := by
  have A : ∀ i, ∥g i∥ = g i := fun i => Real.norm_of_nonneg (hg i)
  have B : ∀ n, ∥∑ i in range n, g i∥ = ∑ i in range n, g i := fun n => by
    rwa [Real.norm_eq_abs, abs_sum_of_nonneg']
  apply is_o_iff.2 fun ε εpos => _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ b : ℕ, N ≤ b → ∥f b∥ ≤ ε / 2 * g b := by
    simpa only [← A, ← eventually_at_top] using is_o_iff.mp h (half_pos εpos)
  have : (fun n : ℕ => ∑ i in range N, f i) =o[at_top] fun n : ℕ => ∑ i in range n, g i := by
    apply is_o_const_left.2
    exact Or.inr (h'g.congr fun n => (B n).symm)
  filter_upwards [is_o_iff.1 this (half_pos εpos), Ici_mem_at_top N] with n hn Nn
  calc ∥∑ i in range n, f i∥ = ∥(∑ i in range N, f i) + ∑ i in Ico N n, f i∥ := by
      rw [sum_range_add_sum_Ico _ Nn]_ ≤ ∥∑ i in range N, f i∥ + ∥∑ i in Ico N n, f i∥ :=
      norm_add_le _ _ _ ≤ ∥∑ i in range N, f i∥ + ∑ i in Ico N n, ε / 2 * g i :=
      add_le_add le_rfl
        (norm_sum_le_of_le _ fun i hi =>
          hN _ (mem_Ico.1 hi).1)_ ≤ ∥∑ i in range N, f i∥ + ∑ i in range n, ε / 2 * g i :=
      by
      refine' add_le_add le_rfl _
      apply sum_le_sum_of_subset_of_nonneg
      · rw [range_eq_Ico]
        exact Ico_subset_Ico (zero_le _) le_rfl
        
      · intro i hi hident
        exact mul_nonneg (half_pos εpos).le (hg i)
        _ ≤ ε / 2 * ∥∑ i in range n, g i∥ + ε / 2 * ∑ i in range n, g i :=
      by
      rw [← mul_sum]
      exact add_le_add hn (mul_le_mul_of_nonneg_left le_rfl (half_pos εpos).le)_ = ε * ∥∑ i in range n, g i∥ := by
      simp [← B]
      ring

theorem Asymptotics.is_o_sum_range_of_tendsto_zero {α : Type _} [NormedGroup α] {f : ℕ → α}
    (h : Tendsto f atTop (𝓝 0)) : (fun n => ∑ i in range n, f i) =o[at_top] fun n => (n : ℝ) := by
  have := ((is_o_one_iff ℝ).2 h).sum_range fun i => zero_le_one
  simp only [← sum_const, ← card_range, ← Nat.smul_one_eq_coe] at this
  exact this tendsto_coe_nat_at_top_at_top

/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro_smul {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {u : ℕ → E} {l : E}
    (h : Tendsto u atTop (𝓝 l)) : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ i in range n, u i) atTop (𝓝 l) := by
  rw [← tendsto_sub_nhds_zero_iff, ← is_o_one_iff ℝ]
  have := Asymptotics.is_o_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 h)
  apply ((is_O_refl (fun n : ℕ => (n : ℝ)⁻¹) at_top).smul_is_o this).congr' _ _
  · filter_upwards [Ici_mem_at_top 1] with n npos
    have nposℝ : (0 : ℝ) < n := Nat.cast_pos.2 npos
    simp only [← smul_sub, ← sum_sub_distrib, ← sum_const, ← card_range, ← sub_right_inj]
    rw [nsmul_eq_smul_cast ℝ, smul_smul, inv_mul_cancel nposℝ.ne', one_smul]
    
  · filter_upwards [Ici_mem_at_top 1] with n npos
    have nposℝ : (0 : ℝ) < n := Nat.cast_pos.2 npos
    rw [Algebra.id.smul_eq_mul, inv_mul_cancel nposℝ.ne']
    

/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i in range n, u i) atTop (𝓝 l) :=
  h.cesaro_smul

end Real

