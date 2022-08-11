/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Topology.Instances.Real
import Mathbin.Order.Filter.Archimedean

/-!
# Convergence of subadditive sequences

A subadditive sequence `u : ℕ → ℝ` is a sequence satisfying `u (m + n) ≤ u m + u n` for all `m, n`.
We define this notion as `subadditive u`, and prove in `subadditive.tendsto_lim` that, if `u n / n`
is bounded below, then it converges to a limit (that we denote by `subadditive.lim` for
convenience). This result is known as Fekete's lemma in the literature.
-/


noncomputable section

open Set Filter

open TopologicalSpace

/-- A real-valued sequence is subadditive if it satisfies the inequality `u (m + n) ≤ u m + u n`
for all `m, n`. -/
def Subadditive (u : ℕ → ℝ) : Prop :=
  ∀ m n, u (m + n) ≤ u m + u n

namespace Subadditive

variable {u : ℕ → ℝ} (h : Subadditive u)

include h

/-- The limit of a bounded-below subadditive sequence. The fact that the sequence indeed tends to
this limit is given in `subadditive.tendsto_lim` -/
@[nolint unused_arguments]
protected irreducible_def lim :=
  inf ((fun n : ℕ => u n / n) '' Ici 1)

theorem lim_le_div (hbdd : BddBelow (Range fun n => u n / n)) {n : ℕ} (hn : n ≠ 0) : h.lim ≤ u n / n := by
  rw [Subadditive.lim]
  apply cInf_le _ _
  · rcases hbdd with ⟨c, hc⟩
    exact ⟨c, fun x hx => hc (image_subset_range _ _ hx)⟩
    
  · apply mem_image_of_mem
    exact zero_lt_iff.2 hn
    

theorem apply_mul_add_le (k n r) : u (k * n + r) ≤ k * u n + u r := by
  induction' k with k IH
  · simp only [← Nat.cast_zeroₓ, ← zero_mul, ← zero_addₓ]
    
  calc u ((k + 1) * n + r) = u (n + (k * n + r)) := by
      congr 1
      ring _ ≤ u n + u (k * n + r) := h _ _ _ ≤ u n + (k * u n + u r) :=
      add_le_add_left IH _ _ = (k + 1 : ℕ) * u n + u r := by
      simp <;> ring

theorem eventually_div_lt_of_div_lt {L : ℝ} {n : ℕ} (hn : n ≠ 0) (hL : u n / n < L) : ∀ᶠ p in at_top, u p / p < L := by
  have I : ∀ i : ℕ, 0 < i → (i : ℝ) ≠ 0 := by
    intro i hi
    simp only [← hi.ne', ← Ne.def, ← Nat.cast_eq_zero, ← not_false_iff]
  obtain ⟨w, nw, wL⟩ : ∃ w, u n / n < w ∧ w < L := exists_between hL
  obtain ⟨x, hx⟩ : ∃ x, ∀, ∀ i < n, ∀, u i - i * w ≤ x := by
    obtain ⟨x, hx⟩ : BddAbove ↑(Finset.image (fun i => u i - i * w) (Finset.range n)) := Finset.bdd_above _
    refine' ⟨x, fun i hi => _⟩
    simp only [← UpperBounds, ← mem_image, ← and_imp, ← forall_exists_index, ← mem_set_of_eq, ←
      forall_apply_eq_imp_iff₂, ← Finset.mem_range, ← Finset.mem_coe, ← Finset.coe_image] at hx
    exact hx _ hi
  have A : ∀ p : ℕ, u p ≤ p * w + x := by
    intro p
    let s := p / n
    let r := p % n
    have hp : p = s * n + r := by
      rw [mul_comm, Nat.div_add_modₓ]
    calc u p = u (s * n + r) := by
        rw [hp]_ ≤ s * u n + u r := h.apply_mul_add_le _ _ _ _ = s * n * (u n / n) + u r := by
        field_simp [← I _ hn.bot_lt]
        ring _ ≤ s * n * w + u r :=
        add_le_add_right (mul_le_mul_of_nonneg_left nw.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
          _ _ = (s * n + r) * w + (u r - r * w) :=
        by
        ring _ = p * w + (u r - r * w) := by
        rw [hp]
        simp only [← Nat.cast_addₓ, ← Nat.cast_mulₓ]_ ≤ p * w + x := add_le_add_left (hx _ (Nat.mod_ltₓ _ hn.bot_lt)) _
  have B : ∀ᶠ p in at_top, u p / p ≤ w + x / p := by
    refine' eventually_at_top.2 ⟨1, fun p hp => _⟩
    simp' only [← I p hp, ← Ne.def, ← not_false_iff] with field_simps
    refine' div_le_div_of_le_of_nonneg _ (Nat.cast_nonneg _)
    rw [mul_comm]
    exact A _
  have C : ∀ᶠ p : ℕ in at_top, w + x / p < L := by
    have : tendsto (fun p : ℕ => w + x / p) at_top (𝓝 (w + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_at_top tendsto_coe_nat_at_top_at_top)
    rw [add_zeroₓ] at this
    exact (tendsto_order.1 this).2 _ wL
  filter_upwards [B, C] with _ hp h'p using hp.trans_lt h'p

/-- Fekete's lemma: a subadditive sequence which is bounded below converges. -/
theorem tendsto_lim (hbdd : BddBelow (Range fun n => u n / n)) : Tendsto (fun n => u n / n) atTop (𝓝 h.lim) := by
  refine' tendsto_order.2 ⟨fun l hl => _, fun L hL => _⟩
  · refine' eventually_at_top.2 ⟨1, fun n hn => hl.trans_le (h.lim_le_div hbdd (zero_lt_one.trans_le hn).ne')⟩
    
  · obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ u n / n < L := by
      rw [Subadditive.lim] at hL
      rcases exists_lt_of_cInf_lt
          (by
            simp )
          hL with
        ⟨x, hx, xL⟩
      rcases(mem_image _ _ _).1 hx with ⟨n, hn, rfl⟩
      exact ⟨n, zero_lt_one.trans_le hn, xL⟩
    exact h.eventually_div_lt_of_div_lt npos.ne' hn
    

end Subadditive

