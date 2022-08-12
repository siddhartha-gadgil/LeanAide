/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathbin.Data.Real.Ennreal
import Mathbin.Topology.ContinuousFunction.Bounded

/-!
# Thickened indicators

This file is about thickened indicators of sets in (pseudo e)metric spaces. For a decreasing
sequence of thickening radii tending to 0, the thickened indicators of a closed set form a
decreasing pointwise converging approximation of the indicator function of the set, where the
members of the approximating sequence are nonnegative bounded continuous functions.

## Main definitions

 * `thickened_indicator_aux δ E`: The `δ`-thickened indicator of a set `E` as an
   unbundled `ℝ≥0∞`-valued function.
 * `thickened_indicator δ E`: The `δ`-thickened indicator of a set `E` as a bundled
   bounded continuous `ℝ≥0`-valued function.

## Main results

 * For a sequence of thickening radii tending to 0, the `δ`-thickened indicators of a set `E` tend
   pointwise to the indicator of `closure E`.
   - `thickened_indicator_aux_tendsto_indicator_closure`: The version is for the
     unbundled `ℝ≥0∞`-valued functions.
   - `thickened_indicator_tendsto_indicator_closure`: The version is for the bundled `ℝ≥0`-valued
     bounded continuous functions.

-/


noncomputable section

open Classical Nnreal Ennreal TopologicalSpace BoundedContinuousFunction

open Nnreal Ennreal Set Metric Emetric Filter

section thickenedIndicator

variable {α : Type _} [PseudoEmetricSpace α]

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `inf_edist _ E`.

`thickened_indicator_aux` is the unbundled `ℝ≥0∞`-valued function. See `thickened_indicator`
for the (bundled) bounded continuous function with `ℝ≥0`-values. -/
def thickenedIndicatorAux (δ : ℝ) (E : Set α) : α → ℝ≥0∞ := fun x : α => (1 : ℝ≥0∞) - infEdist x E / Ennreal.ofReal δ

theorem continuous_thickened_indicator_aux {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    Continuous (thickenedIndicatorAux δ E) := by
  unfold thickenedIndicatorAux
  let f := fun x : α => (⟨1, inf_edist x E / Ennreal.ofReal δ⟩ : ℝ≥0 × ℝ≥0∞)
  let sub := fun p : ℝ≥0 × ℝ≥0∞ => (p.1 : ℝ≥0∞) - p.2
  rw
    [show (fun x : α => (1 : ℝ≥0∞) - inf_edist x E / Ennreal.ofReal δ) = sub ∘ f by
      rfl]
  apply (@Ennreal.continuous_nnreal_sub 1).comp
  apply (Ennreal.continuous_div_const (Ennreal.ofReal δ) _).comp continuous_inf_edist
  norm_num [← δ_pos]

theorem thickened_indicator_aux_le_one (δ : ℝ) (E : Set α) (x : α) : thickenedIndicatorAux δ E x ≤ 1 := by
  apply @tsub_le_self _ _ _ _ (1 : ℝ≥0∞)

theorem thickened_indicator_aux_lt_top {δ : ℝ} {E : Set α} {x : α} : thickenedIndicatorAux δ E x < ∞ :=
  lt_of_le_of_ltₓ (thickened_indicator_aux_le_one _ _ _) one_lt_top

theorem thickened_indicator_aux_closure_eq (δ : ℝ) (E : Set α) :
    thickenedIndicatorAux δ (Closure E) = thickenedIndicatorAux δ E := by
  simp_rw [thickenedIndicatorAux, inf_edist_closure]

theorem thickened_indicator_aux_one (δ : ℝ) (E : Set α) {x : α} (x_in_E : x ∈ E) : thickenedIndicatorAux δ E x = 1 := by
  simp [← thickenedIndicatorAux, ← inf_edist_zero_of_mem x_in_E, ← tsub_zero]

theorem thickened_indicator_aux_one_of_mem_closure (δ : ℝ) (E : Set α) {x : α} (x_mem : x ∈ Closure E) :
    thickenedIndicatorAux δ E x = 1 := by
  rw [← thickened_indicator_aux_closure_eq, thickened_indicator_aux_one δ (Closure E) x_mem]

theorem thickened_indicator_aux_zero {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_out : x ∉ Thickening δ E) :
    thickenedIndicatorAux δ E x = 0 := by
  rw [thickening, mem_set_of_eq, not_ltₓ] at x_out
  unfold thickenedIndicatorAux
  apply le_antisymmₓ _ bot_le
  have key := tsub_le_tsub (@rfl _ (1 : ℝ≥0∞)).le (Ennreal.div_le_div x_out rfl.le)
  rw [Ennreal.div_self (ne_of_gtₓ (ennreal.of_real_pos.mpr δ_pos)) of_real_ne_top] at key
  simpa using key

theorem thickened_indicator_aux_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickenedIndicatorAux δ₁ E ≤ thickenedIndicatorAux δ₂ E := fun _ =>
  tsub_le_tsub (@rfl ℝ≥0∞ 1).le (Ennreal.div_le_div rfl.le (of_real_le_of_real hle))

theorem indicator_le_thickened_indicator_aux (δ : ℝ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0∞)) ≤ thickenedIndicatorAux δ E := by
  intro a
  by_cases' a ∈ E
  · simp only [← h, ← indicator_of_mem, ← thickened_indicator_aux_one δ E h, ← le_reflₓ]
    
  · simp only [← h, ← indicator_of_not_mem, ← not_false_iff, ← zero_le]
    

theorem thickened_indicator_aux_subset (δ : ℝ) {E₁ E₂ : Set α} (subset : E₁ ⊆ E₂) :
    thickenedIndicatorAux δ E₁ ≤ thickenedIndicatorAux δ E₂ := fun _ =>
  tsub_le_tsub (@rfl ℝ≥0∞ 1).le (Ennreal.div_le_div (inf_edist_anti subset) rfl.le)

/-- As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in α) tends
pointwise (i.e., w.r.t. the product topology on `α → ℝ≥0∞`) to the indicator function of the
closure of E.

This statement is for the unbundled `ℝ≥0∞`-valued functions `thickened_indicator_aux δ E`, see
`thickened_indicator_tendsto_indicator_closure` for the version for bundled `ℝ≥0`-valued
bounded continuous functions. -/
theorem thickened_indicator_aux_tendsto_indicator_closure {δseq : ℕ → ℝ} (δseq_lim : Tendsto δseq atTop (𝓝 0))
    (E : Set α) :
    Tendsto (fun n => thickenedIndicatorAux (δseq n) E) atTop (𝓝 (indicatorₓ (Closure E) fun x => (1 : ℝ≥0∞))) := by
  rw [tendsto_pi_nhds]
  intro x
  by_cases' x_mem_closure : x ∈ Closure E
  · simp_rw [thickened_indicator_aux_one_of_mem_closure _ E x_mem_closure]
    rw
      [show (indicator (Closure E) fun _ => (1 : ℝ≥0∞)) x = 1 by
        simp only [← x_mem_closure, ← indicator_of_mem]]
    exact tendsto_const_nhds
    
  · rw
      [show (Closure E).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 by
        simp only [← x_mem_closure, ← indicator_of_not_mem, ← not_false_iff]]
    rw [mem_closure_iff_inf_edist_zero] at x_mem_closure
    obtain ⟨ε, ⟨ε_pos, ε_le⟩⟩ : ∃ ε : ℝ, 0 < ε ∧ Ennreal.ofReal ε ≤ inf_edist x E := by
      by_cases' dist_infty : inf_edist x E = ∞
      · rw [dist_infty]
        use 1, zero_lt_one, le_top
        
      · use (inf_edist x E).toReal
        exact ⟨(to_real_lt_to_real zero_ne_top dist_infty).mpr (pos_iff_ne_zero.mpr x_mem_closure), of_real_to_real_le⟩
        
    rw [Metric.tendsto_nhds] at δseq_lim
    specialize δseq_lim ε ε_pos
    simp only [← dist_zero_right, ← Real.norm_eq_abs, ← eventually_at_top, ← ge_iff_le] at δseq_lim
    rcases δseq_lim with ⟨N, hN⟩
    apply @tendsto_at_top_of_eventually_const _ _ _ _ _ _ _ N
    intro n n_large
    have key : x ∉ thickening ε E := by
      rwa [thickening, mem_set_of_eq, not_ltₓ]
    refine' le_antisymmₓ _ bot_le
    apply (thickened_indicator_aux_mono (lt_of_abs_lt (hN n n_large)).le E x).trans
    exact (thickened_indicator_aux_zero ε_pos E key).le
    

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `inf_edist _ E`.

`thickened_indicator` is the (bundled) bounded continuous function with `ℝ≥0`-values.
See `thickened_indicator_aux` for the unbundled `ℝ≥0∞`-valued function. -/
@[simps]
def thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) : α →ᵇ ℝ≥0 where
  toFun := fun x : α => (thickenedIndicatorAux δ E x).toNnreal
  continuous_to_fun := by
    apply ContinuousOn.comp_continuous continuous_on_to_nnreal (continuous_thickened_indicator_aux δ_pos E)
    intro x
    exact (lt_of_le_of_ltₓ (@thickened_indicator_aux_le_one _ _ δ E x) one_lt_top).Ne
  map_bounded' := by
    use 2
    intro x y
    rw [Nnreal.dist_eq]
    apply (abs_sub _ _).trans
    rw [Nnreal.abs_eq, Nnreal.abs_eq, ← one_add_one_eq_two]
    have key := @thickened_indicator_aux_le_one _ _ δ E
    apply add_le_add <;>
      · norm_cast
        refine' (to_nnreal_le_to_nnreal (lt_of_le_of_ltₓ (key _) one_lt_top).Ne one_ne_top).mpr (key _)
        

theorem thickenedIndicator.coe_fn_eq_comp {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    ⇑(thickenedIndicator δ_pos E) = Ennreal.toNnreal ∘ thickenedIndicatorAux δ E :=
  rfl

theorem thickened_indicator_le_one {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α) : thickenedIndicator δ_pos E x ≤ 1 := by
  rw [thickenedIndicator.coe_fn_eq_comp]
  simpa using
    (to_nnreal_le_to_nnreal thickened_indicator_aux_lt_top.ne one_ne_top).mpr (thickened_indicator_aux_le_one δ E x)

theorem thickened_indicator_one_of_mem_closure {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_mem : x ∈ Closure E) :
    thickenedIndicator δ_pos E x = 1 := by
  rw [thickened_indicator_apply, thickened_indicator_aux_one_of_mem_closure δ E x_mem, one_to_nnreal]

theorem thickened_indicator_one {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_in_E : x ∈ E) :
    thickenedIndicator δ_pos E x = 1 :=
  thickened_indicator_one_of_mem_closure _ _ (subset_closure x_in_E)

theorem thickened_indicator_zero {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_out : x ∉ Thickening δ E) :
    thickenedIndicator δ_pos E x = 0 := by
  rw [thickened_indicator_apply, thickened_indicator_aux_zero δ_pos E x_out, zero_to_nnreal]

theorem indicator_le_thickened_indicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0 )) ≤ thickenedIndicator δ_pos E := by
  intro a
  by_cases' a ∈ E
  · simp only [← h, ← indicator_of_mem, ← thickened_indicator_one δ_pos E h, ← le_reflₓ]
    
  · simp only [← h, ← indicator_of_not_mem, ← not_false_iff, ← zero_le]
    

theorem thickened_indicator_mono {δ₁ δ₂ : ℝ} (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂) (hle : δ₁ ≤ δ₂) (E : Set α) :
    ⇑(thickenedIndicator δ₁_pos E) ≤ thickenedIndicator δ₂_pos E := by
  intro x
  apply (to_nnreal_le_to_nnreal thickened_indicator_aux_lt_top.ne thickened_indicator_aux_lt_top.ne).mpr
  apply thickened_indicator_aux_mono hle

theorem thickened_indicator_subset {δ : ℝ} (δ_pos : 0 < δ) {E₁ E₂ : Set α} (subset : E₁ ⊆ E₂) :
    ⇑(thickenedIndicator δ_pos E₁) ≤ thickenedIndicator δ_pos E₂ := fun x =>
  (to_nnreal_le_to_nnreal thickened_indicator_aux_lt_top.Ne thickened_indicator_aux_lt_top.Ne).mpr
    (thickened_indicator_aux_subset δ subset x)

/-- As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in α) tends
pointwise to the indicator function of the closure of E.

Note: This version is for the bundled bounded continuous functions, but the topology is not
the topology on `α →ᵇ ℝ≥0`. Coercions to functions `α → ℝ≥0` are done first, so the topology
instance is the product topology (the topology of pointwise convergence). -/
theorem thickened_indicator_tendsto_indicator_closure {δseq : ℕ → ℝ} (δseq_pos : ∀ n, 0 < δseq n)
    (δseq_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) :
    Tendsto (fun n : ℕ => (coeFn : (α →ᵇ ℝ≥0 ) → α → ℝ≥0 ) (thickenedIndicator (δseq_pos n) E)) atTop
      (𝓝 (indicatorₓ (Closure E) fun x => (1 : ℝ≥0 ))) :=
  by
  have key := thickened_indicator_aux_tendsto_indicator_closure δseq_lim E
  rw [tendsto_pi_nhds] at *
  intro x
  rw
    [show indicator (Closure E) (fun x => (1 : ℝ≥0 )) x = (indicator (Closure E) (fun x => (1 : ℝ≥0∞)) x).toNnreal by
      refine' (congr_fun (comp_indicator_const 1 Ennreal.toNnreal zero_to_nnreal) x).symm]
  refine' tendsto.comp (tendsto_to_nnreal _) (key x)
  by_cases' x_mem : x ∈ Closure E <;> simp [← x_mem]

end thickenedIndicator

-- section
