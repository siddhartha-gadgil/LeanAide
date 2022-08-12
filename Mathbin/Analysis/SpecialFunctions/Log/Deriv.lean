/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathbin.Analysis.SpecialFunctions.Log.Basic
import Mathbin.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivative and series expansion of real logarithm

In this file we prove that `real.log` is infinitely smooth at all nonzero `x : ℝ`. We also prove
that the series `∑' n : ℕ, x ^ (n + 1) / (n + 1)` converges to `(-real.log (1 - x))` for all
`x : ℝ`, `|x| < 1`.

## Tags

logarithm, derivative
-/


open Filter Finset Set

open TopologicalSpace BigOperators

namespace Real

variable {x : ℝ}

theorem has_strict_deriv_at_log_of_pos (hx : 0 < x) : HasStrictDerivAt log x⁻¹ x := by
  have : HasStrictDerivAt log (exp <| log x)⁻¹ x :=
    (has_strict_deriv_at_exp <| log x).of_local_left_inverse (continuous_at_log hx.ne') (ne_of_gtₓ <| exp_pos _) <|
      Eventually.mono (lt_mem_nhds hx) @exp_log
  rwa [exp_log hx] at this

theorem has_strict_deriv_at_log (hx : x ≠ 0) : HasStrictDerivAt log x⁻¹ x := by
  cases' hx.lt_or_lt with hx hx
  · convert (has_strict_deriv_at_log_of_pos (neg_pos.mpr hx)).comp x (has_strict_deriv_at_neg x)
    · ext y
      exact (log_neg_eq_log y).symm
      
    · field_simp [← hx.ne]
      
    
  · exact has_strict_deriv_at_log_of_pos hx
    

theorem has_deriv_at_log (hx : x ≠ 0) : HasDerivAt log x⁻¹ x :=
  (has_strict_deriv_at_log hx).HasDerivAt

theorem differentiable_at_log (hx : x ≠ 0) : DifferentiableAt ℝ log x :=
  (has_deriv_at_log hx).DifferentiableAt

theorem differentiable_on_log : DifferentiableOn ℝ log ({0}ᶜ) := fun x hx =>
  (differentiable_at_log hx).DifferentiableWithinAt

@[simp]
theorem differentiable_at_log_iff : DifferentiableAt ℝ log x ↔ x ≠ 0 :=
  ⟨fun h => continuous_at_log_iff.1 h.ContinuousAt, differentiable_at_log⟩

theorem deriv_log (x : ℝ) : deriv log x = x⁻¹ :=
  if hx : x = 0 then by
    rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_log_iff.1 (not_not.2 hx)), hx, inv_zero]
  else (has_deriv_at_log hx).deriv

@[simp]
theorem deriv_log' : deriv log = Inv.inv :=
  funext deriv_log

theorem cont_diff_on_log {n : WithTop ℕ} : ContDiffOn ℝ n log ({0}ᶜ) := by
  suffices : ContDiffOn ℝ ⊤ log ({0}ᶜ)
  exact this.of_le le_top
  refine' (cont_diff_on_top_iff_deriv_of_open is_open_compl_singleton).2 _
  simp [← differentiable_on_log, ← cont_diff_on_inv]

theorem cont_diff_at_log {n : WithTop ℕ} : ContDiffAt ℝ n log x ↔ x ≠ 0 :=
  ⟨fun h => continuous_at_log_iff.1 h.ContinuousAt, fun hx =>
    (cont_diff_on_log x hx).ContDiffAt <| IsOpen.mem_nhds is_open_compl_singleton hx⟩

end Real

section LogDifferentiable

open Real

section deriv

variable {f : ℝ → ℝ} {x f' : ℝ} {s : Set ℝ}

theorem HasDerivWithinAt.log (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun y => log (f y)) (f' / f x) s x := by
  rw [div_eq_inv_mul]
  exact (has_deriv_at_log hx).comp_has_deriv_within_at x hf

theorem HasDerivAt.log (hf : HasDerivAt f f' x) (hx : f x ≠ 0) : HasDerivAt (fun y => log (f y)) (f' / f x) x := by
  rw [← has_deriv_within_at_univ] at *
  exact hf.log hx

theorem HasStrictDerivAt.log (hf : HasStrictDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictDerivAt (fun y => log (f y)) (f' / f x) x := by
  rw [div_eq_inv_mul]
  exact (has_strict_deriv_at_log hx).comp x hf

theorem derivWithin.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => log (f x)) s x = derivWithin f s x / f x :=
  (hf.HasDerivWithinAt.log hx).derivWithin hxs

@[simp]
theorem deriv.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) : deriv (fun x => log (f x)) x = deriv f x / f x :=
  (hf.HasDerivAt.log hx).deriv

end deriv

section fderiv

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ} {s : Set E}

theorem HasFderivWithinAt.log (hf : HasFderivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasFderivWithinAt (fun x => log (f x)) ((f x)⁻¹ • f') s x :=
  (has_deriv_at_log hx).comp_has_fderiv_within_at x hf

theorem HasFderivAt.log (hf : HasFderivAt f f' x) (hx : f x ≠ 0) : HasFderivAt (fun x => log (f x)) ((f x)⁻¹ • f') x :=
  (has_deriv_at_log hx).comp_has_fderiv_at x hf

theorem HasStrictFderivAt.log (hf : HasStrictFderivAt f f' x) (hx : f x ≠ 0) :
    HasStrictFderivAt (fun x => log (f x)) ((f x)⁻¹ • f') x :=
  (has_strict_deriv_at_log hx).comp_has_strict_fderiv_at x hf

theorem DifferentiableWithinAt.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun x => log (f x)) s x :=
  (hf.HasFderivWithinAt.log hx).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) : DifferentiableAt ℝ (fun x => log (f x)) x :=
  (hf.HasFderivAt.log hx).DifferentiableAt

theorem ContDiffAt.log {n} (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0) : ContDiffAt ℝ n (fun x => log (f x)) x :=
  (cont_diff_at_log.2 hx).comp x hf

theorem ContDiffWithinAt.log {n} (hf : ContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun x => log (f x)) s x :=
  (cont_diff_at_log.2 hx).comp_cont_diff_within_at x hf

theorem ContDiffOn.log {n} (hf : ContDiffOn ℝ n f s) (hs : ∀, ∀ x ∈ s, ∀, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => log (f x)) s := fun x hx => (hf x hx).log (hs x hx)

theorem ContDiff.log {n} (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) : ContDiff ℝ n fun x => log (f x) :=
  cont_diff_iff_cont_diff_at.2 fun x => hf.ContDiffAt.log (h x)

theorem DifferentiableOn.log (hf : DifferentiableOn ℝ f s) (hx : ∀, ∀ x ∈ s, ∀, f x ≠ 0) :
    DifferentiableOn ℝ (fun x => log (f x)) s := fun x h => (hf x h).log (hx x h)

@[simp]
theorem Differentiable.log (hf : Differentiable ℝ f) (hx : ∀ x, f x ≠ 0) : Differentiable ℝ fun x => log (f x) :=
  fun x => (hf x).log (hx x)

theorem fderivWithin.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => log (f x)) s x = (f x)⁻¹ • fderivWithin ℝ f s x :=
  (hf.HasFderivWithinAt.log hx).fderivWithin hxs

@[simp]
theorem fderiv.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    fderiv ℝ (fun x => log (f x)) x = (f x)⁻¹ • fderiv ℝ f x :=
  (hf.HasFderivAt.log hx).fderiv

end fderiv

end LogDifferentiable

namespace Real

/-- The function `x * log (1 + t / x)` tends to `t` at `+∞`. -/
theorem tendsto_mul_log_one_plus_div_at_top (t : ℝ) : Tendsto (fun x => x * log (1 + t / x)) atTop (𝓝 t) := by
  have h₁ : tendsto (fun h => h⁻¹ * log (1 + t * h)) (𝓝[≠] 0) (𝓝 t) := by
    simpa [← has_deriv_at_iff_tendsto_slope, ← slope_fun_def] using
      (((has_deriv_at_id (0 : ℝ)).const_mul t).const_add 1).log
        (by
          simp )
  have h₂ : tendsto (fun x : ℝ => x⁻¹) at_top (𝓝[≠] 0) :=
    tendsto_inv_at_top_zero'.mono_right (nhds_within_mono _ fun x hx => (set.mem_Ioi.mp hx).ne')
  simpa only [← (· ∘ ·), ← inv_invₓ] using h₁.comp h₂

open BigOperators

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `has_sum_pow_div_log_of_abs_lt_1`.
-/
theorem abs_log_sub_add_sum_range_le {x : ℝ} (h : abs x < 1) (n : ℕ) :
    abs ((∑ i in Range n, x ^ (i + 1) / (i + 1)) + log (1 - x)) ≤ abs x ^ (n + 1) / (1 - abs x) := by
  /- For the proof, we show that the derivative of the function to be estimated is small,
    and then apply the mean value inequality. -/
  let F : ℝ → ℝ := fun x => (∑ i in range n, x ^ (i + 1) / (i + 1)) + log (1 - x)
  -- First step: compute the derivative of `F`
  have A : ∀, ∀ y ∈ Ioo (-1 : ℝ) 1, ∀, deriv F y = -(y ^ n) / (1 - y) := by
    intro y hy
    have : (∑ i in range n, (↑i + 1) * y ^ i / (↑i + 1)) = ∑ i in range n, y ^ i := by
      congr with i
      exact mul_div_cancel_left _ (Nat.cast_add_one_pos i).ne'
    field_simp [← F, ← this, ← geom_sum_eq (ne_of_ltₓ hy.2), ← sub_ne_zero_of_ne (ne_of_gtₓ hy.2), ←
      sub_ne_zero_of_ne (ne_of_ltₓ hy.2)]
    ring
  -- second step: show that the derivative of `F` is small
  have B : ∀, ∀ y ∈ Icc (-abs x) (abs x), ∀, abs (deriv F y) ≤ abs x ^ n / (1 - abs x) := by
    intro y hy
    have : y ∈ Ioo (-(1 : ℝ)) 1 := ⟨lt_of_lt_of_leₓ (neg_lt_neg h) hy.1, lt_of_le_of_ltₓ hy.2 h⟩
    calc abs (deriv F y) = abs (-(y ^ n) / (1 - y)) := by
        rw [A y this]_ ≤ abs x ^ n / (1 - abs x) := by
        have : abs y ≤ abs x := abs_le.2 hy
        have : 0 < 1 - abs x := by
          linarith
        have : 1 - abs x ≤ abs (1 - y) :=
          le_transₓ
            (by
              linarith [hy.2])
            (le_abs_self _)
        simp only [pow_abs, ← abs_div, ← abs_neg]
        apply_rules [div_le_div, pow_nonneg, abs_nonneg, pow_le_pow_of_le_left]
  -- third step: apply the mean value inequality
  have C : ∥F x - F 0∥ ≤ abs x ^ n / (1 - abs x) * ∥x - 0∥ := by
    have : ∀, ∀ y ∈ Icc (-abs x) (abs x), ∀, DifferentiableAt ℝ F y := by
      intro y hy
      have : 1 - y ≠ 0 := sub_ne_zero_of_ne (ne_of_gtₓ (lt_of_le_of_ltₓ hy.2 h))
      simp [← F, ← this]
    apply Convex.norm_image_sub_le_of_norm_deriv_le this B (convex_Icc _ _) _ _
    · simp
      
    · simp [← le_abs_self x, ← neg_le.mp (neg_le_abs_self x)]
      
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [← F, ← norm_eq_abs, ← div_mul_eq_mul_div, ← pow_succ'ₓ] using C

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- Power series expansion of the logarithm around `1`. -/
theorem has_sum_pow_div_log_of_abs_lt_1 {x : ℝ} (h : abs x < 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / (n + 1)) (-log (1 - x)) := by
  rw [Summable.has_sum_iff_tendsto_nat]
  show tendsto (fun n : ℕ => ∑ i : ℕ in range n, x ^ (i + 1) / (i + 1)) at_top (𝓝 (-log (1 - x)))
  · rw [tendsto_iff_norm_tendsto_zero]
    simp only [← norm_eq_abs, ← sub_neg_eq_add]
    refine' squeeze_zero (fun n => abs_nonneg _) (abs_log_sub_add_sum_range_le h) _
    suffices tendsto (fun t : ℕ => abs x ^ (t + 1) / (1 - abs x)) at_top (𝓝 (abs x * 0 / (1 - abs x))) by
      simpa
    simp only [← pow_succₓ]
    refine' (tendsto_const_nhds.mul _).div_const
    exact tendsto_pow_at_top_nhds_0_of_lt_1 (abs_nonneg _) h
    
  show Summable fun n : ℕ => x ^ (n + 1) / (n + 1)
  · refine' summable_of_norm_bounded _ (summable_geometric_of_lt_1 (abs_nonneg _) h) fun i => _
    calc ∥x ^ (i + 1) / (i + 1)∥ = abs x ^ (i + 1) / (i + 1) := by
        have : (0 : ℝ) ≤ i + 1 := le_of_ltₓ (Nat.cast_add_one_pos i)
        rw [norm_eq_abs, abs_div, ← pow_abs, abs_of_nonneg this]_ ≤ abs x ^ (i + 1) / (0 + 1) := by
        apply_rules [div_le_div_of_le_left, pow_nonneg, abs_nonneg, add_le_add_right, i.cast_nonneg]
        norm_num _ ≤ abs x ^ i := by
        simpa [← pow_succ'ₓ] using mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) i) (le_of_ltₓ h)
    

/-- Power series expansion of `log(1 + x) - log(1 - x)` for `|x| < 1`. -/
theorem has_sum_log_sub_log_of_abs_lt_1 {x : ℝ} (h : abs x < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * x ^ (2 * k + 1)) (log (1 + x) - log (1 - x)) := by
  let term := fun n : ℕ => -1 * (-x ^ (n + 1) / ((n : ℝ) + 1)) + x ^ (n + 1) / (n + 1)
  have h_term_eq_goal : term ∘ (· * ·) 2 = fun k : ℕ => 2 * (1 / (2 * k + 1)) * x ^ (2 * k + 1) := by
    ext n
    dsimp' [← term]
    rw [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)) x]
    push_cast
    ring_nf
  rw [← h_term_eq_goal, (Nat.mul_right_injective two_pos).has_sum_iff]
  · have h₁ := (has_sum_pow_div_log_of_abs_lt_1 (Eq.trans_lt (abs_neg x) h)).mul_left (-1)
    convert h₁.add (has_sum_pow_div_log_of_abs_lt_1 h)
    ring_nf
    
  · intro m hm
    rw [range_two_mul, Set.mem_set_of_eq, ← Nat.even_add_one] at hm
    dsimp' [← term]
    rw [Even.neg_pow hm, neg_one_mul, neg_add_selfₓ]
    

/-- Expansion of `log (1 + a⁻¹)` as a series in powers of `1 / (2 * a + 1)`. -/
theorem has_sum_log_one_add_inv {a : ℝ} (h : 0 < a) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1)) (log (1 + a⁻¹)) := by
  have h₁ : abs (1 / (2 * a + 1)) < 1 := by
    rw [abs_of_pos, div_lt_one]
    · linarith
      
    · linarith
      
    · exact
        div_pos one_pos
          (by
            linarith)
      
  convert has_sum_log_sub_log_of_abs_lt_1 h₁
  have h₂ : (2 : ℝ) * a + 1 ≠ 0 := by
    linarith
  have h₃ := h.ne'
  rw [← log_div]
  · congr
    field_simp
    linarith
    
  · field_simp
    linarith
    
  · field_simp
    

end Real

