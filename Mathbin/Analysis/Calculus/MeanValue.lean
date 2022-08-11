/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathbin.Analysis.Calculus.LocalExtr
import Mathbin.Analysis.Convex.Slope
import Mathbin.Analysis.Convex.Topology
import Mathbin.Data.Complex.IsROrC

/-!
# The mean value inequality and equalities

In this file we prove the following facts:

* `convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentiable on a convex set `s`
  and the norm of its derivative is bounded by `C`, then `f` is Lipschitz continuous on `s` with
  constant `C`; also a variant in which what is bounded by `C` is the norm of the difference of the
  derivative from a fixed linear map. This lemma and its versions are formulated using `is_R_or_C`,
  so they work both for real and complex derivatives.

* `image_le_of*`, `image_norm_le_of_*` : several similar lemmas deducing `f x ≤ B x` or
  `∥f x∥ ≤ B x` from upper estimates on `f'` or `∥f'∥`, respectively. These lemmas differ by
  their assumptions:

  * `of_liminf_*` lemmas assume that limit inferior of some ratio is less than `B' x`;
  * `of_deriv_right_*`, `of_norm_deriv_right_*` lemmas assume that the right derivative
    or its norm is less than `B' x`;
  * `of_*_lt_*` lemmas assume a strict inequality whenever `f x = B x` or `∥f x∥ = B x`;
  * `of_*_le_*` lemmas assume a non-strict inequality everywhere on `[a, b)`;
  * name of a lemma ends with `'` if (1) it assumes that `B` is continuous on `[a, b]`
    and has a right derivative at every point of `[a, b)`, and (2) the lemma has
    a counterpart assuming that `B` is differentiable everywhere on `ℝ`

* `norm_image_sub_le_*_segment` : if derivative of `f` on `[a, b]` is bounded above
  by a constant `C`, then `∥f x - f a∥ ≤ C * ∥x - a∥`; several versions deal with
  right derivative and derivative within `[a, b]` (`has_deriv_within_at` or `deriv_within`).

* `convex.is_const_of_fderiv_within_eq_zero` : if a function has derivative `0` on a convex set `s`,
  then it is a constant on `s`.

* `exists_ratio_has_deriv_at_eq_ratio_slope` and `exists_ratio_deriv_eq_ratio_slope` :
  Cauchy's Mean Value Theorem.

* `exists_has_deriv_at_eq_slope` and `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem.

* `domain_mvt` : Lagrange's Mean Value Theorem, applied to a segment in a convex domain.

* `convex.image_sub_lt_mul_sub_of_deriv_lt`, `convex.mul_sub_lt_image_sub_of_lt_deriv`,
  `convex.image_sub_le_mul_sub_of_deriv_le`, `convex.mul_sub_le_image_sub_of_le_deriv`,
  if `∀ x, C (</≤/>/≥) (f' x)`, then `C * (y - x) (</≤/>/≥) (f y - f x)` whenever `x < y`.

* `convex.monotone_on_of_deriv_nonneg`, `convex.antitone_on_of_deriv_nonpos`,
  `convex.strict_mono_of_deriv_pos`, `convex.strict_anti_of_deriv_neg` :
  if the derivative of a function is non-negative/non-positive/positive/negative, then
  the function is monotone/antitone/strictly monotone/strictly monotonically
  decreasing.

* `convex_on_of_deriv_monotone_on`, `convex_on_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.

* `strict_fderiv_of_cont_diff` : a C^1 function over the reals is strictly differentiable.  (This
  is a corollary of the mean value inequality.)
-/


variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {F : Type _} [NormedGroup F] [NormedSpace ℝ F]

open Metric Set Asymptotics ContinuousLinearMap Filter

open Classical TopologicalSpace Nnreal

/-! ### One-dimensional fencing inequalities -/


/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀, ∀ x ∈ Ico a b, ∀, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  change Icc a b ⊆ { x | f x ≤ B x }
  set s := { x | f x ≤ B x } ∩ Icc a b
  have A : ContinuousOn (fun x => (f x, B x)) (Icc a b) := hf.prod hB
  have : IsClosed s := by
    simp only [← s, ← inter_comm]
    exact A.preimage_closed_of_closed is_closed_Icc OrderClosedTopology.is_closed_le'
  apply this.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨hxB : f x ≤ B x, xab⟩ y hy
  cases' hxB.lt_or_eq with hxB hxB
  · -- If `f x < B x`, then all we need is continuity of both sides
    refine' nonempty_of_mem (inter_mem _ (Ioc_mem_nhds_within_Ioi ⟨le_rfl, hy⟩))
    have : ∀ᶠ x in 𝓝[Icc a b] x, f x < B x :=
      A x (Ico_subset_Icc_self xab) (IsOpen.mem_nhds (is_open_lt continuous_fst continuous_snd) hxB)
    have : ∀ᶠ x in 𝓝[>] x, f x < B x := nhds_within_le_of_mem (Icc_mem_nhds_within_Ioi xab) this
    exact this.mono fun y => le_of_ltₓ
    
  · rcases exists_between (bound x xab hxB) with ⟨r, hfr, hrB⟩
    specialize hf' x xab r hfr
    have HB : ∀ᶠ z in 𝓝[>] x, r < slope B x z :=
      (has_deriv_within_at_iff_tendsto_slope' <| lt_irreflₓ x).1 (hB' x xab).Ioi_of_Ici (Ioi_mem_nhds hrB)
    obtain ⟨z, hfz, hzB, hz⟩ : ∃ z, slope f x z < r ∧ r < slope B x z ∧ z ∈ Ioc x y
    exact (hf'.and_eventually (HB.and (Ioc_mem_nhds_within_Ioi ⟨le_rfl, hy⟩))).exists
    refine' ⟨z, _, hz⟩
    have := (hfz.trans hzB).le
    rwa [slope_def_field, slope_def_field, div_le_div_right (sub_pos.2 hz.1), hxB, sub_le_sub_iff_right] at this
    

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀, ∀ x ∈ Ico a b, ∀, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha (fun x hx => (hB x).ContinuousAt.ContinuousWithinAt)
    (fun x hx => (hB x).HasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by `B'`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_le_deriv_boundary {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt B (B' x) (Ici x) x)
    -- `bound` actually says `liminf (f z - f x) / (z - x) ≤ B' x`
    (bound : ∀, ∀ x ∈ Ico a b, ∀, ∀ r, B' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r) :
    ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  have Hr : ∀, ∀ x ∈ Icc a b, ∀, ∀, ∀ r > 0, ∀, f x ≤ B x + r * (x - a) := by
    intro x hx r hr
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound
    · rwa [sub_self, mul_zero, add_zeroₓ]
      
    · exact hB.add (continuous_on_const.mul (continuous_id.continuous_on.sub continuous_on_const))
      
    · intro x hx
      exact (hB' x hx).add (((has_deriv_within_at_id x (Ici x)).sub_const a).const_mul r)
      
    · intro x hx _
      rw [mul_oneₓ]
      exact (lt_add_iff_pos_right _).2 hr
      
    exact hx
  intro x hx
  have : ContinuousWithinAt (fun r => B x + r * (x - a)) (Ioi 0) 0 :=
    continuous_within_at_const.add (continuous_within_at_id.mul continuous_within_at_const)
  convert continuous_within_at_const.closure_le _ this (Hr x hx) <;> simp

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : f a ≤ B a)
    (hB : ContinuousOn B (Icc a b)) (hB' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀, ∀ x ∈ Ico a b, ∀, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf (fun x hx r hr => (hf' x hx).liminf_right_slope_le hr) ha hB hB'
    bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : f a ≤ B a)
    (hB : ∀ x, HasDerivAt B (B' x) x) (bound : ∀, ∀ x ∈ Ico a b, ∀, f x = B x → f' x < B' x) :
    ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha (fun x hx => (hB x).ContinuousAt.ContinuousWithinAt)
    (fun x hx => (hB x).HasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x ≤ B' x` on `[a, b)`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_le_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : f a ≤ B a)
    (hB : ContinuousOn B (Icc a b)) (hB' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀, ∀ x ∈ Ico a b, ∀, f' x ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  (image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB') fun x hx r hr =>
    (hf' x hx).liminf_right_slope_le (lt_of_le_of_ltₓ (bound x hx) hr)

/-! ### Vector-valued functions `f : ℝ → E` -/


section

variable {f : ℝ → E} {a b : ℝ}

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `B` has right derivative at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(∥f z∥ - ∥f x∥) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. -/
theorem image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type _} [NormedGroup E] {f : ℝ → E} {f' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (∥f z∥ - ∥f x∥) / (z - x) ≤ f' x`
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope (norm ∘ f) x z < r)
    {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀, ∀ x ∈ Ico a b, ∀, ∥f x∥ = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuous_on hf) hf' ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* the norm of `f'` is strictly less than `B'` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {f' : ℝ → E} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a)
    (hB : ContinuousOn B (Icc a b)) (hB' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀, ∀ x ∈ Ico a b, ∀, ∥f x∥ = B x → ∥f' x∥ < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
  image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
    (fun x hx r hr => (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* the norm of `f'` is strictly less than `B'` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary {f' : ℝ → E} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a)
    (hB : ∀ x, HasDerivAt B (B' x) x) (bound : ∀, ∀ x ∈ Ico a b, ∀, ∥f x∥ = B x → ∥f' x∥ < B' x) :
    ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
  image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha (fun x hx => (hB x).ContinuousAt.ContinuousWithinAt)
    (fun x hx => (hB x).HasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* we have `∥f' x∥ ≤ B x` everywhere on `[a, b)`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary' {f' : ℝ → E} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a)
    (hB : ContinuousOn B (Icc a b)) (hB' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀, ∀ x ∈ Ico a b, ∀, ∥f' x∥ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
  (image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuous_on hf) ha hB hB') fun x hx r hr =>
    (hf' x hx).liminf_right_slope_norm_le (lt_of_le_of_ltₓ (bound x hx) hr)

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* we have `∥f' x∥ ≤ B x` everywhere on `[a, b)`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary {f' : ℝ → E} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a)
    (hB : ∀ x, HasDerivAt B (B' x) x) (bound : ∀, ∀ x ∈ Ico a b, ∀, ∥f' x∥ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha (fun x hx => (hB x).ContinuousAt.ContinuousWithinAt)
    (fun x hx => (hB x).HasDerivWithinAt) bound

/-- A function on `[a, b]` with the norm of the right derivative bounded by `C`
satisfies `∥f x - f a∥ ≤ C * (x - a)`. -/
theorem norm_image_sub_le_of_norm_deriv_right_le_segment {f' : ℝ → E} {C : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt f (f' x) (Ici x) x) (bound : ∀, ∀ x ∈ Ico a b, ∀, ∥f' x∥ ≤ C) :
    ∀, ∀ x ∈ Icc a b, ∀, ∥f x - f a∥ ≤ C * (x - a) := by
  let g := fun x => f x - f a
  have hg : ContinuousOn g (Icc a b) := hf.sub continuous_on_const
  have hg' : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt g (f' x) (Ici x) x := by
    intro x hx
    simpa using (hf' x hx).sub (has_deriv_within_at_const _ _ _)
  let B := fun x => C * (x - a)
  have hB : ∀ x, HasDerivAt B C x := by
    intro x
    simpa using (has_deriv_at_const x C).mul ((has_deriv_at_id x).sub (has_deriv_at_const x a))
  convert image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound
  simp only [← g, ← B]
  rw [sub_self, norm_zero, sub_self, mul_zero]

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `∥f x - f a∥ ≤ C * (x - a)`, `has_deriv_within_at`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment' {f' : ℝ → E} {C : ℝ}
    (hf : ∀, ∀ x ∈ Icc a b, ∀, HasDerivWithinAt f (f' x) (Icc a b) x) (bound : ∀, ∀ x ∈ Ico a b, ∀, ∥f' x∥ ≤ C) :
    ∀, ∀ x ∈ Icc a b, ∀, ∥f x - f a∥ ≤ C * (x - a) := by
  refine'
    norm_image_sub_le_of_norm_deriv_right_le_segment (fun x hx => (hf x hx).ContinuousWithinAt) (fun x hx => _) bound
  exact (hf x <| Ico_subset_Icc_self hx).nhdsWithin (Icc_mem_nhds_within_Ici hx)

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `∥f x - f a∥ ≤ C * (x - a)`, `deriv_within`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment {C : ℝ} (hf : DifferentiableOn ℝ f (Icc a b))
    (bound : ∀, ∀ x ∈ Ico a b, ∀, ∥derivWithin f (Icc a b) x∥ ≤ C) : ∀, ∀ x ∈ Icc a b, ∀, ∥f x - f a∥ ≤ C * (x - a) :=
  by
  refine' norm_image_sub_le_of_norm_deriv_le_segment' _ bound
  exact fun x hx => (hf x hx).HasDerivWithinAt

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `∥f 1 - f 0∥ ≤ C`, `has_deriv_within_at`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : ℝ → E} {C : ℝ}
    (hf : ∀, ∀ x ∈ Icc (0 : ℝ) 1, ∀, HasDerivWithinAt f (f' x) (Icc (0 : ℝ) 1) x)
    (bound : ∀, ∀ x ∈ Ico (0 : ℝ) 1, ∀, ∥f' x∥ ≤ C) : ∥f 1 - f 0∥ ≤ C := by
  simpa only [← sub_zero, ← mul_oneₓ] using
    norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `∥f 1 - f 0∥ ≤ C`, `deriv_within` version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {C : ℝ} (hf : DifferentiableOn ℝ f (Icc (0 : ℝ) 1))
    (bound : ∀, ∀ x ∈ Ico (0 : ℝ) 1, ∀, ∥derivWithin f (Icc (0 : ℝ) 1) x∥ ≤ C) : ∥f 1 - f 0∥ ≤ C := by
  simpa only [← sub_zero, ← mul_oneₓ] using
    norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)

theorem constant_of_has_deriv_right_zero (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt f 0 (Ici x) x) : ∀, ∀ x ∈ Icc a b, ∀, f x = f a := by
  simpa only [← zero_mul, ← norm_le_zero_iff, ← sub_eq_zero] using fun x hx =>
    norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv
      (fun y hy => by
        rw [norm_le_zero_iff])
      x hx

theorem constant_of_deriv_within_zero (hdiff : DifferentiableOn ℝ f (Icc a b))
    (hderiv : ∀, ∀ x ∈ Ico a b, ∀, derivWithin f (Icc a b) x = 0) : ∀, ∀ x ∈ Icc a b, ∀, f x = f a := by
  have H : ∀, ∀ x ∈ Ico a b, ∀, ∥derivWithin f (Icc a b) x∥ ≤ 0 := by
    simpa only [← norm_le_zero_iff] using fun x hx => hderiv x hx
  simpa only [← zero_mul, ← norm_le_zero_iff, ← sub_eq_zero] using fun x hx =>
    norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx

variable {f' g : ℝ → E}

/-- If two continuous functions on `[a, b]` have the same right derivative and are equal at `a`,
  then they are equal everywhere on `[a, b]`. -/
theorem eq_of_has_deriv_right_eq (derivf : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt f (f' x) (Ici x) x)
    (derivg : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt g (f' x) (Ici x) x) (fcont : ContinuousOn f (Icc a b))
    (gcont : ContinuousOn g (Icc a b)) (hi : f a = g a) : ∀, ∀ y ∈ Icc a b, ∀, f y = g y := by
  simp only [@sub_eq_zero _ _ (f _)] at hi⊢
  exact
    hi ▸
      constant_of_has_deriv_right_zero (fcont.sub gcont) fun y hy => by
        simpa only [← sub_self] using (derivf y hy).sub (derivg y hy)

/-- If two differentiable functions on `[a, b]` have the same derivative within `[a, b]` everywhere
  on `[a, b)` and are equal at `a`, then they are equal everywhere on `[a, b]`. -/
theorem eq_of_deriv_within_eq (fdiff : DifferentiableOn ℝ f (Icc a b)) (gdiff : DifferentiableOn ℝ g (Icc a b))
    (hderiv : EqOn (derivWithin f (Icc a b)) (derivWithin g (Icc a b)) (Ico a b)) (hi : f a = g a) :
    ∀, ∀ y ∈ Icc a b, ∀, f y = g y := by
  have A : ∀, ∀ y ∈ Ico a b, ∀, HasDerivWithinAt f (derivWithin f (Icc a b) y) (Ici y) y := fun y hy =>
    (fdiff y (mem_Icc_of_Ico hy)).HasDerivWithinAt.nhdsWithin (Icc_mem_nhds_within_Ici hy)
  have B : ∀, ∀ y ∈ Ico a b, ∀, HasDerivWithinAt g (derivWithin g (Icc a b) y) (Ici y) y := fun y hy =>
    (gdiff y (mem_Icc_of_Ico hy)).HasDerivWithinAt.nhdsWithin (Icc_mem_nhds_within_Ici hy)
  exact eq_of_has_deriv_right_eq A (fun y hy => (hderiv hy).symm ▸ B y hy) fdiff.continuous_on gdiff.continuous_on hi

end

/-!
### Vector-valued functions `f : E → G`

Theorems in this section work both for real and complex differentiable functions. We use assumptions
`[is_R_or_C 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 G]` to achieve this result. For the domain `E` we
also assume `[normed_space ℝ E]` to have a notion of a `convex` set. -/


section

variable {𝕜 G : Type _} [IsROrC 𝕜] [NormedSpace 𝕜 E] [NormedGroup G] [NormedSpace 𝕜 G]

namespace Convex

variable {f : E → G} {C : ℝ} {s : Set E} {x y : E} {f' : E → E →L[𝕜] G} {φ : E →L[𝕜] G}

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`, then
the function is `C`-Lipschitz. Version with `has_fderiv_within`. -/
theorem norm_image_sub_le_of_norm_has_fderiv_within_le (hf : ∀, ∀ x ∈ s, ∀, HasFderivWithinAt f (f' x) s x)
    (bound : ∀, ∀ x ∈ s, ∀, ∥f' x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ := by
  let this : NormedSpace ℝ G := RestrictScalars.normedSpace ℝ 𝕜 G
  /- By composition with `t ↦ x + t • (y-x)`, we reduce to a statement for functions defined
    on `[0,1]`, for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
    We just have to check the differentiability of the composition and bounds on its derivative,
    which is straightforward but tedious for lack of automation. -/
  have C0 : 0 ≤ C := le_transₓ (norm_nonneg _) (bound x xs)
  set g : ℝ → E := fun t => x + t • (y - x)
  have Dg : ∀ t, HasDerivAt g (y - x) t := by
    intro t
    simpa only [← one_smul] using ((has_deriv_at_id t).smul_const (y - x)).const_add x
  have segm : Icc 0 1 ⊆ g ⁻¹' s := by
    rw [← image_subset_iff, ← segment_eq_image']
    apply hs.segment_subset xs ys
  have : f x = f (g 0) := by
    simp only [← g]
    rw [zero_smul, add_zeroₓ]
  rw [this]
  have : f y = f (g 1) := by
    simp only [← g]
    rw [one_smul, add_sub_cancel'_right]
  rw [this]
  have D2 : ∀, ∀ t ∈ Icc (0 : ℝ) 1, ∀, HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) (Icc 0 1) t := by
    intro t ht
    have : HasFderivWithinAt f ((f' (g t)).restrictScalars ℝ) s (g t) := hf (g t) (segm ht)
    exact this.comp_has_deriv_within_at _ (Dg t).HasDerivWithinAt segm
  apply norm_image_sub_le_of_norm_deriv_le_segment_01' D2
  refine' fun t ht => le_of_op_norm_le _ _ _
  exact bound (g t) (segm <| Ico_subset_Icc_self ht)

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `has_fderiv_within` and
`lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_has_fderiv_within_le {C : ℝ≥0 } (hf : ∀, ∀ x ∈ s, ∀, HasFderivWithinAt f (f' x) s x)
    (bound : ∀, ∀ x ∈ s, ∀, ∥f' x∥₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s := by
  rw [lipschitz_on_with_iff_norm_sub_le]
  intro x x_in y y_in
  exact hs.norm_image_sub_le_of_norm_has_fderiv_within_le hf bound y_in x_in

/-- Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Suppose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `∥f' x∥₊`, `f` is
`K`-Lipschitz on some neighborhood of `x` within `s`. See also
`convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at` for a version that claims
existence of `K` instead of an explicit estimate. -/
theorem exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt (hs : Convex ℝ s) {f : E → G}
    (hder : ∀ᶠ y in 𝓝[s] x, HasFderivWithinAt f (f' y) s y) (hcont : ContinuousWithinAt f' s x) (K : ℝ≥0 )
    (hK : ∥f' x∥₊ < K) : ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  obtain ⟨ε, ε0, hε⟩ : ∃ ε > 0, ball x ε ∩ s ⊆ { y | HasFderivWithinAt f (f' y) s y ∧ ∥f' y∥₊ < K }
  exact mem_nhds_within_iff.1 (hder.and <| hcont.nnnorm.eventually (gt_mem_nhds hK))
  rw [inter_comm] at hε
  refine' ⟨s ∩ ball x ε, inter_mem_nhds_within _ (ball_mem_nhds _ ε0), _⟩
  exact
    (hs.inter (convex_ball _ _)).lipschitz_on_with_of_nnnorm_has_fderiv_within_le
      (fun y hy => (hε hy).1.mono (inter_subset_left _ _)) fun y hy => (hε hy).2.le

/-- Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Suppose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `∥f' x∥₊`, `f` is Lipschitz
on some neighborhood of `x` within `s`. See also
`convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt` for a version
with an explicit estimate on the Lipschitz constant. -/
theorem exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at (hs : Convex ℝ s) {f : E → G}
    (hder : ∀ᶠ y in 𝓝[s] x, HasFderivWithinAt f (f' y) s y) (hcont : ContinuousWithinAt f' s x) :
    ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <| hs.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt hder hcont

/-- The mean value theorem on a convex set: if the derivative of a function within this set is
bounded by `C`, then the function is `C`-Lipschitz. Version with `fderiv_within`. -/
theorem norm_image_sub_le_of_norm_fderiv_within_le (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀, ∀ x ∈ s, ∀, ∥fderivWithin 𝕜 f s x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∥f y - f x∥ ≤ C * ∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivWithinAt) bound xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv_within` and
`lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_fderiv_within_le {C : ℝ≥0 } (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀, ∀ x ∈ s, ∀, ∥fderivWithin 𝕜 f s x∥₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitz_on_with_of_nnnorm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivWithinAt) bound

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `fderiv`. -/
theorem norm_image_sub_le_of_norm_fderiv_le (hf : ∀, ∀ x ∈ s, ∀, DifferentiableAt 𝕜 f x)
    (bound : ∀, ∀ x ∈ s, ∀, ∥fderiv 𝕜 f x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∥f y - f x∥ ≤ C * ∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivAt.HasFderivWithinAt) bound xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv` and `lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_fderiv_le {C : ℝ≥0 } (hf : ∀, ∀ x ∈ s, ∀, DifferentiableAt 𝕜 f x)
    (bound : ∀, ∀ x ∈ s, ∀, ∥fderiv 𝕜 f x∥₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitz_on_with_of_nnnorm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivAt.HasFderivWithinAt) bound

/-- Variant of the mean value inequality on a convex set, using a bound on the difference between
the derivative and a fixed linear map, rather than a bound on the derivative itself. Version with
`has_fderiv_within`. -/
theorem norm_image_sub_le_of_norm_has_fderiv_within_le' (hf : ∀, ∀ x ∈ s, ∀, HasFderivWithinAt f (f' x) s x)
    (bound : ∀, ∀ x ∈ s, ∀, ∥f' x - φ∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∥f y - f x - φ (y - x)∥ ≤ C * ∥y - x∥ := by
  /- We subtract `φ` to define a new function `g` for which `g' = 0`, for which the previous theorem
    applies, `convex.norm_image_sub_le_of_norm_has_fderiv_within_le`. Then, we just need to glue
    together the pieces, expressing back `f` in terms of `g`. -/
  let g := fun y => f y - φ y
  have hg : ∀, ∀ x ∈ s, ∀, HasFderivWithinAt g (f' x - φ) s x := fun x xs => (hf x xs).sub φ.has_fderiv_within_at
  calc ∥f y - f x - φ (y - x)∥ = ∥f y - f x - (φ y - φ x)∥ := by
      simp _ = ∥f y - φ y - (f x - φ x)∥ := by
      abel _ = ∥g y - g x∥ := by
      simp _ ≤ C * ∥y - x∥ := Convex.norm_image_sub_le_of_norm_has_fderiv_within_le hg bound hs xs ys

/-- Variant of the mean value inequality on a convex set. Version with `fderiv_within`. -/
theorem norm_image_sub_le_of_norm_fderiv_within_le' (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀, ∀ x ∈ s, ∀, ∥fderivWithin 𝕜 f s x - φ∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∥f y - f x - φ (y - x)∥ ≤ C * ∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_fderiv_within_le' (fun x hx => (hf x hx).HasFderivWithinAt) bound xs ys

/-- Variant of the mean value inequality on a convex set. Version with `fderiv`. -/
theorem norm_image_sub_le_of_norm_fderiv_le' (hf : ∀, ∀ x ∈ s, ∀, DifferentiableAt 𝕜 f x)
    (bound : ∀, ∀ x ∈ s, ∀, ∥fderiv 𝕜 f x - φ∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∥f y - f x - φ (y - x)∥ ≤ C * ∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_fderiv_within_le' (fun x hx => (hf x hx).HasFderivAt.HasFderivWithinAt) bound xs ys

/-- If a function has zero Fréchet derivative at every point of a convex set,
then it is a constant on this set. -/
theorem is_const_of_fderiv_within_eq_zero (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : ∀, ∀ x ∈ s, ∀, fderivWithin 𝕜 f s x = 0) (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  have bound : ∀, ∀ x ∈ s, ∀, ∥fderivWithin 𝕜 f s x∥ ≤ 0 := fun x hx => by
    simp only [← hf' x hx, ← norm_zero]
  simpa only [← (dist_eq_norm _ _).symm, ← zero_mul, ← dist_le_zero, ← eq_comm] using
    hs.norm_image_sub_le_of_norm_fderiv_within_le hf bound hx hy

theorem _root_.is_const_of_fderiv_eq_zero (hf : Differentiable 𝕜 f) (hf' : ∀ x, fderiv 𝕜 f x = 0) (x y : E) :
    f x = f y :=
  convex_univ.is_const_of_fderiv_within_eq_zero hf.DifferentiableOn
    (fun x _ => by
      rw [fderiv_within_univ] <;> exact hf' x)
    trivialₓ trivialₓ

end Convex

namespace Convex

variable {f f' : 𝕜 → G} {s : Set 𝕜} {x y : 𝕜}

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `has_deriv_within`. -/
theorem norm_image_sub_le_of_norm_has_deriv_within_le {C : ℝ} (hf : ∀, ∀ x ∈ s, ∀, HasDerivWithinAt f (f' x) s x)
    (bound : ∀, ∀ x ∈ s, ∀, ∥f' x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
  Convex.norm_image_sub_le_of_norm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivWithinAt)
    (fun x hx =>
      le_transₓ
        (by
          simp )
        (bound x hx))
    hs xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `has_deriv_within` and `lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_has_deriv_within_le {C : ℝ≥0 } (hs : Convex ℝ s)
    (hf : ∀, ∀ x ∈ s, ∀, HasDerivWithinAt f (f' x) s x) (bound : ∀, ∀ x ∈ s, ∀, ∥f' x∥₊ ≤ C) : LipschitzOnWith C f s :=
  Convex.lipschitz_on_with_of_nnnorm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivWithinAt)
    (fun x hx =>
      le_transₓ
        (by
          simp )
        (bound x hx))
    hs

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function within
this set is bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv_within` -/
theorem norm_image_sub_le_of_norm_deriv_within_le {C : ℝ} (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀, ∀ x ∈ s, ∀, ∥derivWithin f s x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∥f y - f x∥ ≤ C * ∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_deriv_within_le (fun x hx => (hf x hx).HasDerivWithinAt) bound xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv_within` and `lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_deriv_within_le {C : ℝ≥0 } (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀, ∀ x ∈ s, ∀, ∥derivWithin f s x∥₊ ≤ C) : LipschitzOnWith C f s :=
  hs.lipschitz_on_with_of_nnnorm_has_deriv_within_le (fun x hx => (hf x hx).HasDerivWithinAt) bound

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv`. -/
theorem norm_image_sub_le_of_norm_deriv_le {C : ℝ} (hf : ∀, ∀ x ∈ s, ∀, DifferentiableAt 𝕜 f x)
    (bound : ∀, ∀ x ∈ s, ∀, ∥deriv f x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_deriv_within_le (fun x hx => (hf x hx).HasDerivAt.HasDerivWithinAt) bound xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv` and `lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_deriv_le {C : ℝ≥0 } (hf : ∀, ∀ x ∈ s, ∀, DifferentiableAt 𝕜 f x)
    (bound : ∀, ∀ x ∈ s, ∀, ∥deriv f x∥₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitz_on_with_of_nnnorm_has_deriv_within_le (fun x hx => (hf x hx).HasDerivAt.HasDerivWithinAt) bound

/-- The mean value theorem set in dimension 1: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz.  Version with `deriv` and `lipschitz_with`. -/
theorem _root_.lipschitz_with_of_nnnorm_deriv_le {C : ℝ≥0 } (hf : Differentiable 𝕜 f) (bound : ∀ x, ∥deriv f x∥₊ ≤ C) :
    LipschitzWith C f :=
  lipschitz_on_univ.1 <| convex_univ.lipschitz_on_with_of_nnnorm_deriv_le (fun x hx => hf x) fun x hx => bound x

/-- If `f : 𝕜 → G`, `𝕜 = R` or `𝕜 = ℂ`, is differentiable everywhere and its derivative equal zero,
then it is a constant function. -/
theorem _root_.is_const_of_deriv_eq_zero (hf : Differentiable 𝕜 f) (hf' : ∀ x, deriv f x = 0) (x y : 𝕜) : f x = f y :=
  is_const_of_fderiv_eq_zero hf
    (fun z => by
      ext
      simp [deriv_fderiv, ← hf'])
    _ _

end Convex

end

/-! ### Functions `[a, b] → ℝ`. -/


section Interval

-- Declare all variables here to make sure they come in a correct order
variable (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
  (hff' : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt f (f' x) x) (hfd : DifferentiableOn ℝ f (Ioo a b)) (g g' : ℝ → ℝ)
  (hgc : ContinuousOn g (Icc a b)) (hgg' : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt g (g' x) x)
  (hgd : DifferentiableOn ℝ g (Ioo a b))

include hab hfc hff' hgc hgg'

/-- Cauchy's **Mean Value Theorem**, `has_deriv_at` version. -/
theorem exists_ratio_has_deriv_at_eq_ratio_slope : ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by
  let h := fun x => (g b - g a) * f x - (f b - f a) * g x
  have hI : h a = h b := by
    simp only [← h]
    ring
  let h' := fun x => (g b - g a) * f' x - (f b - f a) * g' x
  have hhh' : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt h (h' x) x := fun x hx =>
    ((hff' x hx).const_mul (g b - g a)).sub ((hgg' x hx).const_mul (f b - f a))
  have hhc : ContinuousOn h (Icc a b) := (continuous_on_const.mul hfc).sub (continuous_on_const.mul hgc)
  rcases exists_has_deriv_at_eq_zero h h' hab hhc hI hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩

omit hfc hgc

/-- Cauchy's **Mean Value Theorem**, extended `has_deriv_at` version. -/
theorem exists_ratio_has_deriv_at_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
    (hff' : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt f (f' x) x) (hgg' : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt g (g' x) x)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga)) (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb))
    (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) : ∃ c ∈ Ioo a b, (lgb - lga) * f' c = (lfb - lfa) * g' c := by
  let h := fun x => (lgb - lga) * f x - (lfb - lfa) * g x
  have hha : tendsto h (𝓝[>] a) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : tendsto h (𝓝[>] a) (𝓝 <| (lgb - lga) * lfa - (lfb - lfa) * lga) :=
      (tendsto_const_nhds.mul hfa).sub (tendsto_const_nhds.mul hga)
    convert this using 2
    ring
  have hhb : tendsto h (𝓝[<] b) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : tendsto h (𝓝[<] b) (𝓝 <| (lgb - lga) * lfb - (lfb - lfa) * lgb) :=
      (tendsto_const_nhds.mul hfb).sub (tendsto_const_nhds.mul hgb)
    convert this using 2
    ring
  let h' := fun x => (lgb - lga) * f' x - (lfb - lfa) * g' x
  have hhh' : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt h (h' x) x := by
    intro x hx
    exact ((hff' x hx).const_mul _).sub ((hgg' x hx).const_mul _)
  rcases exists_has_deriv_at_eq_zero' hab hha hhb hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩

include hfc

omit hgg'

/-- Lagrange's Mean Value Theorem, `has_deriv_at` version -/
theorem exists_has_deriv_at_eq_slope : ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  rcases exists_ratio_has_deriv_at_eq_ratio_slope f f' hab hfc hff' id 1 continuous_id.continuous_on fun x hx =>
      has_deriv_at_id x with
    ⟨c, cmem, hc⟩
  use c, cmem
  simp only [← _root_.id, ← Pi.one_apply, ← mul_oneₓ] at hc
  rw [← hc, mul_div_cancel_left]
  exact ne_of_gtₓ (sub_pos.2 hab)

omit hff'

/-- Cauchy's Mean Value Theorem, `deriv` version. -/
theorem exists_ratio_deriv_eq_ratio_slope : ∃ c ∈ Ioo a b, (g b - g a) * deriv f c = (f b - f a) * deriv g c :=
  (exists_ratio_has_deriv_at_eq_ratio_slope f (deriv f) hab hfc
      (fun x hx => ((hfd x hx).DifferentiableAt <| IsOpen.mem_nhds is_open_Ioo hx).HasDerivAt) g (deriv g) hgc)
    fun x hx => ((hgd x hx).DifferentiableAt <| IsOpen.mem_nhds is_open_Ioo hx).HasDerivAt

omit hfc

/-- Cauchy's Mean Value Theorem, extended `deriv` version. -/
theorem exists_ratio_deriv_eq_ratio_slope' {lfa lga lfb lgb : ℝ} (hdf : DifferentiableOn ℝ f <| Ioo a b)
    (hdg : DifferentiableOn ℝ g <| Ioo a b) (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    ∃ c ∈ Ioo a b, (lgb - lga) * deriv f c = (lfb - lfa) * deriv g c :=
  exists_ratio_has_deriv_at_eq_ratio_slope' _ _ hab _ _
    (fun x hx => ((hdf x hx).DifferentiableAt <| Ioo_mem_nhds hx.1 hx.2).HasDerivAt)
    (fun x hx => ((hdg x hx).DifferentiableAt <| Ioo_mem_nhds hx.1 hx.2).HasDerivAt) hfa hga hfb hgb

/-- Lagrange's **Mean Value Theorem**, `deriv` version. -/
theorem exists_deriv_eq_slope : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_has_deriv_at_eq_slope f (deriv f) hab hfc fun x hx =>
    ((hfd x hx).DifferentiableAt <| IsOpen.mem_nhds is_open_Ioo hx).HasDerivAt

end Interval

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » D)
/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C < f'`, then
`f` grows faster than `C * x` on `D`, i.e., `C * (y - x) < f y - f x` whenever `x, y ∈ D`,
`x < y`. -/
theorem Convex.mul_sub_lt_image_sub_of_lt_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (Interior D)) {C} (hf'_gt : ∀, ∀ x ∈ Interior D, ∀, C < deriv f x) :
    ∀ (x y) (_ : x ∈ D) (_ : y ∈ D), x < y → C * (y - x) < f y - f x := by
  intro x hx y hy hxy
  have hxyD : Icc x y ⊆ D := hD.ord_connected.out hx hy
  have hxyD' : Ioo x y ⊆ Interior D := subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x)
  exact exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
  have : C < (f y - f x) / (y - x) := by
    rw [← ha]
    exact hf'_gt _ (hxyD' a_mem)
  exact (lt_div_iff (sub_pos.2 hxy)).1 this

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C < f'`, then `f` grows faster than
`C * x`, i.e., `C * (y - x) < f y - f x` whenever `x < y`. -/
theorem mul_sub_lt_image_sub_of_lt_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C} (hf'_gt : ∀ x, C < deriv f x) ⦃x y⦄
    (hxy : x < y) : C * (y - x) < f y - f x :=
  convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.Continuous.ContinuousOn hf.DifferentiableOn (fun x _ => hf'_gt x) x
    trivialₓ y trivialₓ hxy

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » D)
/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C ≤ f'`, then
`f` grows at least as fast as `C * x` on `D`, i.e., `C * (y - x) ≤ f y - f x` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem Convex.mul_sub_le_image_sub_of_le_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (Interior D)) {C} (hf'_ge : ∀, ∀ x ∈ Interior D, ∀, C ≤ deriv f x) :
    ∀ (x y) (_ : x ∈ D) (_ : y ∈ D), x ≤ y → C * (y - x) ≤ f y - f x := by
  intro x hx y hy hxy
  cases' eq_or_lt_of_le hxy with hxy' hxy'
  · rw [hxy', sub_self, sub_self, mul_zero]
    
  have hxyD : Icc x y ⊆ D := hD.ord_connected.out hx hy
  have hxyD' : Ioo x y ⊆ Interior D := subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x)
  exact exists_deriv_eq_slope f hxy' (hf.mono hxyD) (hf'.mono hxyD')
  have : C ≤ (f y - f x) / (y - x) := by
    rw [← ha]
    exact hf'_ge _ (hxyD' a_mem)
  exact (le_div_iff (sub_pos.2 hxy')).1 this

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C ≤ f'`, then `f` grows at least as fast
as `C * x`, i.e., `C * (y - x) ≤ f y - f x` whenever `x ≤ y`. -/
theorem mul_sub_le_image_sub_of_le_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C} (hf'_ge : ∀ x, C ≤ deriv f x) ⦃x y⦄
    (hxy : x ≤ y) : C * (y - x) ≤ f y - f x :=
  convex_univ.mul_sub_le_image_sub_of_le_deriv hf.Continuous.ContinuousOn hf.DifferentiableOn (fun x _ => hf'_ge x) x
    trivialₓ y trivialₓ hxy

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » D)
/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' < C`, then
`f` grows slower than `C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x, y ∈ D`,
`x < y`. -/
theorem Convex.image_sub_lt_mul_sub_of_deriv_lt {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (Interior D)) {C} (lt_hf' : ∀, ∀ x ∈ Interior D, ∀, deriv f x < C) :
    ∀ (x y) (_ : x ∈ D) (_ : y ∈ D), x < y → f y - f x < C * (y - x) := by
  intro x hx y hy hxy
  have hf'_gt : ∀, ∀ x ∈ Interior D, ∀, -C < deriv (fun y => -f y) x := by
    intro x hx
    rw [deriv.neg, neg_lt_neg_iff]
    exact lt_hf' x hx
  simpa [-neg_lt_neg_iff] using neg_lt_neg (hD.mul_sub_lt_image_sub_of_lt_deriv hf.neg hf'.neg hf'_gt x hx y hy hxy)

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' < C`, then `f` grows slower than
`C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x < y`. -/
theorem image_sub_lt_mul_sub_of_deriv_lt {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C} (lt_hf' : ∀ x, deriv f x < C) ⦃x y⦄
    (hxy : x < y) : f y - f x < C * (y - x) :=
  convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.Continuous.ContinuousOn hf.DifferentiableOn (fun x _ => lt_hf' x) x
    trivialₓ y trivialₓ hxy

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » D)
/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' ≤ C`, then
`f` grows at most as fast as `C * x` on `D`, i.e., `f y - f x ≤ C * (y - x)` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem Convex.image_sub_le_mul_sub_of_deriv_le {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (Interior D)) {C} (le_hf' : ∀, ∀ x ∈ Interior D, ∀, deriv f x ≤ C) :
    ∀ (x y) (_ : x ∈ D) (_ : y ∈ D), x ≤ y → f y - f x ≤ C * (y - x) := by
  intro x hx y hy hxy
  have hf'_ge : ∀, ∀ x ∈ Interior D, ∀, -C ≤ deriv (fun y => -f y) x := by
    intro x hx
    rw [deriv.neg, neg_le_neg_iff]
    exact le_hf' x hx
  simpa [-neg_le_neg_iff] using neg_le_neg (hD.mul_sub_le_image_sub_of_le_deriv hf.neg hf'.neg hf'_ge x hx y hy hxy)

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' ≤ C`, then `f` grows at most as fast
as `C * x`, i.e., `f y - f x ≤ C * (y - x)` whenever `x ≤ y`. -/
theorem image_sub_le_mul_sub_of_deriv_le {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C} (le_hf' : ∀ x, deriv f x ≤ C) ⦃x y⦄
    (hxy : x ≤ y) : f y - f x ≤ C * (y - x) :=
  convex_univ.image_sub_le_mul_sub_of_deriv_le hf.Continuous.ContinuousOn hf.DifferentiableOn (fun x _ => le_hf' x) x
    trivialₓ y trivialₓ hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is positive, then
`f` is a strictly monotone function on `D`.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly positive. -/
theorem Convex.strict_mono_on_of_deriv_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : ∀, ∀ x ∈ Interior D, ∀, 0 < deriv f x) : StrictMonoOn f D := by
  rintro x hx y hy
  simpa only [← zero_mul, ← sub_pos] using hD.mul_sub_lt_image_sub_of_lt_deriv hf _ hf' x hx y hy
  exact fun z hz => (differentiable_at_of_deriv_ne_zero (hf' z hz).ne').DifferentiableWithinAt

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is positive, then
`f` is a strictly monotone function.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly positive. -/
theorem strict_mono_of_deriv_pos {f : ℝ → ℝ} (hf' : ∀ x, 0 < deriv f x) : StrictMono f :=
  strict_mono_on_univ.1 <|
    convex_univ.strict_mono_on_of_deriv_pos
      (fun z _ => (differentiable_at_of_deriv_ne_zero (hf' z).ne').DifferentiableWithinAt.ContinuousWithinAt) fun x _ =>
      hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotone function on `D`. -/
theorem Convex.monotone_on_of_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (Interior D)) (hf'_nonneg : ∀, ∀ x ∈ Interior D, ∀, 0 ≤ deriv f x) : MonotoneOn f D :=
  fun x hx y hy hxy => by
  simpa only [← zero_mul, ← sub_nonneg] using hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg x hx y hy hxy

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotone function. -/
theorem monotone_of_deriv_nonneg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, 0 ≤ deriv f x) : Monotone f :=
  monotone_on_univ.1 <|
    convex_univ.monotone_on_of_deriv_nonneg hf.Continuous.ContinuousOn hf.DifferentiableOn fun x _ => hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is negative, then
`f` is a strictly antitone function on `D`. -/
theorem Convex.strict_anti_on_of_deriv_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : ∀, ∀ x ∈ Interior D, ∀, deriv f x < 0) : StrictAntiOn f D := fun x hx y => by
  simpa only [← zero_mul, ← sub_lt_zero] using
    hD.image_sub_lt_mul_sub_of_deriv_lt hf
      (fun z hz => (differentiable_at_of_deriv_ne_zero (hf' z hz).Ne).DifferentiableWithinAt) hf' x hx y

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is negative, then
`f` is a strictly antitone function.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly negative. -/
theorem strict_anti_of_deriv_neg {f : ℝ → ℝ} (hf' : ∀ x, deriv f x < 0) : StrictAnti f :=
  strict_anti_on_univ.1 <|
    convex_univ.strict_anti_on_of_deriv_neg
      (fun z _ => (differentiable_at_of_deriv_ne_zero (hf' z).Ne).DifferentiableWithinAt.ContinuousWithinAt) fun x _ =>
      hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is an antitone function on `D`. -/
theorem Convex.antitone_on_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (Interior D)) (hf'_nonpos : ∀, ∀ x ∈ Interior D, ∀, deriv f x ≤ 0) : AntitoneOn f D :=
  fun x hx y hy hxy => by
  simpa only [← zero_mul, ← sub_nonpos] using hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos x hx y hy hxy

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then
`f` is an antitone function. -/
theorem antitone_of_deriv_nonpos {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, deriv f x ≤ 0) : Antitone f :=
  antitone_on_univ.1 <|
    convex_univ.antitone_on_of_deriv_nonpos hf.Continuous.ContinuousOn hf.DifferentiableOn fun x _ => hf' x

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is monotone on the interior, then `f` is convex on `D`. -/
theorem MonotoneOn.convex_on_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (Interior D)) (hf'_mono : MonotoneOn (deriv f) (Interior D)) : ConvexOn ℝ D f :=
  convex_on_of_slope_mono_adjacent hD
    (by
      intro x y z hx hz hxy hyz
      -- First we prove some trivial inclusions
      have hxzD : Icc x z ⊆ D := hD.ord_connected.out hx hz
      have hxyD : Icc x y ⊆ D := subset.trans (Icc_subset_Icc_right <| le_of_ltₓ hyz) hxzD
      have hxyD' : Ioo x y ⊆ Interior D := subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩
      have hyzD : Icc y z ⊆ D := subset.trans (Icc_subset_Icc_left <| le_of_ltₓ hxy) hxzD
      have hyzD' : Ioo y z ⊆ Interior D := subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hyzD⟩
      -- Then we apply MVT to both `[x, y]` and `[y, z]`
      obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x)
      exact exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
      obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b = (f z - f y) / (z - y)
      exact exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD')
      rw [← ha, ← hb]
      exact hf'_mono (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb).le)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is antitone on the interior, then `f` is concave on `D`. -/
theorem AntitoneOn.concave_on_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (Interior D)) (h_anti : AntitoneOn (deriv f) (Interior D)) : ConcaveOn ℝ D f := by
  have : MonotoneOn (deriv (-f)) (Interior D) := by
    intro x hx y hy hxy
    convert neg_le_neg (h_anti hx hy hxy) <;> convert deriv.neg
  exact neg_convex_on_iff.mp (this.convex_on_of_deriv hD hf.neg hf'.neg)

theorem StrictMonoOn.exists_slope_lt_deriv_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y)) (hxy : x < y)
    (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀, ∀ w ∈ Ioo x y, ∀, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiable_at_of_deriv_ne_zero (h w wmem)).DifferentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x)
  exact exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hay with ⟨b, ⟨hab, hby⟩⟩
  refine' ⟨b, ⟨hxa.trans hab, hby⟩, _⟩
  rw [← ha]
  exact hf'_mono ⟨hxa, hay⟩ ⟨hxa.trans hab, hby⟩ hab

theorem StrictMonoOn.exists_slope_lt_deriv {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y)) (hxy : x < y)
    (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) : ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  by_cases' h : ∀, ∀ w ∈ Ioo x y, ∀, deriv f w ≠ 0
  · apply StrictMonoOn.exists_slope_lt_deriv_aux hf hxy hf'_mono h
    
  · push_neg  at h
    rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ (a : ℝ)(H : a ∈ Ioo x w), (f w - f x) / (w - x) < deriv f a := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
        
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
        
      · intro z hz
        rw [← hw]
        apply ne_of_ltₓ
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
        
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ (b : ℝ)(H : b ∈ Ioo w y), (f y - f w) / (y - w) < deriv f b := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hwy _ _
      · refine' hf.mono (Icc_subset_Icc hxw.le le_rfl)
        
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
        
      · intro z hz
        rw [← hw]
        apply ne_of_gtₓ
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
        
    refine' ⟨b, ⟨hxw.trans hwb, hby⟩, _⟩
    simp only [← div_lt_iff, ← hxy, ← hxw, ← hwy, ← sub_pos] at ha hb⊢
    have : deriv f a * (w - x) < deriv f b * (w - x) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hxw) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
        
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
        
    linarith
    

theorem StrictMonoOn.exists_deriv_lt_slope_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y)) (hxy : x < y)
    (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀, ∀ w ∈ Ioo x y, ∀, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiable_at_of_deriv_ne_zero (h w wmem)).DifferentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x)
  exact exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hxa with ⟨b, ⟨hxb, hba⟩⟩
  refine' ⟨b, ⟨hxb, hba.trans hay⟩, _⟩
  rw [← ha]
  exact hf'_mono ⟨hxb, hba.trans hay⟩ ⟨hxa, hay⟩ hba

theorem StrictMonoOn.exists_deriv_lt_slope {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y)) (hxy : x < y)
    (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) : ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  by_cases' h : ∀, ∀ w ∈ Ioo x y, ∀, deriv f w ≠ 0
  · apply StrictMonoOn.exists_deriv_lt_slope_aux hf hxy hf'_mono h
    
  · push_neg  at h
    rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ (a : ℝ)(H : a ∈ Ioo x w), deriv f a < (f w - f x) / (w - x) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
        
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
        
      · intro z hz
        rw [← hw]
        apply ne_of_ltₓ
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
        
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ (b : ℝ)(H : b ∈ Ioo w y), deriv f b < (f y - f w) / (y - w) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hwy _ _
      · refine' hf.mono (Icc_subset_Icc hxw.le le_rfl)
        
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
        
      · intro z hz
        rw [← hw]
        apply ne_of_gtₓ
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
        
    refine' ⟨a, ⟨hxa, haw.trans hwy⟩, _⟩
    simp only [← lt_div_iff, ← hxy, ← hxw, ← hwy, ← sub_pos] at ha hb⊢
    have : deriv f a * (y - w) < deriv f b * (y - w) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hwy) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
        
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
        
    linarith
    

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, and `f'` is strictly monotone on the
interior, then `f` is strictly convex on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
theorem StrictMonoOn.strict_convex_on_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : StrictMonoOn (deriv f) (Interior D)) : StrictConvexOn ℝ D f :=
  strict_convex_on_of_slope_strict_mono_adjacent hD
    (by
      intro x y z hx hz hxy hyz
      -- First we prove some trivial inclusions
      have hxzD : Icc x z ⊆ D := hD.ord_connected.out hx hz
      have hxyD : Icc x y ⊆ D := subset.trans (Icc_subset_Icc_right <| le_of_ltₓ hyz) hxzD
      have hxyD' : Ioo x y ⊆ Interior D := subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩
      have hyzD : Icc y z ⊆ D := subset.trans (Icc_subset_Icc_left <| le_of_ltₓ hxy) hxzD
      have hyzD' : Ioo y z ⊆ Interior D := subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hyzD⟩
      -- Then we get points `a` and `b` in each interval `[x, y]` and `[y, z]` where the derivatives
      -- can be compared to the slopes between `x, y` and `y, z` respectively.
      obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a
      exact StrictMonoOn.exists_slope_lt_deriv (hf.mono hxyD) hxy (hf'.mono hxyD')
      obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b < (f z - f y) / (z - y)
      exact StrictMonoOn.exists_deriv_lt_slope (hf.mono hyzD) hyz (hf'.mono hyzD')
      apply ha.trans (lt_transₓ _ hb)
      exact hf' (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb))

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f'` is strictly antitone on the
interior, then `f` is strictly concave on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
theorem StrictAntiOn.strict_concave_on_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (h_anti : StrictAntiOn (deriv f) (Interior D)) : StrictConcaveOn ℝ D f := by
  have : StrictMonoOn (deriv (-f)) (Interior D) := by
    intro x hx y hy hxy
    convert neg_lt_neg (h_anti hx hy hxy) <;> convert deriv.neg
  exact neg_strict_convex_on_iff.mp (this.strict_convex_on_of_deriv hD hf.neg)

/-- If a function `f` is differentiable and `f'` is monotone on `ℝ` then `f` is convex. -/
theorem Monotone.convex_on_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf'_mono : Monotone (deriv f)) :
    ConvexOn ℝ Univ f :=
  (hf'_mono.MonotoneOn _).convex_on_of_deriv convex_univ hf.Continuous.ContinuousOn hf.DifferentiableOn

/-- If a function `f` is differentiable and `f'` is antitone on `ℝ` then `f` is concave. -/
theorem Antitone.concave_on_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf'_anti : Antitone (deriv f)) :
    ConcaveOn ℝ Univ f :=
  (hf'_anti.AntitoneOn _).concave_on_of_deriv convex_univ hf.Continuous.ContinuousOn hf.DifferentiableOn

/-- If a function `f` is continuous and `f'` is strictly monotone on `ℝ` then `f` is strictly
convex. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
theorem StrictMono.strict_convex_on_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f) (hf'_mono : StrictMono (deriv f)) :
    StrictConvexOn ℝ Univ f :=
  (hf'_mono.StrictMonoOn _).strict_convex_on_of_deriv convex_univ hf.ContinuousOn

/-- If a function `f` is continuous and `f'` is strictly antitone on `ℝ` then `f` is strictly
concave. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
theorem StrictAnti.strict_concave_on_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f) (hf'_anti : StrictAnti (deriv f)) :
    StrictConcaveOn ℝ Univ f :=
  (hf'_anti.StrictAntiOn _).strict_concave_on_of_deriv convex_univ hf.ContinuousOn

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
theorem convex_on_of_deriv2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (Interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (Interior D))
    (hf''_nonneg : ∀, ∀ x ∈ Interior D, ∀, 0 ≤ (deriv^[2]) f x) : ConvexOn ℝ D f :=
  (hD.Interior.monotone_on_of_deriv_nonneg hf''.ContinuousOn
          (by
            rwa [interior_interior]) <|
        by
        rwa [interior_interior]).convex_on_of_deriv
    hD hf hf'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
theorem concave_on_of_deriv2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (Interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (Interior D))
    (hf''_nonpos : ∀, ∀ x ∈ Interior D, ∀, (deriv^[2]) f x ≤ 0) : ConcaveOn ℝ D f :=
  (hD.Interior.antitone_on_of_deriv_nonpos hf''.ContinuousOn
          (by
            rwa [interior_interior]) <|
        by
        rwa [interior_interior]).concave_on_of_deriv
    hD hf hf'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on the
interior, then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strict_convex_on_of_deriv2_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf'' : ∀, ∀ x ∈ Interior D, ∀, 0 < ((deriv^[2]) f) x) : StrictConvexOn ℝ D f :=
  ((hD.Interior.strict_mono_on_of_deriv_pos fun z hz =>
          (differentiable_at_of_deriv_ne_zero (hf'' z hz).ne').DifferentiableWithinAt.ContinuousWithinAt) <|
        by
        rwa [interior_interior]).strict_convex_on_of_deriv
    hD hf

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on the
interior, then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strict_concave_on_of_deriv2_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf'' : ∀, ∀ x ∈ Interior D, ∀, (deriv^[2]) f x < 0) : StrictConcaveOn ℝ D f :=
  ((hD.Interior.strict_anti_on_of_deriv_neg fun z hz =>
          (differentiable_at_of_deriv_ne_zero (hf'' z hz).Ne).DifferentiableWithinAt.ContinuousWithinAt) <|
        by
        rwa [interior_interior]).strict_concave_on_of_deriv
    hD hf

/-- If a function `f` is twice differentiable on a open convex set `D ⊆ ℝ` and
`f''` is nonnegative on `D`, then `f` is convex on `D`. -/
theorem convex_on_of_deriv2_nonneg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf' : DifferentiableOn ℝ f D)
    (hf'' : DifferentiableOn ℝ (deriv f) D) (hf''_nonneg : ∀, ∀ x ∈ D, ∀, 0 ≤ ((deriv^[2]) f) x) : ConvexOn ℝ D f :=
  convex_on_of_deriv2_nonneg hD hf'.ContinuousOn (hf'.mono interior_subset) (hf''.mono interior_subset) fun x hx =>
    hf''_nonneg x (interior_subset hx)

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonpositive on `D`, then `f` is concave on `D`. -/
theorem concave_on_of_deriv2_nonpos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf' : DifferentiableOn ℝ f D)
    (hf'' : DifferentiableOn ℝ (deriv f) D) (hf''_nonpos : ∀, ∀ x ∈ D, ∀, (deriv^[2]) f x ≤ 0) : ConcaveOn ℝ D f :=
  concave_on_of_deriv2_nonpos hD hf'.ContinuousOn (hf'.mono interior_subset) (hf''.mono interior_subset) fun x hx =>
    hf''_nonpos x (interior_subset hx)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on `D`,
then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strict_convex_on_of_deriv2_pos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf'' : ∀, ∀ x ∈ D, ∀, 0 < ((deriv^[2]) f) x) : StrictConvexOn ℝ D f :=
  (strict_convex_on_of_deriv2_pos hD hf) fun x hx => hf'' x (interior_subset hx)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on `D`,
then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strict_concave_on_of_deriv2_neg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf'' : ∀, ∀ x ∈ D, ∀, (deriv^[2]) f x < 0) : StrictConcaveOn ℝ D f :=
  (strict_concave_on_of_deriv2_neg hD hf) fun x hx => hf'' x (interior_subset hx)

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ`,
then `f` is convex on `ℝ`. -/
theorem convex_on_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : Differentiable ℝ f) (hf'' : Differentiable ℝ (deriv f))
    (hf''_nonneg : ∀ x, 0 ≤ ((deriv^[2]) f) x) : ConvexOn ℝ Univ f :=
  convex_on_of_deriv2_nonneg' convex_univ hf'.DifferentiableOn hf''.DifferentiableOn fun x _ => hf''_nonneg x

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonpositive on `ℝ`,
then `f` is concave on `ℝ`. -/
theorem concave_on_univ_of_deriv2_nonpos {f : ℝ → ℝ} (hf' : Differentiable ℝ f) (hf'' : Differentiable ℝ (deriv f))
    (hf''_nonpos : ∀ x, (deriv^[2]) f x ≤ 0) : ConcaveOn ℝ Univ f :=
  concave_on_of_deriv2_nonpos' convex_univ hf'.DifferentiableOn hf''.DifferentiableOn fun x _ => hf''_nonpos x

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly positive on `ℝ`,
then `f` is strictly convex on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point.  -/
theorem strict_convex_on_univ_of_deriv2_pos {f : ℝ → ℝ} (hf : Continuous f) (hf'' : ∀ x, 0 < ((deriv^[2]) f) x) :
    StrictConvexOn ℝ Univ f :=
  (strict_convex_on_of_deriv2_pos' convex_univ hf.ContinuousOn) fun x _ => hf'' x

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly negative on `ℝ`,
then `f` is strictly concave on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point.  -/
theorem strict_concave_on_univ_of_deriv2_neg {f : ℝ → ℝ} (hf : Continuous f) (hf'' : ∀ x, (deriv^[2]) f x < 0) :
    StrictConcaveOn ℝ Univ f :=
  (strict_concave_on_of_deriv2_neg' convex_univ hf.ContinuousOn) fun x _ => hf'' x

/-! ### Functions `f : E → ℝ` -/


/-- Lagrange's Mean Value Theorem, applied to convex domains. -/
theorem domain_mvt {f : E → ℝ} {s : Set E} {x y : E} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀, ∀ x ∈ s, ∀, HasFderivWithinAt f (f' x) s x) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∃ z ∈ Segment ℝ x y, f y - f x = f' z (y - x) := by
  have hIccIoo := @Ioo_subset_Icc_self ℝ _ 0 1
  -- parametrize segment
  set g : ℝ → E := fun t => x + t • (y - x)
  have hseg : ∀, ∀ t ∈ Icc (0 : ℝ) 1, ∀, g t ∈ Segment ℝ x y := by
    rw [segment_eq_image']
    simp only [← mem_image, ← and_imp, ← add_right_injₓ]
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hseg' : Icc 0 1 ⊆ g ⁻¹' s := by
    rw [← image_subset_iff]
    unfold image
    change ∀ _, _
    intro z Hz
    rw [mem_set_of_eq] at Hz
    rcases Hz with ⟨t, Ht, hgt⟩
    rw [← hgt]
    exact hs.segment_subset xs ys (hseg t Ht)
  -- derivative of pullback of f under parametrization
  have hfg : ∀, ∀ t ∈ Icc (0 : ℝ) 1, ∀, HasDerivWithinAt (f ∘ g) ((f' (g t) : E → ℝ) (y - x)) (Icc (0 : ℝ) 1) t := by
    intro t Ht
    have hg : HasDerivAt g (y - x) t := by
      have := ((has_deriv_at_id t).smul_const (y - x)).const_add x
      rwa [one_smul] at this
    exact (hf (g t) <| hseg' Ht).comp_has_deriv_within_at _ hg.has_deriv_within_at hseg'
  -- apply 1-variable mean value theorem to pullback
  have hMVT : ∃ t ∈ Ioo (0 : ℝ) 1, (f' (g t) : E → ℝ) (y - x) = (f (g 1) - f (g 0)) / (1 - 0) := by
    refine'
      exists_has_deriv_at_eq_slope (f ∘ g) _
        (by
          norm_num)
        _ _
    · exact fun t Ht => (hfg t Ht).ContinuousWithinAt
      
    · exact fun t Ht => (hfg t <| hIccIoo Ht).HasDerivAt (Icc_mem_nhds Ht.1 Ht.2)
      
  -- reinterpret on domain
  rcases hMVT with ⟨t, Ht, hMVT'⟩
  use g t
  refine' ⟨hseg t <| hIccIoo Ht, _⟩
  simp [← g, ← hMVT']

section IsROrC

/-!
### Vector-valued functions `f : E → F`.  Strict differentiability.

A `C^1` function is strictly differentiable, when the field is `ℝ` or `ℂ`. This follows from the
mean value inequality on balls, which is a particular case of the above results after restricting
the scalars to `ℝ`. Note that it does not make sense to talk of a convex set over `ℂ`, but balls
make sense and are enough. Many formulations of the mean value inequality could be generalized to
balls over `ℝ` or `ℂ`. For now, we only include the ones that we need.
-/


variable {𝕜 : Type _} [IsROrC 𝕜] {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G] {H : Type _} [NormedGroup H]
  [NormedSpace 𝕜 H] {f : G → H} {f' : G → G →L[𝕜] H} {x : G}

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
theorem has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at (hder : ∀ᶠ y in 𝓝 x, HasFderivAt f (f' y) y)
    (hcont : ContinuousAt f' x) : HasStrictFderivAt f (f' x) x := by
  -- turn little-o definition of strict_fderiv into an epsilon-delta statement
  refine' is_o_iff.mpr fun c hc => metric.eventually_nhds_iff_ball.mpr _
  -- the correct ε is the modulus of continuity of f'
  rcases metric.mem_nhds_iff.mp (inter_mem hder (hcont <| ball_mem_nhds _ hc)) with ⟨ε, ε0, hε⟩
  refine' ⟨ε, ε0, _⟩
  -- simplify formulas involving the product E × E
  rintro ⟨a, b⟩ h
  rw [← ball_prod_same, prod_mk_mem_set_prod_eq] at h
  -- exploit the choice of ε as the modulus of continuity of f'
  have hf' : ∀, ∀ x' ∈ ball x ε, ∀, ∥f' x' - f' x∥ ≤ c := by
    intro x' H'
    rw [← dist_eq_norm]
    exact le_of_ltₓ (hε H').2
  -- apply mean value theorem
  let this : NormedSpace ℝ G := RestrictScalars.normedSpace ℝ 𝕜 G
  refine' (convex_ball _ _).norm_image_sub_le_of_norm_has_fderiv_within_le' _ hf' h.2 h.1
  exact fun y hy => (hε hy).1.HasFderivWithinAt

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
theorem has_strict_deriv_at_of_has_deriv_at_of_continuous_at {f f' : 𝕜 → G} {x : 𝕜}
    (hder : ∀ᶠ y in 𝓝 x, HasDerivAt f (f' y) y) (hcont : ContinuousAt f' x) : HasStrictDerivAt f (f' x) x :=
  has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at (hder.mono fun y hy => hy.HasFderivAt) <|
    (smulRightL 𝕜 𝕜 G 1).Continuous.ContinuousAt.comp hcont

end IsROrC

