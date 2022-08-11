/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.Calculus.Deriv
import Mathbin.Analysis.Calculus.MeanValue
import Mathbin.Analysis.Convex.Topology

/-!
# Symmetry of the second derivative

We show that, over the reals, the second derivative is symmetric.

The most precise result is `convex.second_derivative_within_at_symmetric`. It asserts that,
if a function is differentiable inside a convex set `s` with nonempty interior, and has a second
derivative within `s` at a point `x`, then this second derivative at `x` is symmetric. Note that
this result does not require continuity of the first derivative.

The following particular cases of this statement are especially relevant:

`second_derivative_symmetric_of_eventually` asserts that, if a function is differentiable on a
neighborhood of `x`, and has a second derivative at `x`, then this second derivative is symmetric.

`second_derivative_symmetric` asserts that, if a function is differentiable, and has a second
derivative at `x`, then this second derivative is symmetric.

## Implementation note

For the proof, we obtain an asymptotic expansion to order two of `f (x + v + w) - f (x + v)`, by
using the mean value inequality applied to a suitable function along the
segment `[x + v, x + v + w]`. This expansion involves `f'' ⬝ w` as we move along a segment directed
by `w` (see `convex.taylor_approx_two_segment`).

Consider the alternate sum `f (x + v + w) + f x - f (x + v) - f (x + w)`, corresponding to the
values of `f` along a rectangle based at `x` with sides `v` and `w`. One can write it using the two
sides directed by `w`, as `(f (x + v + w) - f (x + v)) - (f (x + w) - f x)`. Together with the
previous asymptotic expansion, one deduces that it equals `f'' v w + o(1)` when `v, w` tends to `0`.
Exchanging the roles of `v` and `w`, one instead gets an asymptotic expansion `f'' w v`, from which
the equality `f'' v w = f'' w v` follows.

In our most general statement, we only assume that `f` is differentiable inside a convex set `s`, so
a few modifications have to be made. Since we don't assume continuity of `f` at `x`, we consider
instead the rectangle based at `x + v + w` with sides `v` and `w`,
in `convex.is_o_alternate_sum_square`, but the argument is essentially the same. It only works
when `v` and `w` both point towards the interior of `s`, to make sure that all the sides of the
rectangle are contained in `s` by convexity. The general case follows by linearity, though.
-/


open Asymptotics Set

open TopologicalSpace

variable {E F : Type _} [NormedGroup E] [NormedSpace ℝ E] [NormedGroup F] [NormedSpace ℝ F] {s : Set E}
  (s_conv : Convex ℝ s) {f : E → F} {f' : E → E →L[ℝ] F} {f'' : E →L[ℝ] E →L[ℝ] F}
  (hf : ∀, ∀ x ∈ Interior s, ∀, HasFderivAt f (f' x) x) {x : E} (xs : x ∈ s)
  (hx : HasFderivWithinAt f' f'' (Interior s) x)

include s_conv xs hx hf

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- Assume that `f` is differentiable inside a convex set `s`, and that its derivative `f'` is
differentiable at a point `x`. Then, given two vectors `v` and `w` pointing inside `s`, one can
Taylor-expand to order two the function `f` on the segment `[x + h v, x + h (v + w)]`, giving a
bilinear estimate for `f (x + hv + hw) - f (x + hv)` in terms of `f' w` and of `f'' ⬝ w`, up to
`o(h^2)`.

This is a technical statement used to show that the second derivative is symmetric.
-/
theorem Convex.taylor_approx_two_segment {v w : E} (hv : x + v ∈ Interior s) (hw : x + v + w ∈ Interior s) :
    (fun h : ℝ =>
        f (x + h • v + h • w) - f (x + h • v) - h • f' x w - h ^ 2 • f'' v w - (h ^ 2 / 2) • f'' w w) =o[𝓝[>] 0]
      fun h => h ^ 2 :=
  by
  -- it suffices to check that the expression is bounded by `ε * ((∥v∥ + ∥w∥) * ∥w∥) * h^2` for
  -- small enough `h`, for any positive `ε`.
  apply is_o.trans_is_O (is_o_iff.2 fun ε εpos => _) (is_O_const_mul_self ((∥v∥ + ∥w∥) * ∥w∥) _ _)
  -- consider a ball of radius `δ` around `x` in which the Taylor approximation for `f''` is
  -- good up to `δ`.
  rw [HasFderivWithinAt, HasFderivAtFilter, is_o_iff] at hx
  rcases Metric.mem_nhds_within_iff.1 (hx εpos) with ⟨δ, δpos, sδ⟩
  have E1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), h * (∥v∥ + ∥w∥) < δ := by
    have : Filter.Tendsto (fun h => h * (∥v∥ + ∥w∥)) (𝓝[>] (0 : ℝ)) (𝓝 (0 * (∥v∥ + ∥w∥))) :=
      (continuous_id.mul continuous_const).ContinuousWithinAt
    apply (tendsto_order.1 this).2 δ
    simpa only [← zero_mul] using δpos
  have E2 : ∀ᶠ h in 𝓝[>] (0 : ℝ), (h : ℝ) < 1 :=
    mem_nhds_within_Ioi_iff_exists_Ioo_subset.2
      ⟨(1 : ℝ), by
        simp only [← mem_Ioi, ← zero_lt_one], fun x hx => hx.2⟩
  filter_upwards [E1, E2, self_mem_nhds_within] with h hδ h_lt_1 hpos
  -- we consider `h` small enough that all points under consideration belong to this ball,
  -- and also with `0 < h < 1`.
  replace hpos : 0 < h := hpos
  have xt_mem : ∀, ∀ t ∈ Icc (0 : ℝ) 1, ∀, x + h • v + (t * h) • w ∈ Interior s := by
    intro t ht
    have : x + h • v ∈ Interior s := s_conv.add_smul_mem_interior xs hv ⟨hpos, h_lt_1.le⟩
    rw [← smul_smul]
    apply s_conv.interior.add_smul_mem this _ ht
    rw [add_assocₓ] at hw
    rw [add_assocₓ, ← smul_add]
    exact s_conv.add_smul_mem_interior xs hw ⟨hpos, h_lt_1.le⟩
  -- define a function `g` on `[0,1]` (identified with `[v, v + w]`) such that `g 1 - g 0` is the
  -- quantity to be estimated. We will check that its derivative is given by an explicit
  -- expression `g'`, that we can bound. Then the desired bound for `g 1 - g 0` follows from the
  -- mean value inequality.
  let g := fun t => f (x + h • v + (t * h) • w) - (t * h) • f' x w - (t * h ^ 2) • f'' v w - ((t * h) ^ 2 / 2) • f'' w w
  set g' := fun t => f' (x + h • v + (t * h) • w) (h • w) - h • f' x w - h ^ 2 • f'' v w - (t * h ^ 2) • f'' w w with
    hg'
  -- check that `g'` is the derivative of `g`, by a straightforward computation
  have g_deriv : ∀, ∀ t ∈ Icc (0 : ℝ) 1, ∀, HasDerivWithinAt g (g' t) (Icc 0 1) t := by
    intro t ht
    apply_rules [HasDerivWithinAt.sub, HasDerivWithinAt.add]
    · refine' (hf _ _).comp_has_deriv_within_at _ _
      · exact xt_mem t ht
        
      apply_rules [HasDerivAt.has_deriv_within_at, HasDerivAt.const_add, HasDerivAt.smul_const, has_deriv_at_mul_const]
      
    · apply_rules [HasDerivAt.has_deriv_within_at, HasDerivAt.smul_const, has_deriv_at_mul_const]
      
    · apply_rules [HasDerivAt.has_deriv_within_at, HasDerivAt.smul_const, has_deriv_at_mul_const]
      
    · suffices H :
        HasDerivWithinAt (fun u => ((u * h) ^ 2 / 2) • f'' w w)
          ((((2 : ℕ) : ℝ) * (t * h) ^ (2 - 1) * (1 * h) / 2) • f'' w w) (Icc 0 1) t
      · convert H using 2
        simp only [← one_mulₓ, ← Nat.cast_bit0, ← pow_oneₓ, ← Nat.cast_oneₓ]
        ring
        
      apply_rules [HasDerivAt.has_deriv_within_at, HasDerivAt.smul_const, has_deriv_at_id', HasDerivAt.pow,
        HasDerivAt.mul_const]
      
  -- check that `g'` is uniformly bounded, with a suitable bound `ε * ((∥v∥ + ∥w∥) * ∥w∥) * h^2`.
  have g'_bound : ∀, ∀ t ∈ Ico (0 : ℝ) 1, ∀, ∥g' t∥ ≤ ε * ((∥v∥ + ∥w∥) * ∥w∥) * h ^ 2 := by
    intro t ht
    have I : ∥h • v + (t * h) • w∥ ≤ h * (∥v∥ + ∥w∥) :=
      calc
        ∥h • v + (t * h) • w∥ ≤ ∥h • v∥ + ∥(t * h) • w∥ := norm_add_le _ _
        _ = h * ∥v∥ + t * (h * ∥w∥) := by
          simp only [← norm_smul, ← Real.norm_eq_abs, ← hpos.le, ← abs_of_nonneg, ← abs_mul, ← ht.left, ← mul_assoc]
        _ ≤ h * ∥v∥ + 1 * (h * ∥w∥) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right ht.2.le (mul_nonneg hpos.le (norm_nonneg _)))
        _ = h * (∥v∥ + ∥w∥) := by
          ring
        
    calc ∥g' t∥ = ∥(f' (x + h • v + (t * h) • w) - f' x - f'' (h • v + (t * h) • w)) (h • w)∥ := by
        rw [hg']
        have : h * (t * h) = t * (h * h) := by
          ring
        simp only [← ContinuousLinearMap.coe_sub', ← ContinuousLinearMap.map_add, ← pow_two, ←
          ContinuousLinearMap.add_apply, ← Pi.smul_apply, ← smul_sub, ← smul_add, ← smul_smul, sub_sub, ←
          ContinuousLinearMap.coe_smul', ← Pi.sub_apply, ← ContinuousLinearMap.map_smul, ←
          this]_ ≤ ∥f' (x + h • v + (t * h) • w) - f' x - f'' (h • v + (t * h) • w)∥ * ∥h • w∥ :=
        ContinuousLinearMap.le_op_norm _ _ _ ≤ ε * ∥h • v + (t * h) • w∥ * ∥h • w∥ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have H : x + h • v + (t * h) • w ∈ Metric.Ball x δ ∩ Interior s := by
          refine' ⟨_, xt_mem t ⟨ht.1, ht.2.le⟩⟩
          rw [add_assocₓ, add_mem_ball_iff_norm]
          exact I.trans_lt hδ
        simpa only [← mem_set_of_eq, ← add_assocₓ x, ← add_sub_cancel'] using
          sδ H _ ≤ ε * (∥h • v∥ + ∥h • w∥) * ∥h • w∥ :=
        by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ εpos.le
        apply (norm_add_le _ _).trans
        refine' add_le_add le_rfl _
        simp only [← norm_smul, ← Real.norm_eq_abs, ← abs_mul, ← abs_of_nonneg, ← ht.1, ← hpos.le, ← mul_assoc]
        exact mul_le_of_le_one_left (mul_nonneg hpos.le (norm_nonneg _)) ht.2.le _ = ε * ((∥v∥ + ∥w∥) * ∥w∥) * h ^ 2 :=
        by
        simp only [← norm_smul, ← Real.norm_eq_abs, ← abs_mul, ← abs_of_nonneg, ← hpos.le]
        ring
  -- conclude using the mean value inequality
  have I : ∥g 1 - g 0∥ ≤ ε * ((∥v∥ + ∥w∥) * ∥w∥) * h ^ 2 := by
    simpa only [← mul_oneₓ, ← sub_zero] using
      norm_image_sub_le_of_norm_deriv_le_segment' g_deriv g'_bound 1 (right_mem_Icc.2 zero_le_one)
  convert I using 1
  · congr 1
    dsimp' only [← g]
    simp only [← Nat.one_ne_zero, ← add_zeroₓ, ← one_mulₓ, ← zero_div, ← zero_mul, ← sub_zero, ← zero_smul, ← Ne.def, ←
      not_false_iff, ← bit0_eq_zero, ← zero_pow']
    abel
    
  · simp only [← Real.norm_eq_abs, ← abs_mul, ← add_nonneg (norm_nonneg v) (norm_nonneg w), ← abs_of_nonneg, ←
      mul_assoc, ← pow_bit0_abs, ← norm_nonneg, ← abs_pow]
    

/-- One can get `f'' v w` as the limit of `h ^ (-2)` times the alternate sum of the values of `f`
along the vertices of a quadrilateral with sides `h v` and `h w` based at `x`.
In a setting where `f` is not guaranteed to be continuous at `f`, we can still
get this if we use a quadrilateral based at `h v + h w`. -/
theorem Convex.is_o_alternate_sum_square {v w : E} (h4v : x + (4 : ℝ) • v ∈ Interior s)
    (h4w : x + (4 : ℝ) • w ∈ Interior s) :
    (fun h : ℝ =>
        f (x + h • (2 • v + 2 • w)) + f (x + h • (v + w)) - f (x + h • (2 • v + w)) - f (x + h • (v + 2 • w)) -
          h ^ 2 • f'' v w) =o[𝓝[>] 0]
      fun h => h ^ 2 :=
  by
  have A : (1 : ℝ) / 2 ∈ Ioc (0 : ℝ) 1 :=
    ⟨by
      norm_num, by
      norm_num⟩
  have B : (1 : ℝ) / 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨by
      norm_num, by
      norm_num⟩
  have C : ∀ w : E, (2 : ℝ) • w = 2 • w := fun w => by
    simp only [← two_smul]
  have h2v2w : x + (2 : ℝ) • v + (2 : ℝ) • w ∈ Interior s := by
    convert s_conv.interior.add_smul_sub_mem h4v h4w B using 1
    simp only [← smul_sub, ← smul_smul, ← one_div, ← add_sub_add_left_eq_sub, ← mul_addₓ, ← add_smul]
    norm_num
    simp only [←
      show (4 : ℝ) = (2 : ℝ) + (2 : ℝ) by
        norm_num,
      ← add_smul]
    abel
  have h2vww : x + (2 • v + w) + w ∈ Interior s := by
    convert h2v2w using 1
    simp only [← two_smul]
    abel
  have h2v : x + (2 : ℝ) • v ∈ Interior s := by
    convert s_conv.add_smul_sub_mem_interior xs h4v A using 1
    simp only [← smul_smul, ← one_div, ← add_sub_cancel', ← add_right_injₓ]
    norm_num
  have h2w : x + (2 : ℝ) • w ∈ Interior s := by
    convert s_conv.add_smul_sub_mem_interior xs h4w A using 1
    simp only [← smul_smul, ← one_div, ← add_sub_cancel', ← add_right_injₓ]
    norm_num
  have hvw : x + (v + w) ∈ Interior s := by
    convert s_conv.add_smul_sub_mem_interior xs h2v2w A using 1
    simp only [← smul_smul, ← one_div, ← add_sub_cancel', ← add_right_injₓ, ← smul_add, ← smul_sub]
    norm_num
    abel
  have h2vw : x + (2 • v + w) ∈ Interior s := by
    convert s_conv.interior.add_smul_sub_mem h2v h2v2w B using 1
    simp only [← smul_add, ← smul_sub, ← smul_smul, C]
    norm_num
    abel
  have hvww : x + (v + w) + w ∈ Interior s := by
    convert s_conv.interior.add_smul_sub_mem h2w h2v2w B using 1
    simp only [← one_div, ← add_sub_cancel', ← inv_smul_smul₀, ← add_sub_add_right_eq_sub, ← Ne.def, ← not_false_iff, ←
      bit0_eq_zero, ← one_ne_zero]
    rw [two_smul]
    abel
  have TA1 := s_conv.taylor_approx_two_segment hf xs hx h2vw h2vww
  have TA2 := s_conv.taylor_approx_two_segment hf xs hx hvw hvww
  convert TA1.sub TA2
  ext h
  simp only [← two_smul, ← smul_add, add_assocₓ, ← ContinuousLinearMap.map_add, ← ContinuousLinearMap.add_apply, ←
    Pi.smul_apply, ← ContinuousLinearMap.coe_smul', ← ContinuousLinearMap.map_smul]
  abel

/-- Assume that `f` is differentiable inside a convex set `s`, and that its derivative `f'` is
differentiable at a point `x`. Then, given two vectors `v` and `w` pointing inside `s`, one
has `f'' v w = f'' w v`. Superseded by `convex.second_derivative_within_at_symmetric`, which
removes the assumption that `v` and `w` point inside `s`.
-/
theorem Convex.second_derivative_within_at_symmetric_of_mem_interior {v w : E} (h4v : x + (4 : ℝ) • v ∈ Interior s)
    (h4w : x + (4 : ℝ) • w ∈ Interior s) : f'' w v = f'' v w := by
  have A : (fun h : ℝ => h ^ 2 • (f'' w v - f'' v w)) =o[𝓝[>] 0] fun h => h ^ 2 := by
    convert (s_conv.is_o_alternate_sum_square hf xs hx h4v h4w).sub (s_conv.is_o_alternate_sum_square hf xs hx h4w h4v)
    ext h
    simp only [← add_commₓ, ← smul_add, ← smul_sub]
    abel
  have B : (fun h : ℝ => f'' w v - f'' v w) =o[𝓝[>] 0] fun h => (1 : ℝ) := by
    have : (fun h : ℝ => 1 / h ^ 2) =O[𝓝[>] 0] fun h => 1 / h ^ 2 := is_O_refl _ _
    have C := this.smul_is_o A
    apply C.congr' _ _
    · filter_upwards [self_mem_nhds_within]
      intro h hpos
      rw [← one_smul ℝ (f'' w v - f'' v w), smul_smul, smul_smul]
      congr 1
      field_simp [← LT.lt.ne' hpos]
      
    · filter_upwards [self_mem_nhds_within] with _ hpos
      field_simp [← LT.lt.ne' hpos, ← HasSmul.smul]
      
  simpa only [← sub_eq_zero] using is_o_const_const_iff.1 B

omit s_conv xs hx hf

/-- If a function is differentiable inside a convex set with nonempty interior, and has a second
derivative at a point of this convex set, then this second derivative is symmetric. -/
theorem Convex.second_derivative_within_at_symmetric {s : Set E} (s_conv : Convex ℝ s) (hne : (Interior s).Nonempty)
    {f : E → F} {f' : E → E →L[ℝ] F} {f'' : E →L[ℝ] E →L[ℝ] F} (hf : ∀, ∀ x ∈ Interior s, ∀, HasFderivAt f (f' x) x)
    {x : E} (xs : x ∈ s) (hx : HasFderivWithinAt f' f'' (Interior s) x) (v w : E) : f'' v w = f'' w v := by
  /- we work around a point `x + 4 z` in the interior of `s`. For any vector `m`,
    then `x + 4 (z + t m)` also belongs to the interior of `s` for small enough `t`. This means that
    we will be able to apply `second_derivative_within_at_symmetric_of_mem_interior` to show
    that `f''` is symmetric, after cancelling all the contributions due to `z`. -/
  rcases hne with ⟨y, hy⟩
  obtain ⟨z, hz⟩ : ∃ z, z = ((1 : ℝ) / 4) • (y - x) := ⟨((1 : ℝ) / 4) • (y - x), rfl⟩
  have A : ∀ m : E, Filter.Tendsto (fun t : ℝ => x + (4 : ℝ) • (z + t • m)) (𝓝 0) (𝓝 y) := by
    intro m
    have : x + (4 : ℝ) • (z + (0 : ℝ) • m) = y := by
      simp [← hz]
    rw [← this]
    refine' tendsto_const_nhds.add _
    refine' tendsto_const_nhds.smul _
    refine' tendsto_const_nhds.add _
    exact continuous_at_id.smul continuous_at_const
  have B : ∀ m : E, ∀ᶠ t in 𝓝[>] (0 : ℝ), x + (4 : ℝ) • (z + t • m) ∈ Interior s := by
    intro m
    apply nhds_within_le_nhds
    apply A m
    rw [mem_interior_iff_mem_nhds] at hy
    exact interior_mem_nhds.2 hy
  -- we choose `t m > 0` such that `x + 4 (z + (t m) m)` belongs to the interior of `s`, for any
  -- vector `m`.
  choose t ts tpos using fun m => ((B m).And self_mem_nhds_within).exists
  -- applying `second_derivative_within_at_symmetric_of_mem_interior` to the vectors `z`
  -- and `z + (t m) m`, we deduce that `f'' m z = f'' z m` for all `m`.
  have C : ∀ m : E, f'' m z = f'' z m := by
    intro m
    have : f'' (z + t m • m) (z + t 0 • 0) = f'' (z + t 0 • 0) (z + t m • m) :=
      s_conv.second_derivative_within_at_symmetric_of_mem_interior hf xs hx (ts 0) (ts m)
    simp only [← ContinuousLinearMap.map_add, ← ContinuousLinearMap.map_smul, ← add_right_injₓ, ←
      ContinuousLinearMap.add_apply, ← Pi.smul_apply, ← ContinuousLinearMap.coe_smul', ← add_zeroₓ, ←
      ContinuousLinearMap.zero_apply, ← smul_zero, ← ContinuousLinearMap.map_zero] at this
    exact smul_right_injective F (tpos m).ne' this
  -- applying `second_derivative_within_at_symmetric_of_mem_interior` to the vectors `z + (t v) v`
  -- and `z + (t w) w`, we deduce that `f'' v w = f'' w v`. Cross terms involving `z` can be
  -- eliminated thanks to the fact proved above that `f'' m z = f'' z m`.
  have : f'' (z + t v • v) (z + t w • w) = f'' (z + t w • w) (z + t v • v) :=
    s_conv.second_derivative_within_at_symmetric_of_mem_interior hf xs hx (ts w) (ts v)
  simp only [← ContinuousLinearMap.map_add, ← ContinuousLinearMap.map_smul, ← smul_add, ← smul_smul, ←
    ContinuousLinearMap.add_apply, ← Pi.smul_apply, ← ContinuousLinearMap.coe_smul', ← C] at this
  rw [← sub_eq_zero] at this
  abel  at this
  simp only [← one_zsmul, ← neg_smul, ← sub_eq_zero, ← mul_comm, sub_eq_add_neg] at this
  apply smul_right_injective F _ this
  simp [← (tpos v).ne', ← (tpos w).ne']

/-- If a function is differentiable around `x`, and has two derivatives at `x`, then the second
derivative is symmetric. -/
theorem second_derivative_symmetric_of_eventually {f : E → F} {f' : E → E →L[ℝ] F} {f'' : E →L[ℝ] E →L[ℝ] F}
    (hf : ∀ᶠ y in 𝓝 x, HasFderivAt f (f' y) y) (hx : HasFderivAt f' f'' x) (v w : E) : f'' v w = f'' w v := by
  rcases Metric.mem_nhds_iff.1 hf with ⟨ε, εpos, hε⟩
  have A : (Interior (Metric.Ball x ε)).Nonempty := by
    rwa [metric.is_open_ball.interior_eq, Metric.nonempty_ball]
  exact
    Convex.second_derivative_within_at_symmetric (convex_ball x ε) A (fun y hy => hε (interior_subset hy))
      (Metric.mem_ball_self εpos) hx.has_fderiv_within_at v w

/-- If a function is differentiable, and has two derivatives at `x`, then the second
derivative is symmetric. -/
theorem second_derivative_symmetric {f : E → F} {f' : E → E →L[ℝ] F} {f'' : E →L[ℝ] E →L[ℝ] F}
    (hf : ∀ y, HasFderivAt f (f' y) y) (hx : HasFderivAt f' f'' x) (v w : E) : f'' v w = f'' w v :=
  second_derivative_symmetric_of_eventually (Filter.eventually_of_forall hf) hx v w

