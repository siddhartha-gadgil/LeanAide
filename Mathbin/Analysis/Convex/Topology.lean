/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
import Mathbin.Analysis.Convex.Jensen
import Mathbin.Analysis.Normed.Group.Pointwise
import Mathbin.Analysis.NormedSpace.FiniteDimension
import Mathbin.Analysis.NormedSpace.Ray
import Mathbin.Topology.PathConnected
import Mathbin.Topology.Algebra.Affine

/-!
# Topological and metric properties of convex sets

We prove the following facts:

* `convex.interior` : interior of a convex set is convex;
* `convex.closure` : closure of a convex set is convex;
* `set.finite.compact_convex_hull` : convex hull of a finite set is compact;
* `set.finite.is_closed_convex_hull` : convex hull of a finite set is closed;
* `convex_on_norm`, `convex_on_dist` : norm and distance to a fixed point is convex on any convex
  set;
* `convex_on_univ_norm`, `convex_on_univ_dist` : norm and distance to a fixed point is convex on
  the whole space;
* `convex_hull_ediam`, `convex_hull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `bounded_convex_hull` : convex hull of a set is bounded if and only if the original set
  is bounded.
* `bounded_std_simplex`, `is_closed_std_simplex`, `compact_std_simplex`: topological properties
  of the standard simplex;
-/


variable {ι : Type _} {E : Type _}

open Metric Set

open Pointwise Convex

theorem Real.convex_iff_is_preconnected {s : Set ℝ} : Convex ℝ s ↔ IsPreconnected s :=
  convex_iff_ord_connected.trans is_preconnected_iff_ord_connected.symm

alias Real.convex_iff_is_preconnected ↔ _ IsPreconnected.convex

/-! ### Standard simplex -/


section StdSimplex

variable [Fintype ι]

/-- Every vector in `std_simplex 𝕜 ι` has `max`-norm at most `1`. -/
theorem std_simplex_subset_closed_ball : StdSimplex ℝ ι ⊆ Metric.ClosedBall 0 1 := by
  intro f hf
  rw [Metric.mem_closed_ball, dist_zero_right]
  refine' Nnreal.coe_one ▸ Nnreal.coe_le_coe.2 <| Finset.sup_le fun x hx => _
  change abs (f x) ≤ 1
  rw [abs_of_nonneg <| hf.1 x]
  exact (mem_Icc_of_mem_std_simplex hf x).2

variable (ι)

/-- `std_simplex ℝ ι` is bounded. -/
theorem bounded_std_simplex : Metric.Bounded (StdSimplex ℝ ι) :=
  (Metric.bounded_iff_subset_ball 0).2 ⟨1, std_simplex_subset_closed_ball⟩

/-- `std_simplex ℝ ι` is closed. -/
theorem is_closed_std_simplex : IsClosed (StdSimplex ℝ ι) :=
  (std_simplex_eq_inter ℝ ι).symm ▸
    IsClosed.inter (is_closed_Inter fun i => is_closed_le continuous_const (continuous_apply i))
      (is_closed_eq ((continuous_finset_sum _) fun x _ => continuous_apply x) continuous_const)

/-- `std_simplex ℝ ι` is compact. -/
theorem compact_std_simplex : IsCompact (StdSimplex ℝ ι) :=
  Metric.compact_iff_closed_bounded.2 ⟨is_closed_std_simplex ι, bounded_std_simplex ι⟩

end StdSimplex

/-! ### Topological vector space -/


section HasContinuousConstSmul

variable {𝕜 : Type _} [LinearOrderedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
  [HasContinuousConstSmul 𝕜 E]

/-- If `s` is a convex set, then `a • interior s + b • closure s ⊆ interior s` for all `0 < a`,
`0 ≤ b`, `a + b = 1`. See also `convex.combo_interior_self_subset_interior` for a weaker version. -/
theorem Convex.combo_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a • Interior s + b • Closure s ⊆ Interior s :=
  interior_smul₀ ha.ne' s ▸
    calc
      Interior (a • s) + b • Closure s ⊆ Interior (a • s) + Closure (b • s) :=
        add_subset_add Subset.rfl (smul_closure_subset b s)
      _ = Interior (a • s) + b • s := by
        rw [is_open_interior.add_closure (b • s)]
      _ ⊆ Interior (a • s + b • s) := subset_interior_add_left
      _ ⊆ Interior s := interior_mono <| hs.set_combo_subset ha.le hb hab
      

/-- If `s` is a convex set, then `a • interior s + b • s ⊆ interior s` for all `0 < a`, `0 ≤ b`,
`a + b = 1`. See also `convex.combo_interior_closure_subset_interior` for a stronger version. -/
theorem Convex.combo_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a • Interior s + b • s ⊆ Interior s :=
  calc
    a • Interior s + b • s ⊆ a • Interior s + b • Closure s :=
      add_subset_add Subset.rfl <| image_subset _ subset_closure
    _ ⊆ Interior s := hs.combo_interior_closure_subset_interior ha hb hab
    

/-- If `s` is a convex set, then `a • closure s + b • interior s ⊆ interior s` for all `0 ≤ a`,
`0 < b`, `a + b = 1`. See also `convex.combo_self_interior_subset_interior` for a weaker version. -/
theorem Convex.combo_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + b = 1) : a • Closure s + b • Interior s ⊆ Interior s := by
  rw [add_commₓ]
  exact hs.combo_interior_closure_subset_interior hb ha (add_commₓ a b ▸ hab)

/-- If `s` is a convex set, then `a • s + b • interior s ⊆ interior s` for all `0 ≤ a`, `0 < b`,
`a + b = 1`. See also `convex.combo_closure_interior_subset_interior` for a stronger version. -/
theorem Convex.combo_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + b = 1) : a • s + b • Interior s ⊆ Interior s := by
  rw [add_commₓ]
  exact hs.combo_interior_self_subset_interior hb ha (add_commₓ a b ▸ hab)

theorem Convex.combo_interior_closure_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ Interior s)
    (hy : y ∈ Closure s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) : a • x + b • y ∈ Interior s :=
  hs.combo_interior_closure_subset_interior ha hb hab <| add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

theorem Convex.combo_interior_self_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ Interior s)
    (hy : y ∈ s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) : a • x + b • y ∈ Interior s :=
  hs.combo_interior_closure_mem_interior hx (subset_closure hy) ha hb hab

theorem Convex.combo_closure_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ Closure s)
    (hy : y ∈ Interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) : a • x + b • y ∈ Interior s :=
  hs.combo_closure_interior_subset_interior ha hb hab <| add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

theorem Convex.combo_self_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ Interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) : a • x + b • y ∈ Interior s :=
  hs.combo_closure_interior_mem_interior (subset_closure hx) hy ha hb hab

theorem Convex.open_segment_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ Interior s) (hy : y ∈ Closure s) : OpenSegment 𝕜 x y ⊆ Interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_interior_closure_mem_interior hx hy ha hb.le hab

theorem Convex.open_segment_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ Interior s)
    (hy : y ∈ s) : OpenSegment 𝕜 x y ⊆ Interior s :=
  hs.open_segment_interior_closure_subset_interior hx (subset_closure hy)

theorem Convex.open_segment_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ Closure s) (hy : y ∈ Interior s) : OpenSegment 𝕜 x y ⊆ Interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_closure_interior_mem_interior hx hy ha.le hb hab

theorem Convex.open_segment_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ Interior s) : OpenSegment 𝕜 x y ⊆ Interior s :=
  hs.open_segment_closure_interior_subset_interior (subset_closure hx) hy

/-- If `x ∈ closure s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`.
-/
theorem Convex.add_smul_sub_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ Closure s)
    (hy : y ∈ Interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • (y - x) ∈ Interior s := by
  simpa only [← sub_smul, ← smul_sub, ← one_smul, ← add_sub, ← add_commₓ] using
    hs.combo_interior_closure_mem_interior hy hx ht.1 (sub_nonneg.mpr ht.2) (add_sub_cancel'_right _ _)

/-- If `x ∈ s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`. -/
theorem Convex.add_smul_sub_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ Interior s)
    {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • (y - x) ∈ Interior s :=
  hs.add_smul_sub_mem_interior' (subset_closure hx) hy ht

/-- If `x ∈ closure s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
theorem Convex.add_smul_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ Closure s)
    (hy : x + y ∈ Interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • y ∈ Interior s := by
  simpa only [← add_sub_cancel'] using hs.add_smul_sub_mem_interior' hx hy ht

/-- If `x ∈ s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
theorem Convex.add_smul_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : x + y ∈ Interior s)
    {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • y ∈ Interior s :=
  hs.add_smul_mem_interior' (subset_closure hx) hy ht

/-- In a topological vector space, the interior of a convex set is convex. -/
protected theorem Convex.interior {s : Set E} (hs : Convex 𝕜 s) : Convex 𝕜 (Interior s) :=
  convex_iff_open_segment_subset.mpr fun x y hx hy =>
    hs.open_segment_closure_interior_subset_interior (interior_subset_closure hx) hy

/-- In a topological vector space, the closure of a convex set is convex. -/
protected theorem Convex.closure {s : Set E} (hs : Convex 𝕜 s) : Convex 𝕜 (Closure s) := fun x y hx hy a b ha hb hab =>
  let f : E → E → E := fun x' y' => a • x' + b • y'
  have hf : Continuous fun p : E × E => f p.1 p.2 := (continuous_fst.const_smul _).add (continuous_snd.const_smul _)
  show f x y ∈ Closure s from
    mem_closure_of_continuous2 hf hx hy fun x' hx' y' hy' => subset_closure (hs hx' hy' ha hb hab)

end HasContinuousConstSmul

section HasContinuousSmul

variable [AddCommGroupₓ E] [Module ℝ E] [TopologicalSpace E] [TopologicalAddGroup E] [HasContinuousSmul ℝ E]

/-- Convex hull of a finite set is compact. -/
theorem Set.Finite.compact_convex_hull {s : Set E} (hs : s.Finite) : IsCompact (convexHull ℝ s) := by
  rw [hs.convex_hull_eq_image]
  apply (compact_std_simplex _).Image
  have := hs.fintype
  apply LinearMap.continuous_on_pi

/-- Convex hull of a finite set is closed. -/
theorem Set.Finite.is_closed_convex_hull [T2Space E] {s : Set E} (hs : s.Finite) : IsClosed (convexHull ℝ s) :=
  hs.compact_convex_hull.IsClosed

open AffineMap

/-- If we dilate the interior of a convex set about a point in its interior by a scale `t > 1`,
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.closure_subset_image_homothety_interior_of_one_lt {s : Set E} (hs : Convex ℝ s) {x : E}
    (hx : x ∈ Interior s) (t : ℝ) (ht : 1 < t) : Closure s ⊆ homothety x t '' Interior s := by
  intro y hy
  have hne : t ≠ 0 := (one_pos.trans ht).ne'
  refine'
    ⟨homothety x t⁻¹ y, hs.open_segment_interior_closure_subset_interior hx hy _,
      (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t hne)).apply_symm_apply y⟩
  rw [open_segment_eq_image_line_map, ← inv_one, ← inv_Ioi (@one_pos ℝ _ _), ← image_inv, image_image,
    homothety_eq_line_map]
  exact mem_image_of_mem _ ht

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.closure_subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex ℝ s) {x : E}
    (hx : x ∈ Interior s) (t : ℝ) (ht : 1 < t) : Closure s ⊆ Interior (homothety x t '' s) :=
  (hs.closure_subset_image_homothety_interior_of_one_lt hx t ht).trans <|
    (homothety_is_open_map x t (one_pos.trans ht).ne').image_interior_subset _

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex ℝ s) {x : E} (hx : x ∈ Interior s)
    (t : ℝ) (ht : 1 < t) : s ⊆ Interior (homothety x t '' s) :=
  subset_closure.trans <| hs.closure_subset_interior_image_homothety_of_one_lt hx t ht

/-- A nonempty convex set is path connected. -/
protected theorem Convex.is_path_connected {s : Set E} (hconv : Convex ℝ s) (hne : s.Nonempty) : IsPathConnected s := by
  refine' is_path_connected_iff.mpr ⟨hne, _⟩
  intro x x_in y y_in
  have H := hconv.segment_subset x_in y_in
  rw [segment_eq_image_line_map] at H
  exact
    JoinedIn.of_line affine_map.line_map_continuous.continuous_on (line_map_apply_zero _ _) (line_map_apply_one _ _) H

/-- A nonempty convex set is connected. -/
protected theorem Convex.is_connected {s : Set E} (h : Convex ℝ s) (hne : s.Nonempty) : IsConnected s :=
  (h.IsPathConnected hne).IsConnected

/-- A convex set is preconnected. -/
protected theorem Convex.is_preconnected {s : Set E} (h : Convex ℝ s) : IsPreconnected s :=
  s.eq_empty_or_nonempty.elim (fun h => h.symm ▸ is_preconnected_empty) fun hne => (h.IsConnected hne).IsPreconnected

/-- Every topological vector space over ℝ is path connected.

Not an instance, because it creates enormous TC subproblems (turn on `pp.all`).
-/
protected theorem TopologicalAddGroup.path_connected : PathConnectedSpace E :=
  path_connected_space_iff_univ.mpr <| convex_univ.IsPathConnected ⟨(0 : E), trivialₓ⟩

end HasContinuousSmul

/-! ### Normed vector space -/


section NormedSpace

variable [SemiNormedGroup E] [NormedSpace ℝ E] {s t : Set E}

/-- The norm on a real normed space is convex on any convex set. See also `seminorm.convex_on`
and `convex_on_univ_norm`. -/
theorem convex_on_norm (hs : Convex ℝ s) : ConvexOn ℝ s norm :=
  ⟨hs, fun x y hx hy a b ha hb hab =>
    calc
      ∥a • x + b • y∥ ≤ ∥a • x∥ + ∥b • y∥ := norm_add_le _ _
      _ = a * ∥x∥ + b * ∥y∥ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      ⟩

/-- The norm on a real normed space is convex on the whole space. See also `seminorm.convex_on`
and `convex_on_norm`. -/
theorem convex_on_univ_norm : ConvexOn ℝ Univ (norm : E → ℝ) :=
  convex_on_norm convex_univ

theorem convex_on_dist (z : E) (hs : Convex ℝ s) : ConvexOn ℝ s fun z' => dist z' z := by
  simpa [← dist_eq_norm, ← preimage_preimage] using
    (convex_on_norm (hs.translate (-z))).comp_affine_map (AffineMap.id ℝ E - AffineMap.const ℝ E z)

theorem convex_on_univ_dist (z : E) : ConvexOn ℝ Univ fun z' => dist z' z :=
  convex_on_dist z convex_univ

theorem convex_ball (a : E) (r : ℝ) : Convex ℝ (Metric.Ball a r) := by
  simpa only [← Metric.Ball, ← sep_univ] using (convex_on_univ_dist a).convex_lt r

theorem convex_closed_ball (a : E) (r : ℝ) : Convex ℝ (Metric.ClosedBall a r) := by
  simpa only [← Metric.ClosedBall, ← sep_univ] using (convex_on_univ_dist a).convex_le r

theorem Convex.thickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (Thickening δ s) := by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)

theorem Convex.cthickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (Cthickening δ s) := by
  obtain hδ | hδ := le_totalₓ 0 δ
  · rw [cthickening_eq_Inter_thickening hδ]
    exact convex_Inter₂ fun _ _ => hs.thickening _
    
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure
    

/-- If `s`, `t` are disjoint convex sets, `s` is compact and `t` is closed then we can find open
disjoint convex sets containing them. -/
theorem Disjoint.exists_open_convexes (disj : Disjoint s t) (hs₁ : Convex ℝ s) (hs₂ : IsCompact s) (ht₁ : Convex ℝ t)
    (ht₂ : IsClosed t) : ∃ u v, IsOpen u ∧ IsOpen v ∧ Convex ℝ u ∧ Convex ℝ v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v :=
  let ⟨δ, hδ, hst⟩ := disj.exists_thickenings hs₂ ht₂
  ⟨_, _, is_open_thickening, is_open_thickening, hs₁.Thickening _, ht₁.Thickening _, self_subset_thickening hδ _,
    self_subset_thickening hδ _, hst⟩

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
theorem convex_hull_exists_dist_ge {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) (y : E) :
    ∃ x' ∈ s, dist x y ≤ dist x' y :=
  (convex_on_dist y (convex_convex_hull ℝ _)).exists_ge_of_mem_convex_hull hx

/-- Given a point `x` in the convex hull of `s` and a point `y` in the convex hull of `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`. -/
theorem convex_hull_exists_dist_ge2 {s t : Set E} {x y : E} (hx : x ∈ convexHull ℝ s) (hy : y ∈ convexHull ℝ t) :
    ∃ x' ∈ s, ∃ y' ∈ t, dist x y ≤ dist x' y' := by
  rcases convex_hull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩
  rcases convex_hull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩
  use x', hx', y', hy'
  exact le_transₓ Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp]
theorem convex_hull_ediam (s : Set E) : Emetric.diam (convexHull ℝ s) = Emetric.diam s := by
  refine' (Emetric.diam_le fun x hx y hy => _).antisymm (Emetric.diam_mono <| subset_convex_hull ℝ s)
  rcases convex_hull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩
  rw [edist_dist]
  apply le_transₓ (Ennreal.of_real_le_of_real H)
  rw [← edist_dist]
  exact Emetric.edist_le_diam_of_mem hx' hy'

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp]
theorem convex_hull_diam (s : Set E) : Metric.diam (convexHull ℝ s) = Metric.diam s := by
  simp only [← Metric.diam, ← convex_hull_ediam]

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp]
theorem bounded_convex_hull {s : Set E} : Metric.Bounded (convexHull ℝ s) ↔ Metric.Bounded s := by
  simp only [← Metric.bounded_iff_ediam_ne_top, ← convex_hull_ediam]

instance (priority := 100) NormedSpace.path_connected : PathConnectedSpace E :=
  TopologicalAddGroup.path_connected

instance (priority := 100) NormedSpace.loc_path_connected : LocPathConnectedSpace E :=
  loc_path_connected_of_bases (fun x => Metric.nhds_basis_ball) fun x r r_pos =>
    (convex_ball x r).IsPathConnected <| by
      simp [← r_pos]

theorem dist_add_dist_of_mem_segment {x y z : E} (h : y ∈ [x -[ℝ] z]) : dist x y + dist y z = dist x z := by
  simp only [← dist_eq_norm, ← mem_segment_iff_same_ray] at *
  simpa only [← sub_add_sub_cancel', ← norm_sub_rev] using h.norm_add.symm

end NormedSpace

