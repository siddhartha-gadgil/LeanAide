/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies
-/
import Mathbin.Analysis.Normed.Group.Pointwise
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Properties of pointwise scalar multiplication of sets in normed spaces.

We explore the relationships between scalar multiplication of sets in vector spaces, and the norm.
Notably, we express arbitrary balls as rescaling of other balls, and we show that the
multiplication of bounded sets remain bounded.
-/


open Metric Set

open Pointwise TopologicalSpace

variable {𝕜 E : Type _} [NormedField 𝕜]

section SemiNormedGroup

variable [SemiNormedGroup E] [NormedSpace 𝕜 E]

theorem smul_ball {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) : c • Ball x r = Ball (c • x) (∥c∥ * r) := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp [div_eq_inv_mul, ← div_lt_iff (norm_pos_iff.2 hc), ← mul_comm _ r, ← dist_smul]

theorem smul_unit_ball {c : 𝕜} (hc : c ≠ 0) : c • Ball (0 : E) (1 : ℝ) = Ball (0 : E) ∥c∥ := by
  rw [smul_ball hc, smul_zero, mul_oneₓ]

theorem smul_sphere' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) : c • Sphere x r = Sphere (c • x) (∥c∥ * r) := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp only [← mem_sphere, ← dist_smul, ← norm_inv, div_eq_inv_mul, ← div_eq_iff (norm_pos_iff.2 hc).ne', ← mul_comm r]

theorem smul_closed_ball' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) : c • ClosedBall x r = ClosedBall (c • x) (∥c∥ * r) := by
  simp only [ball_union_sphere, ← Set.smul_set_union, ← smul_ball hc, ← smul_sphere' hc]

theorem Metric.Bounded.smul {s : Set E} (hs : Bounded s) (c : 𝕜) : Bounded (c • s) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀, ∀ x ∈ s, ∀, ∥x∥ ≤ R := hs.exists_norm_le
  refine' bounded_iff_exists_norm_le.2 ⟨∥c∥ * R, _⟩
  intro z hz
  obtain ⟨y, ys, rfl⟩ : ∃ y : E, y ∈ s ∧ c • y = z := mem_smul_set.1 hz
  calc ∥c • y∥ = ∥c∥ * ∥y∥ := norm_smul _ _ _ ≤ ∥c∥ * R := mul_le_mul_of_nonneg_left (hR y ys) (norm_nonneg _)

/-- If `s` is a bounded set, then for small enough `r`, the set `{x} + r • s` is contained in any
fixed neighborhood of `x`. -/
theorem eventually_singleton_add_smul_subset {x : E} {s : Set E} (hs : Bounded s) {u : Set E} (hu : u ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝 (0 : 𝕜), {x} + r • s ⊆ u := by
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : _)(hε : 0 < ε), closed_ball x ε ⊆ u := nhds_basis_closed_ball.mem_iff.1 hu
  obtain ⟨R, Rpos, hR⟩ : ∃ R : ℝ, 0 < R ∧ s ⊆ closed_ball 0 R := hs.subset_ball_lt 0 0
  have : Metric.ClosedBall (0 : 𝕜) (ε / R) ∈ 𝓝 (0 : 𝕜) := closed_ball_mem_nhds _ (div_pos εpos Rpos)
  filter_upwards [this] with r hr
  simp only [← image_add_left, ← singleton_add]
  intro y hy
  obtain ⟨z, zs, hz⟩ : ∃ z : E, z ∈ s ∧ r • z = -x + y := by
    simpa [← mem_smul_set] using hy
  have I : ∥r • z∥ ≤ ε :=
    calc
      ∥r • z∥ = ∥r∥ * ∥z∥ := norm_smul _ _
      _ ≤ ε / R * R :=
        mul_le_mul (mem_closed_ball_zero_iff.1 hr) (mem_closed_ball_zero_iff.1 (hR zs)) (norm_nonneg _)
          (div_pos εpos Rpos).le
      _ = ε := by
        field_simp [← Rpos.ne']
      
  have : y = x + r • z := by
    simp only [← hz, ← add_neg_cancel_left]
  apply hε
  simpa only [← this, ← dist_eq_norm, ← add_sub_cancel', ← mem_closed_ball] using I

variable [NormedSpace ℝ E] {x y z : E} {δ ε : ℝ}

/-- In a real normed space, the image of the unit ball under scalar multiplication by a positive
constant `r` is the ball of radius `r`. -/
theorem smul_unit_ball_of_pos {r : ℝ} (hr : 0 < r) : r • Ball 0 1 = Ball (0 : E) r := by
  rw [smul_unit_ball hr.ne', Real.norm_of_nonneg hr.le]

-- This is also true for `ℚ`-normed spaces
theorem exists_dist_eq (x z : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∃ y, dist x y = b * dist x z ∧ dist y z = a * dist x z := by
  use a • x + b • z
  nth_rw 0[← one_smul ℝ x]
  nth_rw 3[← one_smul ℝ z]
  simp [← dist_eq_norm, hab, ← add_smul, smul_sub, ← norm_smul_of_nonneg, ← ha, ← hb]

theorem exists_dist_le_le (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (h : dist x z ≤ ε + δ) : ∃ y, dist x y ≤ δ ∧ dist y z ≤ ε := by
  obtain rfl | hε' := hε.eq_or_lt
  · exact
      ⟨z, by
        rwa [zero_addₓ] at h, (dist_self _).le⟩
    
  have hεδ := add_pos_of_pos_of_nonneg hε' hδ
  refine'
    (exists_dist_eq x z (div_nonneg hε <| add_nonneg hε hδ) (div_nonneg hδ <| add_nonneg hε hδ) <| by
          rw [← add_div, div_self hεδ.ne']).imp
      fun y hy => _
  rw [hy.1, hy.2, div_mul_comm, div_mul_comm ε]
  rw [← div_le_one hεδ] at h
  exact ⟨mul_le_of_le_one_left hδ h, mul_le_of_le_one_left hε h⟩

-- This is also true for `ℚ`-normed spaces
theorem exists_dist_le_lt (hδ : 0 ≤ δ) (hε : 0 < ε) (h : dist x z < ε + δ) : ∃ y, dist x y ≤ δ ∧ dist y z < ε := by
  refine'
    (exists_dist_eq x z (div_nonneg hε.le <| add_nonneg hε.le hδ) (div_nonneg hδ <| add_nonneg hε.le hδ) <| by
          rw [← add_div, div_self (add_pos_of_pos_of_nonneg hε hδ).ne']).imp
      fun y hy => _
  rw [hy.1, hy.2, div_mul_comm, div_mul_comm ε]
  rw [← div_lt_one (add_pos_of_pos_of_nonneg hε hδ)] at h
  exact ⟨mul_le_of_le_one_left hδ h.le, mul_lt_of_lt_one_left hε h⟩

-- This is also true for `ℚ`-normed spaces
theorem exists_dist_lt_le (hδ : 0 < δ) (hε : 0 ≤ ε) (h : dist x z < ε + δ) : ∃ y, dist x y < δ ∧ dist y z ≤ ε := by
  obtain ⟨y, yz, xy⟩ :=
    exists_dist_le_lt hε hδ
      (show dist z x < δ + ε by
        simpa only [← dist_comm, ← add_commₓ] using h)
  exact
    ⟨y, by
      simp [← dist_comm x y, ← dist_comm y z, *]⟩

-- This is also true for `ℚ`-normed spaces
theorem exists_dist_lt_lt (hδ : 0 < δ) (hε : 0 < ε) (h : dist x z < ε + δ) : ∃ y, dist x y < δ ∧ dist y z < ε := by
  refine'
    (exists_dist_eq x z (div_nonneg hε.le <| add_nonneg hε.le hδ.le) (div_nonneg hδ.le <| add_nonneg hε.le hδ.le) <| by
          rw [← add_div, div_self (add_pos hε hδ).ne']).imp
      fun y hy => _
  rw [hy.1, hy.2, div_mul_comm, div_mul_comm ε]
  rw [← div_lt_one (add_pos hε hδ)] at h
  exact ⟨mul_lt_of_lt_one_left hδ h, mul_lt_of_lt_one_left hε h⟩

-- This is also true for `ℚ`-normed spaces
theorem disjoint_ball_ball_iff (hδ : 0 < δ) (hε : 0 < ε) : Disjoint (Ball x δ) (Ball y ε) ↔ δ + ε ≤ dist x y := by
  refine' ⟨fun h => le_of_not_ltₓ fun hxy => _, ball_disjoint_ball⟩
  rw [add_commₓ] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_lt hδ hε hxy
  rw [dist_comm] at hxz
  exact h ⟨hxz, hzy⟩

-- This is also true for `ℚ`-normed spaces
theorem disjoint_ball_closed_ball_iff (hδ : 0 < δ) (hε : 0 ≤ ε) :
    Disjoint (Ball x δ) (ClosedBall y ε) ↔ δ + ε ≤ dist x y := by
  refine' ⟨fun h => le_of_not_ltₓ fun hxy => _, ball_disjoint_closed_ball⟩
  rw [add_commₓ] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_le hδ hε hxy
  rw [dist_comm] at hxz
  exact h ⟨hxz, hzy⟩

-- This is also true for `ℚ`-normed spaces
theorem disjoint_closed_ball_ball_iff (hδ : 0 ≤ δ) (hε : 0 < ε) :
    Disjoint (ClosedBall x δ) (Ball y ε) ↔ δ + ε ≤ dist x y := by
  rw [Disjoint.comm, disjoint_ball_closed_ball_iff hε hδ, add_commₓ, dist_comm] <;> infer_instance

theorem disjoint_closed_ball_closed_ball_iff (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    Disjoint (ClosedBall x δ) (ClosedBall y ε) ↔ δ + ε < dist x y := by
  refine' ⟨fun h => lt_of_not_geₓ fun hxy => _, closed_ball_disjoint_closed_ball⟩
  rw [add_commₓ] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_le_le hδ hε hxy
  rw [dist_comm] at hxz
  exact h ⟨hxz, hzy⟩

open Emetric Ennreal

@[simp]
theorem inf_edist_thickening (hδ : 0 < δ) (s : Set E) (x : E) :
    infEdist x (Thickening δ s) = infEdist x s - Ennreal.ofReal δ := by
  obtain hs | hs := lt_or_leₓ (inf_edist x s) (Ennreal.ofReal δ)
  · rw [inf_edist_zero_of_mem, tsub_eq_zero_of_le hs.le]
    exact hs
    
  refine' (tsub_le_iff_right.2 inf_edist_le_inf_edist_thickening_add).antisymm' _
  refine' le_sub_of_add_le_right of_real_ne_top _
  refine' le_inf_edist.2 fun z hz => le_of_forall_lt' fun r h => _
  cases r
  · exact add_lt_top.2 ⟨lt_top_iff_ne_top.2 <| inf_edist_ne_top ⟨z, self_subset_thickening hδ _ hz⟩, of_real_lt_top⟩
    
  have hr : 0 < ↑r - δ := by
    refine' sub_pos_of_lt _
    have := hs.trans_lt ((inf_edist_le_edist_of_mem hz).trans_lt h)
    rw [of_real_eq_coe_nnreal hδ.le, some_eq_coe] at this
    exact_mod_cast this
  rw [some_eq_coe, edist_lt_coe, ← dist_lt_coe, ← add_sub_cancel'_right δ ↑r] at h
  obtain ⟨y, hxy, hyz⟩ := exists_dist_lt_lt hr hδ h
  refine'
    (Ennreal.add_lt_add_right of_real_ne_top <|
          inf_edist_lt_iff.2 ⟨_, mem_thickening_iff.2 ⟨_, hz, hyz⟩, edist_lt_of_real.2 hxy⟩).trans_le
      _
  rw [← of_real_add hr.le hδ.le, sub_add_cancel, of_real_coe_nnreal]
  exact le_rfl

@[simp]
theorem thickening_thickening (hε : 0 < ε) (hδ : 0 < δ) (s : Set E) :
    Thickening ε (Thickening δ s) = Thickening (ε + δ) s :=
  (thickening_thickening_subset _ _ _).antisymm fun x => by
    simp_rw [mem_thickening_iff]
    rintro ⟨z, hz, hxz⟩
    rw [add_commₓ] at hxz
    obtain ⟨y, hxy, hyz⟩ := exists_dist_lt_lt hε hδ hxz
    exact ⟨y, ⟨_, hz, hyz⟩, hxy⟩

@[simp]
theorem cthickening_thickening (hε : 0 ≤ ε) (hδ : 0 < δ) (s : Set E) :
    Cthickening ε (Thickening δ s) = Cthickening (ε + δ) s :=
  (cthickening_thickening_subset hε _ _).antisymm fun x => by
    simp_rw [mem_cthickening_iff, Ennreal.of_real_add hε hδ.le, inf_edist_thickening hδ]
    exact tsub_le_iff_right.2

-- Note: `interior (cthickening δ s) ≠ thickening δ s` in general
@[simp]
theorem closure_thickening (hδ : 0 < δ) (s : Set E) : Closure (Thickening δ s) = Cthickening δ s := by
  rw [← cthickening_zero, cthickening_thickening le_rfl hδ, zero_addₓ]
  infer_instance

@[simp]
theorem inf_edist_cthickening (δ : ℝ) (s : Set E) (x : E) :
    infEdist x (Cthickening δ s) = infEdist x s - Ennreal.ofReal δ := by
  obtain hδ | hδ := le_or_ltₓ δ 0
  · rw [cthickening_of_nonpos hδ, inf_edist_closure, of_real_of_nonpos hδ, tsub_zero]
    
  · rw [← closure_thickening hδ, inf_edist_closure, inf_edist_thickening hδ] <;> infer_instance
    

@[simp]
theorem thickening_cthickening (hε : 0 < ε) (hδ : 0 ≤ δ) (s : Set E) :
    Thickening ε (Cthickening δ s) = Thickening (ε + δ) s := by
  obtain rfl | hδ := hδ.eq_or_lt
  · rw [cthickening_zero, thickening_closure, add_zeroₓ]
    
  · rw [← closure_thickening hδ, thickening_closure, thickening_thickening hε hδ] <;> infer_instance
    

@[simp]
theorem cthickening_cthickening (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (s : Set E) :
    Cthickening ε (Cthickening δ s) = Cthickening (ε + δ) s :=
  (cthickening_cthickening_subset hε hδ _).antisymm fun x => by
    simp_rw [mem_cthickening_iff, Ennreal.of_real_add hε hδ, inf_edist_cthickening]
    exact tsub_le_iff_right.2

@[simp]
theorem thickening_ball (hε : 0 < ε) (hδ : 0 < δ) (x : E) : Thickening ε (Ball x δ) = Ball x (ε + δ) := by
  rw [← thickening_singleton, thickening_thickening hε hδ, thickening_singleton] <;> infer_instance

@[simp]
theorem thickening_closed_ball (hε : 0 < ε) (hδ : 0 ≤ δ) (x : E) : Thickening ε (ClosedBall x δ) = Ball x (ε + δ) := by
  rw [← cthickening_singleton _ hδ, thickening_cthickening hε hδ, thickening_singleton] <;> infer_instance

@[simp]
theorem cthickening_ball (hε : 0 ≤ ε) (hδ : 0 < δ) (x : E) : Cthickening ε (Ball x δ) = ClosedBall x (ε + δ) := by
  rw [← thickening_singleton, cthickening_thickening hε hδ, cthickening_singleton _ (add_nonneg hε hδ.le)] <;>
    infer_instance

@[simp]
theorem cthickening_closed_ball (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (x : E) :
    Cthickening ε (ClosedBall x δ) = ClosedBall x (ε + δ) := by
  rw [← cthickening_singleton _ hδ, cthickening_cthickening hε hδ, cthickening_singleton _ (add_nonneg hε hδ)] <;>
    infer_instance

theorem ball_add_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) : Ball a ε + Ball b δ = Ball (a + b) (ε + δ) := by
  rw [ball_add, thickening_ball hε hδ, vadd_ball, vadd_eq_add] <;> infer_instance

theorem ball_sub_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) : Ball a ε - Ball b δ = Ball (a - b) (ε + δ) := by
  simp_rw [sub_eq_add_neg, neg_ball, ball_add_ball hε hδ]

theorem ball_add_closed_ball (hε : 0 < ε) (hδ : 0 ≤ δ) (a b : E) : Ball a ε + ClosedBall b δ = Ball (a + b) (ε + δ) :=
  by
  rw [ball_add, thickening_closed_ball hε hδ, vadd_ball, vadd_eq_add] <;> infer_instance

theorem ball_sub_closed_ball (hε : 0 < ε) (hδ : 0 ≤ δ) (a b : E) : Ball a ε - ClosedBall b δ = Ball (a - b) (ε + δ) :=
  by
  simp_rw [sub_eq_add_neg, neg_closed_ball, ball_add_closed_ball hε hδ]

theorem closed_ball_add_ball (hε : 0 ≤ ε) (hδ : 0 < δ) (a b : E) : ClosedBall a ε + Ball b δ = Ball (a + b) (ε + δ) :=
  by
  rw [add_commₓ, ball_add_closed_ball hδ hε, add_commₓ, add_commₓ δ] <;> infer_instance

theorem closed_ball_sub_ball (hε : 0 ≤ ε) (hδ : 0 < δ) (a b : E) : ClosedBall a ε - Ball b δ = Ball (a - b) (ε + δ) :=
  by
  simp_rw [sub_eq_add_neg, neg_ball, closed_ball_add_ball hε hδ]

theorem closed_ball_add_closed_ball [ProperSpace E] (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (a b : E) :
    ClosedBall a ε + ClosedBall b δ = ClosedBall (a + b) (ε + δ) := by
  rw [(is_compact_closed_ball _ _).add_closed_ball hδ, cthickening_closed_ball hδ hε, vadd_closed_ball, vadd_eq_add,
      add_commₓ, add_commₓ δ] <;>
    infer_instance

theorem closed_ball_sub_closed_ball [ProperSpace E] (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (a b : E) :
    ClosedBall a ε - ClosedBall b δ = ClosedBall (a - b) (ε + δ) := by
  simp_rw [sub_eq_add_neg, neg_closed_ball, closed_ball_add_closed_ball hε hδ]

end SemiNormedGroup

section NormedGroup

variable [NormedGroup E] [NormedSpace 𝕜 E]

theorem smul_closed_ball (c : 𝕜) (x : E) {r : ℝ} (hr : 0 ≤ r) : c • ClosedBall x r = ClosedBall (c • x) (∥c∥ * r) := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [← hr, ← zero_smul_set, ← Set.singleton_zero, nonempty_closed_ball]
    
  · exact smul_closed_ball' hc x r
    

theorem smul_closed_unit_ball (c : 𝕜) : c • ClosedBall (0 : E) (1 : ℝ) = ClosedBall (0 : E) ∥c∥ := by
  rw [smul_closed_ball _ _ zero_le_one, smul_zero, mul_oneₓ]

variable [NormedSpace ℝ E]

/-- In a real normed space, the image of the unit closed ball under multiplication by a nonnegative
number `r` is the closed ball of radius `r` with center at the origin. -/
theorem smul_closed_unit_ball_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r • ClosedBall 0 1 = ClosedBall (0 : E) r := by
  rw [smul_closed_unit_ball, Real.norm_of_nonneg hr]

/-- In a nontrivial real normed space, a sphere is nonempty if and only if its radius is
nonnegative. -/
@[simp]
theorem NormedSpace.sphere_nonempty [Nontrivial E] {x : E} {r : ℝ} : (Sphere x r).Nonempty ↔ 0 ≤ r := by
  obtain ⟨y, hy⟩ := exists_ne x
  refine'
    ⟨fun h => nonempty_closed_ball.1 (h.mono sphere_subset_closed_ball), fun hr => ⟨r • ∥y - x∥⁻¹ • (y - x) + x, _⟩⟩
  have : ∥y - x∥ ≠ 0 := by
    simpa [← sub_eq_zero]
  simp [← norm_smul, ← this, ← Real.norm_of_nonneg hr]

theorem smul_sphere [Nontrivial E] (c : 𝕜) (x : E) {r : ℝ} (hr : 0 ≤ r) : c • Sphere x r = Sphere (c • x) (∥c∥ * r) :=
  by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [← zero_smul_set, ← Set.singleton_zero, ← hr]
    
  · exact smul_sphere' hc x r
    

/-- Any ball `metric.ball x r`, `0 < r` is the image of the unit ball under `λ y, x + r • y`. -/
theorem affinity_unit_ball {r : ℝ} (hr : 0 < r) (x : E) : x +ᵥ r • Ball 0 1 = Ball x r := by
  rw [smul_unit_ball_of_pos hr, vadd_ball_zero]

/-- Any closed ball `metric.closed_ball x r`, `0 ≤ r` is the image of the unit closed ball under
`λ y, x + r • y`. -/
theorem affinity_unit_closed_ball {r : ℝ} (hr : 0 ≤ r) (x : E) : x +ᵥ r • ClosedBall 0 1 = ClosedBall x r := by
  rw [smul_closed_unit_ball, Real.norm_of_nonneg hr, vadd_closed_ball_zero]

end NormedGroup

