/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel
-/
import Mathbin.MeasureTheory.Measure.Lebesgue
import Mathbin.MeasureTheory.Measure.Haar
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.Analysis.NormedSpace.Pointwise
import Mathbin.MeasureTheory.Group.Pointwise

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`, in
`measure_theory.add_haar_measure_eq_volume` and `measure_theory.add_haar_measure_eq_volume_pi`.

We deduce basic properties of any Haar measure on a finite dimensional real vector space:
* `map_linear_map_add_haar_eq_smul_add_haar`: a linear map rescales the Haar measure by the
  absolute value of its determinant.
* `add_haar_preimage_linear_map` : when `f` is a linear map with nonzero determinant, the measure
  of `f ⁻¹' s` is the measure of `s` multiplied by the absolute value of the inverse of the
  determinant of `f`.
* `add_haar_image_linear_map` :  when `f` is a linear map, the measure of `f '' s` is the
  measure of `s` multiplied by the absolute value of the determinant of `f`.
* `add_haar_submodule` : a strict submodule has measure `0`.
* `add_haar_smul` : the measure of `r • s` is `|r| ^ dim * μ s`.
* `add_haar_ball`: the measure of `ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_closed_ball`: the measure of `closed_ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_sphere`: spheres have zero measure.

We also show that a Lebesgue density point `x` of a set `s` (with respect to closed balls) has
density one for the rescaled copies `{x} + r • t` of a given set `t` with positive measure, in
`tendsto_add_haar_inter_smul_one_of_density_one`. In particular, `s` intersects `{x} + r • t` for
small `r`, see `eventually_nonempty_inter_smul_of_density_one`.
-/


open TopologicalSpace Set Filter Metric

open Ennreal Pointwise TopologicalSpace

/-- The interval `[0,1]` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.icc01 : PositiveCompacts ℝ where
  Carrier := Icc 0 1
  compact' := is_compact_Icc
  interior_nonempty' := by
    simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]

universe u

/-- The set `[0,1]^ι` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.piIcc01 (ι : Type _) [Fintype ι] : PositiveCompacts (ι → ℝ) where
  Carrier := pi Univ fun i => Icc 0 1
  compact' := is_compact_univ_pi fun i => is_compact_Icc
  interior_nonempty' := by
    simp only [← interior_pi_set, ← Set.to_finite, ← interior_Icc, ← univ_pi_nonempty_iff, ← nonempty_Ioo, ←
      implies_true_iff, ← zero_lt_one]

namespace MeasureTheory

open Measureₓ TopologicalSpace.PositiveCompacts FiniteDimensional

/-!
### The Lebesgue measure is a Haar measure on `ℝ` and on `ℝ^ι`.
-/


/-- The Haar measure equals the Lebesgue measure on `ℝ`. -/
theorem add_haar_measure_eq_volume : addHaarMeasure icc01 = volume := by
  convert (add_haar_measure_unique volume Icc01).symm
  simp [← Icc01]

instance : IsAddHaarMeasure (volume : Measure ℝ) := by
  rw [← add_haar_measure_eq_volume]
  infer_instance

/-- The Haar measure equals the Lebesgue measure on `ℝ^ι`. -/
theorem add_haar_measure_eq_volume_pi (ι : Type _) [Fintype ι] : addHaarMeasure (piIcc01 ι) = volume := by
  convert (add_haar_measure_unique volume (pi_Icc01 ι)).symm
  simp only [← pi_Icc01, ← volume_pi_pi fun i => Icc (0 : ℝ) 1, ← positive_compacts.coe_mk, ← compacts.coe_mk, ←
    Finset.prod_const_one, ← Ennreal.of_real_one, ← Real.volume_Icc, ← one_smul, ← sub_zero]

instance is_add_haar_measure_volume_pi (ι : Type _) [Fintype ι] : IsAddHaarMeasure (volume : Measure (ι → ℝ)) := by
  rw [← add_haar_measure_eq_volume_pi]
  infer_instance

namespace Measureₓ

/-!
### Strict subspaces have zero measure
-/


/-- If a set is disjoint of its translates by infinitely many bounded vectors, then it has measure
zero. This auxiliary lemma proves this assuming additionally that the set is bounded. -/
theorem add_haar_eq_zero_of_disjoint_translates_aux {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E} (u : ℕ → E) (sb : Bounded s)
    (hu : Bounded (Range u)) (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  by_contra h
  apply lt_irreflₓ ∞
  calc ∞ = ∑' n : ℕ, μ s := (Ennreal.tsum_const_eq_top_of_ne_zero h).symm _ = ∑' n : ℕ, μ ({u n} + s) := by
      congr 1
      ext1 n
      simp only [← image_add_left, ← measure_preimage_add, ← singleton_add]_ = μ (⋃ n, {u n} + s) := by
      rw
        [measure_Union hs fun n => by
          simpa only [← image_add_left, ← singleton_add] using measurable_id.const_add _ h's]_ = μ (range u + s) :=
      by
      rw [← Union_add, Union_singleton_eq_range]_ < ∞ := bounded.measure_lt_top (hu.add sb)

/-- If a set is disjoint of its translates by infinitely many bounded vectors, then it has measure
zero. -/
theorem add_haar_eq_zero_of_disjoint_translates {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E} (u : ℕ → E)
    (hu : Bounded (Range u)) (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  suffices H : ∀ R, μ (s ∩ closed_ball 0 R) = 0
  · apply le_antisymmₓ _ (zero_le _)
    calc μ s ≤ ∑' n : ℕ, μ (s ∩ closed_ball 0 n) := by
        conv_lhs => rw [← Union_inter_closed_ball_nat s 0]
        exact measure_Union_le _ _ = 0 := by
        simp only [← H, ← tsum_zero]
    
  intro R
  apply
    add_haar_eq_zero_of_disjoint_translates_aux μ u (bounded.mono (inter_subset_right _ _) bounded_closed_ball) hu _
      (h's.inter measurable_set_closed_ball)
  apply PairwiseDisjoint.mono hs fun n => _
  exact add_subset_add (subset.refl _) (inter_subset_left _ _)

/-- A strict vector subspace has measure zero. -/
theorem add_haar_submodule {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (s : Submodule ℝ E) (hs : s ≠ ⊤) : μ s = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ s := by
    simpa only [← Submodule.eq_top_iff', ← not_exists, ← Ne.def, ← not_forall] using hs
  obtain ⟨c, cpos, cone⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 :=
    ⟨1 / 2, by
      norm_num, by
      norm_num⟩
  have A : bounded (range fun n : ℕ => c ^ n • x) := by
    have : tendsto (fun n : ℕ => c ^ n • x) at_top (𝓝 ((0 : ℝ) • x)) :=
      (tendsto_pow_at_top_nhds_0_of_lt_1 cpos.le cone).smul_const x
    exact bounded_range_of_tendsto _ this
  apply add_haar_eq_zero_of_disjoint_translates μ _ A _ (Submodule.closed_of_finite_dimensional s).MeasurableSet
  intro m n hmn
  simp only [← Function.onFun, ← image_add_left, ← singleton_add, ← disjoint_left, ← mem_preimage, ← SetLike.mem_coe]
  intro y hym hyn
  have A : (c ^ n - c ^ m) • x ∈ s := by
    convert s.sub_mem hym hyn
    simp only [← sub_smul, ← neg_sub_neg, ← add_sub_add_right_eq_sub]
  have H : c ^ n - c ^ m ≠ 0 := by
    simpa only [← sub_eq_zero, ← Ne.def] using (strict_anti_pow cpos cone).Injective.Ne hmn.symm
  have : x ∈ s := by
    convert s.smul_mem (c ^ n - c ^ m)⁻¹ A
    rw [smul_smul, inv_mul_cancel H, one_smul]
  exact hx this

/-- A strict affine subspace has measure zero. -/
theorem add_haar_affine_subspace {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (s : AffineSubspace ℝ E) (hs : s ≠ ⊤) : μ s = 0 := by
  rcases s.eq_bot_or_nonempty with (rfl | hne)
  · rw [AffineSubspace.bot_coe, measure_empty]
    
  rw [Ne.def, ← AffineSubspace.direction_eq_top_iff_of_nonempty hne] at hs
  rcases hne with ⟨x, hx : x ∈ s⟩
  simpa only [← AffineSubspace.coe_direction_eq_vsub_set_right hx, ← vsub_eq_sub, ← sub_eq_add_neg, ← image_add_right, ←
    neg_negₓ, ← measure_preimage_add_right] using add_haar_submodule μ s.direction hs

/-!
### Applying a linear map rescales Haar measure by the determinant

We first prove this on `ι → ℝ`, using that this is already known for the product Lebesgue
measure (thanks to matrices computations). Then, we extend this to any finite-dimensional real
vector space by using a linear equiv with a space of the form `ι → ℝ`, and arguing that such a
linear equiv maps Haar measure to Haar measure.
-/


theorem map_linear_map_add_haar_pi_eq_smul_add_haar {ι : Type _} [Fintype ι] {f : (ι → ℝ) →ₗ[ℝ] ι → ℝ} (hf : f.det ≠ 0)
    (μ : Measure (ι → ℝ)) [IsAddHaarMeasure μ] : Measure.map f μ = Ennreal.ofReal (abs f.det⁻¹) • μ := by
  /- We have already proved the result for the Lebesgue product measure, using matrices.
    We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := add_haar_measure_unique μ (pi_Icc01 ι)
  rw [this, add_haar_measure_eq_volume_pi, measure.map_smul, Real.map_linear_map_volume_pi_eq_smul_volume_pi hf,
    smul_comm]

theorem map_linear_map_add_haar_eq_smul_add_haar {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) :
    Measure.map f μ = Ennreal.ofReal (abs f.det⁻¹) • μ := by
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `map_linear_map_add_haar_pi_eq_smul_add_haar`.
  let ι := Finₓ (finrank ℝ E)
  have : FiniteDimensional ℝ (ι → ℝ) := by
    infer_instance
  have : finrank ℝ E = finrank ℝ (ι → ℝ) := by
    simp
  have e : E ≃ₗ[ℝ] ι → ℝ := linear_equiv.of_finrank_eq E (ι → ℝ) this
  -- next line is to avoid `g` getting reduced by `simp`.
  obtain ⟨g, hg⟩ : ∃ g, g = (e : E →ₗ[ℝ] ι → ℝ).comp (f.comp (e.symm : (ι → ℝ) →ₗ[ℝ] E)) := ⟨_, rfl⟩
  have gdet : g.det = f.det := by
    rw [hg]
    exact LinearMap.det_conj f e
  rw [← gdet] at hf⊢
  have fg : f = (e.symm : (ι → ℝ) →ₗ[ℝ] E).comp (g.comp (e : E →ₗ[ℝ] ι → ℝ)) := by
    ext x
    simp only [← LinearEquiv.coe_coe, ← Function.comp_app, ← LinearMap.coe_comp, ← LinearEquiv.symm_apply_apply, ← hg]
  simp only [← fg, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp]
  have Ce : Continuous e := (e : E →ₗ[ℝ] ι → ℝ).continuous_of_finite_dimensional
  have Cg : Continuous g := LinearMap.continuous_of_finite_dimensional g
  have Cesymm : Continuous e.symm := (e.symm : (ι → ℝ) →ₗ[ℝ] E).continuous_of_finite_dimensional
  rw [← map_map Cesymm.measurable (Cg.comp Ce).Measurable, ← map_map Cg.measurable Ce.measurable]
  have : is_add_haar_measure (map e μ) := is_add_haar_measure_map μ e.to_add_equiv Ce Cesymm
  have ecomp : e.symm ∘ e = id := by
    ext x
    simp only [← id.def, ← Function.comp_app, ← LinearEquiv.symm_apply_apply]
  rw [map_linear_map_add_haar_pi_eq_smul_add_haar hf (map e μ), measure.map_smul,
    map_map Cesymm.measurable Ce.measurable, ecomp, measure.map_id]

/-- The preimage of a set `s` under a linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_linear_map {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = Ennreal.ofReal (abs f.det⁻¹) * μ s :=
  calc
    μ (f ⁻¹' s) = Measure.map f μ s :=
      ((f.equivOfDetNeZero hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply s).symm
    _ = Ennreal.ofReal (abs f.det⁻¹) * μ s := by
      rw [map_linear_map_add_haar_eq_smul_add_haar μ hf]
      rfl
    

/-- The preimage of a set `s` under a continuous linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_continuous_linear_map {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {f : E →L[ℝ] E}
    (hf : LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = Ennreal.ofReal (abs (LinearMap.det (f : E →ₗ[ℝ] E))⁻¹) * μ s :=
  add_haar_preimage_linear_map μ hf s

/-- The preimage of a set `s` under a linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_linear_equiv {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (f : E ≃ₗ[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = Ennreal.ofReal (abs (f.symm : E →ₗ[ℝ] E).det) * μ s := by
  have A : (f : E →ₗ[ℝ] E).det ≠ 0 := (LinearEquiv.is_unit_det' f).ne_zero
  convert add_haar_preimage_linear_map μ A s
  simp only [← LinearEquiv.det_coe_symm]

/-- The preimage of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_continuous_linear_equiv {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = Ennreal.ofReal (abs (f.symm : E →ₗ[ℝ] E).det) * μ s :=
  add_haar_preimage_linear_equiv μ _ s

/-- The image of a set `s` under a linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem add_haar_image_linear_map {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (f : E →ₗ[ℝ] E) (s : Set E) :
    μ (f '' s) = Ennreal.ofReal (abs f.det) * μ s := by
  rcases ne_or_eq f.det 0 with (hf | hf)
  · let g := (f.equiv_of_det_ne_zero hf).toContinuousLinearEquiv
    change μ (g '' s) = _
    rw [ContinuousLinearEquiv.image_eq_preimage g s, add_haar_preimage_continuous_linear_equiv]
    congr
    ext x
    simp only [← LinearEquiv.coe_to_continuous_linear_equiv, ← LinearEquiv.of_is_unit_det_apply, ← LinearEquiv.coe_coe,
      ← ContinuousLinearEquiv.symm_symm]
    
  · simp only [← hf, ← zero_mul, ← Ennreal.of_real_zero, ← abs_zero]
    have : μ f.range = 0 := add_haar_submodule μ _ (LinearMap.range_lt_top_of_det_eq_zero hf).Ne
    exact le_antisymmₓ (le_transₓ (measure_mono (image_subset_range _ _)) this.le) (zero_le _)
    

/-- The image of a set `s` under a continuous linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem add_haar_image_continuous_linear_map {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (f : E →L[ℝ] E) (s : Set E) :
    μ (f '' s) = Ennreal.ofReal (abs (f : E →ₗ[ℝ] E).det) * μ s :=
  add_haar_image_linear_map μ _ s

/-- The image of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem add_haar_image_continuous_linear_equiv {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f '' s) = Ennreal.ofReal (abs (f : E →ₗ[ℝ] E).det) * μ s :=
  μ.add_haar_image_linear_map (f : E →ₗ[ℝ] E) s

/-!
### Basic properties of Haar measures on real vector spaces
-/


variable {E : Type _} [NormedGroup E] [MeasurableSpace E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

theorem map_add_haar_smul {r : ℝ} (hr : r ≠ 0) :
    Measure.map ((· • ·) r) μ = Ennreal.ofReal (abs (r ^ finrank ℝ E)⁻¹) • μ := by
  let f : E →ₗ[ℝ] E := r • 1
  change measure.map f μ = _
  have hf : f.det ≠ 0 := by
    simp only [← mul_oneₓ, ← LinearMap.det_smul, ← Ne.def, ← MonoidHom.map_one]
    intro h
    exact hr (pow_eq_zero h)
  simp only [← map_linear_map_add_haar_eq_smul_add_haar μ hf, ← mul_oneₓ, ← LinearMap.det_smul, ← MonoidHom.map_one]

@[simp]
theorem add_haar_preimage_smul {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    μ ((· • ·) r ⁻¹' s) = Ennreal.ofReal (abs (r ^ finrank ℝ E)⁻¹) * μ s :=
  calc
    μ ((· • ·) r ⁻¹' s) = Measure.map ((· • ·) r) μ s :=
      ((Homeomorph.smul (is_unit_iff_ne_zero.2 hr).Unit).toMeasurableEquiv.map_apply s).symm
    _ = Ennreal.ofReal (abs (r ^ finrank ℝ E)⁻¹) * μ s := by
      rw [map_add_haar_smul μ hr]
      rfl
    

/-- Rescaling a set by a factor `r` multiplies its measure by `abs (r ^ dim)`. -/
@[simp]
theorem add_haar_smul (r : ℝ) (s : Set E) : μ (r • s) = Ennreal.ofReal (abs (r ^ finrank ℝ E)) * μ s := by
  rcases ne_or_eq r 0 with (h | rfl)
  · rw [← preimage_smul_inv₀ h, add_haar_preimage_smul μ (inv_ne_zero h), inv_pow, inv_invₓ]
    
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp only [← measure_empty, ← mul_zero, ← smul_set_empty]
    
  rw [zero_smul_set hs, ← singleton_zero]
  by_cases' h : finrank ℝ E = 0
  · have : Subsingleton E := finrank_zero_iff.1 h
    simp only [← h, ← one_mulₓ, ← Ennreal.of_real_one, ← abs_one, ← Subsingleton.eq_univ_of_nonempty hs, ← pow_zeroₓ, ←
      Subsingleton.eq_univ_of_nonempty (singleton_nonempty (0 : E))]
    
  · have : Nontrivial E := nontrivial_of_finrank_pos (bot_lt_iff_ne_bot.2 h)
    simp only [← h, ← zero_mul, ← Ennreal.of_real_zero, ← abs_zero, ← Ne.def, ← not_false_iff, ← zero_pow', ←
      measure_singleton]
    

@[simp]
theorem add_haar_image_homothety (x : E) (r : ℝ) (s : Set E) :
    μ (AffineMap.homothety x r '' s) = Ennreal.ofReal (abs (r ^ finrank ℝ E)) * μ s :=
  calc
    μ (AffineMap.homothety x r '' s) = μ ((fun y => y + x) '' (r • (fun y => y + -x) '' s)) := by
      simp only [image_smul, ← image_image, sub_eq_add_neg]
      rfl
    _ = Ennreal.ofReal (abs (r ^ finrank ℝ E)) * μ s := by
      simp only [← image_add_right, ← measure_preimage_add_right, ← add_haar_smul]
    

/-! We don't need to state `map_add_haar_neg` here, because it has already been proved for
general Haar measures on general commutative groups. -/


/-! ### Measure of balls -/


theorem add_haar_ball_center {E : Type _} [NormedGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [IsAddHaarMeasure μ] (x : E) (r : ℝ) : μ (Ball x r) = μ (Ball (0 : E) r) := by
  have : ball (0 : E) r = (· + ·) x ⁻¹' ball x r := by
    simp [← preimage_add_ball]
  rw [this, measure_preimage_add]

theorem add_haar_closed_ball_center {E : Type _} [NormedGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [IsAddHaarMeasure μ] (x : E) (r : ℝ) : μ (ClosedBall x r) = μ (ClosedBall (0 : E) r) := by
  have : closed_ball (0 : E) r = (· + ·) x ⁻¹' closed_ball x r := by
    simp [← preimage_add_closed_ball]
  rw [this, measure_preimage_add]

theorem add_haar_ball_mul_of_pos (x : E) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    μ (Ball x (r * s)) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (Ball 0 s) := by
  have : ball (0 : E) (r * s) = r • ball 0 s := by
    simp only [← smul_ball hr.ne' (0 : E) s, ← Real.norm_eq_abs, ← abs_of_nonneg hr.le, ← smul_zero]
  simp only [← this, ← add_haar_smul, ← abs_of_nonneg hr.le, ← add_haar_ball_center, ← abs_pow]

theorem add_haar_ball_of_pos (x : E) {r : ℝ} (hr : 0 < r) :
    μ (Ball x r) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (Ball 0 1) := by
  rw [← add_haar_ball_mul_of_pos μ x hr, mul_oneₓ]

theorem add_haar_ball_mul [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    μ (Ball x (r * s)) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (Ball 0 s) := by
  rcases LE.le.eq_or_lt hr with (h | h)
  · simp only [h, ← zero_pow finrank_pos, ← measure_empty, ← zero_mul, ← Ennreal.of_real_zero, ← ball_zero]
    
  · exact add_haar_ball_mul_of_pos μ x h s
    

theorem add_haar_ball [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (Ball x r) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (Ball 0 1) := by
  rw [← add_haar_ball_mul μ x hr, mul_oneₓ]

theorem add_haar_closed_ball_mul_of_pos (x : E) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    μ (ClosedBall x (r * s)) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (ClosedBall 0 s) := by
  have : closed_ball (0 : E) (r * s) = r • closed_ball 0 s := by
    simp [← smul_closed_ball' hr.ne' (0 : E), ← abs_of_nonneg hr.le]
  simp only [← this, ← add_haar_smul, ← abs_of_nonneg hr.le, ← add_haar_closed_ball_center, ← abs_pow]

theorem add_haar_closed_ball_mul (x : E) {r : ℝ} (hr : 0 ≤ r) {s : ℝ} (hs : 0 ≤ s) :
    μ (ClosedBall x (r * s)) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (ClosedBall 0 s) := by
  have : closed_ball (0 : E) (r * s) = r • closed_ball 0 s := by
    simp [← smul_closed_ball r (0 : E) hs, ← abs_of_nonneg hr]
  simp only [← this, ← add_haar_smul, ← abs_of_nonneg hr, ← add_haar_closed_ball_center, ← abs_pow]

/-- The measure of a closed ball can be expressed in terms of the measure of the closed unit ball.
Use instead `add_haar_closed_ball`, which uses the measure of the open unit ball as a standard
form. -/
theorem add_haar_closed_ball' (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (ClosedBall x r) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (ClosedBall 0 1) := by
  rw [← add_haar_closed_ball_mul μ x hr zero_le_one, mul_oneₓ]

theorem add_haar_closed_unit_ball_eq_add_haar_unit_ball : μ (ClosedBall (0 : E) 1) = μ (Ball 0 1) := by
  apply le_antisymmₓ _ (measure_mono ball_subset_closed_ball)
  have A :
    tendsto (fun r : ℝ => Ennreal.ofReal (r ^ finrank ℝ E) * μ (closed_ball (0 : E) 1)) (𝓝[<] 1)
      (𝓝 (Ennreal.ofReal (1 ^ finrank ℝ E) * μ (closed_ball (0 : E) 1))) :=
    by
    refine'
      Ennreal.Tendsto.mul _
        (by
          simp )
        tendsto_const_nhds
        (by
          simp )
    exact Ennreal.tendsto_of_real ((tendsto_id'.2 nhds_within_le_nhds).pow _)
  simp only [← one_pow, ← one_mulₓ, ← Ennreal.of_real_one] at A
  refine' le_of_tendsto A _
  refine'
    mem_nhds_within_Iio_iff_exists_Ioo_subset.2
      ⟨(0 : ℝ), by
        simp , fun r hr => _⟩
  dsimp'
  rw [← add_haar_closed_ball' μ (0 : E) hr.1.le]
  exact measure_mono (closed_ball_subset_ball hr.2)

theorem add_haar_closed_ball (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (ClosedBall x r) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (Ball 0 1) := by
  rw [add_haar_closed_ball' μ x hr, add_haar_closed_unit_ball_eq_add_haar_unit_ball]

theorem add_haar_sphere_of_ne_zero (x : E) {r : ℝ} (hr : r ≠ 0) : μ (Sphere x r) = 0 := by
  rcases hr.lt_or_lt with (h | h)
  · simp only [← empty_diff, ← measure_empty, closed_ball_diff_ball, ← closed_ball_eq_empty.2 h]
    
  · rw [← closed_ball_diff_ball, measure_diff ball_subset_closed_ball measurable_set_ball measure_ball_lt_top.ne,
        add_haar_ball_of_pos μ _ h, add_haar_closed_ball μ _ h.le, tsub_self] <;>
      infer_instance
    

theorem add_haar_sphere [Nontrivial E] (x : E) (r : ℝ) : μ (Sphere x r) = 0 := by
  rcases eq_or_ne r 0 with (rfl | h)
  · rw [sphere_zero, measure_singleton]
    
  · exact add_haar_sphere_of_ne_zero μ x h
    

theorem add_haar_singleton_add_smul_div_singleton_add_smul {r : ℝ} (hr : r ≠ 0) (x y : E) (s t : Set E) :
    μ ({x} + r • s) / μ ({y} + r • t) = μ s / μ t :=
  calc
    μ ({x} + r • s) / μ ({y} + r • t) =
        Ennreal.ofReal (abs r ^ finrank ℝ E) * μ s * (Ennreal.ofReal (abs r ^ finrank ℝ E) * μ t)⁻¹ :=
      by
      simp only [← div_eq_mul_inv, ← add_haar_smul, ← image_add_left, ← measure_preimage_add, ← abs_pow, ←
        singleton_add]
    _ = Ennreal.ofReal (abs r ^ finrank ℝ E) * (Ennreal.ofReal (abs r ^ finrank ℝ E))⁻¹ * (μ s * (μ t)⁻¹) := by
      rw [Ennreal.mul_inv]
      · ring
        
      · simp only [← pow_pos (abs_pos.mpr hr), ← Ennreal.of_real_eq_zero, ← not_leₓ, ← Ne.def, ← true_orₓ]
        
      · simp only [← Ennreal.of_real_ne_top, ← true_orₓ, ← Ne.def, ← not_false_iff]
        
    _ = μ s / μ t := by
      rw [Ennreal.mul_inv_cancel, one_mulₓ, div_eq_mul_inv]
      · simp only [← pow_pos (abs_pos.mpr hr), ← Ennreal.of_real_eq_zero, ← not_leₓ, ← Ne.def]
        
      · simp only [← Ennreal.of_real_ne_top, ← Ne.def, ← not_false_iff]
        
    

/-!
### Density points

Besicovitch covering theorem ensures that, for any locally finite measure on a finite-dimensional
real vector space, almost every point of a set `s` is a density point, i.e.,
`μ (s ∩ closed_ball x r) / μ (closed_ball x r)` tends to `1` as `r` tends to `0`
(see `besicovitch.ae_tendsto_measure_inter_div`).
When `μ` is a Haar measure, one can deduce the same property for any rescaling sequence of sets,
of the form `{x} + r • t` where `t` is a set with positive finite measure, instead of the sequence
of closed balls.

We argue first for the dual property, i.e., if `s` has density `0` at `x`, then
`μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)` tends to `0`. First when `t` is contained in the ball
of radius `1`, in `tendsto_add_haar_inter_smul_zero_of_density_zero_aux1`,
(by arguing by inclusion). Then when `t` is bounded, reducing to the previous one by rescaling, in
`tendsto_add_haar_inter_smul_zero_of_density_zero_aux2`.
Then for a general set `t`, by cutting it into a bounded part and a part with small measure, in
`tendsto_add_haar_inter_smul_zero_of_density_zero`.
Going to the complement, one obtains the desired property at points of density `1`, first when
`s` is measurable in `tendsto_add_haar_inter_smul_one_of_density_one_aux`, and then without this
assumption in `tendsto_add_haar_inter_smul_one_of_density_one` by applying the previous lemma to
the measurable hull `to_measurable μ s`
-/


theorem tendsto_add_haar_inter_smul_zero_of_density_zero_aux1 (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ ClosedBall x r) / μ (ClosedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E) (u : Set E)
    (h'u : μ u ≠ 0) (t_bound : t ⊆ ClosedBall 0 1) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0) := by
  have A : tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ (closed_ball x r)) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h (eventually_of_forall fun b => zero_le _)
    filter_upwards [self_mem_nhds_within]
    rintro r (rpos : 0 < r)
    apply Ennreal.mul_le_mul (measure_mono (inter_subset_inter_right _ _)) le_rfl
    intro y hy
    have : y - x ∈ r • closed_ball (0 : E) 1 := by
      apply smul_set_mono t_bound
      simpa [← neg_add_eq_sub] using hy
    simpa only [← smul_closed_ball _ _ zero_le_one, ← Real.norm_of_nonneg rpos.le, ← mem_closed_ball_iff_norm, ←
      mul_oneₓ, ← sub_zero, ← smul_zero]
  have B :
    tendsto (fun r : ℝ => μ (closed_ball x r) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 (μ (closed_ball x 1) / μ ({x} + u))) := by
    apply tendsto_const_nhds.congr' _
    filter_upwards [self_mem_nhds_within]
    rintro r (rpos : 0 < r)
    have : closed_ball x r = {x} + r • closed_ball 0 1 := by
      simp only [← smul_closed_ball, ← Real.norm_of_nonneg rpos.le, ← zero_le_one, ← add_zeroₓ, ← mul_oneₓ, ←
        singleton_add_closed_ball, ← smul_zero]
    simp only [← this, ← add_haar_singleton_add_smul_div_singleton_add_smul μ rpos.ne']
    simp only [← add_haar_closed_ball_center, ← image_add_left, ← measure_preimage_add, ← singleton_add]
  have C :
    tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ (closed_ball x r) * (μ (closed_ball x r) / μ ({x} + r • u)))
      (𝓝[>] 0) (𝓝 (0 * (μ (closed_ball x 1) / μ ({x} + u)))) :=
    by
    apply Ennreal.Tendsto.mul A _ B (Or.inr Ennreal.zero_ne_top)
    simp only [← Ennreal.div_eq_top, ← h'u, ← measure_closed_ball_lt_top.ne, ← false_orₓ, ← image_add_left, ←
      eq_self_iff_true, ← not_true, ← Ne.def, ← not_false_iff, ← measure_preimage_add, ← singleton_add, ← and_falseₓ, ←
      false_andₓ]
  simp only [← zero_mul] at C
  apply C.congr' _
  filter_upwards [self_mem_nhds_within]
  rintro r (rpos : 0 < r)
  calc
    μ (s ∩ ({x} + r • t)) / μ (closed_ball x r) * (μ (closed_ball x r) / μ ({x} + r • u)) =
        μ (closed_ball x r) * (μ (closed_ball x r))⁻¹ * (μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) :=
      by
      simp only [← div_eq_mul_inv]
      ring _ = μ (s ∩ ({x} + r • t)) / μ ({x} + r • u) := by
      rw [Ennreal.mul_inv_cancel (measure_closed_ball_pos μ x rpos).ne' measure_closed_ball_lt_top.ne, one_mulₓ]

theorem tendsto_add_haar_inter_smul_zero_of_density_zero_aux2 (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ ClosedBall x r) / μ (ClosedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E) (u : Set E)
    (h'u : μ u ≠ 0) (R : ℝ) (Rpos : 0 < R) (t_bound : t ⊆ ClosedBall 0 R) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0) := by
  set t' := R⁻¹ • t with ht'
  set u' := R⁻¹ • u with hu'
  have A : tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t')) / μ ({x} + r • u')) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_add_haar_inter_smul_zero_of_density_zero_aux1 μ s x h t' u'
    · simp only [← h'u, ← (pow_pos Rpos _).ne', ← abs_nonpos_iff, ← add_haar_smul, ← not_false_iff, ←
        Ennreal.of_real_eq_zero, ← inv_eq_zero, ← inv_pow, ← Ne.def, ← or_selfₓ, ← mul_eq_zero]
      
    · convert smul_set_mono t_bound
      rw [smul_closed_ball _ _ Rpos.le, smul_zero, Real.norm_of_nonneg (inv_nonneg.2 Rpos.le), inv_mul_cancel Rpos.ne']
      
  have B : tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] (R * 0)) := by
    apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
    · exact (tendsto_const_nhds.mul tendsto_id).mono_left nhds_within_le_nhds
      
    · filter_upwards [self_mem_nhds_within]
      intro r rpos
      rw [mul_zero]
      exact mul_pos Rpos rpos
      
  rw [mul_zero] at B
  apply (A.comp B).congr' _
  filter_upwards [self_mem_nhds_within]
  rintro r (rpos : 0 < r)
  have T : (R * r) • t' = r • t := by
    rw [mul_comm, ht', smul_smul, mul_assoc, mul_inv_cancel Rpos.ne', mul_oneₓ]
  have U : (R * r) • u' = r • u := by
    rw [mul_comm, hu', smul_smul, mul_assoc, mul_inv_cancel Rpos.ne', mul_oneₓ]
  dsimp'
  rw [T, U]

/-- Consider a point `x` at which a set `s` has density zero, with respect to closed balls. Then it
also has density zero with respect to any measurable set `t`: the proportion of points in `s`
belonging to a rescaled copy `{x} + r • t` of `t` tends to zero as `r` tends to zero. -/
theorem tendsto_add_haar_inter_smul_zero_of_density_zero (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ ClosedBall x r) / μ (ClosedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (ht : MeasurableSet t) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) := by
  refine' tendsto_order.2 ⟨fun a' ha' => (Ennreal.not_lt_zero ha').elim, fun ε (εpos : 0 < ε) => _⟩
  rcases eq_or_ne (μ t) 0 with (h't | h't)
  · apply eventually_of_forall fun r => _
    suffices H : μ (s ∩ ({x} + r • t)) = 0
    · rw [H]
      simpa only [← Ennreal.zero_div] using εpos
      
    apply le_antisymmₓ _ (zero_le _)
    calc μ (s ∩ ({x} + r • t)) ≤ μ ({x} + r • t) := measure_mono (inter_subset_right _ _)_ = 0 := by
        simp only [← h't, ← add_haar_smul, ← image_add_left, ← measure_preimage_add, ← singleton_add, ← mul_zero]
    
  obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ μ (t \ closed_ball 0 n) < ε / 2 * μ t := by
    have A : tendsto (fun n : ℕ => μ (t \ closed_ball 0 n)) at_top (𝓝 (μ (⋂ n : ℕ, t \ closed_ball 0 n))) := by
      have N : ∃ n : ℕ, μ (t \ closed_ball 0 n) ≠ ∞ := ⟨0, ((measure_mono (diff_subset t _)).trans_lt h''t.lt_top).Ne⟩
      refine' tendsto_measure_Inter (fun n => ht.diff measurable_set_closed_ball) (fun m n hmn => _) N
      exact diff_subset_diff subset.rfl (closed_ball_subset_closed_ball (Nat.cast_le.2 hmn))
    have : (⋂ n : ℕ, t \ closed_ball 0 n) = ∅ := by
      simp_rw [diff_eq, ← inter_Inter, Inter_eq_compl_Union_compl, compl_compl, Union_closed_ball_nat, compl_univ,
        inter_empty]
    simp only [← this, ← measure_empty] at A
    have I : 0 < ε / 2 * μ t := Ennreal.mul_pos (Ennreal.half_pos εpos.ne').ne' h't
    exact (eventually.and (Ioi_mem_at_top 0) ((tendsto_order.1 A).2 _ I)).exists
  have L : tendsto (fun r : ℝ => μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n))) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_add_haar_inter_smul_zero_of_density_zero_aux2 μ s x h _ t h't n (Nat.cast_pos.2 npos)
      (inter_subset_right _ _)
  filter_upwards [(tendsto_order.1 L).2 _ (Ennreal.half_pos εpos.ne'), self_mem_nhds_within]
  rintro r hr (rpos : 0 < r)
  have I : μ (s ∩ ({x} + r • t)) ≤ μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n))) + μ ({x} + r • (t \ closed_ball 0 n)) :=
    calc
      μ (s ∩ ({x} + r • t)) = μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n)) ∪ s ∩ ({x} + r • (t \ closed_ball 0 n))) := by
        rw [← inter_union_distrib_left, ← add_union, ← smul_set_union, inter_union_diff]
      _ ≤ μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n))) + μ (s ∩ ({x} + r • (t \ closed_ball 0 n))) := measure_union_le _ _
      _ ≤ μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n))) + μ ({x} + r • (t \ closed_ball 0 n)) :=
        add_le_add le_rfl (measure_mono (inter_subset_right _ _))
      
  calc
    μ (s ∩ ({x} + r • t)) / μ ({x} + r • t) ≤
        (μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n))) + μ ({x} + r • (t \ closed_ball 0 n))) / μ ({x} + r • t) :=
      Ennreal.mul_le_mul I le_rfl _ < ε / 2 + ε / 2 := by
      rw [Ennreal.add_div]
      apply Ennreal.add_lt_add hr _
      rwa [add_haar_singleton_add_smul_div_singleton_add_smul μ rpos.ne',
        Ennreal.div_lt_iff (Or.inl h't) (Or.inl h''t)]_ = ε :=
      Ennreal.add_halves _

theorem tendsto_add_haar_inter_smul_one_of_density_one_aux (s : Set E) (hs : MeasurableSet s) (x : E)
    (h : Tendsto (fun r => μ (s ∩ ClosedBall x r) / μ (ClosedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t ≠ 0) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
  have I : ∀ u v, μ u ≠ 0 → μ u ≠ ∞ → MeasurableSet v → μ u / μ u - μ (vᶜ ∩ u) / μ u = μ (v ∩ u) / μ u := by
    intro u v uzero utop vmeas
    simp_rw [div_eq_mul_inv]
    rw [← Ennreal.sub_mul]
    swap
    · simp only [← uzero, ← Ennreal.inv_eq_top, ← implies_true_iff, ← Ne.def, ← not_false_iff]
      
    congr 1
    apply Ennreal.sub_eq_of_add_eq (ne_top_of_le_ne_top utop (measure_mono (inter_subset_right _ _)))
    rw [inter_comm _ u, inter_comm _ u]
    exact measure_inter_add_diff u vmeas
  have L : tendsto (fun r => μ (sᶜ ∩ closed_ball x r) / μ (closed_ball x r)) (𝓝[>] 0) (𝓝 0) := by
    have A : tendsto (fun r => μ (closed_ball x r) / μ (closed_ball x r)) (𝓝[>] 0) (𝓝 1) := by
      apply tendsto_const_nhds.congr' _
      filter_upwards [self_mem_nhds_within]
      intro r hr
      rw [div_eq_mul_inv, Ennreal.mul_inv_cancel]
      · exact (measure_closed_ball_pos μ _ hr).ne'
        
      · exact measure_closed_ball_lt_top.ne
        
    have B := Ennreal.Tendsto.sub A h (Or.inl Ennreal.one_ne_top)
    simp only [← tsub_self] at B
    apply B.congr' _
    filter_upwards [self_mem_nhds_within]
    rintro r (rpos : 0 < r)
    convert I (closed_ball x r) (sᶜ) (measure_closed_ball_pos μ _ rpos).ne' measure_closed_ball_lt_top.Ne hs.compl
    rw [compl_compl]
  have L' : tendsto (fun r : ℝ => μ (sᶜ ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_add_haar_inter_smul_zero_of_density_zero μ (sᶜ) x L t ht h''t
  have L'' : tendsto (fun r : ℝ => μ ({x} + r • t) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_const_nhds.congr' _
    filter_upwards [self_mem_nhds_within]
    rintro r (rpos : 0 < r)
    rw [add_haar_singleton_add_smul_div_singleton_add_smul μ rpos.ne', Ennreal.div_self h't h''t]
  have := Ennreal.Tendsto.sub L'' L' (Or.inl Ennreal.one_ne_top)
  simp only [← tsub_zero] at this
  apply this.congr' _
  filter_upwards [self_mem_nhds_within]
  rintro r (rpos : 0 < r)
  refine' I ({x} + r • t) s _ _ hs
  · simp only [← h't, ← abs_of_nonneg rpos.le, ← pow_pos rpos, ← add_haar_smul, ← image_add_left, ←
      Ennreal.of_real_eq_zero, ← not_leₓ, ← or_falseₓ, ← Ne.def, ← measure_preimage_add, ← abs_pow, ← singleton_add, ←
      mul_eq_zero]
    
  · simp only [← h''t, ← Ennreal.of_real_ne_top, ← add_haar_smul, ← image_add_left, ← WithTop.mul_eq_top_iff, ← Ne.def,
      ← not_false_iff, ← measure_preimage_add, ← singleton_add, ← and_falseₓ, ← false_andₓ, ← or_selfₓ]
    

/-- Consider a point `x` at which a set `s` has density one, with respect to closed balls (i.e.,
a Lebesgue density point of `s`). Then `s` has also density one at `x` with respect to any
measurable set `t`: the proportion of points in `s` belonging to a rescaled copy `{x} + r • t`
of `t` tends to one as `r` tends to zero. -/
theorem tendsto_add_haar_inter_smul_one_of_density_one (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ ClosedBall x r) / μ (ClosedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t ≠ 0) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
  have : tendsto (fun r : ℝ => μ (to_measurable μ s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_add_haar_inter_smul_one_of_density_one_aux μ _ (measurable_set_to_measurable _ _) _ _ t ht h't h''t
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h tendsto_const_nhds
    · apply eventually_of_forall fun r => _
      apply Ennreal.mul_le_mul _ le_rfl
      exact measure_mono (inter_subset_inter_left _ (subset_to_measurable _ _))
      
    · filter_upwards [self_mem_nhds_within]
      rintro r (rpos : 0 < r)
      apply Ennreal.div_le_of_le_mul
      rw [one_mulₓ]
      exact measure_mono (inter_subset_right _ _)
      
  apply this.congr fun r => _
  congr 1
  apply measure_to_measurable_inter_of_sigma_finite
  simp only [← image_add_left, ← singleton_add]
  apply (continuous_add_left (-x)).Measurable (ht.const_smul₀ r)

/-- Consider a point `x` at which a set `s` has density one, with respect to closed balls (i.e.,
a Lebesgue density point of `s`). Then `s` intersects the rescaled copies `{x} + r • t` of a given
set `t` with positive measure, for any small enough `r`. -/
theorem eventually_nonempty_inter_smul_of_density_one (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ ClosedBall x r) / μ (ClosedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t ≠ 0) : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • t)).Nonempty := by
  obtain ⟨t', t'_meas, t't, t'pos, t'top⟩ : ∃ t', MeasurableSet t' ∧ t' ⊆ t ∧ 0 < μ t' ∧ μ t' < ⊤ :=
    exists_subset_measure_lt_top ht h't.bot_lt
  filter_upwards [(tendsto_order.1
          (tendsto_add_haar_inter_smul_one_of_density_one μ s x h t' t'_meas t'pos.ne' t'top.ne)).1
      0 Ennreal.zero_lt_one]
  intro r hr
  have : μ (s ∩ ({x} + r • t')) ≠ 0 := fun h' => by
    simpa only [← Ennreal.not_lt_zero, ← Ennreal.zero_div, ← h'] using hr
  have : (s ∩ ({x} + r • t')).Nonempty := nonempty_of_measure_ne_zero this
  apply this.mono (inter_subset_inter subset.rfl _)
  exact add_subset_add subset.rfl (smul_set_mono t't)

end Measureₓ

end MeasureTheory

