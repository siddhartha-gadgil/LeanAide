/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Algebra.Algebra.Spectrum
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.Analysis.SpecialFunctions.Exponential
import Mathbin.Analysis.Complex.Liouville
import Mathbin.Analysis.Analytic.RadiusLiminf

/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.

## Main definitions

* `spectral_radius : ℝ≥0∞`: supremum of `∥k∥₊` for all `k ∈ spectrum 𝕜 a`

## Main statements

* `spectrum.is_open_resolvent_set`: the resolvent set is open.
* `spectrum.is_closed`: the spectrum is closed.
* `spectrum.subset_closed_ball_norm`: the spectrum is a subset of closed disk of radius
  equal to the norm.
* `spectrum.is_compact`: the spectrum is compact.
* `spectrum.spectral_radius_le_nnnorm`: the spectral radius is bounded above by the norm.
* `spectrum.has_deriv_at_resolvent`: the resolvent function is differentiable on the resolvent set.
* `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius`: Gelfand's formula for the
  spectral radius in Banach algebras over `ℂ`.
* `spectrum.nonempty`: the spectrum of any element in a complex Banach algebra is nonempty.
* `normed_division_ring.alg_equiv_complex_of_complete`: **Gelfand-Mazur theorem** For a complex
  Banach division algebra, the natural `algebra_map ℂ A` is an algebra isomorphism whose inverse
  is given by selecting the (unique) element of `spectrum ℂ a`


## TODO

* compute all derivatives of `resolvent a`.

-/


open Ennreal

/-- The *spectral radius* is the supremum of the `nnnorm` (`∥⬝∥₊`) of elements in the spectrum,
    coerced into an element of `ℝ≥0∞`. Note that it is possible for `spectrum 𝕜 a = ∅`. In this
    case, `spectral_radius a = 0`.  It is also possible that `spectrum 𝕜 a` be unbounded (though
    not for Banach algebras, see `spectrum.is_bounded`, below).  In this case,
    `spectral_radius a = ∞`. -/
noncomputable def spectralRadius (𝕜 : Type _) {A : Type _} [NormedField 𝕜] [Ringₓ A] [Algebra 𝕜 A] (a : A) : ℝ≥0∞ :=
  ⨆ k ∈ Spectrum 𝕜 a, ∥k∥₊

variable {𝕜 : Type _} {A : Type _}

namespace Spectrum

section SpectrumCompact

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

-- mathport name: «exprσ»
local notation "σ" => Spectrum 𝕜

-- mathport name: «exprρ»
local notation "ρ" => ResolventSet 𝕜

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

theorem mem_resolvent_set_of_spectral_radius_lt {a : A} {k : 𝕜} (h : spectralRadius 𝕜 a < ∥k∥₊) : k ∈ ρ a :=
  not_not.mp fun hn => h.not_le <| le_supr₂ k hn

variable [CompleteSpace A]

theorem is_open_resolvent_set (a : A) : IsOpen (ρ a) :=
  Units.is_open.Preimage ((algebraMapClm 𝕜 A).Continuous.sub continuous_const)

theorem is_closed (a : A) : IsClosed (σ a) :=
  (is_open_resolvent_set a).is_closed_compl

theorem mem_resolvent_of_norm_lt [NormOneClass A] {a : A} {k : 𝕜} (h : ∥a∥ < ∥k∥) : k ∈ ρ a := by
  rw [ResolventSet, Set.mem_set_of_eq, Algebra.algebra_map_eq_smul_one]
  have hk : k ≠ 0 :=
    ne_zero_of_norm_ne_zero
      (by
        linarith [norm_nonneg a])
  let ku := Units.map ↑ₐ.toMonoidHom (Units.mk0 k hk)
  have hku : ∥-a∥ < ∥(↑ku⁻¹ : A)∥⁻¹ := by
    simpa [← ku, ← algebra_map_isometry] using h
  simpa [← ku, ← sub_eq_add_neg, ← Algebra.algebra_map_eq_smul_one] using (ku.add (-a) hku).IsUnit

theorem norm_le_norm_of_mem [NormOneClass A] {a : A} {k : 𝕜} (hk : k ∈ σ a) : ∥k∥ ≤ ∥a∥ :=
  le_of_not_ltₓ <| mt mem_resolvent_of_norm_lt hk

theorem subset_closed_ball_norm [NormOneClass A] (a : A) : σ a ⊆ Metric.ClosedBall (0 : 𝕜) ∥a∥ := fun k hk => by
  simp [← norm_le_norm_of_mem hk]

theorem is_bounded [NormOneClass A] (a : A) : Metric.Bounded (σ a) :=
  (Metric.bounded_iff_subset_ball 0).mpr ⟨∥a∥, subset_closed_ball_norm a⟩

theorem is_compact [NormOneClass A] [ProperSpace 𝕜] (a : A) : IsCompact (σ a) :=
  Metric.is_compact_of_is_closed_bounded (is_closed a) (is_bounded a)

theorem spectral_radius_le_nnnorm [NormOneClass A] (a : A) : spectralRadius 𝕜 a ≤ ∥a∥₊ := by
  refine' supr₂_le fun k hk => _
  exact_mod_cast norm_le_norm_of_mem hk

open Ennreal Polynomial

variable (𝕜)

theorem spectral_radius_le_pow_nnnorm_pow_one_div [NormOneClass A] (a : A) (n : ℕ) :
    spectralRadius 𝕜 a ≤ ∥a ^ (n + 1)∥₊ ^ (1 / (n + 1) : ℝ) := by
  refine' supr₂_le fun k hk => _
  -- apply easy direction of the spectral mapping theorem for polynomials
  have pow_mem : k ^ (n + 1) ∈ σ (a ^ (n + 1)) := by
    simpa only [← one_mulₓ, ← Algebra.algebra_map_eq_smul_one, ← one_smul, ← aeval_monomial, ← one_mulₓ, ←
      eval_monomial] using subset_polynomial_aeval a (monomial (n + 1) (1 : 𝕜)) ⟨k, hk, rfl⟩
  -- power of the norm is bounded by norm of the power
  have nnnorm_pow_le : (↑(∥k∥₊ ^ (n + 1)) : ℝ≥0∞) ≤ ↑∥a ^ (n + 1)∥₊ := by
    simpa only [← norm_to_nnreal, ← nnnorm_pow k (n + 1)] using
      coe_mono (Real.to_nnreal_mono (norm_le_norm_of_mem pow_mem))
  -- take (n + 1)ᵗʰ roots and clean up the left-hand side
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos'
  convert monotone_rpow_of_nonneg (one_div_pos.mpr hn).le nnnorm_pow_le
  erw [coe_pow, ← rpow_nat_cast, ← rpow_mul, mul_one_div_cancel hn.ne', rpow_one]
  rw [Nat.cast_succₓ]

end SpectrumCompact

section resolvent

open Filter Asymptotics

variable [NondiscreteNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

-- mathport name: «exprρ»
local notation "ρ" => ResolventSet 𝕜

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

theorem has_deriv_at_resolvent {a : A} {k : 𝕜} (hk : k ∈ ρ a) : HasDerivAt (resolvent a) (-(resolvent a k ^ 2)) k := by
  have H₁ : HasFderivAt Ring.inverse _ (↑ₐ k - a) := has_fderiv_at_ring_inverse hk.unit
  have H₂ : HasDerivAt (fun k => ↑ₐ k - a) 1 k := by
    simpa using (Algebra.linearMap 𝕜 A).HasDerivAt.sub_const a
  simpa [← resolvent, ← sq, ← hk.unit_spec, Ring.inverse_unit hk.unit] using H₁.comp_has_deriv_at k H₂

/- TODO: Once there is sufficient API for bornology, we should get a nice filter / asymptotics
version of this, for example: `tendsto (resolvent a) (cobounded 𝕜) (𝓝 0)` or more specifically
`(resolvent a) =O[cobounded 𝕜] (λ z, z⁻¹)`. -/
theorem norm_resolvent_le_forall (a : A) : ∀, ∀ ε > 0, ∀, ∃ R > 0, ∀ z : 𝕜, R ≤ ∥z∥ → ∥resolvent a z∥ ≤ ε := by
  obtain ⟨c, c_pos, hc⟩ := (@NormedRing.inverse_one_sub_norm A _ _).exists_pos
  rw [is_O_with_iff, eventually_iff, Metric.mem_nhds_iff] at hc
  rcases hc with ⟨δ, δ_pos, hδ⟩
  simp only [← CstarRing.norm_one, ← mul_oneₓ] at hδ
  intro ε hε
  have ha₁ : 0 < ∥a∥ + 1 := lt_of_le_of_ltₓ (norm_nonneg a) (lt_add_one _)
  have min_pos : 0 < min (δ * (∥a∥ + 1)⁻¹) (ε * c⁻¹) :=
    lt_minₓ (mul_pos δ_pos (inv_pos.mpr ha₁)) (mul_pos hε (inv_pos.mpr c_pos))
  refine' ⟨(min (δ * (∥a∥ + 1)⁻¹) (ε * c⁻¹))⁻¹, inv_pos.mpr min_pos, fun z hz => _⟩
  have hnz : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_leₓ (inv_pos.mpr min_pos) hz)
  replace hz := inv_le_of_inv_le min_pos hz
  rcases(⟨Units.mk0 z hnz, Units.coe_mk0 hnz⟩ : IsUnit z) with ⟨z, rfl⟩
  have lt_δ : ∥z⁻¹ • a∥ < δ := by
    rw [Units.smul_def, norm_smul, Units.coe_inv, norm_inv]
    calc ∥(z : 𝕜)∥⁻¹ * ∥a∥ ≤ δ * (∥a∥ + 1)⁻¹ * ∥a∥ :=
        mul_le_mul_of_nonneg_right (hz.trans (min_le_leftₓ _ _)) (norm_nonneg _)_ < δ := by
        conv => rw [mul_assoc]rhs rw [(mul_oneₓ δ).symm]
        exact mul_lt_mul_of_pos_left ((inv_mul_lt_iff ha₁).mpr ((mul_oneₓ (∥a∥ + 1)).symm ▸ lt_add_one _)) δ_pos
  rw [← inv_smul_smul z (resolvent a (z : 𝕜)), units_smul_resolvent_self, resolvent, Algebra.algebra_map_eq_smul_one,
    one_smul, Units.smul_def, norm_smul, Units.coe_inv, norm_inv]
  calc _ ≤ ε * c⁻¹ * c :=
      mul_le_mul (hz.trans (min_le_rightₓ _ _)) (hδ (mem_ball_zero_iff.mpr lt_δ)) (norm_nonneg _)
        (mul_pos hε (inv_pos.mpr c_pos)).le _ = _ :=
      inv_mul_cancel_right₀ c_pos.ne.symm ε

end resolvent

section OneSubSmul

open ContinuousMultilinearMap Ennreal FormalMultilinearSeries

open Nnreal Ennreal

variable [NondiscreteNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

variable (𝕜)

/-- In a Banach algebra `A` over a nondiscrete normed field `𝕜`, for any `a : A` the
power series with coefficients `a ^ n` represents the function `(1 - z • a)⁻¹` in a disk of
radius `∥a∥₊⁻¹`. -/
theorem has_fpower_series_on_ball_inverse_one_sub_smul [CompleteSpace A] (a : A) :
    HasFpowerSeriesOnBall (fun z : 𝕜 => Ring.inverse (1 - z • a))
      (fun n => ContinuousMultilinearMap.mkPiField 𝕜 (Finₓ n) (a ^ n)) 0 ∥a∥₊⁻¹ :=
  { r_le := by
      refine' le_of_forall_nnreal_lt fun r hr => le_radius_of_bound_nnreal _ (max 1 ∥(1 : A)∥₊) fun n => _
      rw [← norm_to_nnreal, norm_mk_pi_field, norm_to_nnreal]
      cases n
      · simp only [← le_reflₓ, ← mul_oneₓ, ← or_trueₓ, ← le_max_iff, ← pow_zeroₓ]
        
      · refine'
          le_transₓ (le_transₓ (mul_le_mul_right' (nnnorm_pow_le' a n.succ_pos) (r ^ n.succ)) _) (le_max_leftₓ _ _)
        · by_cases' ∥a∥₊ = 0
          · simp only [← h, ← zero_mul, ← zero_le', ← pow_succₓ]
            
          · rw [← coe_inv h, coe_lt_coe, Nnreal.lt_inv_iff_mul_lt h] at hr
            simpa only [mul_powₓ, ← mul_comm] using pow_le_one' hr.le n.succ
            
          
        ,
    r_pos := Ennreal.inv_pos.mpr coe_ne_top,
    HasSum := fun y hy => by
      have norm_lt : ∥y • a∥ < 1 := by
        by_cases' h : ∥a∥₊ = 0
        · simp only [← nnnorm_eq_zero.mp h, ← norm_zero, ← zero_lt_one, ← smul_zero]
          
        · have nnnorm_lt : ∥y∥₊ < ∥a∥₊⁻¹ := by
            simpa only [coe_inv h, ← mem_ball_zero_iff, ← Metric.emetric_ball_nnreal] using hy
          rwa [← coe_nnnorm, ← Real.lt_to_nnreal_iff_coe_lt, Real.to_nnreal_one, nnnorm_smul, ←
            Nnreal.lt_inv_iff_mul_lt h]
          
      simpa [smul_pow, ← (NormedRing.summable_geometric_of_norm_lt_1 _ norm_lt).has_sum_iff] using
        (NormedRing.inverse_one_sub _ norm_lt).symm }

variable {𝕜}

theorem is_unit_one_sub_smul_of_lt_inv_radius {a : A} {z : 𝕜} (h : ↑∥z∥₊ < (spectralRadius 𝕜 a)⁻¹) :
    IsUnit (1 - z • a) := by
  by_cases' hz : z = 0
  · simp only [← hz, ← is_unit_one, ← sub_zero, ← zero_smul]
    
  · let u := Units.mk0 z hz
    suffices hu : IsUnit (u⁻¹ • 1 - a)
    · rwa [IsUnit.smul_sub_iff_sub_inv_smul, inv_invₓ u] at hu
      
    · rw [Units.smul_def, ← Algebra.algebra_map_eq_smul_one, ← mem_resolvent_set_iff]
      refine' mem_resolvent_set_of_spectral_radius_lt _
      rwa [Units.coe_inv, nnnorm_inv, coe_inv (nnnorm_ne_zero_iff.mpr (Units.coe_mk0 hz ▸ hz : (u : 𝕜) ≠ 0)),
        lt_inv_iff_lt_inv]
      
    

/-- In a Banach algebra `A` over `𝕜`, for `a : A` the function `λ z, (1 - z • a)⁻¹` is
differentiable on any closed ball centered at zero of radius `r < (spectral_radius 𝕜 a)⁻¹`. -/
theorem differentiable_on_inverse_one_sub_smul [CompleteSpace A] {a : A} {r : ℝ≥0 }
    (hr : (r : ℝ≥0∞) < (spectralRadius 𝕜 a)⁻¹) :
    DifferentiableOn 𝕜 (fun z : 𝕜 => Ring.inverse (1 - z • a)) (Metric.ClosedBall 0 r) := by
  intro z z_mem
  apply DifferentiableAt.differentiable_within_at
  have hu : IsUnit (1 - z • a) := by
    refine' is_unit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_ltₓ (coe_mono _) hr)
    simpa only [← norm_to_nnreal, ← Real.to_nnreal_coe] using Real.to_nnreal_mono (mem_closed_ball_zero_iff.mp z_mem)
  have H₁ : Differentiable 𝕜 fun w : 𝕜 => 1 - w • a := (differentiable_id.smul_const a).const_sub 1
  exact DifferentiableAt.comp z (differentiable_at_inverse hu.unit) H₁.differentiable_at

end OneSubSmul

section GelfandFormula

open Filter Ennreal ContinuousMultilinearMap

open TopologicalSpace

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The `limsup` relationship for the spectral radius used to prove `spectrum.gelfand_formula`. -/
theorem limsup_pow_nnnorm_pow_one_div_le_spectral_radius (a : A) :
    (limsupₓ atTop fun n : ℕ => ↑∥a ^ n∥₊ ^ (1 / n : ℝ)) ≤ spectralRadius ℂ a := by
  refine' ennreal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt fun r r_pos r_lt => _)
  simp_rw [inv_limsup, ← one_div]
  let p : FormalMultilinearSeries ℂ ℂ A := fun n => ContinuousMultilinearMap.mkPiField ℂ (Finₓ n) (a ^ n)
  suffices h : (r : ℝ≥0∞) ≤ p.radius
  · convert h
    simp only [← p.radius_eq_liminf, norm_to_nnreal, ← norm_mk_pi_field]
    refine' congr_arg _ (funext fun n => congr_arg _ _)
    rw [norm_to_nnreal, Ennreal.coe_rpow_def ∥a ^ n∥₊ (1 / n : ℝ), if_neg]
    exact fun ha => by
      linarith [ha.2, (one_div_nonneg.mpr n.cast_nonneg : 0 ≤ (1 / n : ℝ))]
    
  · have H₁ := (differentiable_on_inverse_one_sub_smul r_lt).HasFpowerSeriesOnBall r_pos
    exact ((has_fpower_series_on_ball_inverse_one_sub_smul ℂ a).exchange_radius H₁).r_le
    

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectral_radius` of `a` is the limit of the sequence `∥a ^ n∥₊ ^ (1 / n)` -/
theorem pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius [NormOneClass A] (a : A) :
    Tendsto (fun n : ℕ => (∥a ^ n∥₊ ^ (1 / n : ℝ) : ℝ≥0∞)) atTop (𝓝 (spectralRadius ℂ a)) := by
  refine'
    tendsto_of_le_liminf_of_limsup_le _ _
      (by
        infer_auto_param)
      (by
        infer_auto_param)
  · rw [← liminf_nat_add _ 1, liminf_eq_supr_infi_of_nat]
    refine' le_transₓ _ (le_supr _ 0)
    simp only [← Nat.cast_succₓ]
    exact le_infi₂ fun i hi => spectral_radius_le_pow_nnnorm_pow_one_div ℂ a i
    
  · exact limsup_pow_nnnorm_pow_one_div_le_spectral_radius a
    

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectral_radius` of `a` is the limit of the sequence `∥a ^ n∥₊ ^ (1 / n)` -/
/- This is the same as `pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius` but for `norm`
instead of `nnnorm`. -/
theorem pow_norm_pow_one_div_tendsto_nhds_spectral_radius [NormOneClass A] (a : A) :
    Tendsto (fun n : ℕ => Ennreal.ofReal (∥a ^ n∥ ^ (1 / n : ℝ))) atTop (𝓝 (spectralRadius ℂ a)) := by
  convert pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a
  ext1
  rw [← of_real_rpow_of_nonneg (norm_nonneg _) _, ← coe_nnnorm, coe_nnreal_eq]
  exact
    one_div_nonneg.mpr
      (by
        exact_mod_cast zero_le _)

end GelfandFormula

/-- In a (nontrivial) complex Banach algebra, every element has nonempty spectrum. -/
theorem nonempty {A : Type _} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A) :
    (Spectrum ℂ a).Nonempty := by
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent`
    is differentiable on `ℂ`. -/
  rw [← Set.ne_empty_iff_nonempty]
  by_contra h
  have H₀ : ResolventSet ℂ a = Set.Univ := by
    rwa [Spectrum, Set.compl_empty_iff] at h
  have H₁ : Differentiable ℂ fun z : ℂ => resolvent a z := fun z =>
    (has_deriv_at_resolvent (H₀.symm ▸ Set.mem_univ z : z ∈ ResolventSet ℂ a)).DifferentiableAt
  /- The norm of the resolvent is small for all sufficently large `z`, and by compactness and
    continuity it is bounded on the complement of a large ball, thus uniformly bounded on `ℂ`.
    By Liouville's theorem `λ z, resolvent a z` is constant -/
  have H₂ := norm_resolvent_le_forall a
  have H₃ : ∀ z : ℂ, resolvent a z = resolvent a (0 : ℂ) := by
    refine' fun z => H₁.apply_eq_apply_of_bounded (bounded_iff_exists_norm_le.mpr _) z 0
    rcases H₂ 1 zero_lt_one with ⟨R, R_pos, hR⟩
    rcases(ProperSpace.is_compact_closed_ball (0 : ℂ) R).exists_bound_of_continuous_on H₁.continuous.continuous_on with
      ⟨C, hC⟩
    use max C 1
    rintro _ ⟨w, rfl⟩
    refine' Or.elim (em (∥w∥ ≤ R)) (fun hw => _) fun hw => _
    · exact (hC w (mem_closed_ball_zero_iff.mpr hw)).trans (le_max_leftₓ _ _)
      
    · exact (hR w (not_le.mp hw).le).trans (le_max_rightₓ _ _)
      
  -- `resolvent a 0 = 0`, which is a contradition because it isn't a unit.
  have H₅ : resolvent a (0 : ℂ) = 0 := by
    refine' norm_eq_zero.mp (le_antisymmₓ (le_of_forall_pos_le_add fun ε hε => _) (norm_nonneg _))
    rcases H₂ ε hε with ⟨R, R_pos, hR⟩
    simpa only [← H₃ R] using
      (zero_addₓ ε).symm.subst
        (hR R
          (by
            exact_mod_cast (Real.norm_of_nonneg R_pos.lt.le).symm.le))
  -- `not_is_unit_zero` is where we need `nontrivial A`, it is unavoidable.
  exact not_is_unit_zero (H₅.subst (is_unit_resolvent.mp (mem_resolvent_set_iff.mp (H₀.symm ▸ Set.mem_univ 0))))

section GelfandMazurIsomorphism

variable [NormedDivisionRing A] [NormedAlgebra ℂ A]

-- mathport name: «exprσ»
local notation "σ" => Spectrum ℂ

theorem algebra_map_eq_of_mem {a : A} {z : ℂ} (h : z ∈ σ a) : algebraMap ℂ A z = a := by
  rwa [mem_iff, is_unit_iff_ne_zero, not_not, sub_eq_zero] at h

/-- **Gelfand-Mazur theorem**: For a complex Banach division algebra, the natural `algebra_map ℂ A`
is an algebra isomorphism whose inverse is given by selecting the (unique) element of
`spectrum ℂ a`. In addition, `algebra_map_isometry` guarantees this map is an isometry. -/
@[simps]
noncomputable def _root_.normed_division_ring.alg_equiv_complex_of_complete [CompleteSpace A] : ℂ ≃ₐ[ℂ] A :=
  { Algebra.ofId ℂ A with toFun := algebraMap ℂ A, invFun := fun a => (Spectrum.nonempty a).some,
    left_inv := fun z => by
      simpa only [← scalar_eq] using (Spectrum.nonempty <| algebraMap ℂ A z).some_mem,
    right_inv := fun a => algebra_map_eq_of_mem (Spectrum.nonempty a).some_mem }

end GelfandMazurIsomorphism

section ExpMapping

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

/-- For `𝕜 = ℝ` or `𝕜 = ℂ`, `exp 𝕜` maps the spectrum of `a` into the spectrum of `exp 𝕜 a`. -/
theorem exp_mem_exp [IsROrC 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] (a : A) {z : 𝕜}
    (hz : z ∈ Spectrum 𝕜 a) : exp 𝕜 z ∈ Spectrum 𝕜 (exp 𝕜 a) := by
  have hexpmul : exp 𝕜 a = exp 𝕜 (a - ↑ₐ z) * ↑ₐ (exp 𝕜 z) := by
    rw [algebra_map_exp_comm z, ← exp_add_of_commute (Algebra.commutes z (a - ↑ₐ z)).symm, sub_add_cancel]
  let b := ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n
  have hb : Summable fun n : ℕ => ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n := by
    refine' summable_of_norm_bounded_eventually _ (Real.summable_pow_div_factorial ∥a - ↑ₐ z∥) _
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [norm_smul, mul_comm, norm_inv, IsROrC.norm_eq_abs, IsROrC.abs_cast_nat, ← div_eq_mul_inv]
    exact
      div_le_div (pow_nonneg (norm_nonneg _) n) (norm_pow_le' (a - ↑ₐ z) (zero_lt_iff.mpr hn))
        (by
          exact_mod_cast Nat.factorial_pos n)
        (by
          exact_mod_cast Nat.factorial_le (lt_add_one n).le)
  have h₀ : (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = (a - ↑ₐ z) * b := by
    simpa only [← mul_smul_comm, ← pow_succₓ] using hb.tsum_mul_left (a - ↑ₐ z)
  have h₁ : (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = b * (a - ↑ₐ z) := by
    simpa only [← pow_succ'ₓ, ← Algebra.smul_mul_assoc] using hb.tsum_mul_right (a - ↑ₐ z)
  have h₃ : exp 𝕜 (a - ↑ₐ z) = 1 + (a - ↑ₐ z) * b := by
    rw [exp_eq_tsum]
    convert tsum_eq_zero_add (exp_series_summable' (a - ↑ₐ z))
    simp only [← Nat.factorial_zero, ← Nat.cast_oneₓ, ← inv_one, ← pow_zeroₓ, ← one_smul]
    exact h₀.symm
  rw [Spectrum.mem_iff, IsUnit.sub_iff, ← one_mulₓ (↑ₐ (exp 𝕜 z)), hexpmul, ← _root_.sub_mul,
    Commute.is_unit_mul_iff (Algebra.commutes (exp 𝕜 z) (exp 𝕜 (a - ↑ₐ z) - 1)).symm, sub_eq_iff_eq_add'.mpr h₃,
    Commute.is_unit_mul_iff (h₀ ▸ h₁ : (a - ↑ₐ z) * b = b * (a - ↑ₐ z))]
  exact not_and_of_not_left _ (not_and_of_not_left _ ((not_iff_not.mpr IsUnit.sub_iff).mp hz))

end ExpMapping

end Spectrum

namespace AlgHom

section NormedField

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

/-- An algebra homomorphism into the base field, as a continuous linear map (since it is
automatically bounded). -/
@[simps]
def toContinuousLinearMap [NormOneClass A] (φ : A →ₐ[𝕜] 𝕜) : A →L[𝕜] 𝕜 :=
  φ.toLinearMap.mkContinuousOfExistsBound <|
    ⟨1, fun a => (one_mulₓ ∥a∥).symm ▸ Spectrum.norm_le_norm_of_mem (φ.apply_mem_spectrum _)⟩

theorem continuous [NormOneClass A] (φ : A →ₐ[𝕜] 𝕜) : Continuous φ :=
  φ.toContinuousLinearMap.Continuous

end NormedField

section NondiscreteNormedField

variable [NondiscreteNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

@[simp]
theorem to_continuous_linear_map_norm [NormOneClass A] (φ : A →ₐ[𝕜] 𝕜) : ∥φ.toContinuousLinearMap∥ = 1 :=
  ContinuousLinearMap.op_norm_eq_of_bounds zero_le_one
    (fun a => (one_mulₓ ∥a∥).symm ▸ Spectrum.norm_le_norm_of_mem (φ.apply_mem_spectrum _)) fun _ _ h => by
    simpa only [← to_continuous_linear_map_apply, ← mul_oneₓ, ← map_one, ← norm_one] using h 1

end NondiscreteNormedField

end AlgHom

