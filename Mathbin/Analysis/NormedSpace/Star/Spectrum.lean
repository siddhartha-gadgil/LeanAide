/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Analysis.NormedSpace.Star.Basic
import Mathbin.Analysis.NormedSpace.Spectrum
import Mathbin.Algebra.Star.Module
import Mathbin.Analysis.NormedSpace.Star.Exponential

/-! # Spectral properties in C⋆-algebras
In this file, we establish various propreties related to the spectrum of elements in C⋆-algebras.
-/


-- mathport name: «expr ⋆»
local postfix:max "⋆" => star

open TopologicalSpace Ennreal

open Filter Ennreal Spectrum CstarRing

section UnitarySpectrum

variable {𝕜 : Type _} [NormedField 𝕜] {E : Type _} [NormedRing E] [StarRing E] [CstarRing E] [NormedAlgebra 𝕜 E]
  [CompleteSpace E] [Nontrivial E]

theorem unitary.spectrum_subset_circle (u : unitary E) : Spectrum 𝕜 (u : E) ⊆ Metric.Sphere 0 1 := by
  refine' fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymmₓ _ _)
  · simpa only [← CstarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
    
  · rw [← unitary.coe_to_units_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_invₓ (unitary.toUnits u), ← Spectrum.map_inv, Set.mem_inv] at hk
    have : ∥k∥⁻¹ ≤ ∥↑(unitary.toUnits u)⁻¹∥
    simpa only [← norm_inv] using norm_le_norm_of_mem hk
    simpa using inv_le_of_inv_le (norm_pos_iff.mpr hnk) this
    

theorem Spectrum.subset_circle_of_unitary {u : E} (h : u ∈ unitary E) : Spectrum 𝕜 u ⊆ Metric.Sphere 0 1 :=
  unitary.spectrum_subset_circle ⟨u, h⟩

end UnitarySpectrum

section ComplexScalars

open Complex

variable {A : Type _} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A] [CstarRing A]

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap ℂ A

theorem spectral_radius_eq_nnnorm_of_self_adjoint [NormOneClass A] {a : A} (ha : a ∈ selfAdjoint A) :
    spectralRadius ℂ a = ∥a∥₊ := by
  have hconst : tendsto (fun n : ℕ => (∥a∥₊ : ℝ≥0∞)) at_top _ := tendsto_const_nhds
  refine' tendsto_nhds_unique _ hconst
  convert
    (Spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A)).comp
      (Nat.tendsto_pow_at_top_at_top_of_one_lt
        (by
          linarith : 1 < 2))
  refine' funext fun n => _
  rw [Function.comp_app, nnnorm_pow_two_pow_of_self_adjoint ha, Ennreal.coe_pow, ← rpow_nat_cast, ← rpow_mul]
  simp

theorem spectral_radius_eq_nnnorm_of_star_normal [NormOneClass A] (a : A) [IsStarNormal a] :
    spectralRadius ℂ a = ∥a∥₊ := by
  refine' (Ennreal.pow_strict_mono two_ne_zero).Injective _
  have ha : a⋆ * a ∈ selfAdjoint A :=
    self_adjoint.mem_iff.mpr
      (by
        simpa only [← star_star] using star_mul a⋆ a)
  have heq :
    (fun n : ℕ => (∥(a⋆ * a) ^ n∥₊ ^ (1 / n : ℝ) : ℝ≥0∞)) =
      (fun x => x ^ 2) ∘ fun n : ℕ => (∥a ^ n∥₊ ^ (1 / n : ℝ) : ℝ≥0∞) :=
    by
    funext
    rw [Function.comp_applyₓ, ← rpow_nat_cast, ← rpow_mul, mul_comm, rpow_mul, rpow_nat_cast, ← coe_pow, sq, ←
      nnnorm_star_mul_self, Commute.mul_pow (star_comm_self' a), star_pow]
  have h₂ :=
    ((Ennreal.continuous_pow 2).Tendsto (spectralRadius ℂ a)).comp
      (Spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a)
  rw [← HEq] at h₂
  convert tendsto_nhds_unique h₂ (pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a⋆ * a))
  rw [spectral_radius_eq_nnnorm_of_self_adjoint ha, sq, nnnorm_star_mul_self, coe_mul]

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem selfAdjoint.mem_spectrum_eq_re [StarModule ℂ A] [Nontrivial A] {a : A} (ha : a ∈ selfAdjoint A) {z : ℂ}
    (hz : z ∈ Spectrum ℂ a) : z = z.re := by
  let Iu := Units.mk0 I I_ne_zero
  have : exp ℂ (I • z) ∈ Spectrum ℂ (exp ℂ (I • a)) := by
    simpa only [← Units.smul_def, ← Units.coe_mk0] using Spectrum.exp_mem_exp (Iu • a) (smul_mem_smul_iff.mpr hz)
  exact
    Complex.ext (of_real_re _)
      (by
        simpa only [Complex.exp_eq_exp_ℂ, ← mem_sphere_zero_iff_norm, ← norm_eq_abs, ← abs_exp, ← Real.exp_eq_one_iff, ←
          smul_eq_mul, ← I_mul, ← neg_eq_zero] using
          Spectrum.subset_circle_of_unitary (selfAdjoint.exp_i_smul_unitary ha) this)

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem selfAdjoint.mem_spectrum_eq_re' [StarModule ℂ A] [Nontrivial A] (a : selfAdjoint A) {z : ℂ}
    (hz : z ∈ Spectrum ℂ (a : A)) : z = z.re :=
  selfAdjoint.mem_spectrum_eq_re a.property hz

/-- The spectrum of a selfadjoint is real -/
theorem selfAdjoint.coe_re_map_spectrum [StarModule ℂ A] [Nontrivial A] {a : A} (ha : a ∈ selfAdjoint A) :
    Spectrum ℂ a = (coe ∘ re '' Spectrum ℂ a : Set ℂ) :=
  le_antisymmₓ (fun z hz => ⟨z, hz, (selfAdjoint.mem_spectrum_eq_re ha hz).symm⟩) fun z => by
    rintro ⟨z, hz, rfl⟩
    simpa only [← (selfAdjoint.mem_spectrum_eq_re ha hz).symm, ← Function.comp_app] using hz

/-- The spectrum of a selfadjoint is real -/
theorem selfAdjoint.coe_re_map_spectrum' [StarModule ℂ A] [Nontrivial A] (a : selfAdjoint A) :
    Spectrum ℂ (a : A) = (coe ∘ re '' Spectrum ℂ (a : A) : Set ℂ) :=
  selfAdjoint.coe_re_map_spectrum a.property

end ComplexScalars

