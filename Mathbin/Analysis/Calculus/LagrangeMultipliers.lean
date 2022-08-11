/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Calculus.Inverse
import Mathbin.LinearAlgebra.Dual

/-!
# Lagrange multipliers

In this file we formalize the
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) method of solving
conditional extremum problems: if a function `φ` has a local extremum at `x₀` on the set
`f ⁻¹' {f x₀}`, `f x = (f₀ x, ..., fₙ₋₁ x)`, then the differentials of `fₖ` and `φ` are linearly
dependent. First we formulate a geometric version of this theorem which does not rely on the
target space being `ℝⁿ`, then restate it in terms of coordinates.

## TODO

Formalize Karush-Kuhn-Tucker theorem

## Tags

lagrange multiplier, local extremum

-/


open Filter Set

open TopologicalSpace Filter BigOperators

variable {E F : Type _} [NormedGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {f : E → F} {φ : E → ℝ} {x₀ : E} {f' : E →L[ℝ] F} {φ' : E →L[ℝ] ℝ}

/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, both `f : E → F` and `φ` are strictly differentiable at `x₀`, and the codomain of `f` is
a complete space, then the linear map `x ↦ (f' x, φ' x)` is not surjective. -/
theorem IsLocalExtrOn.range_ne_top_of_has_strict_fderiv_at (hextr : IsLocalExtrOn φ { x | f x = f x₀ } x₀)
    (hf' : HasStrictFderivAt f f' x₀) (hφ' : HasStrictFderivAt φ φ' x₀) : (f'.Prod φ').range ≠ ⊤ := by
  intro htop
  set fφ := fun x => (f x, φ x)
  have A : map φ (𝓝[f ⁻¹' {f x₀}] x₀) = 𝓝 (φ x₀) := by
    change map (Prod.snd ∘ fφ) (𝓝[fφ ⁻¹' { p | p.1 = f x₀ }] x₀) = 𝓝 (φ x₀)
    rw [← map_map, nhdsWithin, map_inf_principal_preimage, (hf'.prod hφ').map_nhds_eq_of_surj htop]
    exact map_snd_nhds_within _
  exact hextr.not_nhds_le_map A.ge

/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, both `f : E → F` and `φ` are strictly differentiable at `x₀`, and the codomain of `f` is
a complete space, then there exist `Λ : dual ℝ F` and `Λ₀ : ℝ` such that `(Λ, Λ₀) ≠ 0` and
`Λ (f' x) + Λ₀ • φ' x = 0` for all `x`. -/
theorem IsLocalExtrOn.exists_linear_map_of_has_strict_fderiv_at (hextr : IsLocalExtrOn φ { x | f x = f x₀ } x₀)
    (hf' : HasStrictFderivAt f f' x₀) (hφ' : HasStrictFderivAt φ φ' x₀) :
    ∃ (Λ : Module.Dual ℝ F)(Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∀ x, Λ (f' x) + Λ₀ • φ' x = 0 := by
  rcases Submodule.exists_le_ker_of_lt_top _
      (lt_top_iff_ne_top.2 <| hextr.range_ne_top_of_has_strict_fderiv_at hf' hφ') with
    ⟨Λ', h0, hΛ'⟩
  set e : ((F →ₗ[ℝ] ℝ) × ℝ) ≃ₗ[ℝ] F × ℝ →ₗ[ℝ] ℝ :=
    ((LinearEquiv.refl ℝ (F →ₗ[ℝ] ℝ)).Prod (LinearMap.ringLmapEquivSelf ℝ ℝ ℝ).symm).trans (LinearMap.coprodEquiv ℝ)
  rcases e.surjective Λ' with ⟨⟨Λ, Λ₀⟩, rfl⟩
  refine' ⟨Λ, Λ₀, e.map_ne_zero_iff.1 h0, fun x => _⟩
  convert LinearMap.congr_fun (LinearMap.range_le_ker_iff.1 hΛ') x using 1
  -- squeezed `simp [mul_comm]` to speed up elaboration
  simp only [← LinearMap.coprod_equiv_apply, ← LinearEquiv.refl_apply, ← LinearMap.ring_lmap_equiv_self_symm_apply, ←
    LinearMap.comp_apply, ← ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.prod_apply, ← LinearEquiv.trans_apply, ←
    LinearEquiv.prod_apply, ← LinearMap.coprod_apply, ← LinearMap.smul_right_apply, ← LinearMap.one_apply, ←
    smul_eq_mul, ← mul_comm]

/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, and both `f : E → ℝ` and `φ` are strictly differentiable at `x₀`, then there exist
`a b : ℝ` such that `(a, b) ≠ 0` and `a • f' + b • φ' = 0`. -/
theorem IsLocalExtrOn.exists_multipliers_of_has_strict_fderiv_at_1d {f : E → ℝ} {f' : E →L[ℝ] ℝ}
    (hextr : IsLocalExtrOn φ { x | f x = f x₀ } x₀) (hf' : HasStrictFderivAt f f' x₀)
    (hφ' : HasStrictFderivAt φ φ' x₀) : ∃ a b : ℝ, (a, b) ≠ 0 ∧ a • f' + b • φ' = 0 := by
  obtain ⟨Λ, Λ₀, hΛ, hfΛ⟩ := hextr.exists_linear_map_of_has_strict_fderiv_at hf' hφ'
  refine' ⟨Λ 1, Λ₀, _, _⟩
  · contrapose! hΛ
    simp only [← Prod.mk_eq_zero] at hΛ⊢
    refine' ⟨LinearMap.ext fun x => _, hΛ.2⟩
    simpa [← hΛ.1] using Λ.map_smul x 1
    
  · ext x
    have H₁ : Λ (f' x) = f' x * Λ 1 := by
      simpa only [← mul_oneₓ, ← Algebra.id.smul_eq_mul] using Λ.map_smul (f' x) 1
    have H₂ : f' x * Λ 1 + Λ₀ * φ' x = 0 := by
      simpa only [← Algebra.id.smul_eq_mul, ← H₁] using hfΛ x
    simpa [← mul_comm] using H₂
    

/-- Lagrange multipliers theorem, 1d version. Let `f : ι → E → ℝ` be a finite family of functions.
Suppose that `φ : E → ℝ` has a local extremum on the set `{x | ∀ i, f i x = f i x₀}` at `x₀`.
Suppose that all functions `f i` as well as `φ` are strictly differentiable at `x₀`.
Then the derivatives `f' i : E → L[ℝ] ℝ` and `φ' : E →L[ℝ] ℝ` are linearly dependent:
there exist `Λ : ι → ℝ` and `Λ₀ : ℝ`, `(Λ, Λ₀) ≠ 0`, such that `∑ i, Λ i • f' i + Λ₀ • φ' = 0`.

See also `is_local_extr_on.linear_dependent_of_has_strict_fderiv_at` for a version that
states `¬linear_independent ℝ _` instead of existence of `Λ` and `Λ₀`. -/
theorem IsLocalExtrOn.exists_multipliers_of_has_strict_fderiv_at {ι : Type _} [Fintype ι] {f : ι → E → ℝ}
    {f' : ι → E →L[ℝ] ℝ} (hextr : IsLocalExtrOn φ { x | ∀ i, f i x = f i x₀ } x₀)
    (hf' : ∀ i, HasStrictFderivAt (f i) (f' i) x₀) (hφ' : HasStrictFderivAt φ φ' x₀) :
    ∃ (Λ : ι → ℝ)(Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ (∑ i, Λ i • f' i) + Λ₀ • φ' = 0 := by
  let this := Classical.decEq ι
  replace hextr : IsLocalExtrOn φ { x | (fun i => f i x) = fun i => f i x₀ } x₀
  · simpa only [← Function.funext_iffₓ] using hextr
    
  rcases hextr.exists_linear_map_of_has_strict_fderiv_at (has_strict_fderiv_at_pi.2 fun i => hf' i) hφ' with
    ⟨Λ, Λ₀, h0, hsum⟩
  rcases(LinearEquiv.piRing ℝ ℝ ι ℝ).symm.Surjective Λ with ⟨Λ, rfl⟩
  refine' ⟨Λ, Λ₀, _, _⟩
  · simpa only [← Ne.def, ← Prod.ext_iff, ← LinearEquiv.map_eq_zero_iff, ← Prod.fst_zero] using h0
    
  · ext x
    simpa [← mul_comm] using hsum x
    

/-- Lagrange multipliers theorem. Let `f : ι → E → ℝ` be a finite family of functions.
Suppose that `φ : E → ℝ` has a local extremum on the set `{x | ∀ i, f i x = f i x₀}` at `x₀`.
Suppose that all functions `f i` as well as `φ` are strictly differentiable at `x₀`.
Then the derivatives `f' i : E → L[ℝ] ℝ` and `φ' : E →L[ℝ] ℝ` are linearly dependent.

See also `is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at` for a version that
that states existence of Lagrange multipliers `Λ` and `Λ₀` instead of using
`¬linear_independent ℝ _` -/
theorem IsLocalExtrOn.linear_dependent_of_has_strict_fderiv_at {ι : Type _} [Fintype ι] {f : ι → E → ℝ}
    {f' : ι → E →L[ℝ] ℝ} (hextr : IsLocalExtrOn φ { x | ∀ i, f i x = f i x₀ } x₀)
    (hf' : ∀ i, HasStrictFderivAt (f i) (f' i) x₀) (hφ' : HasStrictFderivAt φ φ' x₀) :
    ¬LinearIndependent ℝ (Option.elimₓ φ' f' : Option ι → E →L[ℝ] ℝ) := by
  rw [Fintype.linear_independent_iff]
  push_neg
  rcases hextr.exists_multipliers_of_has_strict_fderiv_at hf' hφ' with ⟨Λ, Λ₀, hΛ, hΛf⟩
  refine' ⟨Option.elimₓ Λ₀ Λ, _, _⟩
  · simpa [← add_commₓ] using hΛf
    
  · simpa [← Function.funext_iffₓ, ← not_and_distrib, ← or_comm, ← Option.exists] using hΛ
    

