/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
import Mathbin.Analysis.Calculus.Fderiv
import Mathbin.Data.Polynomial.Derivative
import Mathbin.LinearAlgebra.AffineSpace.Slope

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.html). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

 - `has_deriv_at_filter f f' x L` states that the function `f` has the
    derivative `f'` at the point `x` as `x` goes along the filter `L`.

 - `has_deriv_within_at f f' s x` states that the function `f` has the
    derivative `f'` at the point `x` within the subset `s`.

 - `has_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x`.

 - `has_strict_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x` in the sense of strict differentiability, i.e.,
   `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

For the last two notions we also define a functional version:

  - `deriv_within f s x` is a derivative of `f` at `x` within `s`. If the
    derivative does not exist, then `deriv_within f s x` equals zero.

  - `deriv f x` is a derivative of `f` at `x`. If the derivative does not
    exist, then `deriv f x` equals zero.

The theorems `fderiv_within_deriv_within` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps
  - addition
  - sum of finitely many functions
  - negation
  - subtraction
  - multiplication
  - inverse `x → x⁻¹`
  - multiplication of two functions in `𝕜 → 𝕜`
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E`
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜`
  - composition of a function in `F → E` with a function in `𝕜 → F`
  - inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)
  - division
  - polynomials

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }
```

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in `fderiv.lean`.
See the explanations there.
-/


universe u v w

noncomputable section

open Classical TopologicalSpace BigOperators Filter Ennreal Polynomial

open Filter Asymptotics Set

open ContinuousLinearMap (smul_right smul_right_one_eq_iff)

variable {𝕜 : Type u} [NondiscreteNormedField 𝕜]

section

variable {F : Type v} [NormedGroup F] [NormedSpace 𝕜 F]

variable {E : Type w} [NormedGroup E] [NormedSpace 𝕜 E]

/-- `f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges along the filter `L`.
-/
def HasDerivAtFilter (f : 𝕜 → F) (f' : F) (x : 𝕜) (L : Filter 𝕜) :=
  HasFderivAtFilter f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x L

/-- `f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def HasDerivWithinAt (f : 𝕜 → F) (f' : F) (s : Set 𝕜) (x : 𝕜) :=
  HasDerivAtFilter f f' x (𝓝[s] x)

/-- `f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' x (𝓝 x)

/-- `f` has the derivative `f'` at the point `x` in the sense of strict differentiability.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`. -/
def HasStrictDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasStrictFderivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x

/-- Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_within_at f f' s x`), then
`f x' = f x + (x' - x) • deriv_within f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def derivWithin (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) :=
  fderivWithin 𝕜 f s x 1

/-- Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_at f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv (f : 𝕜 → F) (x : 𝕜) :=
  fderiv 𝕜 f x 1

variable {f f₀ f₁ g : 𝕜 → F}

variable {f' f₀' f₁' g' : F}

variable {x : 𝕜}

variable {s t : Set 𝕜}

variable {L L₁ L₂ : Filter 𝕜}

/-- Expressing `has_fderiv_at_filter f f' x L` in terms of `has_deriv_at_filter` -/
theorem has_fderiv_at_filter_iff_has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
    HasFderivAtFilter f f' x L ↔ HasDerivAtFilter f (f' 1) x L := by
  simp [← HasDerivAtFilter]

theorem HasFderivAtFilter.has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
    HasFderivAtFilter f f' x L → HasDerivAtFilter f (f' 1) x L :=
  has_fderiv_at_filter_iff_has_deriv_at_filter.mp

/-- Expressing `has_fderiv_within_at f f' s x` in terms of `has_deriv_within_at` -/
theorem has_fderiv_within_at_iff_has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
    HasFderivWithinAt f f' s x ↔ HasDerivWithinAt f (f' 1) s x :=
  has_fderiv_at_filter_iff_has_deriv_at_filter

/-- Expressing `has_deriv_within_at f f' s x` in terms of `has_fderiv_within_at` -/
theorem has_deriv_within_at_iff_has_fderiv_within_at {f' : F} :
    HasDerivWithinAt f f' s x ↔ HasFderivWithinAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
  Iff.rfl

theorem HasFderivWithinAt.has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
    HasFderivWithinAt f f' s x → HasDerivWithinAt f (f' 1) s x :=
  has_fderiv_within_at_iff_has_deriv_within_at.mp

theorem HasDerivWithinAt.has_fderiv_within_at {f' : F} :
    HasDerivWithinAt f f' s x → HasFderivWithinAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
  has_deriv_within_at_iff_has_fderiv_within_at.mp

/-- Expressing `has_fderiv_at f f' x` in terms of `has_deriv_at` -/
theorem has_fderiv_at_iff_has_deriv_at {f' : 𝕜 →L[𝕜] F} : HasFderivAt f f' x ↔ HasDerivAt f (f' 1) x :=
  has_fderiv_at_filter_iff_has_deriv_at_filter

theorem HasFderivAt.has_deriv_at {f' : 𝕜 →L[𝕜] F} : HasFderivAt f f' x → HasDerivAt f (f' 1) x :=
  has_fderiv_at_iff_has_deriv_at.mp

theorem has_strict_fderiv_at_iff_has_strict_deriv_at {f' : 𝕜 →L[𝕜] F} :
    HasStrictFderivAt f f' x ↔ HasStrictDerivAt f (f' 1) x := by
  simp [← HasStrictDerivAt, ← HasStrictFderivAt]

protected theorem HasStrictFderivAt.has_strict_deriv_at {f' : 𝕜 →L[𝕜] F} :
    HasStrictFderivAt f f' x → HasStrictDerivAt f (f' 1) x :=
  has_strict_fderiv_at_iff_has_strict_deriv_at.mp

theorem has_strict_deriv_at_iff_has_strict_fderiv_at :
    HasStrictDerivAt f f' x ↔ HasStrictFderivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
  Iff.rfl

alias has_strict_deriv_at_iff_has_strict_fderiv_at ↔ HasStrictDerivAt.has_strict_fderiv_at _

/-- Expressing `has_deriv_at f f' x` in terms of `has_fderiv_at` -/
theorem has_deriv_at_iff_has_fderiv_at {f' : F} : HasDerivAt f f' x ↔ HasFderivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
  Iff.rfl

alias has_deriv_at_iff_has_fderiv_at ↔ HasDerivAt.has_fderiv_at _

theorem deriv_within_zero_of_not_differentiable_within_at (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    derivWithin f s x = 0 := by
  unfold derivWithin
  rw [fderiv_within_zero_of_not_differentiable_within_at]
  simp
  assumption

theorem differentiable_within_at_of_deriv_within_ne_zero (h : derivWithin f s x ≠ 0) : DifferentiableWithinAt 𝕜 f s x :=
  not_imp_comm.1 deriv_within_zero_of_not_differentiable_within_at h

theorem deriv_zero_of_not_differentiable_at (h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0 := by
  unfold deriv
  rw [fderiv_zero_of_not_differentiable_at]
  simp
  assumption

theorem differentiable_at_of_deriv_ne_zero (h : deriv f x ≠ 0) : DifferentiableAt 𝕜 f x :=
  not_imp_comm.1 deriv_zero_of_not_differentiable_at h

theorem UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x) (h : HasDerivWithinAt f f' s x)
    (h₁ : HasDerivWithinAt f f₁' s x) : f' = f₁' :=
  smul_right_one_eq_iff.mp <| UniqueDiffWithinAt.eq H h h₁

theorem has_deriv_at_filter_iff_is_o :
    HasDerivAtFilter f f' x L ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[L] fun x' => x' - x :=
  Iff.rfl

theorem has_deriv_at_filter_iff_tendsto :
    HasDerivAtFilter f f' x L ↔ Tendsto (fun x' : 𝕜 => ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) L (𝓝 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem has_deriv_within_at_iff_is_o :
    HasDerivWithinAt f f' s x ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝[s] x] fun x' => x' - x :=
  Iff.rfl

theorem has_deriv_within_at_iff_tendsto :
    HasDerivWithinAt f f' s x ↔ Tendsto (fun x' => ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) (𝓝[s] x) (𝓝 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem has_deriv_at_iff_is_o :
    HasDerivAt f f' x ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝 x] fun x' => x' - x :=
  Iff.rfl

theorem has_deriv_at_iff_tendsto :
    HasDerivAt f f' x ↔ Tendsto (fun x' => ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) (𝓝 x) (𝓝 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem HasStrictDerivAt.has_deriv_at (h : HasStrictDerivAt f f' x) : HasDerivAt f f' x :=
  h.HasFderivAt

/-- If the domain has dimension one, then Fréchet derivative is equivalent to the classical
definition with a limit. In this version we have to take the limit along the subset `-{x}`,
because for `y=x` the slope equals zero due to the convention `0⁻¹=0`. -/
theorem has_deriv_at_filter_iff_tendsto_slope {x : 𝕜} {L : Filter 𝕜} :
    HasDerivAtFilter f f' x L ↔ Tendsto (slope f x) (L⊓𝓟 ({x}ᶜ)) (𝓝 f') := by
  conv_lhs =>
    simp only [← has_deriv_at_filter_iff_tendsto, ← (norm_inv _).symm, ← (norm_smul _ _).symm, ←
      tendsto_zero_iff_norm_tendsto_zero.symm]
  conv_rhs => rw [← nhds_translation_sub f', tendsto_comap_iff]
  refine'
    (tendsto_inf_principal_nhds_iff_of_forall_eq <| by
            simp ).symm.trans
      (tendsto_congr' _)
  refine' (eventually_principal.2 fun z hz => _).filter_mono inf_le_right
  simp only [← (· ∘ ·)]
  rw [smul_sub, ← mul_smul, inv_mul_cancel (sub_ne_zero.2 hz), one_smul, slope_def_module]

theorem has_deriv_within_at_iff_tendsto_slope : HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f') :=
  by
  simp only [← HasDerivWithinAt, ← nhdsWithin, ← diff_eq, ← inf_assoc.symm, ← inf_principal.symm]
  exact has_deriv_at_filter_iff_tendsto_slope

theorem has_deriv_within_at_iff_tendsto_slope' (hs : x ∉ s) :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s] x) (𝓝 f') := by
  convert ← has_deriv_within_at_iff_tendsto_slope
  exact diff_singleton_eq_self hs

theorem has_deriv_at_iff_tendsto_slope : HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[≠] x) (𝓝 f') :=
  has_deriv_at_filter_iff_tendsto_slope

theorem has_deriv_within_at_congr_set {s t u : Set 𝕜} (hu : u ∈ 𝓝 x) (h : s ∩ u = t ∩ u) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x := by
  simp_rw [HasDerivWithinAt, nhds_within_eq_nhds_within' hu h]

alias has_deriv_within_at_congr_set ↔ HasDerivWithinAt.congr_set _

@[simp]
theorem has_deriv_within_at_diff_singleton : HasDerivWithinAt f f' (s \ {x}) x ↔ HasDerivWithinAt f f' s x := by
  simp only [← has_deriv_within_at_iff_tendsto_slope, ← sdiff_idem]

@[simp]
theorem has_deriv_within_at_Ioi_iff_Ici [PartialOrderₓ 𝕜] :
    HasDerivWithinAt f f' (Ioi x) x ↔ HasDerivWithinAt f f' (Ici x) x := by
  rw [← Ici_diff_left, has_deriv_within_at_diff_singleton]

alias has_deriv_within_at_Ioi_iff_Ici ↔ HasDerivWithinAt.Ici_of_Ioi HasDerivWithinAt.Ioi_of_Ici

@[simp]
theorem has_deriv_within_at_Iio_iff_Iic [PartialOrderₓ 𝕜] :
    HasDerivWithinAt f f' (Iio x) x ↔ HasDerivWithinAt f f' (Iic x) x := by
  rw [← Iic_diff_right, has_deriv_within_at_diff_singleton]

alias has_deriv_within_at_Iio_iff_Iic ↔ HasDerivWithinAt.Iic_of_Iio HasDerivWithinAt.Iio_of_Iic

theorem HasDerivWithinAt.Ioi_iff_Ioo [LinearOrderₓ 𝕜] [OrderClosedTopology 𝕜] {x y : 𝕜} (h : x < y) :
    HasDerivWithinAt f f' (Ioo x y) x ↔ HasDerivWithinAt f f' (Ioi x) x :=
  has_deriv_within_at_congr_set (is_open_Iio.mem_nhds h) <| by
    rw [Ioi_inter_Iio, inter_eq_left_iff_subset]
    exact Ioo_subset_Iio_self

alias HasDerivWithinAt.Ioi_iff_Ioo ↔ HasDerivWithinAt.Ioi_of_Ioo HasDerivWithinAt.Ioo_of_Ioi

theorem has_deriv_at_iff_is_o_nhds_zero : HasDerivAt f f' x ↔ (fun h => f (x + h) - f x - h • f') =o[𝓝 0] fun h => h :=
  has_fderiv_at_iff_is_o_nhds_zero

theorem HasDerivAtFilter.mono (h : HasDerivAtFilter f f' x L₂) (hst : L₁ ≤ L₂) : HasDerivAtFilter f f' x L₁ :=
  HasFderivAtFilter.mono h hst

theorem HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s ⊆ t) : HasDerivWithinAt f f' s x :=
  HasFderivWithinAt.mono h hst

theorem HasDerivAt.has_deriv_at_filter (h : HasDerivAt f f' x) (hL : L ≤ 𝓝 x) : HasDerivAtFilter f f' x L :=
  HasFderivAt.has_fderiv_at_filter h hL

theorem HasDerivAt.has_deriv_within_at (h : HasDerivAt f f' x) : HasDerivWithinAt f f' s x :=
  HasFderivAt.has_fderiv_within_at h

theorem HasDerivWithinAt.differentiable_within_at (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x :=
  HasFderivWithinAt.differentiable_within_at h

theorem HasDerivAt.differentiable_at (h : HasDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  HasFderivAt.differentiable_at h

@[simp]
theorem has_deriv_within_at_univ : HasDerivWithinAt f f' Univ x ↔ HasDerivAt f f' x :=
  has_fderiv_within_at_univ

theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
  smul_right_one_eq_iff.mp <| h₀.HasFderivAt.unique h₁

theorem has_deriv_within_at_inter' (h : t ∈ 𝓝[s] x) : HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  has_fderiv_within_at_inter' h

theorem has_deriv_within_at_inter (h : t ∈ 𝓝 x) : HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  has_fderiv_within_at_inter h

theorem HasDerivWithinAt.union (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWithinAt f f' t x) :
    HasDerivWithinAt f f' (s ∪ t) x :=
  hs.HasFderivWithinAt.union ht.HasFderivWithinAt

theorem HasDerivWithinAt.nhds_within (h : HasDerivWithinAt f f' s x) (ht : s ∈ 𝓝[t] x) : HasDerivWithinAt f f' t x :=
  (has_deriv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))

theorem HasDerivWithinAt.has_deriv_at (h : HasDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) : HasDerivAt f f' x :=
  HasFderivWithinAt.has_fderiv_at h hs

theorem DifferentiableWithinAt.has_deriv_within_at (h : DifferentiableWithinAt 𝕜 f s x) :
    HasDerivWithinAt f (derivWithin f s x) s x :=
  h.HasFderivWithinAt.HasDerivWithinAt

theorem DifferentiableAt.has_deriv_at (h : DifferentiableAt 𝕜 f x) : HasDerivAt f (deriv f x) x :=
  h.HasFderivAt.HasDerivAt

@[simp]
theorem has_deriv_at_deriv_iff : HasDerivAt f (deriv f x) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => h.DifferentiableAt, fun h => h.HasDerivAt⟩

@[simp]
theorem has_deriv_within_at_deriv_within_iff :
    HasDerivWithinAt f (derivWithin f s x) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => h.DifferentiableWithinAt, fun h => h.HasDerivWithinAt⟩

theorem DifferentiableOn.has_deriv_at (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) : HasDerivAt f (deriv f x) x :=
  (h.HasFderivAt hs).HasDerivAt

theorem HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f' :=
  h.DifferentiableAt.HasDerivAt.unique h

theorem deriv_eq {f' : 𝕜 → F} (h : ∀ x, HasDerivAt f (f' x) x) : deriv f = f' :=
  funext fun x => (h x).deriv

theorem HasDerivWithinAt.deriv_within (h : HasDerivWithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = f' :=
  hxs.eq_deriv _ h.DifferentiableWithinAt.HasDerivWithinAt h

theorem fderiv_within_deriv_within : (fderivWithin 𝕜 f s x : 𝕜 → F) 1 = derivWithin f s x :=
  rfl

theorem deriv_within_fderiv_within : smulRight (1 : 𝕜 →L[𝕜] 𝕜) (derivWithin f s x) = fderivWithin 𝕜 f s x := by
  simp [← derivWithin]

theorem fderiv_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x :=
  rfl

theorem deriv_fderiv : smulRight (1 : 𝕜 →L[𝕜] 𝕜) (deriv f x) = fderiv 𝕜 f x := by
  simp [← deriv]

theorem DifferentiableAt.deriv_within (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = deriv f x := by
  unfold derivWithin deriv
  rw [h.fderiv_within hxs]

theorem HasDerivWithinAt.deriv_eq_zero (hd : HasDerivWithinAt f 0 s x) (H : UniqueDiffWithinAt 𝕜 s x) : deriv f x = 0 :=
  ((em' (DifferentiableAt 𝕜 f x)).elim deriv_zero_of_not_differentiable_at) fun h =>
    H.eq_deriv _ h.HasDerivAt.HasDerivWithinAt hd

theorem deriv_within_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f t x) :
    derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.has_deriv_within_at h).mono st).derivWithin ht

@[simp]
theorem deriv_within_univ : derivWithin f Univ = deriv f := by
  ext
  unfold derivWithin deriv
  rw [fderiv_within_univ]

theorem deriv_within_inter (ht : t ∈ 𝓝 x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f (s ∩ t) x = derivWithin f s x := by
  unfold derivWithin
  rw [fderiv_within_inter ht hs]

theorem deriv_within_of_open (hs : IsOpen s) (hx : x ∈ s) : derivWithin f s x = deriv f x := by
  unfold derivWithin
  rw [fderiv_within_of_open hs hx]
  rfl

theorem deriv_mem_iff {f : 𝕜 → F} {s : Set F} {x : 𝕜} :
    deriv f x ∈ s ↔ DifferentiableAt 𝕜 f x ∧ deriv f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : F) ∈ s := by
  by_cases' hx : DifferentiableAt 𝕜 f x <;> simp [← deriv_zero_of_not_differentiable_at, *]

theorem deriv_within_mem_iff {f : 𝕜 → F} {t : Set 𝕜} {s : Set F} {x : 𝕜} :
    derivWithin f t x ∈ s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ derivWithin f t x ∈ s ∨ ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : F) ∈ s :=
  by
  by_cases' hx : DifferentiableWithinAt 𝕜 f t x <;> simp [← deriv_within_zero_of_not_differentiable_within_at, *]

theorem differentiable_within_at_Ioi_iff_Ici [PartialOrderₓ 𝕜] :
    DifferentiableWithinAt 𝕜 f (Ioi x) x ↔ DifferentiableWithinAt 𝕜 f (Ici x) x :=
  ⟨fun h => h.HasDerivWithinAt.Ici_of_Ioi.DifferentiableWithinAt, fun h =>
    h.HasDerivWithinAt.Ioi_of_Ici.DifferentiableWithinAt⟩

theorem deriv_within_Ioi_eq_Ici {E : Type _} [NormedGroup E] [NormedSpace ℝ E] (f : ℝ → E) (x : ℝ) :
    derivWithin f (Ioi x) x = derivWithin f (Ici x) x := by
  by_cases' H : DifferentiableWithinAt ℝ f (Ioi x) x
  · have A := H.has_deriv_within_at.Ici_of_Ioi
    have B := (differentiable_within_at_Ioi_iff_Ici.1 H).HasDerivWithinAt
    simpa using (unique_diff_on_Ici x).Eq le_rfl A B
    
  · rw [deriv_within_zero_of_not_differentiable_within_at H, deriv_within_zero_of_not_differentiable_within_at]
    rwa [differentiable_within_at_Ioi_iff_Ici] at H
    

section congr

/-! ### Congruence properties of derivatives -/


theorem Filter.EventuallyEq.has_deriv_at_filter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x) (h₁ : f₀' = f₁') :
    HasDerivAtFilter f₀ f₀' x L ↔ HasDerivAtFilter f₁ f₁' x L :=
  h₀.has_fderiv_at_filter_iff hx
    (by
      simp [← h₁])

theorem HasDerivAtFilter.congr_of_eventually_eq (h : HasDerivAtFilter f f' x L) (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) :
    HasDerivAtFilter f₁ f' x L := by
  rwa [hL.has_deriv_at_filter_iff hx rfl]

theorem HasDerivWithinAt.congr_mono (h : HasDerivWithinAt f f' s x) (ht : ∀, ∀ x ∈ t, ∀, f₁ x = f x) (hx : f₁ x = f x)
    (h₁ : t ⊆ s) : HasDerivWithinAt f₁ f' t x :=
  HasFderivWithinAt.congr_mono h ht hx h₁

theorem HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x) (hs : ∀, ∀ x ∈ s, ∀, f₁ x = f x) (hx : f₁ x = f x) :
    HasDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)

theorem HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : ∀, ∀ x ∈ s, ∀, f₁ x = f x) (hx : x ∈ s) :
    HasDerivWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)

theorem HasDerivWithinAt.congr_of_eventually_eq (h : HasDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  HasDerivAtFilter.congr_of_eventually_eq h h₁ hx

theorem HasDerivWithinAt.congr_of_eventually_eq_of_mem (h : HasDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
    (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr_of_eventually_eq h₁ (h₁.eq_of_nhds_within hx)

theorem HasDerivAt.congr_of_eventually_eq (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) : HasDerivAt f₁ f' x :=
  HasDerivAtFilter.congr_of_eventually_eq h h₁ (mem_of_mem_nhds h₁ : _)

theorem Filter.EventuallyEq.deriv_within_eq (hs : UniqueDiffWithinAt 𝕜 s x) (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [hL.fderiv_within_eq hs hx]

theorem deriv_within_congr (hs : UniqueDiffWithinAt 𝕜 s x) (hL : ∀, ∀ y ∈ s, ∀, f₁ y = f y) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [fderiv_within_congr hs hL hx]

theorem Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x := by
  unfold deriv
  rwa [Filter.EventuallyEq.fderiv_eq]

protected theorem Filter.EventuallyEq.deriv (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
  h.eventually_eq_nhds.mono fun x h => h.deriv_eq

end congr

section id

/-! ### Derivative of the identity -/


variable (s x L)

theorem has_deriv_at_filter_id : HasDerivAtFilter id 1 x L :=
  (has_fderiv_at_filter_id x L).HasDerivAtFilter

theorem has_deriv_within_at_id : HasDerivWithinAt id 1 s x :=
  has_deriv_at_filter_id _ _

theorem has_deriv_at_id : HasDerivAt id 1 x :=
  has_deriv_at_filter_id _ _

theorem has_deriv_at_id' : HasDerivAt (fun x : 𝕜 => x) 1 x :=
  has_deriv_at_filter_id _ _

theorem has_strict_deriv_at_id : HasStrictDerivAt id 1 x :=
  (has_strict_fderiv_at_id x).HasStrictDerivAt

theorem deriv_id : deriv id x = 1 :=
  HasDerivAt.deriv (has_deriv_at_id x)

@[simp]
theorem deriv_id' : deriv (@id 𝕜) = fun _ => 1 :=
  funext deriv_id

@[simp]
theorem deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1 :=
  deriv_id'

theorem deriv_within_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin id s x = 1 :=
  (has_deriv_within_at_id x s).derivWithin hxs

end id

section Const

/-! ### Derivative of constant functions -/


variable (c : F) (s x L)

theorem has_deriv_at_filter_const : HasDerivAtFilter (fun x => c) 0 x L :=
  (has_fderiv_at_filter_const c x L).HasDerivAtFilter

theorem has_strict_deriv_at_const : HasStrictDerivAt (fun x => c) 0 x :=
  (has_strict_fderiv_at_const c x).HasStrictDerivAt

theorem has_deriv_within_at_const : HasDerivWithinAt (fun x => c) 0 s x :=
  has_deriv_at_filter_const _ _ _

theorem has_deriv_at_const : HasDerivAt (fun x => c) 0 x :=
  has_deriv_at_filter_const _ _ _

theorem deriv_const : deriv (fun x => c) x = 0 :=
  HasDerivAt.deriv (has_deriv_at_const x c)

@[simp]
theorem deriv_const' : (deriv fun x : 𝕜 => c) = fun x => 0 :=
  funext fun x => deriv_const x c

theorem deriv_within_const (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun x => c) s x = 0 :=
  (has_deriv_within_at_const _ _ _).derivWithin hxs

end Const

section ContinuousLinearMap

/-! ### Derivative of continuous linear maps -/


variable (e : 𝕜 →L[𝕜] F)

protected theorem ContinuousLinearMap.has_deriv_at_filter : HasDerivAtFilter e (e 1) x L :=
  e.HasFderivAtFilter.HasDerivAtFilter

protected theorem ContinuousLinearMap.has_strict_deriv_at : HasStrictDerivAt e (e 1) x :=
  e.HasStrictFderivAt.HasStrictDerivAt

protected theorem ContinuousLinearMap.has_deriv_at : HasDerivAt e (e 1) x :=
  e.HasDerivAtFilter

protected theorem ContinuousLinearMap.has_deriv_within_at : HasDerivWithinAt e (e 1) s x :=
  e.HasDerivAtFilter

@[simp]
protected theorem ContinuousLinearMap.deriv : deriv e x = e 1 :=
  e.HasDerivAt.deriv

protected theorem ContinuousLinearMap.deriv_within (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin e s x = e 1 :=
  e.HasDerivWithinAt.derivWithin hxs

end ContinuousLinearMap

section LinearMap

/-! ### Derivative of bundled linear maps -/


variable (e : 𝕜 →ₗ[𝕜] F)

protected theorem LinearMap.has_deriv_at_filter : HasDerivAtFilter e (e 1) x L :=
  e.toContinuousLinearMap₁.HasDerivAtFilter

protected theorem LinearMap.has_strict_deriv_at : HasStrictDerivAt e (e 1) x :=
  e.toContinuousLinearMap₁.HasStrictDerivAt

protected theorem LinearMap.has_deriv_at : HasDerivAt e (e 1) x :=
  e.HasDerivAtFilter

protected theorem LinearMap.has_deriv_within_at : HasDerivWithinAt e (e 1) s x :=
  e.HasDerivAtFilter

@[simp]
protected theorem LinearMap.deriv : deriv e x = e 1 :=
  e.HasDerivAt.deriv

protected theorem LinearMap.deriv_within (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin e s x = e 1 :=
  e.HasDerivWithinAt.derivWithin hxs

end LinearMap

section Add

/-! ### Derivative of the sum of two functions -/


theorem HasDerivAtFilter.add (hf : HasDerivAtFilter f f' x L) (hg : HasDerivAtFilter g g' x L) :
    HasDerivAtFilter (fun y => f y + g y) (f' + g') x L := by
  simpa using (hf.add hg).HasDerivAtFilter

theorem HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (fun y => f y + g y) (f' + g') x := by
  simpa using (hf.add hg).HasStrictDerivAt

theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg

theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg

theorem deriv_within_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y + g y) s x = derivWithin f s x + derivWithin g s x :=
  (hf.HasDerivWithinAt.add hg.HasDerivWithinAt).derivWithin hxs

@[simp]
theorem deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x :=
  (hf.HasDerivAt.add hg.HasDerivAt).deriv

theorem HasDerivAtFilter.add_const (hf : HasDerivAtFilter f f' x L) (c : F) :
    HasDerivAtFilter (fun y => f y + c) f' x L :=
  add_zeroₓ f' ▸ hf.add (has_deriv_at_filter_const x L c)

theorem HasDerivWithinAt.add_const (hf : HasDerivWithinAt f f' s x) (c : F) :
    HasDerivWithinAt (fun y => f y + c) f' s x :=
  hf.AddConst c

theorem HasDerivAt.add_const (hf : HasDerivAt f f' x) (c : F) : HasDerivAt (fun x => f x + c) f' x :=
  hf.AddConst c

theorem deriv_within_add_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => f y + c) s x = derivWithin f s x := by
  simp only [← derivWithin, ← fderiv_within_add_const hxs]

theorem deriv_add_const (c : F) : deriv (fun y => f y + c) x = deriv f x := by
  simp only [← deriv, ← fderiv_add_const]

@[simp]
theorem deriv_add_const' (c : F) : (deriv fun y => f y + c) = deriv f :=
  funext fun x => deriv_add_const c

theorem HasDerivAtFilter.const_add (c : F) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun y => c + f y) f' x L :=
  zero_addₓ f' ▸ (has_deriv_at_filter_const x L c).add hf

theorem HasDerivWithinAt.const_add (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c + f y) f' s x :=
  hf.const_add c

theorem HasDerivAt.const_add (c : F) (hf : HasDerivAt f f' x) : HasDerivAt (fun x => c + f x) f' x :=
  hf.const_add c

theorem deriv_within_const_add (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => c + f y) s x = derivWithin f s x := by
  simp only [← derivWithin, ← fderiv_within_const_add hxs]

theorem deriv_const_add (c : F) : deriv (fun y => c + f y) x = deriv f x := by
  simp only [← deriv, ← fderiv_const_add]

@[simp]
theorem deriv_const_add' (c : F) : (deriv fun y => c + f y) = deriv f :=
  funext fun x => deriv_const_add c

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


open BigOperators

variable {ι : Type _} {u : Finset ι} {A : ι → 𝕜 → F} {A' : ι → F}

theorem HasDerivAtFilter.sum (h : ∀, ∀ i ∈ u, ∀, HasDerivAtFilter (A i) (A' i) x L) :
    HasDerivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x L := by
  simpa [← ContinuousLinearMap.sum_apply] using (HasFderivAtFilter.sum h).HasDerivAtFilter

theorem HasStrictDerivAt.sum (h : ∀, ∀ i ∈ u, ∀, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x := by
  simpa [← ContinuousLinearMap.sum_apply] using (HasStrictFderivAt.sum h).HasStrictDerivAt

theorem HasDerivWithinAt.sum (h : ∀, ∀ i ∈ u, ∀, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x :=
  HasDerivAtFilter.sum h

theorem HasDerivAt.sum (h : ∀, ∀ i ∈ u, ∀, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  HasDerivAtFilter.sum h

theorem deriv_within_sum (hxs : UniqueDiffWithinAt 𝕜 s x) (h : ∀, ∀ i ∈ u, ∀, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin (fun y => ∑ i in u, A i y) s x = ∑ i in u, derivWithin (A i) s x :=
  (HasDerivWithinAt.sum fun i hi => (h i hi).HasDerivWithinAt).derivWithin hxs

@[simp]
theorem deriv_sum (h : ∀, ∀ i ∈ u, ∀, DifferentiableAt 𝕜 (A i) x) :
    deriv (fun y => ∑ i in u, A i y) x = ∑ i in u, deriv (A i) x :=
  (HasDerivAt.sum fun i hi => (h i hi).HasDerivAt).deriv

end Sum

section Pi

/-! ### Derivatives of functions `f : 𝕜 → Π i, E i` -/


variable {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
  {φ : 𝕜 → ∀ i, E' i} {φ' : ∀ i, E' i}

@[simp]
theorem has_strict_deriv_at_pi : HasStrictDerivAt φ φ' x ↔ ∀ i, HasStrictDerivAt (fun x => φ x i) (φ' i) x :=
  has_strict_fderiv_at_pi'

@[simp]
theorem has_deriv_at_filter_pi : HasDerivAtFilter φ φ' x L ↔ ∀ i, HasDerivAtFilter (fun x => φ x i) (φ' i) x L :=
  has_fderiv_at_filter_pi'

theorem has_deriv_at_pi : HasDerivAt φ φ' x ↔ ∀ i, HasDerivAt (fun x => φ x i) (φ' i) x :=
  has_deriv_at_filter_pi

theorem has_deriv_within_at_pi : HasDerivWithinAt φ φ' s x ↔ ∀ i, HasDerivWithinAt (fun x => φ x i) (φ' i) s x :=
  has_deriv_at_filter_pi

theorem deriv_within_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (fun x => φ x i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin φ s x = fun i => derivWithin (fun x => φ x i) s x :=
  (has_deriv_within_at_pi.2 fun i => (h i).HasDerivWithinAt).derivWithin hs

theorem deriv_pi (h : ∀ i, DifferentiableAt 𝕜 (fun x => φ x i) x) : deriv φ x = fun i => deriv (fun x => φ x i) x :=
  (has_deriv_at_pi.2 fun i => (h i).HasDerivAt).deriv

end Pi

section Smul

/-! ### Derivative of the multiplication of a scalar function and a vector function -/


variable {𝕜' : Type _} [NondiscreteNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {c : 𝕜 → 𝕜'} {c' : 𝕜'}

theorem HasDerivWithinAt.smul (hc : HasDerivWithinAt c c' s x) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c y • f y) (c x • f' + c' • f x) s x := by
  simpa using (HasFderivWithinAt.smul hc hf).HasDerivWithinAt

theorem HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => c y • f y) (c x • f' + c' • f x) x := by
  rw [← has_deriv_within_at_univ] at *
  exact hc.smul hf

theorem HasStrictDerivAt.smul (hc : HasStrictDerivAt c c' x) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y => c y • f y) (c x • f' + c' • f x) x := by
  simpa using (hc.smul hf).HasStrictDerivAt

theorem deriv_within_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c y • f y) s x = c x • derivWithin f s x + derivWithin c s x • f x :=
  (hc.HasDerivWithinAt.smul hf.HasDerivWithinAt).derivWithin hxs

theorem deriv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c y • f y) x = c x • deriv f x + deriv c x • f x :=
  (hc.HasDerivAt.smul hf.HasDerivAt).deriv

theorem HasStrictDerivAt.smul_const (hc : HasStrictDerivAt c c' x) (f : F) :
    HasStrictDerivAt (fun y => c y • f) (c' • f) x := by
  have := hc.smul (has_strict_deriv_at_const x f)
  rwa [smul_zero, zero_addₓ] at this

theorem HasDerivWithinAt.smul_const (hc : HasDerivWithinAt c c' s x) (f : F) :
    HasDerivWithinAt (fun y => c y • f) (c' • f) s x := by
  have := hc.smul (has_deriv_within_at_const x s f)
  rwa [smul_zero, zero_addₓ] at this

theorem HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f : F) : HasDerivAt (fun y => c y • f) (c' • f) x := by
  rw [← has_deriv_within_at_univ] at *
  exact hc.smul_const f

theorem deriv_within_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    derivWithin (fun y => c y • f) s x = derivWithin c s x • f :=
  (hc.HasDerivWithinAt.smul_const f).derivWithin hxs

theorem deriv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) : deriv (fun y => c y • f) x = deriv c x • f :=
  (hc.HasDerivAt.smul_const f).deriv

end Smul

section ConstSmul

variable {R : Type _} [Semiringₓ R] [Module R F] [SmulCommClass 𝕜 R F] [HasContinuousConstSmul R F]

theorem HasStrictDerivAt.const_smul (c : R) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y => c • f y) (c • f') x := by
  simpa using (hf.const_smul c).HasStrictDerivAt

theorem HasDerivAtFilter.const_smul (c : R) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun y => c • f y) (c • f') x L := by
  simpa using (hf.const_smul c).HasDerivAtFilter

theorem HasDerivWithinAt.const_smul (c : R) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c • f y) (c • f') s x :=
  hf.const_smul c

theorem HasDerivAt.const_smul (c : R) (hf : HasDerivAt f f' x) : HasDerivAt (fun y => c • f y) (c • f') x :=
  hf.const_smul c

theorem deriv_within_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (c : R) (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c • f y) s x = c • derivWithin f s x :=
  (hf.HasDerivWithinAt.const_smul c).derivWithin hxs

theorem deriv_const_smul (c : R) (hf : DifferentiableAt 𝕜 f x) : deriv (fun y => c • f y) x = c • deriv f x :=
  (hf.HasDerivAt.const_smul c).deriv

end ConstSmul

section Neg

/-! ### Derivative of the negative of a function -/


theorem HasDerivAtFilter.neg (h : HasDerivAtFilter f f' x L) : HasDerivAtFilter (fun x => -f x) (-f') x L := by
  simpa using h.neg.has_deriv_at_filter

theorem HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s x) : HasDerivWithinAt (fun x => -f x) (-f') s x :=
  h.neg

theorem HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (fun x => -f x) (-f') x :=
  h.neg

theorem HasStrictDerivAt.neg (h : HasStrictDerivAt f f' x) : HasStrictDerivAt (fun x => -f x) (-f') x := by
  simpa using h.neg.has_strict_deriv_at

theorem derivWithin.neg (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun y => -f y) s x = -derivWithin f s x := by
  simp only [← derivWithin, ← fderiv_within_neg hxs, ← ContinuousLinearMap.neg_apply]

theorem deriv.neg : deriv (fun y => -f y) x = -deriv f x := by
  simp only [← deriv, ← fderiv_neg, ← ContinuousLinearMap.neg_apply]

@[simp]
theorem deriv.neg' : (deriv fun y => -f y) = fun x => -deriv f x :=
  funext fun x => deriv.neg

end Neg

section Neg2

/-! ### Derivative of the negation function (i.e `has_neg.neg`) -/


variable (s x L)

theorem has_deriv_at_filter_neg : HasDerivAtFilter Neg.neg (-1) x L :=
  HasDerivAtFilter.neg <| has_deriv_at_filter_id _ _

theorem has_deriv_within_at_neg : HasDerivWithinAt Neg.neg (-1) s x :=
  has_deriv_at_filter_neg _ _

theorem has_deriv_at_neg : HasDerivAt Neg.neg (-1) x :=
  has_deriv_at_filter_neg _ _

theorem has_deriv_at_neg' : HasDerivAt (fun x => -x) (-1) x :=
  has_deriv_at_filter_neg _ _

theorem has_strict_deriv_at_neg : HasStrictDerivAt Neg.neg (-1) x :=
  HasStrictDerivAt.neg <| has_strict_deriv_at_id _

theorem deriv_neg : deriv Neg.neg x = -1 :=
  HasDerivAt.deriv (has_deriv_at_neg x)

@[simp]
theorem deriv_neg' : deriv (Neg.neg : 𝕜 → 𝕜) = fun _ => -1 :=
  funext deriv_neg

@[simp]
theorem deriv_neg'' : deriv (fun x : 𝕜 => -x) x = -1 :=
  deriv_neg x

theorem deriv_within_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin Neg.neg s x = -1 :=
  (has_deriv_within_at_neg x s).derivWithin hxs

theorem differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 → 𝕜) :=
  Differentiable.neg differentiable_id

theorem differentiable_on_neg : DifferentiableOn 𝕜 (Neg.neg : 𝕜 → 𝕜) s :=
  DifferentiableOn.neg differentiable_on_id

end Neg2

section Sub

/-! ### Derivative of the difference of two functions -/


theorem HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' x L) (hg : HasDerivAtFilter g g' x L) :
    HasDerivAtFilter (fun x => f x - g x) (f' - g') x L := by
  simpa only [← sub_eq_add_neg] using hf.add hg.neg

theorem HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun x => f x - g x) (f' - g') s x :=
  hf.sub hg

theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg

theorem HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (fun x => f x - g x) (f' - g') x := by
  simpa only [← sub_eq_add_neg] using hf.add hg.neg

theorem deriv_within_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y - g y) s x = derivWithin f s x - derivWithin g s x :=
  (hf.HasDerivWithinAt.sub hg.HasDerivWithinAt).derivWithin hxs

@[simp]
theorem deriv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y - g y) x = deriv f x - deriv g x :=
  (hf.HasDerivAt.sub hg.HasDerivAt).deriv

theorem HasDerivAtFilter.is_O_sub (h : HasDerivAtFilter f f' x L) : (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  HasFderivAtFilter.is_O_sub h

theorem HasDerivAtFilter.is_O_sub_rev (hf : HasDerivAtFilter f f' x L) (hf' : f' ≠ 0) :
    (fun x' => x' - x) =O[L] fun x' => f x' - f x :=
  suffices AntilipschitzWith ∥f'∥₊⁻¹ (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') from hf.is_O_sub_rev this
  (AddMonoidHomClass.antilipschitz_of_bound (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f')) fun x => by
    simp [← norm_smul, div_eq_inv_mul, ← mul_div_cancel _ (mt norm_eq_zero.1 hf')]

theorem HasDerivAtFilter.sub_const (hf : HasDerivAtFilter f f' x L) (c : F) :
    HasDerivAtFilter (fun x => f x - c) f' x L := by
  simpa only [← sub_eq_add_neg] using hf.add_const (-c)

theorem HasDerivWithinAt.sub_const (hf : HasDerivWithinAt f f' s x) (c : F) :
    HasDerivWithinAt (fun x => f x - c) f' s x :=
  hf.sub_const c

theorem HasDerivAt.sub_const (hf : HasDerivAt f f' x) (c : F) : HasDerivAt (fun x => f x - c) f' x :=
  hf.sub_const c

theorem deriv_within_sub_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => f y - c) s x = derivWithin f s x := by
  simp only [← derivWithin, ← fderiv_within_sub_const hxs]

theorem deriv_sub_const (c : F) : deriv (fun y => f y - c) x = deriv f x := by
  simp only [← deriv, ← fderiv_sub_const]

theorem HasDerivAtFilter.const_sub (c : F) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => c - f x) (-f') x L := by
  simpa only [← sub_eq_add_neg] using hf.neg.const_add c

theorem HasDerivWithinAt.const_sub (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => c - f x) (-f') s x :=
  hf.const_sub c

theorem HasStrictDerivAt.const_sub (c : F) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => c - f x) (-f') x := by
  simpa only [← sub_eq_add_neg] using hf.neg.const_add c

theorem HasDerivAt.const_sub (c : F) (hf : HasDerivAt f f' x) : HasDerivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c

theorem deriv_within_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => c - f y) s x = -derivWithin f s x := by
  simp [← derivWithin, ← fderiv_within_const_sub hxs]

theorem deriv_const_sub (c : F) : deriv (fun y => c - f y) x = -deriv f x := by
  simp only [deriv_within_univ, ← deriv_within_const_sub (unique_diff_within_at_univ : UniqueDiffWithinAt 𝕜 _ _)]

end Sub

section Continuous

/-! ### Continuity of a function admitting a derivative -/


theorem HasDerivAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasDerivAtFilter f f' x L) : Tendsto f L (𝓝 (f x)) :=
  h.tendsto_nhds hL

theorem HasDerivWithinAt.continuous_within_at (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x :=
  HasDerivAtFilter.tendsto_nhds inf_le_left h

theorem HasDerivAt.continuous_at (h : HasDerivAt f f' x) : ContinuousAt f x :=
  HasDerivAtFilter.tendsto_nhds le_rfl h

protected theorem HasDerivAt.continuous_on {f f' : 𝕜 → F} (hderiv : ∀, ∀ x ∈ s, ∀, HasDerivAt f (f' x) x) :
    ContinuousOn f s := fun x hx => (hderiv x hx).ContinuousAt.ContinuousWithinAt

end Continuous

section CartesianProduct

/-! ### Derivative of the cartesian product of two functions -/


variable {G : Type w} [NormedGroup G] [NormedSpace 𝕜 G]

variable {f₂ : 𝕜 → G} {f₂' : G}

theorem HasDerivAtFilter.prod (hf₁ : HasDerivAtFilter f₁ f₁' x L) (hf₂ : HasDerivAtFilter f₂ f₂' x L) :
    HasDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁', f₂') x L :=
  hf₁.Prod hf₂

theorem HasDerivWithinAt.prod (hf₁ : HasDerivWithinAt f₁ f₁' s x) (hf₂ : HasDerivWithinAt f₂ f₂' s x) :
    HasDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') s x :=
  hf₁.Prod hf₂

theorem HasDerivAt.prod (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x) :
    HasDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  hf₁.Prod hf₂

theorem HasStrictDerivAt.prod (hf₁ : HasStrictDerivAt f₁ f₁' x) (hf₂ : HasStrictDerivAt f₂ f₂' x) :
    HasStrictDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  hf₁.Prod hf₂

end CartesianProduct

section Composition

/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector valued and scalar valued functions, and `comp`
in lemmas on composition of scalar valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/


/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variable {𝕜' : Type _} [NondiscreteNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {s' t' : Set 𝕜'} {h : 𝕜 → 𝕜'} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'} {h₁' : 𝕜} {g₁ : 𝕜' → F} {g₁' : F}
  {L' : Filter 𝕜'} (x)

theorem HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁ g₁' (h x) L') (hh : HasDerivAtFilter h h' x L)
    (hL : Tendsto h L L') : HasDerivAtFilter (g₁ ∘ h) (h' • g₁') x L := by
  simpa using ((hg.restrict_scalars 𝕜).comp x hh hL).HasDerivAtFilter

theorem HasDerivWithinAt.scomp_has_deriv_at (hg : HasDerivWithinAt g₁ g₁' s' (h x)) (hh : HasDerivAt h h' x)
    (hs : ∀ x, h x ∈ s') : HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  hg.scomp x hh <| tendsto_inf.2 ⟨hh.ContinuousAt, tendsto_principal.2 <| eventually_of_forall hs⟩

theorem HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁ g₁' t' (h x)) (hh : HasDerivWithinAt h h' s x)
    (hst : MapsTo h s t') : HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  hg.scomp x hh <| hh.ContinuousWithinAt.tendsto_nhds_within hst

/-- The chain rule. -/
theorem HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  hg.scomp x hh hh.ContinuousAt

theorem HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁ g₁' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x := by
  simpa using ((hg.restrict_scalars 𝕜).comp x hh).HasStrictDerivAt

theorem HasDerivAt.scomp_has_deriv_within_at (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivWithinAt h h' s x) :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  HasDerivWithinAt.scomp x hg.HasDerivWithinAt hh (maps_to_univ _ _)

theorem derivWithin.scomp (hg : DifferentiableWithinAt 𝕜' g₁ t' (h x)) (hh : DifferentiableWithinAt 𝕜 h s x)
    (hs : MapsTo h s t') (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) :=
  (HasDerivWithinAt.scomp x hg.HasDerivWithinAt hh.HasDerivWithinAt hs).derivWithin hxs

theorem deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) :=
  (HasDerivAt.scomp x hg.HasDerivAt hh.HasDerivAt).deriv

/-! ### Derivative of the composition of a scalar and vector functions -/


theorem HasDerivAtFilter.comp_has_fderiv_at_filter {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x) {L'' : Filter E}
    (hh₂ : HasDerivAtFilter h₂ h₂' (f x) L') (hf : HasFderivAtFilter f f' x L'') (hL : Tendsto f L'' L') :
    HasFderivAtFilter (h₂ ∘ f) (h₂' • f') x L'' := by
  convert (hh₂.restrict_scalars 𝕜).comp x hf hL
  ext x
  simp [← mul_comm]

theorem HasStrictDerivAt.comp_has_strict_fderiv_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' (f x)) (hf : HasStrictFderivAt f f' x) : HasStrictFderivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [HasStrictDerivAt] at hh
  convert (hh.restrict_scalars 𝕜).comp x hf
  ext x
  simp [← mul_comm]

theorem HasDerivAt.comp_has_fderiv_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x))
    (hf : HasFderivAt f f' x) : HasFderivAt (h₂ ∘ f) (h₂' • f') x :=
  hh.comp_has_fderiv_at_filter x hf hf.ContinuousAt

theorem HasDerivAt.comp_has_fderiv_within_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x))
    (hf : HasFderivWithinAt f f' s x) : HasFderivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.comp_has_fderiv_at_filter x hf hf.ContinuousWithinAt

theorem HasDerivWithinAt.comp_has_fderiv_within_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFderivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFderivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.comp_has_fderiv_at_filter x hf <| hf.ContinuousWithinAt.tendsto_nhds_within hst

/-! ### Derivative of the composition of two scalar functions -/


theorem HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ h₂' (h x) L') (hh : HasDerivAtFilter h h' x L)
    (hL : Tendsto h L L') : HasDerivAtFilter (h₂ ∘ h) (h₂' * h') x L := by
  rw [mul_comm]
  exact hh₂.scomp x hh hL

theorem HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x)) (hh : HasDerivWithinAt h h' s x)
    (hst : MapsTo h s s') : HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [mul_comm]
  exact hh₂.scomp x hh hst

/-- The chain rule. -/
theorem HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x :=
  hh₂.comp x hh hh.ContinuousAt

theorem HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [mul_comm]
  exact hh₂.scomp x hh

theorem HasDerivAt.comp_has_deriv_within_at (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x :=
  hh₂.HasDerivWithinAt.comp x hh (maps_to_univ _ _)

theorem derivWithin.comp (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x)) (hh : DifferentiableWithinAt 𝕜 h s x)
    (hs : MapsTo h s s') (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x :=
  (hh₂.HasDerivWithinAt.comp x hh.HasDerivWithinAt hs).derivWithin hxs

theorem deriv.comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x :=
  (hh₂.HasDerivAt.comp x hh.HasDerivAt).deriv

protected theorem HasDerivAtFilter.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivAtFilter f f' x L) (hL : Tendsto f L L)
    (hx : f x = x) (n : ℕ) : HasDerivAtFilter (f^[n]) (f' ^ n) x L := by
  have := hf.iterate hL hx n
  rwa [ContinuousLinearMap.smul_right_one_pow] at this

protected theorem HasDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x) (hx : f x = x) (n : ℕ) :
    HasDerivAt (f^[n]) (f' ^ n) x := by
  have := HasFderivAt.iterate hf hx n
  rwa [ContinuousLinearMap.smul_right_one_pow] at this

protected theorem HasDerivWithinAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivWithinAt f f' s x) (hx : f x = x)
    (hs : MapsTo f s s) (n : ℕ) : HasDerivWithinAt (f^[n]) (f' ^ n) s x := by
  have := HasFderivWithinAt.iterate hf hx hs n
  rwa [ContinuousLinearMap.smul_right_one_pow] at this

protected theorem HasStrictDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasStrictDerivAt f f' x) (hx : f x = x) (n : ℕ) :
    HasStrictDerivAt (f^[n]) (f' ^ n) x := by
  have := hf.iterate hx n
  rwa [ContinuousLinearMap.smul_right_one_pow] at this

end Composition

section CompositionVector

/-! ### Derivative of the composition of a function between vector spaces and a function on `𝕜` -/


open ContinuousLinearMap

variable {l : F → E} {l' : F →L[𝕜] E}

variable (x)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFderivWithinAt.comp_has_deriv_within_at {t : Set F} (hl : HasFderivWithinAt l l' t (f x))
    (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) : HasDerivWithinAt (l ∘ f) (l' f') s x := by
  simpa only [← one_apply, ← one_smul, ← smul_right_apply, ← coe_comp', ← (· ∘ ·)] using
    (hl.comp x hf.has_fderiv_within_at hst).HasDerivWithinAt

theorem HasFderivAt.comp_has_deriv_within_at (hl : HasFderivAt l l' (f x)) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (l ∘ f) (l' f') s x :=
  hl.HasFderivWithinAt.comp_has_deriv_within_at x hf (maps_to_univ _ _)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFderivAt.comp_has_deriv_at (hl : HasFderivAt l l' (f x)) (hf : HasDerivAt f f' x) :
    HasDerivAt (l ∘ f) (l' f') x :=
  has_deriv_within_at_univ.mp <| hl.comp_has_deriv_within_at x hf.HasDerivWithinAt

theorem HasStrictFderivAt.comp_has_strict_deriv_at (hl : HasStrictFderivAt l l' (f x)) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (l ∘ f) (l' f') x := by
  simpa only [← one_apply, ← one_smul, ← smul_right_apply, ← coe_comp', ← (· ∘ ·)] using
    (hl.comp x hf.has_strict_fderiv_at).HasStrictDerivAt

theorem fderivWithin.comp_deriv_within {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F → E) (derivWithin f s x) :=
  (hl.HasFderivWithinAt.comp_has_deriv_within_at x hf.HasDerivWithinAt hs).derivWithin hxs

theorem fderiv.comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (hf : DifferentiableAt 𝕜 f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) :=
  (hl.HasFderivAt.comp_has_deriv_at x hf.HasDerivAt).deriv

end CompositionVector

section Mul

/-! ### Derivative of the multiplication of two functions -/


variable {𝕜' 𝔸 : Type _} [NormedField 𝕜'] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝕜'] [NormedAlgebra 𝕜 𝔸] {c d : 𝕜 → 𝔸}
  {c' d' : 𝔸} {u v : 𝕜 → 𝕜'}

theorem HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c y * d y) (c' * d x + c x * d') s x := by
  have := (HasFderivWithinAt.mul' hc hd).HasDerivWithinAt
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_right_apply,
    ContinuousLinearMap.smul_right_apply, ContinuousLinearMap.smul_right_apply, ContinuousLinearMap.one_apply, one_smul,
    one_smul, add_commₓ] at this

theorem HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c y * d y) (c' * d x + c x * d') x := by
  rw [← has_deriv_within_at_univ] at *
  exact hc.mul hd

theorem HasStrictDerivAt.mul (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c y * d y) (c' * d x + c x * d') x := by
  have := (HasStrictFderivAt.mul' hc hd).HasStrictDerivAt
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_right_apply,
    ContinuousLinearMap.smul_right_apply, ContinuousLinearMap.smul_right_apply, ContinuousLinearMap.one_apply, one_smul,
    one_smul, add_commₓ] at this

theorem deriv_within_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c y * d y) s x = derivWithin c s x * d x + c x * derivWithin d s x :=
  (hc.HasDerivWithinAt.mul hd.HasDerivWithinAt).derivWithin hxs

@[simp]
theorem deriv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv d x :=
  (hc.HasDerivAt.mul hd.HasDerivAt).deriv

theorem HasDerivWithinAt.mul_const (hc : HasDerivWithinAt c c' s x) (d : 𝔸) :
    HasDerivWithinAt (fun y => c y * d) (c' * d) s x := by
  convert hc.mul (has_deriv_within_at_const x s d)
  rw [mul_zero, add_zeroₓ]

theorem HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d : 𝔸) : HasDerivAt (fun y => c y * d) (c' * d) x := by
  rw [← has_deriv_within_at_univ] at *
  exact hc.mul_const d

theorem has_deriv_at_mul_const (c : 𝕜) : HasDerivAt (fun x => x * c) c x := by
  simpa only [← one_mulₓ] using (has_deriv_at_id' x).mul_const c

theorem HasStrictDerivAt.mul_const (hc : HasStrictDerivAt c c' x) (d : 𝔸) :
    HasStrictDerivAt (fun y => c y * d) (c' * d) x := by
  convert hc.mul (has_strict_deriv_at_const x d)
  rw [mul_zero, add_zeroₓ]

theorem deriv_within_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸) :
    derivWithin (fun y => c y * d) s x = derivWithin c s x * d :=
  (hc.HasDerivWithinAt.mul_const d).derivWithin hxs

theorem deriv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸) : deriv (fun y => c y * d) x = deriv c x * d :=
  (hc.HasDerivAt.mul_const d).deriv

theorem deriv_mul_const_field (v : 𝕜') : deriv (fun y => u y * v) x = deriv u x * v := by
  by_cases' hu : DifferentiableAt 𝕜 u x
  · exact deriv_mul_const hu v
    
  · rw [deriv_zero_of_not_differentiable_at hu, zero_mul]
    rcases eq_or_ne v 0 with (rfl | hd)
    · simp only [← mul_zero, ← deriv_const]
      
    · refine' deriv_zero_of_not_differentiable_at (mt (fun H => _) hu)
      simpa only [← mul_inv_cancel_right₀ hd] using H.mul_const v⁻¹
      
    

@[simp]
theorem deriv_mul_const_field' (v : 𝕜') : (deriv fun x => u x * v) = fun x => deriv u x * v :=
  funext fun _ => deriv_mul_const_field v

theorem HasDerivWithinAt.const_mul (c : 𝔸) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c * d y) (c * d') s x := by
  convert (has_deriv_within_at_const x s c).mul hd
  rw [zero_mul, zero_addₓ]

theorem HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d' x) : HasDerivAt (fun y => c * d y) (c * d') x := by
  rw [← has_deriv_within_at_univ] at *
  exact hd.const_mul c

theorem HasStrictDerivAt.const_mul (c : 𝔸) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c * d y) (c * d') x := by
  convert (has_strict_deriv_at_const _ _).mul hd
  rw [zero_mul, zero_addₓ]

theorem deriv_within_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (c : 𝔸) (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c * d y) s x = c * derivWithin d s x :=
  (hd.HasDerivWithinAt.const_mul c).derivWithin hxs

theorem deriv_const_mul (c : 𝔸) (hd : DifferentiableAt 𝕜 d x) : deriv (fun y => c * d y) x = c * deriv d x :=
  (hd.HasDerivAt.const_mul c).deriv

theorem deriv_const_mul_field (u : 𝕜') : deriv (fun y => u * v y) x = u * deriv v x := by
  simp only [← mul_comm u, ← deriv_mul_const_field]

@[simp]
theorem deriv_const_mul_field' (u : 𝕜') : (deriv fun x => u * v x) = fun x => u * deriv v x :=
  funext fun x => deriv_const_mul_field u

end Mul

section Inverse

/-! ### Derivative of `x ↦ x⁻¹` -/


theorem has_strict_deriv_at_inv (hx : x ≠ 0) : HasStrictDerivAt Inv.inv (-(x ^ 2)⁻¹) x := by
  suffices (fun p : 𝕜 × 𝕜 => (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹)) =o[𝓝 (x, x)] fun p => (p.1 - p.2) * 1 by
    refine' this.congr' _ (eventually_of_forall fun _ => mul_oneₓ _)
    refine' eventually.mono (IsOpen.mem_nhds (is_open_ne.prod is_open_ne) ⟨hx, hx⟩) _
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    simp only [← mem_set_of_eq] at hy hz
    -- hy : y ≠ 0, hz : z ≠ 0
    field_simp [← hx, ← hy, ← hz]
    ring
  refine' (is_O_refl (fun p : 𝕜 × 𝕜 => p.1 - p.2) _).mul_is_o ((is_o_one_iff _).2 _)
  rw [← sub_self (x * x)⁻¹]
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv₀ <| mul_ne_zero hx hx)

theorem has_deriv_at_inv (x_ne_zero : x ≠ 0) : HasDerivAt (fun y => y⁻¹) (-(x ^ 2)⁻¹) x :=
  (has_strict_deriv_at_inv x_ne_zero).HasDerivAt

theorem has_deriv_within_at_inv (x_ne_zero : x ≠ 0) (s : Set 𝕜) : HasDerivWithinAt (fun x => x⁻¹) (-(x ^ 2)⁻¹) s x :=
  (has_deriv_at_inv x_ne_zero).HasDerivWithinAt

theorem differentiable_at_inv : DifferentiableAt 𝕜 (fun x => x⁻¹) x ↔ x ≠ 0 :=
  ⟨fun H => NormedField.continuous_at_inv.1 H.ContinuousAt, fun H => (has_deriv_at_inv H).DifferentiableAt⟩

theorem differentiable_within_at_inv (x_ne_zero : x ≠ 0) : DifferentiableWithinAt 𝕜 (fun x => x⁻¹) s x :=
  (differentiable_at_inv.2 x_ne_zero).DifferentiableWithinAt

theorem differentiable_on_inv : DifferentiableOn 𝕜 (fun x : 𝕜 => x⁻¹) { x | x ≠ 0 } := fun x hx =>
  differentiable_within_at_inv hx

theorem deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with (rfl | hne)
  · simp [← deriv_zero_of_not_differentiable_at (mt differentiable_at_inv.1 (not_not.2 rfl))]
    
  · exact (has_deriv_at_inv hne).deriv
    

@[simp]
theorem deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹ :=
  funext fun x => deriv_inv

theorem deriv_within_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => x⁻¹) s x = -(x ^ 2)⁻¹ := by
  rw [DifferentiableAt.deriv_within (differentiable_at_inv.2 x_ne_zero) hxs]
  exact deriv_inv

theorem has_fderiv_at_inv (x_ne_zero : x ≠ 0) :
    HasFderivAt (fun x => x⁻¹) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
  has_deriv_at_inv x_ne_zero

theorem has_fderiv_within_at_inv (x_ne_zero : x ≠ 0) :
    HasFderivWithinAt (fun x => x⁻¹) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) s x :=
  (has_fderiv_at_inv x_ne_zero).HasFderivWithinAt

theorem fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) := by
  rw [← deriv_fderiv, deriv_inv]

theorem fderiv_within_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => x⁻¹) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) := by
  rw [DifferentiableAt.fderiv_within (differentiable_at_inv.2 x_ne_zero) hxs]
  exact fderiv_inv

variable {c : 𝕜 → 𝕜} {c' : 𝕜}

theorem HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : c x ≠ 0) :
    HasDerivWithinAt (fun y => (c y)⁻¹) (-c' / c x ^ 2) s x := by
  convert (has_deriv_at_inv hx).comp_has_deriv_within_at x hc
  field_simp

theorem HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x ≠ 0) : HasDerivAt (fun y => (c y)⁻¹) (-c' / c x ^ 2) x := by
  rw [← has_deriv_within_at_univ] at *
  exact hc.inv hx

theorem DifferentiableWithinAt.inv (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => (c x)⁻¹) s x :=
  (hc.HasDerivWithinAt.inv hx).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.inv (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) : DifferentiableAt 𝕜 (fun x => (c x)⁻¹) x :=
  (hc.HasDerivAt.inv hx).DifferentiableAt

theorem DifferentiableOn.inv (hc : DifferentiableOn 𝕜 c s) (hx : ∀, ∀ x ∈ s, ∀, c x ≠ 0) :
    DifferentiableOn 𝕜 (fun x => (c x)⁻¹) s := fun x h => (hc x h).inv (hx x h)

@[simp]
theorem Differentiable.inv (hc : Differentiable 𝕜 c) (hx : ∀ x, c x ≠ 0) : Differentiable 𝕜 fun x => (c x)⁻¹ := fun x =>
  (hc x).inv (hx x)

theorem deriv_within_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s x / c x ^ 2 :=
  (hc.HasDerivWithinAt.inv hx).derivWithin hxs

@[simp]
theorem deriv_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) : deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.HasDerivAt.inv hx).deriv

end Inverse

section Division

/-! ### Derivative of `x ↦ c x / d x` -/


variable {𝕜' : Type _} [NondiscreteNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c d : 𝕜 → 𝕜'} {c' d' : 𝕜'}

theorem HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x) (hx : d x ≠ 0) :
    HasDerivWithinAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) s x := by
  convert hc.mul ((has_deriv_at_inv hx).comp_has_deriv_within_at x hd)
  · simp only [← div_eq_mul_inv]
    
  · field_simp
    ring
    

theorem HasStrictDerivAt.div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) (hx : d x ≠ 0) :
    HasStrictDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  convert hc.mul ((has_strict_deriv_at_inv hx).comp x hd)
  · simp only [← div_eq_mul_inv]
    
  · field_simp
    ring
    

theorem HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x ≠ 0) :
    HasDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  rw [← has_deriv_within_at_univ] at *
  exact hc.div hd hx

theorem DifferentiableWithinAt.div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x)
    (hx : d x ≠ 0) : DifferentiableWithinAt 𝕜 (fun x => c x / d x) s x :=
  (hc.HasDerivWithinAt.div hd.HasDerivWithinAt hx).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x ≠ 0) :
    DifferentiableAt 𝕜 (fun x => c x / d x) x :=
  (hc.HasDerivAt.div hd.HasDerivAt hx).DifferentiableAt

theorem DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s) (hx : ∀, ∀ x ∈ s, ∀, d x ≠ 0) :
    DifferentiableOn 𝕜 (fun x => c x / d x) s := fun x h => (hc x h).div (hd x h) (hx x h)

@[simp]
theorem Differentiable.div (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) (hx : ∀ x, d x ≠ 0) :
    Differentiable 𝕜 fun x => c x / d x := fun x => (hc x).div (hd x) (hx x)

theorem deriv_within_div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x ≠ 0)
    (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => c x / d x) s x = (derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2 :=
  (hc.HasDerivWithinAt.div hd.HasDerivWithinAt hx).derivWithin hxs

@[simp]
theorem deriv_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x ≠ 0) :
    deriv (fun x => c x / d x) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2 :=
  (hc.HasDerivAt.div hd.HasDerivAt hx).deriv

theorem HasDerivAt.div_const (hc : HasDerivAt c c' x) (d : 𝕜') : HasDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [← div_eq_mul_inv] using hc.mul_const d⁻¹

theorem HasDerivWithinAt.div_const (hc : HasDerivWithinAt c c' s x) (d : 𝕜') :
    HasDerivWithinAt (fun x => c x / d) (c' / d) s x := by
  simpa only [← div_eq_mul_inv] using hc.mul_const d⁻¹

theorem HasStrictDerivAt.div_const (hc : HasStrictDerivAt c c' x) (d : 𝕜') :
    HasStrictDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [← div_eq_mul_inv] using hc.mul_const d⁻¹

theorem DifferentiableWithinAt.div_const (hc : DifferentiableWithinAt 𝕜 c s x) {d : 𝕜'} :
    DifferentiableWithinAt 𝕜 (fun x => c x / d) s x :=
  (hc.HasDerivWithinAt.div_const _).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.div_const (hc : DifferentiableAt 𝕜 c x) {d : 𝕜'} : DifferentiableAt 𝕜 (fun x => c x / d) x :=
  (hc.HasDerivAt.div_const _).DifferentiableAt

theorem DifferentiableOn.div_const (hc : DifferentiableOn 𝕜 c s) {d : 𝕜'} : DifferentiableOn 𝕜 (fun x => c x / d) s :=
  fun x hx => (hc x hx).div_const

@[simp]
theorem Differentiable.div_const (hc : Differentiable 𝕜 c) {d : 𝕜'} : Differentiable 𝕜 fun x => c x / d := fun x =>
  (hc x).div_const

theorem deriv_within_div_const (hc : DifferentiableWithinAt 𝕜 c s x) {d : 𝕜'} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => c x / d) s x = derivWithin c s x / d := by
  simp [← div_eq_inv_mul, ← deriv_within_const_mul, ← hc, ← hxs]

@[simp]
theorem deriv_div_const (d : 𝕜') : deriv (fun x => c x / d) x = deriv c x / d := by
  simp only [← div_eq_mul_inv, ← deriv_mul_const_field]

end Division

section ClmCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/


open ContinuousLinearMap

variable {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G] {c : 𝕜 → F →L[𝕜] G} {c' : F →L[𝕜] G} {d : 𝕜 → E →L[𝕜] F}
  {d' : E →L[𝕜] F} {u : 𝕜 → F} {u' : F}

theorem HasStrictDerivAt.clm_comp (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x := by
  have := (hc.has_strict_fderiv_at.clm_comp hd.has_strict_fderiv_at).HasStrictDerivAt
  rwa [add_apply, comp_apply, comp_apply, smul_right_apply, smul_right_apply, one_apply, one_smul, one_smul,
    add_commₓ] at this

theorem HasDerivWithinAt.clm_comp (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') s x := by
  have := (hc.has_fderiv_within_at.clm_comp hd.has_fderiv_within_at).HasDerivWithinAt
  rwa [add_apply, comp_apply, comp_apply, smul_right_apply, smul_right_apply, one_apply, one_smul, one_smul,
    add_commₓ] at this

theorem HasDerivAt.clm_comp (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x := by
  rw [← has_deriv_within_at_univ] at *
  exact hc.clm_comp hd

theorem deriv_within_clm_comp (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun y => (c y).comp (d y)) s x = (derivWithin c s x).comp (d x) + (c x).comp (derivWithin d s x) :=
  (hc.HasDerivWithinAt.clm_comp hd.HasDerivWithinAt).derivWithin hxs

theorem deriv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => (c y).comp (d y)) x = (deriv c x).comp (d x) + (c x).comp (deriv d x) :=
  (hc.HasDerivAt.clm_comp hd.HasDerivAt).deriv

theorem HasStrictDerivAt.clm_apply (hc : HasStrictDerivAt c c' x) (hu : HasStrictDerivAt u u' x) :
    HasStrictDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x := by
  have := (hc.has_strict_fderiv_at.clm_apply hu.has_strict_fderiv_at).HasStrictDerivAt
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul, one_smul,
    add_commₓ] at this

theorem HasDerivWithinAt.clm_apply (hc : HasDerivWithinAt c c' s x) (hu : HasDerivWithinAt u u' s x) :
    HasDerivWithinAt (fun y => (c y) (u y)) (c' (u x) + c x u') s x := by
  have := (hc.has_fderiv_within_at.clm_apply hu.has_fderiv_within_at).HasDerivWithinAt
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul, one_smul,
    add_commₓ] at this

theorem HasDerivAt.clm_apply (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x := by
  have := (hc.has_fderiv_at.clm_apply hu.has_fderiv_at).HasDerivAt
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul, one_smul,
    add_commₓ] at this

theorem deriv_within_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) :
    derivWithin (fun y => (c y) (u y)) s x = derivWithin c s x (u x) + c x (derivWithin u s x) :=
  (hc.HasDerivWithinAt.clm_apply hu.HasDerivWithinAt).derivWithin hxs

theorem deriv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    deriv (fun y => (c y) (u y)) x = deriv c x (u x) + c x (deriv u x) :=
  (hc.HasDerivAt.clm_apply hu.HasDerivAt).deriv

end ClmCompApply

theorem HasStrictDerivAt.has_strict_fderiv_at_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x)
    (hf' : f' ≠ 0) : HasStrictFderivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
  hf

theorem HasDerivAt.has_fderiv_at_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜} (hf : HasDerivAt f f' x) (hf' : f' ≠ 0) :
    HasFderivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
  hf

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasStrictDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasStrictDerivAt f f' (g a)) (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasStrictDerivAt g f'⁻¹ a :=
  (hf.has_strict_fderiv_at_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has a
nonzero derivative `f'` at `f.symm a` in the strict sense, then `f.symm` has the derivative `f'⁻¹`
at `a` in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.has_strict_deriv_at_symm (f : LocalHomeomorph 𝕜 𝕜) {a f' : 𝕜} (ha : a ∈ f.Target) (hf' : f' ≠ 0)
    (htff' : HasStrictDerivAt f f' (f.symm a)) : HasStrictDerivAt f.symm f'⁻¹ a :=
  htff'.of_local_left_inverse (f.symm.ContinuousAt ha) hf' (f.eventually_right_inverse ha)

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem HasDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a) (hf : HasDerivAt f f' (g a))
    (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasDerivAt g f'⁻¹ a :=
  (hf.has_fderiv_at_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
nonzero derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.has_deriv_at_symm (f : LocalHomeomorph 𝕜 𝕜) {a f' : 𝕜} (ha : a ∈ f.Target) (hf' : f' ≠ 0)
    (htff' : HasDerivAt f f' (f.symm a)) : HasDerivAt f.symm f'⁻¹ a :=
  htff'.of_local_left_inverse (f.symm.ContinuousAt ha) hf' (f.eventually_right_inverse ha)

theorem HasDerivAt.eventually_ne (h : HasDerivAt f f' x) (hf' : f' ≠ 0) : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x :=
  (has_deriv_at_iff_has_fderiv_at.1 h).eventually_ne
    ⟨∥f'∥⁻¹, fun z => by
      field_simp [← norm_smul, ← mt norm_eq_zero.1 hf']⟩

theorem HasDerivAt.tendsto_punctured_nhds (h : HasDerivAt f f' x) (hf' : f' ≠ 0) : Tendsto f (𝓝[≠] x) (𝓝[≠] f x) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ h.ContinuousAt.ContinuousWithinAt (h.eventually_ne hf')

theorem not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero {f g : 𝕜 → 𝕜} {a : 𝕜} {s t : Set 𝕜}
    (ha : a ∈ s) (hsu : UniqueDiffWithinAt 𝕜 s a) (hf : HasDerivWithinAt f 0 t (g a)) (hst : MapsTo g s t)
    (hfg : f ∘ g =ᶠ[𝓝[s] a] id) : ¬DifferentiableWithinAt 𝕜 g s a := by
  intro hg
  have := (hf.comp a hg.has_deriv_within_at hst).congr_of_eventually_eq_of_mem hfg.symm ha
  simpa using hsu.eq_deriv _ this (has_deriv_within_at_id _ _)

theorem not_differentiable_at_of_local_left_inverse_has_deriv_at_zero {f g : 𝕜 → 𝕜} {a : 𝕜} (hf : HasDerivAt f 0 (g a))
    (hfg : f ∘ g =ᶠ[𝓝 a] id) : ¬DifferentiableAt 𝕜 g a := by
  intro hg
  have := (hf.comp a hg.has_deriv_at).congr_of_eventually_eq hfg.symm
  simpa using this.unique (has_deriv_at_id a)

end

namespace Polynomial

/-! ### Derivative of a polynomial -/


variable {x : 𝕜} {s : Set 𝕜}

variable (p : 𝕜[X])

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem has_strict_deriv_at (x : 𝕜) : HasStrictDerivAt (fun x => p.eval x) (p.derivative.eval x) x := by
  apply p.induction_on
  · simp [← has_strict_deriv_at_const]
    
  · intro p q hp hq
    convert hp.add hq <;> simp
    
  · intro n a h
    convert h.mul (has_strict_deriv_at_id x)
    · ext y
      simp [← pow_addₓ, ← mul_assoc]
      
    · simp [← pow_addₓ]
      ring
      
    

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem has_deriv_at (x : 𝕜) : HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
  (p.HasStrictDerivAt x).HasDerivAt

protected theorem has_deriv_within_at (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => p.eval x) (p.derivative.eval x) s x :=
  (p.HasDerivAt x).HasDerivWithinAt

protected theorem differentiable_at : DifferentiableAt 𝕜 (fun x => p.eval x) x :=
  (p.HasDerivAt x).DifferentiableAt

protected theorem differentiable_within_at : DifferentiableWithinAt 𝕜 (fun x => p.eval x) s x :=
  p.DifferentiableAt.DifferentiableWithinAt

protected theorem differentiable : Differentiable 𝕜 fun x => p.eval x := fun x => p.DifferentiableAt

protected theorem differentiable_on : DifferentiableOn 𝕜 (fun x => p.eval x) s :=
  p.Differentiable.DifferentiableOn

@[simp]
protected theorem deriv : deriv (fun x => p.eval x) x = p.derivative.eval x :=
  (p.HasDerivAt x).deriv

protected theorem deriv_within (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => p.eval x) s x = p.derivative.eval x := by
  rw [DifferentiableAt.deriv_within p.differentiable_at hxs]
  exact p.deriv

protected theorem has_fderiv_at (x : 𝕜) :
    HasFderivAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) x :=
  p.HasDerivAt x

protected theorem has_fderiv_within_at (x : 𝕜) :
    HasFderivWithinAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) s x :=
  (p.HasFderivAt x).HasFderivWithinAt

@[simp]
protected theorem fderiv : fderiv 𝕜 (fun x => p.eval x) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.HasFderivAt x).fderiv

protected theorem fderiv_within (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => p.eval x) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.HasFderivWithinAt x).fderivWithin hxs

end Polynomial

section Pow

/-! ### Derivative of `x ↦ x^n` for `n : ℕ` -/


variable {x : 𝕜} {s : Set 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜}

variable (n : ℕ)

theorem has_strict_deriv_at_pow (n : ℕ) (x : 𝕜) : HasStrictDerivAt (fun x => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x := by
  convert (Polynomial.c (1 : 𝕜) * Polynomial.x ^ n).HasStrictDerivAt x
  · simp
    
  · rw [Polynomial.derivative_C_mul_X_pow]
    simp
    

theorem has_deriv_at_pow (n : ℕ) (x : 𝕜) : HasDerivAt (fun x => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x :=
  (has_strict_deriv_at_pow n x).HasDerivAt

theorem has_deriv_within_at_pow (n : ℕ) (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x ^ n) ((n : 𝕜) * x ^ (n - 1)) s x :=
  (has_deriv_at_pow n x).HasDerivWithinAt

theorem differentiable_at_pow : DifferentiableAt 𝕜 (fun x => x ^ n) x :=
  (has_deriv_at_pow n x).DifferentiableAt

theorem differentiable_within_at_pow : DifferentiableWithinAt 𝕜 (fun x => x ^ n) s x :=
  (differentiable_at_pow n).DifferentiableWithinAt

theorem differentiable_pow : Differentiable 𝕜 fun x : 𝕜 => x ^ n := fun x => differentiable_at_pow n

theorem differentiable_on_pow : DifferentiableOn 𝕜 (fun x => x ^ n) s :=
  (differentiable_pow n).DifferentiableOn

theorem deriv_pow : deriv (fun x => x ^ n) x = (n : 𝕜) * x ^ (n - 1) :=
  (has_deriv_at_pow n x).deriv

@[simp]
theorem deriv_pow' : (deriv fun x => x ^ n) = fun x => (n : 𝕜) * x ^ (n - 1) :=
  funext fun x => deriv_pow n

theorem deriv_within_pow (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun x => x ^ n) s x = (n : 𝕜) * x ^ (n - 1) :=
  (has_deriv_within_at_pow n x s).derivWithin hxs

theorem HasDerivWithinAt.pow (hc : HasDerivWithinAt c c' s x) :
    HasDerivWithinAt (fun y => c y ^ n) ((n : 𝕜) * c x ^ (n - 1) * c') s x :=
  (has_deriv_at_pow n (c x)).comp_has_deriv_within_at x hc

theorem HasDerivAt.pow (hc : HasDerivAt c c' x) : HasDerivAt (fun y => c y ^ n) ((n : 𝕜) * c x ^ (n - 1) * c') x := by
  rw [← has_deriv_within_at_univ] at *
  exact hc.pow n

theorem DifferentiableWithinAt.pow (hc : DifferentiableWithinAt 𝕜 c s x) :
    DifferentiableWithinAt 𝕜 (fun x => c x ^ n) s x :=
  (hc.HasDerivWithinAt.pow n).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.pow (hc : DifferentiableAt 𝕜 c x) : DifferentiableAt 𝕜 (fun x => c x ^ n) x :=
  (hc.HasDerivAt.pow n).DifferentiableAt

theorem DifferentiableOn.pow (hc : DifferentiableOn 𝕜 c s) : DifferentiableOn 𝕜 (fun x => c x ^ n) s := fun x h =>
  (hc x h).pow n

@[simp]
theorem Differentiable.pow (hc : Differentiable 𝕜 c) : Differentiable 𝕜 fun x => c x ^ n := fun x => (hc x).pow n

theorem deriv_within_pow' (hc : DifferentiableWithinAt 𝕜 c s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => c x ^ n) s x = (n : 𝕜) * c x ^ (n - 1) * derivWithin c s x :=
  (hc.HasDerivWithinAt.pow n).derivWithin hxs

@[simp]
theorem deriv_pow'' (hc : DifferentiableAt 𝕜 c x) : deriv (fun x => c x ^ n) x = (n : 𝕜) * c x ^ (n - 1) * deriv c x :=
  (hc.HasDerivAt.pow n).deriv

end Pow

section Zpow

/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/


variable {x : 𝕜} {s : Set 𝕜} {m : ℤ}

theorem has_strict_deriv_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    HasStrictDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x := by
  have : ∀ m : ℤ, 0 < m → HasStrictDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x := by
    intro m hm
    lift m to ℕ using le_of_ltₓ hm
    simp only [← zpow_coe_nat, ← Int.cast_coe_nat]
    convert has_strict_deriv_at_pow _ _ using 2
    rw [← Int.coe_nat_one, ← Int.coe_nat_subₓ, zpow_coe_nat]
    norm_cast  at hm
    exact Nat.succ_le_of_ltₓ hm
  rcases lt_trichotomyₓ m 0 with (hm | hm | hm)
  · have hx : x ≠ 0 := h.resolve_right hm.not_le
    have := (has_strict_deriv_at_inv _).scomp _ (this (-m) (neg_pos.2 hm)) <;> [skip,
      exact zpow_ne_zero_of_ne_zero hx _]
    simp only [← (· ∘ ·), ← zpow_neg, ← one_div, ← inv_invₓ, ← smul_eq_mul] at this
    convert this using 1
    rw [sq, mul_inv, inv_invₓ, Int.cast_neg, neg_mul, neg_mul_neg, ← zpow_add₀ hx, mul_assoc, ← zpow_add₀ hx]
    congr
    abel
    
  · simp only [← hm, ← zpow_zero, ← Int.cast_zeroₓ, ← zero_mul, ← has_strict_deriv_at_const]
    
  · exact this m hm
    

theorem has_deriv_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) : HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x :=
  (has_strict_deriv_at_zpow m x h).HasDerivAt

theorem has_deriv_within_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) s x :=
  (has_deriv_at_zpow m x h).HasDerivWithinAt

theorem differentiable_at_zpow : DifferentiableAt 𝕜 (fun x => x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m :=
  ⟨fun H => NormedField.continuous_at_zpow.1 H.ContinuousAt, fun H => (has_deriv_at_zpow m x H).DifferentiableAt⟩

theorem differentiable_within_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    DifferentiableWithinAt 𝕜 (fun x => x ^ m) s x :=
  (differentiable_at_zpow.mpr h).DifferentiableWithinAt

theorem differentiable_on_zpow (m : ℤ) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 ≤ m) : DifferentiableOn 𝕜 (fun x => x ^ m) s :=
  fun x hxs => differentiable_within_at_zpow m x <| h.imp_left <| ne_of_mem_of_not_mem hxs

theorem deriv_zpow (m : ℤ) (x : 𝕜) : deriv (fun x => x ^ m) x = m * x ^ (m - 1) := by
  by_cases' H : x ≠ 0 ∨ 0 ≤ m
  · exact (has_deriv_at_zpow m x H).deriv
    
  · rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_zpow.1 H)]
    push_neg  at H
    rcases H with ⟨rfl, hm⟩
    rw [zero_zpow _ ((sub_one_lt _).trans hm).Ne, mul_zero]
    

@[simp]
theorem deriv_zpow' (m : ℤ) : (deriv fun x : 𝕜 => x ^ m) = fun x => m * x ^ (m - 1) :=
  funext <| deriv_zpow m

theorem deriv_within_zpow (hxs : UniqueDiffWithinAt 𝕜 s x) (h : x ≠ 0 ∨ 0 ≤ m) :
    derivWithin (fun x => x ^ m) s x = (m : 𝕜) * x ^ (m - 1) :=
  (has_deriv_within_at_zpow m x h s).derivWithin hxs

@[simp]
theorem iter_deriv_zpow' (m : ℤ) (k : ℕ) :
    ((deriv^[k]) fun x : 𝕜 => x ^ m) = fun x => (∏ i in Finset.range k, m - i) * x ^ (m - k) := by
  induction' k with k ihk
  · simp only [← one_mulₓ, ← Int.coe_nat_zero, ← id, ← sub_zero, ← Finset.prod_range_zero, ← Function.iterate_zero]
    
  · simp only [← Function.iterate_succ_apply', ← ihk, ← deriv_const_mul_field', ← deriv_zpow', ← Finset.prod_range_succ,
      ← Int.coe_nat_succ, sub_sub, ← Int.cast_sub, ← Int.cast_coe_nat, ← mul_assoc]
    

theorem iter_deriv_zpow (m : ℤ) (x : 𝕜) (k : ℕ) :
    (deriv^[k]) (fun y => y ^ m) x = (∏ i in Finset.range k, m - i) * x ^ (m - k) :=
  congr_fun (iter_deriv_zpow' m k) x

theorem iter_deriv_pow (n : ℕ) (x : 𝕜) (k : ℕ) :
    (deriv^[k]) (fun x : 𝕜 => x ^ n) x = (∏ i in Finset.range k, n - i) * x ^ (n - k) := by
  simp only [zpow_coe_nat, ← iter_deriv_zpow, ← Int.cast_coe_nat]
  cases' le_or_ltₓ k n with hkn hnk
  · rw [Int.coe_nat_subₓ hkn]
    
  · have : (∏ i in Finset.range k, (n - i : 𝕜)) = 0 := Finset.prod_eq_zero (Finset.mem_range.2 hnk) (sub_self _)
    simp only [← this, ← zero_mul]
    

@[simp]
theorem iter_deriv_pow' (n k : ℕ) :
    ((deriv^[k]) fun x : 𝕜 => x ^ n) = fun x => (∏ i in Finset.range k, n - i) * x ^ (n - k) :=
  funext fun x => iter_deriv_pow n x k

theorem iter_deriv_inv (k : ℕ) (x : 𝕜) : (deriv^[k]) Inv.inv x = (∏ i in Finset.range k, -1 - i) * x ^ (-1 - k : ℤ) :=
  by
  simpa only [← zpow_neg_one, ← Int.cast_neg, ← Int.cast_oneₓ] using iter_deriv_zpow (-1) x k

@[simp]
theorem iter_deriv_inv' (k : ℕ) :
    (deriv^[k]) Inv.inv = fun x : 𝕜 => (∏ i in Finset.range k, -1 - i) * x ^ (-1 - k : ℤ) :=
  funext (iter_deriv_inv k)

end Zpow

/-! ### Support of derivatives -/


section Support

open Function

variable {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F}

theorem support_deriv_subset : Support (deriv f) ⊆ Tsupport f := by
  intro x
  rw [← not_imp_not]
  intro h2x
  rw [not_mem_closure_support_iff_eventually_eq] at h2x
  exact nmem_support.mpr (h2x.deriv_eq.trans (deriv_const x 0))

theorem HasCompactSupport.deriv (hf : HasCompactSupport f) : HasCompactSupport (deriv f) :=
  hf.mono' support_deriv_subset

end Support

/-! ### Upper estimates on liminf and limsup -/


section Real

variable {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ} {r : ℝ}

theorem HasDerivWithinAt.limsup_slope_le (hf : HasDerivWithinAt f f' s x) (hr : f' < r) :
    ∀ᶠ z in 𝓝[s \ {x}] x, slope f x z < r :=
  has_deriv_within_at_iff_tendsto_slope.1 hf (IsOpen.mem_nhds is_open_Iio hr)

theorem HasDerivWithinAt.limsup_slope_le' (hf : HasDerivWithinAt f f' s x) (hs : x ∉ s) (hr : f' < r) :
    ∀ᶠ z in 𝓝[s] x, slope f x z < r :=
  (has_deriv_within_at_iff_tendsto_slope' hs).1 hf (IsOpen.mem_nhds is_open_Iio hr)

theorem HasDerivWithinAt.liminf_right_slope_le (hf : HasDerivWithinAt f f' (Ici x) x) (hr : f' < r) :
    ∃ᶠ z in 𝓝[>] x, slope f x z < r :=
  (hf.Ioi_of_Ici.limsup_slope_le' (lt_irreflₓ x) hr).Frequently

end Real

section RealSpace

open Metric

variable {E : Type u} [NormedGroup E] [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {s : Set ℝ} {x r : ℝ}

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ∥f'∥` the ratio
`∥f z - f x∥ / ∥z - x∥` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `∥f'∥`. -/
theorem HasDerivWithinAt.limsup_norm_slope_le (hf : HasDerivWithinAt f f' s x) (hr : ∥f'∥ < r) :
    ∀ᶠ z in 𝓝[s] x, ∥z - x∥⁻¹ * ∥f z - f x∥ < r := by
  have hr₀ : 0 < r := lt_of_le_of_ltₓ (norm_nonneg f') hr
  have A : ∀ᶠ z in 𝓝[s \ {x}] x, ∥(z - x)⁻¹ • (f z - f x)∥ ∈ Iio r :=
    (has_deriv_within_at_iff_tendsto_slope.1 hf).norm (IsOpen.mem_nhds is_open_Iio hr)
  have B : ∀ᶠ z in 𝓝[{x}] x, ∥(z - x)⁻¹ • (f z - f x)∥ ∈ Iio r :=
    mem_of_superset self_mem_nhds_within
      (singleton_subset_iff.2 <| by
        simp [← hr₀])
  have C := mem_sup.2 ⟨A, B⟩
  rw [← nhds_within_union, diff_union_self, nhds_within_union, mem_sup] at C
  filter_upwards [C.1]
  simp only [← norm_smul, ← mem_Iio, ← norm_inv]
  exact fun _ => id

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ∥f'∥` the ratio
`(∥f z∥ - ∥f x∥) / ∥z - x∥` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `∥f'∥`.

This lemma is a weaker version of `has_deriv_within_at.limsup_norm_slope_le`
where `∥f z∥ - ∥f x∥` is replaced by `∥f z - f x∥`. -/
theorem HasDerivWithinAt.limsup_slope_norm_le (hf : HasDerivWithinAt f f' s x) (hr : ∥f'∥ < r) :
    ∀ᶠ z in 𝓝[s] x, ∥z - x∥⁻¹ * (∥f z∥ - ∥f x∥) < r := by
  apply (hf.limsup_norm_slope_le hr).mono
  intro z hz
  refine' lt_of_le_of_ltₓ (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) _) hz
  exact inv_nonneg.2 (norm_nonneg _)

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ∥f'∥` the ratio
`∥f z - f x∥ / ∥z - x∥` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `∥f'∥`. See also `has_deriv_within_at.limsup_norm_slope_le`
for a stronger version using limit superior and any set `s`. -/
theorem HasDerivWithinAt.liminf_right_norm_slope_le (hf : HasDerivWithinAt f f' (Ici x) x) (hr : ∥f'∥ < r) :
    ∃ᶠ z in 𝓝[>] x, ∥z - x∥⁻¹ * ∥f z - f x∥ < r :=
  (hf.Ioi_of_Ici.limsup_norm_slope_le hr).Frequently

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ∥f'∥` the ratio
`(∥f z∥ - ∥f x∥) / (z - x)` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `∥f'∥`.

See also

* `has_deriv_within_at.limsup_norm_slope_le` for a stronger version using
  limit superior and any set `s`;
* `has_deriv_within_at.liminf_right_norm_slope_le` for a stronger version using
  `∥f z - f x∥` instead of `∥f z∥ - ∥f x∥`. -/
theorem HasDerivWithinAt.liminf_right_slope_norm_le (hf : HasDerivWithinAt f f' (Ici x) x) (hr : ∥f'∥ < r) :
    ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (∥f z∥ - ∥f x∥) < r := by
  have := (hf.Ioi_of_Ici.limsup_slope_norm_le hr).Frequently
  refine' this.mp (eventually.mono self_mem_nhds_within _)
  intro z hxz hz
  rwa [Real.norm_eq_abs, abs_of_pos (sub_pos_of_lt hxz)] at hz

end RealSpace

