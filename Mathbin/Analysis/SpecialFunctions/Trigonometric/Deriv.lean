/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathbin.Analysis.SpecialFunctions.ExpDeriv
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathbin.Data.Set.Intervals.Monotone

/-!
# Differentiability of trigonometric functions

## Main statements

The differentiability of the usual trigonometric functions is proved, and their derivatives are
computed.

## Tags

sin, cos, tan, angle
-/


noncomputable section

open Classical TopologicalSpace Filter

open Set Filter

namespace Complex

/-- The complex sine function is everywhere strictly differentiable, with the derivative `cos x`. -/
theorem has_strict_deriv_at_sin (x : ℂ) : HasStrictDerivAt sin (cos x) x := by
  simp only [← cos, ← div_eq_mul_inv]
  convert
    ((((has_strict_deriv_at_id x).neg.mul_const I).cexp.sub ((has_strict_deriv_at_id x).mul_const I).cexp).mul_const
          I).mul_const
      (2 : ℂ)⁻¹
  simp only [← Function.comp, ← id]
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_negₓ, mul_oneₓ, one_mulₓ, mul_assoc, I_mul_I,
    mul_neg_one, sub_neg_eq_add, add_commₓ]

/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
theorem has_deriv_at_sin (x : ℂ) : HasDerivAt sin (cos x) x :=
  (has_strict_deriv_at_sin x).HasDerivAt

theorem cont_diff_sin {n} : ContDiff ℂ n sin :=
  (((cont_diff_neg.mul cont_diff_const).cexp.sub (cont_diff_id.mul cont_diff_const).cexp).mul cont_diff_const).div_const

theorem differentiable_sin : Differentiable ℂ sin := fun x => (has_deriv_at_sin x).DifferentiableAt

theorem differentiable_at_sin {x : ℂ} : DifferentiableAt ℂ sin x :=
  differentiable_sin x

@[simp]
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (has_deriv_at_sin x).deriv

/-- The complex cosine function is everywhere strictly differentiable, with the derivative
`-sin x`. -/
theorem has_strict_deriv_at_cos (x : ℂ) : HasStrictDerivAt cos (-sin x) x := by
  simp only [← sin, ← div_eq_mul_inv, ← neg_mul_eq_neg_mulₓ]
  convert
    (((has_strict_deriv_at_id x).mul_const I).cexp.add ((has_strict_deriv_at_id x).neg.mul_const I).cexp).mul_const
      (2 : ℂ)⁻¹
  simp only [← Function.comp, ← id]
  ring

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
theorem has_deriv_at_cos (x : ℂ) : HasDerivAt cos (-sin x) x :=
  (has_strict_deriv_at_cos x).HasDerivAt

theorem cont_diff_cos {n} : ContDiff ℂ n cos :=
  ((cont_diff_id.mul cont_diff_const).cexp.add (cont_diff_neg.mul cont_diff_const).cexp).div_const

theorem differentiable_cos : Differentiable ℂ cos := fun x => (has_deriv_at_cos x).DifferentiableAt

theorem differentiable_at_cos {x : ℂ} : DifferentiableAt ℂ cos x :=
  differentiable_cos x

theorem deriv_cos {x : ℂ} : deriv cos x = -sin x :=
  (has_deriv_at_cos x).deriv

@[simp]
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun x => deriv_cos

/-- The complex hyperbolic sine function is everywhere strictly differentiable, with the derivative
`cosh x`. -/
theorem has_strict_deriv_at_sinh (x : ℂ) : HasStrictDerivAt sinh (cosh x) x := by
  simp only [← cosh, ← div_eq_mul_inv]
  convert ((has_strict_deriv_at_exp x).sub (has_strict_deriv_at_id x).neg.cexp).mul_const (2 : ℂ)⁻¹
  rw [id, mul_neg_one, sub_eq_add_neg, neg_negₓ]

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`. -/
theorem has_deriv_at_sinh (x : ℂ) : HasDerivAt sinh (cosh x) x :=
  (has_strict_deriv_at_sinh x).HasDerivAt

theorem cont_diff_sinh {n} : ContDiff ℂ n sinh :=
  (cont_diff_exp.sub cont_diff_neg.cexp).div_const

theorem differentiable_sinh : Differentiable ℂ sinh := fun x => (has_deriv_at_sinh x).DifferentiableAt

theorem differentiable_at_sinh {x : ℂ} : DifferentiableAt ℂ sinh x :=
  differentiable_sinh x

@[simp]
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (has_deriv_at_sinh x).deriv

/-- The complex hyperbolic cosine function is everywhere strictly differentiable, with the
derivative `sinh x`. -/
theorem has_strict_deriv_at_cosh (x : ℂ) : HasStrictDerivAt cosh (sinh x) x := by
  simp only [← sinh, ← div_eq_mul_inv]
  convert ((has_strict_deriv_at_exp x).add (has_strict_deriv_at_id x).neg.cexp).mul_const (2 : ℂ)⁻¹
  rw [id, mul_neg_one, sub_eq_add_neg]

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`. -/
theorem has_deriv_at_cosh (x : ℂ) : HasDerivAt cosh (sinh x) x :=
  (has_strict_deriv_at_cosh x).HasDerivAt

theorem cont_diff_cosh {n} : ContDiff ℂ n cosh :=
  (cont_diff_exp.add cont_diff_neg.cexp).div_const

theorem differentiable_cosh : Differentiable ℂ cosh := fun x => (has_deriv_at_cosh x).DifferentiableAt

theorem differentiable_at_cosh {x : ℂ} : DifferentiableAt ℂ cosh x :=
  differentiable_cosh x

@[simp]
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (has_deriv_at_cosh x).deriv

end Complex

section

/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : ℂ → ℂ` -/


variable {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ}

/-! #### `complex.cos` -/


theorem HasStrictDerivAt.ccos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.has_strict_deriv_at_cos (f x)).comp x hf

theorem HasDerivAt.ccos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.has_deriv_at_cos (f x)).comp x hf

theorem HasDerivWithinAt.ccos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') s x :=
  (Complex.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_ccos (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.ccos.derivWithin hxs

@[simp]
theorem deriv_ccos (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cos (f x)) x = -Complex.sin (f x) * deriv f x :=
  hc.HasDerivAt.ccos.deriv

/-! #### `complex.sin` -/


theorem HasStrictDerivAt.csin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.has_strict_deriv_at_sin (f x)).comp x hf

theorem HasDerivAt.csin (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.has_deriv_at_sin (f x)).comp x hf

theorem HasDerivWithinAt.csin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') s x :=
  (Complex.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_csin (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sin (f x)) s x = Complex.cos (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.csin.derivWithin hxs

@[simp]
theorem deriv_csin (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sin (f x)) x = Complex.cos (f x) * deriv f x :=
  hc.HasDerivAt.csin.deriv

/-! #### `complex.cosh` -/


theorem HasStrictDerivAt.ccosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.has_strict_deriv_at_cosh (f x)).comp x hf

theorem HasDerivAt.ccosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.has_deriv_at_cosh (f x)).comp x hf

theorem HasDerivWithinAt.ccosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') s x :=
  (Complex.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.ccosh.derivWithin hxs

@[simp]
theorem deriv_ccosh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) * deriv f x :=
  hc.HasDerivAt.ccosh.deriv

/-! #### `complex.sinh` -/


theorem HasStrictDerivAt.csinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.has_strict_deriv_at_sinh (f x)).comp x hf

theorem HasDerivAt.csinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.has_deriv_at_sinh (f x)).comp x hf

theorem HasDerivWithinAt.csinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') s x :=
  (Complex.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.csinh.derivWithin hxs

@[simp]
theorem deriv_csinh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) * deriv f x :=
  hc.HasDerivAt.csinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : E → ℂ` -/


variable {E : Type _} [NormedGroup E] [NormedSpace ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E} {s : Set E}

/-! #### `complex.cos` -/


theorem HasStrictFderivAt.ccos (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.has_strict_deriv_at_cos (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.ccos (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.has_deriv_at_cos (f x)).comp_has_fderiv_at x hf

theorem HasFderivWithinAt.ccos (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') s x :=
  (Complex.has_deriv_at_cos (f x)).comp_has_fderiv_within_at x hf

theorem DifferentiableWithinAt.ccos (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cos (f x)) s x :=
  hf.HasFderivWithinAt.ccos.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.ccos (hc : DifferentiableAt ℂ f x) : DifferentiableAt ℂ (fun x => Complex.cos (f x)) x :=
  hc.HasFderivAt.ccos.DifferentiableAt

theorem DifferentiableOn.ccos (hc : DifferentiableOn ℂ f s) : DifferentiableOn ℂ (fun x => Complex.cos (f x)) s :=
  fun x h => (hc x h).ccos

@[simp]
theorem Differentiable.ccos (hc : Differentiable ℂ f) : Differentiable ℂ fun x => Complex.cos (f x) := fun x =>
  (hc x).ccos

theorem fderiv_within_ccos (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) • fderivWithin ℂ f s x :=
  hf.HasFderivWithinAt.ccos.fderivWithin hxs

@[simp]
theorem fderiv_ccos (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cos (f x)) x = -Complex.sin (f x) • fderiv ℂ f x :=
  hc.HasFderivAt.ccos.fderiv

theorem ContDiff.ccos {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cos (f x) :=
  Complex.cont_diff_cos.comp h

theorem ContDiffAt.ccos {n} (hf : ContDiffAt ℂ n f x) : ContDiffAt ℂ n (fun x => Complex.cos (f x)) x :=
  Complex.cont_diff_cos.ContDiffAt.comp x hf

theorem ContDiffOn.ccos {n} (hf : ContDiffOn ℂ n f s) : ContDiffOn ℂ n (fun x => Complex.cos (f x)) s :=
  Complex.cont_diff_cos.comp_cont_diff_on hf

theorem ContDiffWithinAt.ccos {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cos (f x)) s x :=
  Complex.cont_diff_cos.ContDiffAt.comp_cont_diff_within_at x hf

/-! #### `complex.sin` -/


theorem HasStrictFderivAt.csin (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.has_strict_deriv_at_sin (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.csin (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.has_deriv_at_sin (f x)).comp_has_fderiv_at x hf

theorem HasFderivWithinAt.csin (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') s x :=
  (Complex.has_deriv_at_sin (f x)).comp_has_fderiv_within_at x hf

theorem DifferentiableWithinAt.csin (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sin (f x)) s x :=
  hf.HasFderivWithinAt.csin.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.csin (hc : DifferentiableAt ℂ f x) : DifferentiableAt ℂ (fun x => Complex.sin (f x)) x :=
  hc.HasFderivAt.csin.DifferentiableAt

theorem DifferentiableOn.csin (hc : DifferentiableOn ℂ f s) : DifferentiableOn ℂ (fun x => Complex.sin (f x)) s :=
  fun x h => (hc x h).csin

@[simp]
theorem Differentiable.csin (hc : Differentiable ℂ f) : Differentiable ℂ fun x => Complex.sin (f x) := fun x =>
  (hc x).csin

theorem fderiv_within_csin (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sin (f x)) s x = Complex.cos (f x) • fderivWithin ℂ f s x :=
  hf.HasFderivWithinAt.csin.fderivWithin hxs

@[simp]
theorem fderiv_csin (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sin (f x)) x = Complex.cos (f x) • fderiv ℂ f x :=
  hc.HasFderivAt.csin.fderiv

theorem ContDiff.csin {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sin (f x) :=
  Complex.cont_diff_sin.comp h

theorem ContDiffAt.csin {n} (hf : ContDiffAt ℂ n f x) : ContDiffAt ℂ n (fun x => Complex.sin (f x)) x :=
  Complex.cont_diff_sin.ContDiffAt.comp x hf

theorem ContDiffOn.csin {n} (hf : ContDiffOn ℂ n f s) : ContDiffOn ℂ n (fun x => Complex.sin (f x)) s :=
  Complex.cont_diff_sin.comp_cont_diff_on hf

theorem ContDiffWithinAt.csin {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sin (f x)) s x :=
  Complex.cont_diff_sin.ContDiffAt.comp_cont_diff_within_at x hf

/-! #### `complex.cosh` -/


theorem HasStrictFderivAt.ccosh (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.has_strict_deriv_at_cosh (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.ccosh (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.has_deriv_at_cosh (f x)).comp_has_fderiv_at x hf

theorem HasFderivWithinAt.ccosh (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') s x :=
  (Complex.has_deriv_at_cosh (f x)).comp_has_fderiv_within_at x hf

theorem DifferentiableWithinAt.ccosh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cosh (f x)) s x :=
  hf.HasFderivWithinAt.ccosh.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.ccosh (hc : DifferentiableAt ℂ f x) : DifferentiableAt ℂ (fun x => Complex.cosh (f x)) x :=
  hc.HasFderivAt.ccosh.DifferentiableAt

theorem DifferentiableOn.ccosh (hc : DifferentiableOn ℂ f s) : DifferentiableOn ℂ (fun x => Complex.cosh (f x)) s :=
  fun x h => (hc x h).ccosh

@[simp]
theorem Differentiable.ccosh (hc : Differentiable ℂ f) : Differentiable ℂ fun x => Complex.cosh (f x) := fun x =>
  (hc x).ccosh

theorem fderiv_within_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) • fderivWithin ℂ f s x :=
  hf.HasFderivWithinAt.ccosh.fderivWithin hxs

@[simp]
theorem fderiv_ccosh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) • fderiv ℂ f x :=
  hc.HasFderivAt.ccosh.fderiv

theorem ContDiff.ccosh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cosh (f x) :=
  Complex.cont_diff_cosh.comp h

theorem ContDiffAt.ccosh {n} (hf : ContDiffAt ℂ n f x) : ContDiffAt ℂ n (fun x => Complex.cosh (f x)) x :=
  Complex.cont_diff_cosh.ContDiffAt.comp x hf

theorem ContDiffOn.ccosh {n} (hf : ContDiffOn ℂ n f s) : ContDiffOn ℂ n (fun x => Complex.cosh (f x)) s :=
  Complex.cont_diff_cosh.comp_cont_diff_on hf

theorem ContDiffWithinAt.ccosh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cosh (f x)) s x :=
  Complex.cont_diff_cosh.ContDiffAt.comp_cont_diff_within_at x hf

/-! #### `complex.sinh` -/


theorem HasStrictFderivAt.csinh (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.has_strict_deriv_at_sinh (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.csinh (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.has_deriv_at_sinh (f x)).comp_has_fderiv_at x hf

theorem HasFderivWithinAt.csinh (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') s x :=
  (Complex.has_deriv_at_sinh (f x)).comp_has_fderiv_within_at x hf

theorem DifferentiableWithinAt.csinh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sinh (f x)) s x :=
  hf.HasFderivWithinAt.csinh.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.csinh (hc : DifferentiableAt ℂ f x) : DifferentiableAt ℂ (fun x => Complex.sinh (f x)) x :=
  hc.HasFderivAt.csinh.DifferentiableAt

theorem DifferentiableOn.csinh (hc : DifferentiableOn ℂ f s) : DifferentiableOn ℂ (fun x => Complex.sinh (f x)) s :=
  fun x h => (hc x h).csinh

@[simp]
theorem Differentiable.csinh (hc : Differentiable ℂ f) : Differentiable ℂ fun x => Complex.sinh (f x) := fun x =>
  (hc x).csinh

theorem fderiv_within_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) • fderivWithin ℂ f s x :=
  hf.HasFderivWithinAt.csinh.fderivWithin hxs

@[simp]
theorem fderiv_csinh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) • fderiv ℂ f x :=
  hc.HasFderivAt.csinh.fderiv

theorem ContDiff.csinh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sinh (f x) :=
  Complex.cont_diff_sinh.comp h

theorem ContDiffAt.csinh {n} (hf : ContDiffAt ℂ n f x) : ContDiffAt ℂ n (fun x => Complex.sinh (f x)) x :=
  Complex.cont_diff_sinh.ContDiffAt.comp x hf

theorem ContDiffOn.csinh {n} (hf : ContDiffOn ℂ n f s) : ContDiffOn ℂ n (fun x => Complex.sinh (f x)) s :=
  Complex.cont_diff_sinh.comp_cont_diff_on hf

theorem ContDiffWithinAt.csinh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sinh (f x)) s x :=
  Complex.cont_diff_sinh.ContDiffAt.comp_cont_diff_within_at x hf

end

namespace Real

variable {x y z : ℝ}

theorem has_strict_deriv_at_sin (x : ℝ) : HasStrictDerivAt sin (cos x) x :=
  (Complex.has_strict_deriv_at_sin x).real_of_complex

theorem has_deriv_at_sin (x : ℝ) : HasDerivAt sin (cos x) x :=
  (has_strict_deriv_at_sin x).HasDerivAt

theorem cont_diff_sin {n} : ContDiff ℝ n sin :=
  Complex.cont_diff_sin.real_of_complex

theorem differentiable_sin : Differentiable ℝ sin := fun x => (has_deriv_at_sin x).DifferentiableAt

theorem differentiable_at_sin : DifferentiableAt ℝ sin x :=
  differentiable_sin x

@[simp]
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (has_deriv_at_sin x).deriv

theorem has_strict_deriv_at_cos (x : ℝ) : HasStrictDerivAt cos (-sin x) x :=
  (Complex.has_strict_deriv_at_cos x).real_of_complex

theorem has_deriv_at_cos (x : ℝ) : HasDerivAt cos (-sin x) x :=
  (Complex.has_deriv_at_cos x).real_of_complex

theorem cont_diff_cos {n} : ContDiff ℝ n cos :=
  Complex.cont_diff_cos.real_of_complex

theorem differentiable_cos : Differentiable ℝ cos := fun x => (has_deriv_at_cos x).DifferentiableAt

theorem differentiable_at_cos : DifferentiableAt ℝ cos x :=
  differentiable_cos x

theorem deriv_cos : deriv cos x = -sin x :=
  (has_deriv_at_cos x).deriv

@[simp]
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun _ => deriv_cos

theorem has_strict_deriv_at_sinh (x : ℝ) : HasStrictDerivAt sinh (cosh x) x :=
  (Complex.has_strict_deriv_at_sinh x).real_of_complex

theorem has_deriv_at_sinh (x : ℝ) : HasDerivAt sinh (cosh x) x :=
  (Complex.has_deriv_at_sinh x).real_of_complex

theorem cont_diff_sinh {n} : ContDiff ℝ n sinh :=
  Complex.cont_diff_sinh.real_of_complex

theorem differentiable_sinh : Differentiable ℝ sinh := fun x => (has_deriv_at_sinh x).DifferentiableAt

theorem differentiable_at_sinh : DifferentiableAt ℝ sinh x :=
  differentiable_sinh x

@[simp]
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (has_deriv_at_sinh x).deriv

theorem has_strict_deriv_at_cosh (x : ℝ) : HasStrictDerivAt cosh (sinh x) x :=
  (Complex.has_strict_deriv_at_cosh x).real_of_complex

theorem has_deriv_at_cosh (x : ℝ) : HasDerivAt cosh (sinh x) x :=
  (Complex.has_deriv_at_cosh x).real_of_complex

theorem cont_diff_cosh {n} : ContDiff ℝ n cosh :=
  Complex.cont_diff_cosh.real_of_complex

theorem differentiable_cosh : Differentiable ℝ cosh := fun x => (has_deriv_at_cosh x).DifferentiableAt

theorem differentiable_at_cosh : DifferentiableAt ℝ cosh x :=
  differentiable_cosh x

@[simp]
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (has_deriv_at_cosh x).deriv

/-- `sinh` is strictly monotone. -/
theorem sinh_strict_mono : StrictMono sinh :=
  strict_mono_of_deriv_pos <| by
    rw [Real.deriv_sinh]
    exact cosh_pos

/-- `sinh` is injective, `∀ a b, sinh a = sinh b → a = b`. -/
theorem sinh_injective : Function.Injective sinh :=
  sinh_strict_mono.Injective

@[simp]
theorem sinh_inj : sinh x = sinh y ↔ x = y :=
  sinh_injective.eq_iff

@[simp]
theorem sinh_le_sinh : sinh x ≤ sinh y ↔ x ≤ y :=
  sinh_strict_mono.le_iff_le

@[simp]
theorem sinh_lt_sinh : sinh x < sinh y ↔ x < y :=
  sinh_strict_mono.lt_iff_lt

@[simp]
theorem sinh_pos_iff : 0 < sinh x ↔ 0 < x := by
  simpa only [← sinh_zero] using @sinh_lt_sinh 0 x

@[simp]
theorem sinh_nonpos_iff : sinh x ≤ 0 ↔ x ≤ 0 := by
  simpa only [← sinh_zero] using @sinh_le_sinh x 0

@[simp]
theorem sinh_neg_iff : sinh x < 0 ↔ x < 0 := by
  simpa only [← sinh_zero] using @sinh_lt_sinh x 0

@[simp]
theorem sinh_nonneg_iff : 0 ≤ sinh x ↔ 0 ≤ x := by
  simpa only [← sinh_zero] using @sinh_le_sinh 0 x

theorem cosh_strict_mono_on : StrictMonoOn cosh (Ici 0) :=
  ((convex_Ici _).strict_mono_on_of_deriv_pos continuous_cosh.ContinuousOn) fun x hx => by
    rw [interior_Ici, mem_Ioi] at hx
    rwa [deriv_cosh, sinh_pos_iff]

@[simp]
theorem cosh_le_cosh : cosh x ≤ cosh y ↔ abs x ≤ abs y :=
  cosh_abs x ▸ cosh_abs y ▸ cosh_strict_mono_on.le_iff_le (abs_nonneg x) (abs_nonneg y)

@[simp]
theorem cosh_lt_cosh : cosh x < cosh y ↔ abs x < abs y :=
  lt_iff_lt_of_le_iff_le cosh_le_cosh

@[simp]
theorem one_le_cosh (x : ℝ) : 1 ≤ cosh x :=
  cosh_zero ▸
    cosh_le_cosh.2
      (by
        simp only [← _root_.abs_zero, ← _root_.abs_nonneg])

@[simp]
theorem one_lt_cosh : 1 < cosh x ↔ x ≠ 0 :=
  cosh_zero ▸
    cosh_lt_cosh.trans
      (by
        simp only [← _root_.abs_zero, ← abs_pos])

theorem sinh_sub_id_strict_mono : StrictMono fun x => sinh x - x := by
  refine'
    strict_mono_of_odd_strict_mono_on_nonneg
      (fun x => by
        simp )
      _
  refine' (convex_Ici _).strict_mono_on_of_deriv_pos _ fun x hx => _
  · exact (continuous_sinh.sub continuous_id).ContinuousOn
    
  · rw [interior_Ici, mem_Ioi] at hx
    rw [deriv_sub, deriv_sinh, deriv_id'', sub_pos, one_lt_cosh]
    exacts[hx.ne', differentiable_at_sinh, differentiable_at_id]
    

@[simp]
theorem self_le_sinh_iff : x ≤ sinh x ↔ 0 ≤ x :=
  calc
    x ≤ sinh x ↔ sinh 0 - 0 ≤ sinh x - x := by
      simp
    _ ↔ 0 ≤ x := sinh_sub_id_strict_mono.le_iff_le
    

@[simp]
theorem sinh_le_self_iff : sinh x ≤ x ↔ x ≤ 0 :=
  calc
    sinh x ≤ x ↔ sinh x - x ≤ sinh 0 - 0 := by
      simp
    _ ↔ x ≤ 0 := sinh_sub_id_strict_mono.le_iff_le
    

@[simp]
theorem self_lt_sinh_iff : x < sinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le sinh_le_self_iff

@[simp]
theorem sinh_lt_self_iff : sinh x < x ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le self_le_sinh_iff

end Real

section

/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : ℝ → ℝ` -/


variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

/-! #### `real.cos` -/


theorem HasStrictDerivAt.cos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.has_strict_deriv_at_cos (f x)).comp x hf

theorem HasDerivAt.cos (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.has_deriv_at_cos (f x)).comp x hf

theorem HasDerivWithinAt.cos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') s x :=
  (Real.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_cos (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cos (f x)) s x = -Real.sin (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.cos.derivWithin hxs

@[simp]
theorem deriv_cos (hc : DifferentiableAt ℝ f x) : deriv (fun x => Real.cos (f x)) x = -Real.sin (f x) * deriv f x :=
  hc.HasDerivAt.cos.deriv

/-! #### `real.sin` -/


theorem HasStrictDerivAt.sin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.has_strict_deriv_at_sin (f x)).comp x hf

theorem HasDerivAt.sin (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.has_deriv_at_sin (f x)).comp x hf

theorem HasDerivWithinAt.sin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') s x :=
  (Real.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_sin (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sin (f x)) s x = Real.cos (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.sin.derivWithin hxs

@[simp]
theorem deriv_sin (hc : DifferentiableAt ℝ f x) : deriv (fun x => Real.sin (f x)) x = Real.cos (f x) * deriv f x :=
  hc.HasDerivAt.sin.deriv

/-! #### `real.cosh` -/


theorem HasStrictDerivAt.cosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.has_strict_deriv_at_cosh (f x)).comp x hf

theorem HasDerivAt.cosh (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.has_deriv_at_cosh (f x)).comp x hf

theorem HasDerivWithinAt.cosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') s x :=
  (Real.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cosh (f x)) s x = Real.sinh (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.cosh.derivWithin hxs

@[simp]
theorem deriv_cosh (hc : DifferentiableAt ℝ f x) : deriv (fun x => Real.cosh (f x)) x = Real.sinh (f x) * deriv f x :=
  hc.HasDerivAt.cosh.deriv

/-! #### `real.sinh` -/


theorem HasStrictDerivAt.sinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.has_strict_deriv_at_sinh (f x)).comp x hf

theorem HasDerivAt.sinh (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.has_deriv_at_sinh (f x)).comp x hf

theorem HasDerivWithinAt.sinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') s x :=
  (Real.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sinh (f x)) s x = Real.cosh (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.sinh.derivWithin hxs

@[simp]
theorem deriv_sinh (hc : DifferentiableAt ℝ f x) : deriv (fun x => Real.sinh (f x)) x = Real.cosh (f x) * deriv f x :=
  hc.HasDerivAt.sinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : E → ℝ` -/


variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E} {s : Set E}

/-! #### `real.cos` -/


theorem HasStrictFderivAt.cos (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.has_strict_deriv_at_cos (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.cos (hf : HasFderivAt f f' x) : HasFderivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.has_deriv_at_cos (f x)).comp_has_fderiv_at x hf

theorem HasFderivWithinAt.cos (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') s x :=
  (Real.has_deriv_at_cos (f x)).comp_has_fderiv_within_at x hf

theorem DifferentiableWithinAt.cos (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cos (f x)) s x :=
  hf.HasFderivWithinAt.cos.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.cos (hc : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun x => Real.cos (f x)) x :=
  hc.HasFderivAt.cos.DifferentiableAt

theorem DifferentiableOn.cos (hc : DifferentiableOn ℝ f s) : DifferentiableOn ℝ (fun x => Real.cos (f x)) s :=
  fun x h => (hc x h).cos

@[simp]
theorem Differentiable.cos (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cos (f x) := fun x => (hc x).cos

theorem fderiv_within_cos (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cos (f x)) s x = -Real.sin (f x) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.cos.fderivWithin hxs

@[simp]
theorem fderiv_cos (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cos (f x)) x = -Real.sin (f x) • fderiv ℝ f x :=
  hc.HasFderivAt.cos.fderiv

theorem ContDiff.cos {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cos (f x) :=
  Real.cont_diff_cos.comp h

theorem ContDiffAt.cos {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.cos (f x)) x :=
  Real.cont_diff_cos.ContDiffAt.comp x hf

theorem ContDiffOn.cos {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.cos (f x)) s :=
  Real.cont_diff_cos.comp_cont_diff_on hf

theorem ContDiffWithinAt.cos {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cos (f x)) s x :=
  Real.cont_diff_cos.ContDiffAt.comp_cont_diff_within_at x hf

/-! #### `real.sin` -/


theorem HasStrictFderivAt.sin (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.has_strict_deriv_at_sin (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.sin (hf : HasFderivAt f f' x) : HasFderivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.has_deriv_at_sin (f x)).comp_has_fderiv_at x hf

theorem HasFderivWithinAt.sin (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') s x :=
  (Real.has_deriv_at_sin (f x)).comp_has_fderiv_within_at x hf

theorem DifferentiableWithinAt.sin (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sin (f x)) s x :=
  hf.HasFderivWithinAt.sin.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.sin (hc : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun x => Real.sin (f x)) x :=
  hc.HasFderivAt.sin.DifferentiableAt

theorem DifferentiableOn.sin (hc : DifferentiableOn ℝ f s) : DifferentiableOn ℝ (fun x => Real.sin (f x)) s :=
  fun x h => (hc x h).sin

@[simp]
theorem Differentiable.sin (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sin (f x) := fun x => (hc x).sin

theorem fderiv_within_sin (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sin (f x)) s x = Real.cos (f x) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.sin.fderivWithin hxs

@[simp]
theorem fderiv_sin (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sin (f x)) x = Real.cos (f x) • fderiv ℝ f x :=
  hc.HasFderivAt.sin.fderiv

theorem ContDiff.sin {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sin (f x) :=
  Real.cont_diff_sin.comp h

theorem ContDiffAt.sin {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.sin (f x)) x :=
  Real.cont_diff_sin.ContDiffAt.comp x hf

theorem ContDiffOn.sin {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.sin (f x)) s :=
  Real.cont_diff_sin.comp_cont_diff_on hf

theorem ContDiffWithinAt.sin {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sin (f x)) s x :=
  Real.cont_diff_sin.ContDiffAt.comp_cont_diff_within_at x hf

/-! #### `real.cosh` -/


theorem HasStrictFderivAt.cosh (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.has_strict_deriv_at_cosh (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.cosh (hf : HasFderivAt f f' x) : HasFderivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.has_deriv_at_cosh (f x)).comp_has_fderiv_at x hf

theorem HasFderivWithinAt.cosh (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') s x :=
  (Real.has_deriv_at_cosh (f x)).comp_has_fderiv_within_at x hf

theorem DifferentiableWithinAt.cosh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cosh (f x)) s x :=
  hf.HasFderivWithinAt.cosh.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.cosh (hc : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun x => Real.cosh (f x)) x :=
  hc.HasFderivAt.cosh.DifferentiableAt

theorem DifferentiableOn.cosh (hc : DifferentiableOn ℝ f s) : DifferentiableOn ℝ (fun x => Real.cosh (f x)) s :=
  fun x h => (hc x h).cosh

@[simp]
theorem Differentiable.cosh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cosh (f x) := fun x =>
  (hc x).cosh

theorem fderiv_within_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cosh (f x)) s x = Real.sinh (f x) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.cosh.fderivWithin hxs

@[simp]
theorem fderiv_cosh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cosh (f x)) x = Real.sinh (f x) • fderiv ℝ f x :=
  hc.HasFderivAt.cosh.fderiv

theorem ContDiff.cosh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cosh (f x) :=
  Real.cont_diff_cosh.comp h

theorem ContDiffAt.cosh {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.cosh (f x)) x :=
  Real.cont_diff_cosh.ContDiffAt.comp x hf

theorem ContDiffOn.cosh {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.cosh (f x)) s :=
  Real.cont_diff_cosh.comp_cont_diff_on hf

theorem ContDiffWithinAt.cosh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cosh (f x)) s x :=
  Real.cont_diff_cosh.ContDiffAt.comp_cont_diff_within_at x hf

/-! #### `real.sinh` -/


theorem HasStrictFderivAt.sinh (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.has_strict_deriv_at_sinh (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.sinh (hf : HasFderivAt f f' x) : HasFderivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.has_deriv_at_sinh (f x)).comp_has_fderiv_at x hf

theorem HasFderivWithinAt.sinh (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') s x :=
  (Real.has_deriv_at_sinh (f x)).comp_has_fderiv_within_at x hf

theorem DifferentiableWithinAt.sinh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sinh (f x)) s x :=
  hf.HasFderivWithinAt.sinh.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.sinh (hc : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun x => Real.sinh (f x)) x :=
  hc.HasFderivAt.sinh.DifferentiableAt

theorem DifferentiableOn.sinh (hc : DifferentiableOn ℝ f s) : DifferentiableOn ℝ (fun x => Real.sinh (f x)) s :=
  fun x h => (hc x h).sinh

@[simp]
theorem Differentiable.sinh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sinh (f x) := fun x =>
  (hc x).sinh

theorem fderiv_within_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sinh (f x)) s x = Real.cosh (f x) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.sinh.fderivWithin hxs

@[simp]
theorem fderiv_sinh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sinh (f x)) x = Real.cosh (f x) • fderiv ℝ f x :=
  hc.HasFderivAt.sinh.fderiv

theorem ContDiff.sinh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sinh (f x) :=
  Real.cont_diff_sinh.comp h

theorem ContDiffAt.sinh {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.sinh (f x)) x :=
  Real.cont_diff_sinh.ContDiffAt.comp x hf

theorem ContDiffOn.sinh {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.sinh (f x)) s :=
  Real.cont_diff_sinh.comp_cont_diff_on hf

theorem ContDiffWithinAt.sinh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sinh (f x)) s x :=
  Real.cont_diff_sinh.ContDiffAt.comp_cont_diff_within_at x hf

end

