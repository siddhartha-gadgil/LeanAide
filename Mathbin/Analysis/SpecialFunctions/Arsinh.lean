/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Chris Hughes, Shing Tak Lam
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathbin.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the sinh function

In this file we prove that sinh is bijective and hence has an
inverse, arsinh.

## Main definitions

- `real.arsinh`: The inverse function of `real.sinh`.

- `real.sinh_equiv`, `real.sinh_order_iso`, `real.sinh_homeomorph`: `real.sinh` as an `equiv`,
  `order_iso`, and `homeomorph`, respectively.

## Main Results

- `real.sinh_surjective`, `real.sinh_bijective`: `real.sinh` is surjective and bijective;

- `real.arsinh_injective`, `real.arsinh_surjective`, `real.arsinh_bijective`: `real.arsinh` is
  injective, surjective, and bijective;

- `real.continuous_arsinh`, `real.differentiable_arsinh`, `real.cont_diff_arsinh`: `real.arsinh` is
  continuous, differentiable, and continuously differentiable; we also provide dot notation
  convenience lemmas like `filter.tendsto.arsinh` and `cont_diff_at.arsinh`.

## Tags

arsinh, arcsinh, argsinh, asinh, sinh injective, sinh bijective, sinh surjective
-/


noncomputable section

open Function Filter Set

open TopologicalSpace

namespace Real

variable {x y : ℝ}

/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + sqrt(1 + x^2))`. -/
@[pp_nodot]
def arsinh (x : ℝ) :=
  log (x + sqrt (1 + x ^ 2))

theorem exp_arsinh (x : ℝ) : exp (arsinh x) = x + sqrt (1 + x ^ 2) := by
  apply exp_log
  rw [← neg_lt_iff_pos_add']
  calc -x ≤ sqrt (x ^ 2) := le_sqrt_of_sq_le (neg_pow_bit0 _ _).le _ < sqrt (1 + x ^ 2) :=
      sqrt_lt_sqrt (sq_nonneg _) (lt_one_add _)

@[simp]
theorem arsinh_zero : arsinh 0 = 0 := by
  simp [← arsinh]

@[simp]
theorem arsinh_neg (x : ℝ) : arsinh (-x) = -arsinh x := by
  rw [← exp_eq_exp, exp_arsinh, exp_neg, exp_arsinh]
  apply eq_inv_of_mul_eq_one_left
  rw [neg_sq, neg_add_eq_sub, add_commₓ x, mul_comm, ← sq_sub_sq, sq_sqrt, add_sub_cancel]
  exact add_nonneg zero_le_one (sq_nonneg _)

/-- `arsinh` is the right inverse of `sinh`. -/
@[simp]
theorem sinh_arsinh (x : ℝ) : sinh (arsinh x) = x := by
  rw [sinh_eq, ← arsinh_neg, exp_arsinh, exp_arsinh, neg_sq]
  field_simp

@[simp]
theorem cosh_arsinh (x : ℝ) : cosh (arsinh x) = sqrt (1 + x ^ 2) := by
  rw [← sqrt_sq (cosh_pos _).le, cosh_sq', sinh_arsinh]

/-- `sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b`. -/
theorem sinh_surjective : Surjective sinh :=
  LeftInverse.surjectiveₓ sinh_arsinh

/-- `sinh` is bijective, both injective and surjective. -/
theorem sinh_bijective : Bijective sinh :=
  ⟨sinh_injective, sinh_surjective⟩

/-- `arsinh` is the left inverse of `sinh`. -/
@[simp]
theorem arsinh_sinh (x : ℝ) : arsinh (sinh x) = x :=
  right_inverse_of_injective_of_left_inverse sinh_injective sinh_arsinh x

/-- `real.sinh` as an `equiv`. -/
@[simps]
def sinhEquiv : ℝ ≃ ℝ where
  toFun := sinh
  invFun := arsinh
  left_inv := arsinh_sinh
  right_inv := sinh_arsinh

/-- `real.sinh` as an `order_iso`. -/
@[simps (config := { fullyApplied := false })]
def sinhOrderIso : ℝ ≃o ℝ where
  toEquiv := sinhEquiv
  map_rel_iff' := @sinh_le_sinh

/-- `real.sinh` as a `homeomorph`. -/
@[simps (config := { fullyApplied := false })]
def sinhHomeomorph : ℝ ≃ₜ ℝ :=
  sinhOrderIso.toHomeomorph

theorem arsinh_bijective : Bijective arsinh :=
  sinhEquiv.symm.Bijective

theorem arsinh_injective : Injective arsinh :=
  sinhEquiv.symm.Injective

theorem arsinh_surjective : Surjective arsinh :=
  sinhEquiv.symm.Surjective

theorem arsinh_strict_mono : StrictMono arsinh :=
  sinhOrderIso.symm.StrictMono

@[simp]
theorem arsinh_inj : arsinh x = arsinh y ↔ x = y :=
  arsinh_injective.eq_iff

@[simp]
theorem arsinh_le_arsinh : arsinh x ≤ arsinh y ↔ x ≤ y :=
  sinhOrderIso.symm.le_iff_le

@[simp]
theorem arsinh_lt_arsinh : arsinh x < arsinh y ↔ x < y :=
  sinhOrderIso.symm.lt_iff_lt

@[simp]
theorem arsinh_eq_zero_iff : arsinh x = 0 ↔ x = 0 :=
  arsinh_injective.eq_iff' arsinh_zero

@[simp]
theorem arsinh_nonneg_iff : 0 ≤ arsinh x ↔ 0 ≤ x := by
  rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]
theorem arsinh_nonpos_iff : arsinh x ≤ 0 ↔ x ≤ 0 := by
  rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]
theorem arsinh_pos_iff : 0 < arsinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arsinh_nonpos_iff

@[simp]
theorem arsinh_neg_iff : arsinh x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arsinh_nonneg_iff

theorem has_strict_deriv_at_arsinh (x : ℝ) : HasStrictDerivAt arsinh (sqrt (1 + x ^ 2))⁻¹ x := by
  convert
    sinh_homeomorph.to_local_homeomorph.has_strict_deriv_at_symm (mem_univ x) (cosh_pos _).ne'
      (has_strict_deriv_at_sinh _)
  exact (cosh_arsinh _).symm

theorem has_deriv_at_arsinh (x : ℝ) : HasDerivAt arsinh (sqrt (1 + x ^ 2))⁻¹ x :=
  (has_strict_deriv_at_arsinh x).HasDerivAt

theorem differentiable_arsinh : Differentiable ℝ arsinh := fun x => (has_deriv_at_arsinh x).DifferentiableAt

theorem cont_diff_arsinh {n : WithTop ℕ} : ContDiff ℝ n arsinh :=
  sinhHomeomorph.cont_diff_symm_deriv (fun x => (cosh_pos x).ne') has_deriv_at_sinh cont_diff_sinh

@[continuity]
theorem continuous_arsinh : Continuous arsinh :=
  sinhHomeomorph.symm.Continuous

end Real

open Real

theorem Filter.Tendsto.arsinh {α : Type _} {l : Filter α} {f : α → ℝ} {a : ℝ} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => arsinh (f x)) l (𝓝 (arsinh a)) :=
  (continuous_arsinh.Tendsto _).comp h

section Continuous

variable {X : Type _} [TopologicalSpace X] {f : X → ℝ} {s : Set X} {a : X}

theorem ContinuousAt.arsinh (h : ContinuousAt f a) : ContinuousAt (fun x => arsinh (f x)) a :=
  h.arsinh

theorem ContinuousWithinAt.arsinh (h : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x => arsinh (f x)) s a :=
  h.arsinh

theorem ContinuousOn.arsinh (h : ContinuousOn f s) : ContinuousOn (fun x => arsinh (f x)) s := fun x hx =>
  (h x hx).arsinh

theorem Continuous.arsinh (h : Continuous f) : Continuous fun x => arsinh (f x) :=
  continuous_arsinh.comp h

end Continuous

section fderiv

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {f : E → ℝ} {s : Set E} {a : E} {f' : E →L[ℝ] ℝ} {n : WithTop ℕ}

theorem HasStrictFderivAt.arsinh (hf : HasStrictFderivAt f f' a) :
    HasStrictFderivAt (fun x => arsinh (f x)) ((sqrt (1 + f a ^ 2))⁻¹ • f') a :=
  (has_strict_deriv_at_arsinh _).comp_has_strict_fderiv_at a hf

theorem HasFderivAt.arsinh (hf : HasFderivAt f f' a) :
    HasFderivAt (fun x => arsinh (f x)) ((sqrt (1 + f a ^ 2))⁻¹ • f') a :=
  (has_deriv_at_arsinh _).comp_has_fderiv_at a hf

theorem HasFderivWithinAt.arsinh (hf : HasFderivWithinAt f f' s a) :
    HasFderivWithinAt (fun x => arsinh (f x)) ((sqrt (1 + f a ^ 2))⁻¹ • f') s a :=
  (has_deriv_at_arsinh _).comp_has_fderiv_within_at a hf

theorem DifferentiableAt.arsinh (h : DifferentiableAt ℝ f a) : DifferentiableAt ℝ (fun x => arsinh (f x)) a :=
  (differentiable_arsinh _).comp a h

theorem DifferentiableWithinAt.arsinh (h : DifferentiableWithinAt ℝ f s a) :
    DifferentiableWithinAt ℝ (fun x => arsinh (f x)) s a :=
  (differentiable_arsinh _).comp_differentiable_within_at a h

theorem DifferentiableOn.arsinh (h : DifferentiableOn ℝ f s) : DifferentiableOn ℝ (fun x => arsinh (f x)) s :=
  fun x hx => (h x hx).arsinh

theorem Differentiable.arsinh (h : Differentiable ℝ f) : Differentiable ℝ fun x => arsinh (f x) :=
  differentiable_arsinh.comp h

theorem ContDiffAt.arsinh (h : ContDiffAt ℝ n f a) : ContDiffAt ℝ n (fun x => arsinh (f x)) a :=
  cont_diff_arsinh.ContDiffAt.comp a h

theorem ContDiffWithinAt.arsinh (h : ContDiffWithinAt ℝ n f s a) : ContDiffWithinAt ℝ n (fun x => arsinh (f x)) s a :=
  cont_diff_arsinh.ContDiffAt.comp_cont_diff_within_at a h

theorem ContDiff.arsinh (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => arsinh (f x) :=
  cont_diff_arsinh.comp h

theorem ContDiffOn.arsinh (h : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => arsinh (f x)) s := fun x hx =>
  (h x hx).arsinh

end fderiv

section deriv

variable {f : ℝ → ℝ} {s : Set ℝ} {a f' : ℝ}

theorem HasStrictDerivAt.arsinh (hf : HasStrictDerivAt f f' a) :
    HasStrictDerivAt (fun x => arsinh (f x)) ((sqrt (1 + f a ^ 2))⁻¹ • f') a :=
  (has_strict_deriv_at_arsinh _).comp a hf

theorem HasDerivAt.arsinh (hf : HasDerivAt f f' a) :
    HasDerivAt (fun x => arsinh (f x)) ((sqrt (1 + f a ^ 2))⁻¹ • f') a :=
  (has_deriv_at_arsinh _).comp a hf

theorem HasDerivWithinAt.arsinh (hf : HasDerivWithinAt f f' s a) :
    HasDerivWithinAt (fun x => arsinh (f x)) ((sqrt (1 + f a ^ 2))⁻¹ • f') s a :=
  (has_deriv_at_arsinh _).comp_has_deriv_within_at a hf

end deriv

