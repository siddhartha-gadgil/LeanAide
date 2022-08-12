/-
Copyright (c) 2022 Cuma Kökmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cuma Kökmen, Yury Kudryashov
-/
import Mathbin.MeasureTheory.Integral.CircleIntegral

/-!
# Integral over a torus in `ℂⁿ`

In this file we define the integral of a function `f : ℂⁿ → E` over a torus
`{z : ℂⁿ | ∀ i, z i ∈ metric.sphere (c i) (R i)}`. In order to do this, we define
`torus_map (c : ℂⁿ) (R θ : ℝⁿ)` to be the point in `ℂⁿ` given by $z_k=c_k+R_ke^{θ_ki}$,
where $i$ is the imaginary unit, then define `torus_integral f c R` as the integral over
the cube $[0, (λ _, 2π)] = \{θ\|∀ k, 0 ≤ θ_k ≤ 2π\}$ of the Jacobian of the
`torus_map` multiplied by `f (torus_map c R θ)`.

We also define a predicate saying that `f ∘ torus_map c R` is integrable on the cube
`[0, (λ _, 2\pi)]`.

## Main definitions

* `torus_map c R`: the generalized multidimensional exponential map from `ℝⁿ` to `ℂⁿ` that sends
  $θ=(θ_0,…,θ_{n-1})$ to $z=(z_0,…,z_{n-1})$, where $z_k= c_k + R_ke^{θ_k i}$;

* `torus_integrable f c R`: a function `f : ℂⁿ → E` is integrable over the generalized torus
  with center `c : ℂⁿ` and radius `R : ℝⁿ` if `f ∘ torus_map c R` is integrable on the
  closed cube `Icc (0 : ℝⁿ) (λ _, 2 * π)`;

* `torus_integral f c R`: the integral of a function `f : ℂⁿ → E` over a torus with
  center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ` defined as
  $\iiint_{[0, 2 * π]} (∏_{k = 1}^{n} i R_k e^{θ_k * i}) • f (c + Re^{θ_k i})\,dθ_0…dθ_{k-1}$.

## Main statements

* `torus_integral_dim0`, `torus_integral_dim1`, `torus_integral_succ`: formulas for `torus_integral`
  in cases of dimension `0`, `1`, and `n + 1`.

## Notations

- `ℝ⁰`, `ℝ¹`, `ℝⁿ`, `ℝⁿ⁺¹`: local notation for `fin 0 → ℝ`, `fin 1 → ℝ`, `fin n → ℝ`, and
  `fin (n + 1) → ℝ`, respectively;
- `ℂ⁰`, `ℂ¹`, `ℂⁿ`, `ℂⁿ⁺¹`: local notation for `fin 0 → ℂ`, `fin 1 → ℂ`, `fin n → ℂ`, and
  `fin (n + 1) → ℂ`, respectively;
- `∯ z in T(c, R), f z`: notation for `torus_integral f c R`;
- `∮ z in C(c, R), f z`: notation for `circle_integral f c R`, defined elsewhere;
- `∏ k, f k`: notation for `finset.prod`, defined elsewhere;
- `π`: notation for `real.pi`, defined elsewhere.

## Tags

integral, torus
-/


variable {n : ℕ}

variable {E : Type _} [NormedGroup E]

noncomputable section

open Complex Set MeasureTheory Function Filter TopologicalSpace

open Real BigOperators

-- mathport name: «exprℝ⁰»
local notation "ℝ⁰" => Finₓ 0 → ℝ

-- mathport name: «exprℂ⁰»
local notation "ℂ⁰" => Finₓ 0 → ℂ

-- mathport name: «exprℝ¹»
local notation "ℝ¹" => Finₓ 1 → ℝ

-- mathport name: «exprℂ¹»
local notation "ℂ¹" => Finₓ 1 → ℂ

-- mathport name: «exprℝⁿ»
local notation "ℝⁿ" => Finₓ n → ℝ

-- mathport name: «exprℂⁿ»
local notation "ℂⁿ" => Finₓ n → ℂ

-- mathport name: «exprℝⁿ⁺¹»
local notation "ℝⁿ⁺¹" => Finₓ (n + 1) → ℝ

-- mathport name: «exprℂⁿ⁺¹»
local notation "ℂⁿ⁺¹" => Finₓ (n + 1) → ℂ

/-!
### `torus_map`, a generalization of a torus
-/


/-- The n dimensional exponential map $θ_i ↦ c + R e^{θ_i*I}, θ ∈ ℝⁿ$ representing
a torus in `ℂⁿ` with center `c ∈ ℂⁿ` and generalized radius `R ∈ ℝⁿ`, so we can adjust
it to every n axis. -/
def torusMap (c : ℂⁿ) (R : ℝⁿ) : ℝⁿ → ℂⁿ := fun θ i => c i + R i * exp (θ i * I)

theorem torus_map_sub_center (c : ℂⁿ) (R : ℝⁿ) (θ : ℝⁿ) : torusMap c R θ - c = torusMap 0 R θ := by
  ext1 i
  simp [← torusMap]

theorem torus_map_eq_center_iff {c : ℂⁿ} {R : ℝⁿ} {θ : ℝⁿ} : torusMap c R θ = c ↔ R = 0 := by
  simp [← funext_iff, ← torusMap, ← exp_ne_zero]

@[simp]
theorem torus_map_zero_radius (c : ℂⁿ) : torusMap c 0 = const ℝⁿ c := by
  ext1
  rw [torus_map_eq_center_iff.2 rfl]

/-!
### Integrability of a function on a generalized torus
-/


/-- A function `f : ℂⁿ → E` is integrable on the generalized torus if the function
`f ∘ torus_map c R θ` is integrable on `Icc (0 : ℝⁿ) (λ _, 2 * π)`-/
def TorusIntegrable (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) : Prop :=
  IntegrableOn (fun θ : ℝⁿ => f (torusMap c R θ)) (Icc (0 : ℝⁿ) fun _ => 2 * π) volume

namespace TorusIntegrable

variable {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

/-- Constant functions are torus integrable -/
theorem torus_integrable_const (a : E) (c : ℂⁿ) (R : ℝⁿ) : TorusIntegrable (fun _ => a) c R := by
  simp [← TorusIntegrable, ← measure_Icc_lt_top]

/-- If `f` is torus integrable then `-f` is torus integrable. -/
protected theorem neg (hf : TorusIntegrable f c R) : TorusIntegrable (-f) c R :=
  hf.neg

/-- If `f` and `g` are two torus integrable functions, then so is `f + g`. -/
protected theorem add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) : TorusIntegrable (f + g) c R :=
  hf.add hg

/-- If `f` and `g` are two torus integrable functions, then so is `f - g`. -/
protected theorem sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) : TorusIntegrable (f - g) c R :=
  hf.sub hg

theorem torus_integrable_zero_radius {f : ℂⁿ → E} {c : ℂⁿ} : TorusIntegrable f c 0 := by
  rw [TorusIntegrable, torus_map_zero_radius]
  apply torus_integrable_const (f c) c 0

/-- The function given in the definition of `torus_integral` is integrable. -/
theorem function_integrable [NormedSpace ℂ E] (hf : TorusIntegrable f c R) :
    IntegrableOn (fun θ : ℝⁿ => (∏ i, R i * exp (θ i * I) * I : ℂ) • f (torusMap c R θ)) (Icc (0 : ℝⁿ) fun _ => 2 * π)
      volume :=
  by
  refine' (hf.norm.const_mul (∏ i, abs (R i))).mono' _ _
  · refine' (Continuous.ae_strongly_measurable _).smul hf.1
    exact
      continuous_finset_prod Finset.univ fun i hi =>
        (continuous_const.mul ((continuous_of_real.comp (continuous_apply i)).mul continuous_const).cexp).mul
          continuous_const
    
  simp [← norm_smul, ← map_prod]

end TorusIntegrable

variable [NormedSpace ℂ E] [CompleteSpace E] {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

/-- The definition of the integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`
as the `•`-product of the derivative of `torus_map` and `f (torus_map c R θ)`-/
def torusIntegral (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :=
  ∫ θ : ℝⁿ in Icc (0 : ℝⁿ) fun _ => 2 * π, (∏ i, R i * exp (θ i * I) * I : ℂ) • f (torusMap c R θ)

-- mathport name: «expr∯ inT( , ), »
notation3"∯ "(...)" in ""T("c", "R")"", "r:(scoped f => torusIntegral f c R) => r

theorem torus_integral_radius_zero (hn : n ≠ 0) (f : ℂⁿ → E) (c : ℂⁿ) : (∯ x in T(c, 0), f x) = 0 := by
  simp only [← torusIntegral, ← Pi.zero_apply, ← of_real_zero, ← mul_zero, ← zero_mul, ← Finₓ.prod_const, ←
    zero_pow' n hn, ← zero_smul, ← integral_zero]

theorem torus_integral_neg (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) : (∯ x in T(c, R), -f x) = -∯ x in T(c, R), f x := by
  simp [← torusIntegral, ← integral_neg]

theorem torus_integral_add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    (∯ x in T(c, R), f x + g x) = (∯ x in T(c, R), f x) + ∯ x in T(c, R), g x := by
  simpa only [← torusIntegral, ← smul_add, ← Pi.add_apply] using
    integral_add hf.function_integrable hg.function_integrable

theorem torus_integral_sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    (∯ x in T(c, R), f x - g x) = (∯ x in T(c, R), f x) - ∯ x in T(c, R), g x := by
  simpa only [← sub_eq_add_neg, torus_integral_neg] using torus_integral_add hf hg.neg

theorem torus_integral_smul {𝕜 : Type _} [IsROrC 𝕜] [NormedSpace 𝕜 E] [SmulCommClass 𝕜 ℂ E] (a : 𝕜) (f : ℂⁿ → E)
    (c : ℂⁿ) (R : ℝⁿ) : (∯ x in T(c, R), a • f x) = a • ∯ x in T(c, R), f x := by
  simp only [← torusIntegral, ← integral_smul, smul_comm a]

theorem torus_integral_const_mul (a : ℂ) (f : ℂⁿ → ℂ) (c : ℂⁿ) (R : ℝⁿ) :
    (∯ x in T(c, R), a * f x) = a * ∯ x in T(c, R), f x :=
  torus_integral_smul a f c R

/-- If for all `θ : ℝⁿ`, `∥f (torus_map c R θ)∥` is less than or equal to a constant `C : ℝ`, then
`∥∯ x in T(c, R), f x∥` is less than or equal to `(2 * π)^n * (∏ i, |R i|) * C`-/
theorem norm_torus_integral_le_of_norm_le_const {C : ℝ} (hf : ∀ θ, ∥f (torusMap c R θ)∥ ≤ C) :
    ∥∯ x in T(c, R), f x∥ ≤ ((2 * π) ^ (n : ℕ) * ∏ i, abs (R i)) * C :=
  calc
    ∥∯ x in T(c, R), f x∥ ≤ (∏ i, abs (R i)) * C * (volume (Icc (0 : ℝⁿ) fun _ => 2 * π)).toReal :=
      (norm_set_integral_le_of_norm_le_const' measure_Icc_lt_top measurable_set_Icc) fun θ hθ =>
        calc
          ∥(∏ i : Finₓ n, R i * exp (θ i * I) * I : ℂ) • f (torusMap c R θ)∥ =
              (∏ i : Finₓ n, abs (R i)) * ∥f (torusMap c R θ)∥ :=
            by
            simp [← norm_smul]
          _ ≤ (∏ i : Finₓ n, abs (R i)) * C :=
            mul_le_mul_of_nonneg_left (hf _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
          
    _ = ((2 * π) ^ (n : ℕ) * ∏ i, abs (R i)) * C := by
      simp only [← Pi.zero_def, ← Real.volume_Icc_pi_to_real fun _ => real.two_pi_pos.le, ← sub_zero, ← Finₓ.prod_const,
        ← mul_assoc, ← mul_comm ((2 * π) ^ (n : ℕ))]
    

@[simp]
theorem torus_integral_dim0 (f : ℂ⁰ → E) (c : ℂ⁰) (R : ℝ⁰) : (∯ x in T(c, R), f x) = f c := by
  simp only [← torusIntegral, ← Finₓ.prod_univ_zero, ← one_smul, ← Subsingleton.elimₓ (fun i : Finₓ 0 => 2 * π) 0, ←
    Icc_self, ← measure.restrict_singleton, ← volume_pi, ← integral_smul_measure, ← integral_dirac, ←
    measure.pi_of_empty _ 0, ← measure.dirac_apply_of_mem (mem_singleton _), ← Subsingleton.elimₓ (torusMap c R 0) c]

/-- In dimension one, `torus_integral` is the same as `circle_integral`
(up to the natural equivalence between `ℂ` and `fin 1 → ℂ`). -/
theorem torus_integral_dim1 (f : ℂ¹ → E) (c : ℂ¹) (R : ℝ¹) : (∯ x in T(c, R), f x) = ∮ z in C(c 0, R 0), f fun _ => z :=
  by
  have : ((fun (x : ℝ) (b : Finₓ 1) => x) ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) :=
    (OrderIso.funUnique (Finₓ 1) ℝ).symm.preimage_Icc _ _
  simp only [← torusIntegral, ← circleIntegral, ← intervalIntegral.integral_of_le real.two_pi_pos.le, ←
    measure.restrict_congr_set Ioc_ae_eq_Icc, ← deriv_circle_map, ← Finₓ.prod_univ_one,
    ((volume_preserving_fun_unique (Finₓ 1) ℝ).symm _).set_integral_preimage_emb
      (MeasurableEquiv.measurable_embedding _),
    ← this, ← MeasurableEquiv.fun_unique_symm_apply]
  simp only [← torusMap, ← circleMap, ← zero_addₓ]
  rcongr

/-- Recurrent formula for `torus_integral`, see also `torus_integral_succ`. -/
theorem torus_integral_succ_above {f : ℂⁿ⁺¹ → E} {c : ℂⁿ⁺¹} {R : ℝⁿ⁺¹} (hf : TorusIntegrable f c R) (i : Finₓ (n + 1)) :
    (∯ x in T(c, R), f x) = ∮ x in C(c i, R i), ∯ y in T(c ∘ i.succAbove, R ∘ i.succAbove), f (i.insertNth x y) := by
  set e : ℝ × ℝⁿ ≃ᵐ ℝⁿ⁺¹ := (MeasurableEquiv.piFinSuccAboveEquiv (fun _ => ℝ) i).symm
  have hem : measure_preserving e := (volume_preserving_pi_fin_succ_above_equiv (fun j : Finₓ (n + 1) => ℝ) i).symm _
  have heπ : (e ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) ×ˢ Icc (0 : ℝⁿ) fun _ => 2 * π :=
    ((OrderIso.piFinSuccAboveIso (fun _ => ℝ) i).symm.preimage_Icc _ _).trans (Icc_prod_eq _ _)
  rw [torusIntegral, ← hem.map_eq, set_integral_map_equiv, heπ, measure.volume_eq_prod, set_integral_prod,
    circle_integral_def_Icc]
  · refine' set_integral_congr measurable_set_Icc fun θ hθ => _
    simp only [← torusIntegral, integral_smul, ← deriv_circle_map, ← i.prod_univ_succ_above _, ← smul_smul, ← torusMap,
      ← circle_map_zero]
    refine' set_integral_congr measurable_set_Icc fun Θ hΘ => _
    simp only [← MeasurableEquiv.pi_fin_succ_above_equiv_symm_apply, ← i.insert_nth_apply_same, ←
      i.insert_nth_apply_succ_above, ← (· ∘ ·)]
    congr 2
    simp only [← funext_iff, ← i.forall_iff_succ_above, ← circleMap, ← Finₓ.insert_nth_apply_same, ← eq_self_iff_true, ←
      Finₓ.insert_nth_apply_succ_above, ← implies_true_iff, ← and_selfₓ]
    
  · have := hf.function_integrable
    rwa [← hem.integrable_on_comp_preimage e.measurable_embedding, heπ] at this
    

/-- Recurrent formula for `torus_integral`, see also `torus_integral_succ_above`. -/
theorem torus_integral_succ {f : ℂⁿ⁺¹ → E} {c : ℂⁿ⁺¹} {R : ℝⁿ⁺¹} (hf : TorusIntegrable f c R) :
    (∯ x in T(c, R), f x) = ∮ x in C(c 0, R 0), ∯ y in T(c ∘ Finₓ.succ, R ∘ Finₓ.succ), f (Finₓ.cons x y) := by
  simpa using torus_integral_succ_above hf 0

