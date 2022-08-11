/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import Mathbin.Analysis.Convex.SpecificFunctions
import Mathbin.Data.Real.ConjugateExponents

/-!
# Mean value inequalities

In this file we prove several inequalities for finite sums, including AM-GM inequality,
Young's inequality, Hölder inequality, and Minkowski inequality. Versions for integrals of some of
these inequalities are available in `measure_theory.mean_inequalities`.

## Main theorems

### AM-GM inequality:

The inequality says that the geometric mean of a tuple of non-negative numbers is less than or equal
to their arithmetic mean. We prove the weighted version of this inequality: if $w$ and $z$
are two non-negative vectors and $\sum_{i\in s} w_i=1$, then
$$
\prod_{i\in s} z_i^{w_i} ≤ \sum_{i\in s} w_iz_i.
$$
The classical version is a special case of this inequality for $w_i=\frac{1}{n}$.

We prove a few versions of this inequality. Each of the following lemmas comes in two versions:
a version for real-valued non-negative functions is in the `real` namespace, and a version for
`nnreal`-valued functions is in the `nnreal` namespace.

- `geom_mean_le_arith_mean_weighted` : weighted version for functions on `finset`s;
- `geom_mean_le_arith_mean2_weighted` : weighted version for two numbers;
- `geom_mean_le_arith_mean3_weighted` : weighted version for three numbers;
- `geom_mean_le_arith_mean4_weighted` : weighted version for four numbers.

### Young's inequality

Young's inequality says that for non-negative numbers `a`, `b`, `p`, `q` such that
$\frac{1}{p}+\frac{1}{q}=1$ we have
$$
ab ≤ \frac{a^p}{p} + \frac{b^q}{q}.
$$

This inequality is a special case of the AM-GM inequality. It is then used to prove Hölder's
inequality (see below).

### Hölder's inequality

The inequality says that for two conjugate exponents `p` and `q` (i.e., for two positive numbers
such that $\frac{1}{p}+\frac{1}{q}=1$) and any two non-negative vectors their inner product is
less than or equal to the product of the $L_p$ norm of the first vector and the $L_q$ norm of the
second vector:
$$
\sum_{i\in s} a_ib_i ≤ \sqrt[p]{\sum_{i\in s} a_i^p}\sqrt[q]{\sum_{i\in s} b_i^q}.
$$

We give versions of this result in `ℝ`, `ℝ≥0` and `ℝ≥0∞`.

There are at least two short proofs of this inequality. In our proof we prenormalize both vectors,
then apply Young's inequality to each $a_ib_i$. Another possible proof would be to deduce this
inequality from the generalized mean inequality for well-chosen vectors and weights.

### Minkowski's inequality

The inequality says that for `p ≥ 1` the function
$$
\|a\|_p=\sqrt[p]{\sum_{i\in s} a_i^p}
$$
satisfies the triangle inequality $\|a+b\|_p\le \|a\|_p+\|b\|_p$.

We give versions of this result in `real`, `ℝ≥0` and `ℝ≥0∞`.

We deduce this inequality from Hölder's inequality. Namely, Hölder inequality implies that $\|a\|_p$
is the maximum of the inner product $\sum_{i\in s}a_ib_i$ over `b` such that $\|b\|_q\le 1$. Now
Minkowski's inequality follows from the fact that the maximum value of the sum of two functions is
less than or equal to the sum of the maximum values of the summands.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `strict_convex_on` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/


universe u v

open Finset

open Classical BigOperators Nnreal Ennreal

noncomputable section

variable {ι : Type u} (s : Finset ι)

section GeomMeanLeArithMean

/-! ### AM-GM inequality -/


namespace Real

/-- AM-GM inequality: the **geometric mean is less than or equal to the arithmetic mean**, weighted
version for real-valued nonnegative functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ) (hw : ∀, ∀ i ∈ s, ∀, 0 ≤ w i) (hw' : (∑ i in s, w i) = 1)
    (hz : ∀, ∀ i ∈ s, ∀, 0 ≤ z i) : (∏ i in s, z i ^ w i) ≤ ∑ i in s, w i * z i := by
  -- If some number `z i` equals zero and has non-zero weight, then LHS is 0 and RHS is nonnegative.
  by_cases' A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · exact sum_nonneg fun j hj => mul_nonneg (hw j hj) (hz j hj)
      
    · rw [hzi]
      exact zero_rpow hwi
      
    
  -- If all numbers `z i` with non-zero weight are positive, then we apply Jensen's inequality
  -- for `exp` and numbers `log (z i)` with weights `w i`.
  · simp only [← not_exists, ← not_and, ← Ne.def, ← not_not] at A
    have := convex_on_exp.map_sum_le hw hw' fun i _ => Set.mem_univ <| log (z i)
    simp only [← exp_sum, ← (· ∘ ·), ← smul_eq_mul, ← mul_comm (w _) (log _)] at this
    convert this using 1 <;> [apply prod_congr rfl, apply sum_congr rfl] <;> intro i hi
    · cases' eq_or_lt_of_le (hz i hi) with hz hz
      · simp [← A i hi hz.symm]
        
      · exact rpow_def_of_pos hz _
        
      
    · cases' eq_or_lt_of_le (hz i hi) with hz hz
      · simp [← A i hi hz.symm]
        
      · rw [exp_log hz]
        
      
    

theorem geom_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw : ∀, ∀ i ∈ s, ∀, 0 ≤ w i) (hw' : (∑ i in s, w i) = 1)
    (hz : ∀, ∀ i ∈ s, ∀, 0 ≤ z i) (hx : ∀, ∀ i ∈ s, ∀, w i ≠ 0 → z i = x) : (∏ i in s, z i ^ w i) = x :=
  calc
    (∏ i in s, z i ^ w i) = ∏ i in s, x ^ w i := by
      refine' prod_congr rfl fun i hi => _
      cases' eq_or_ne (w i) 0 with h₀ h₀
      · rw [h₀, rpow_zero, rpow_zero]
        
      · rw [hx i hi h₀]
        
    _ = x := by
      rw [← rpow_sum_of_nonneg _ hw, hw', rpow_one]
      have : (∑ i in s, w i) ≠ 0 := by
        rw [hw']
        exact one_ne_zero
      obtain ⟨i, his, hi⟩ := exists_ne_zero_of_sum_ne_zero this
      rw [← hx i his hi]
      exact hz i his
    

theorem arith_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw' : (∑ i in s, w i) = 1)
    (hx : ∀, ∀ i ∈ s, ∀, w i ≠ 0 → z i = x) : (∑ i in s, w i * z i) = x :=
  calc
    (∑ i in s, w i * z i) = ∑ i in s, w i * x := by
      refine' sum_congr rfl fun i hi => _
      cases' eq_or_ne (w i) 0 with hwi hwi
      · rw [hwi, zero_mul, zero_mul]
        
      · rw [hx i hi hwi]
        
    _ = x := by
      rw [← sum_mul, hw', one_mulₓ]
    

theorem geom_mean_eq_arith_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw : ∀, ∀ i ∈ s, ∀, 0 ≤ w i)
    (hw' : (∑ i in s, w i) = 1) (hz : ∀, ∀ i ∈ s, ∀, 0 ≤ z i) (hx : ∀, ∀ i ∈ s, ∀, w i ≠ 0 → z i = x) :
    (∏ i in s, z i ^ w i) = ∑ i in s, w i * z i := by
  rw [geom_mean_weighted_of_constant, arith_mean_weighted_of_constant] <;> assumption

end Real

namespace Nnreal

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for `nnreal`-valued functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ≥0 ) (hw' : (∑ i in s, w i) = 1) :
    (∏ i in s, z i ^ (w i : ℝ)) ≤ ∑ i in s, w i * z i := by
  exact_mod_cast
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => (w i).coe_nonneg)
      (by
        assumption_mod_cast)
      fun i _ => (z i).coe_nonneg

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for two `nnreal` numbers. -/
theorem geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0 ) :
    w₁ + w₂ = 1 → p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ := by
  simpa only [← Finₓ.prod_univ_succ, ← Finₓ.sum_univ_succ, ← Finset.prod_empty, ← Finset.sum_empty, ←
    Fintype.univ_of_is_empty, ← Finₓ.cons_succ, ← Finₓ.cons_zero, ← add_zeroₓ, ← mul_oneₓ] using
    geom_mean_le_arith_mean_weighted univ ![w₁, w₂] ![p₁, p₂]

theorem geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0 ) :
    w₁ + w₂ + w₃ = 1 → p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ := by
  simpa only [← Finₓ.prod_univ_succ, ← Finₓ.sum_univ_succ, ← Finset.prod_empty, ← Finset.sum_empty, ←
    Fintype.univ_of_is_empty, ← Finₓ.cons_succ, ← Finₓ.cons_zero, ← add_zeroₓ, ← mul_oneₓ, add_assocₓ, ←
    mul_assoc] using geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃] ![p₁, p₂, p₃]

theorem geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ≥0 ) :
    w₁ + w₂ + w₃ + w₄ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) * p₄ ^ (w₄ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
  by
  simpa only [← Finₓ.prod_univ_succ, ← Finₓ.sum_univ_succ, ← Finset.prod_empty, ← Finset.sum_empty, ←
    Fintype.univ_of_is_empty, ← Finₓ.cons_succ, ← Finₓ.cons_zero, ← add_zeroₓ, ← mul_oneₓ, add_assocₓ, ←
    mul_assoc] using geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃, w₄] ![p₁, p₂, p₃, p₄]

end Nnreal

namespace Real

theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    (hw : w₁ + w₂ = 1) : p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
  Nnreal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ <|
    Nnreal.coe_eq.1 <| by
      assumption

theorem geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hw : w₁ + w₂ + w₃ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
  Nnreal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ <|
    Nnreal.coe_eq.1 hw

theorem geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hw₄ : 0 ≤ w₄) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hp₄ : 0 ≤ p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
  Nnreal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩
      ⟨p₄, hp₄⟩ <|
    Nnreal.coe_eq.1 <| by
      assumption

end Real

end GeomMeanLeArithMean

section Young

/-! ### Young's inequality -/


namespace Real

/-- Young's inequality, a version for nonnegative real numbers. -/
theorem young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hpq : p.IsConjugateExponent q) :
    a * b ≤ a ^ p / p + b ^ q / q := by
  simpa [rpow_mul, ← ha, ← hb, ← hpq.ne_zero, ← hpq.symm.ne_zero, ← div_eq_inv_mul] using
    geom_mean_le_arith_mean2_weighted hpq.one_div_nonneg hpq.symm.one_div_nonneg (rpow_nonneg_of_nonneg ha p)
      (rpow_nonneg_of_nonneg hb q) hpq.inv_add_inv_conj

/-- Young's inequality, a version for arbitrary real numbers. -/
theorem young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.IsConjugateExponent q) : a * b ≤ abs a ^ p / p + abs b ^ q / q :=
  calc
    a * b ≤ abs (a * b) := le_abs_self (a * b)
    _ = abs a * abs b := abs_mul a b
    _ ≤ abs a ^ p / p + abs b ^ q / q := Real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq
    

end Real

namespace Nnreal

/-- Young's inequality, `ℝ≥0` version. We use `{p q : ℝ≥0}` in order to avoid constructing
witnesses of `0 ≤ p` and `0 ≤ q` for the denominators.  -/
theorem young_inequality (a b : ℝ≥0 ) {p q : ℝ≥0 } (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    a * b ≤ a ^ (p : ℝ) / p + b ^ (q : ℝ) / q :=
  Real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg ⟨hp, Nnreal.coe_eq.2 hpq⟩

/-- Young's inequality, `ℝ≥0` version with real conjugate exponents. -/
theorem young_inequality_real (a b : ℝ≥0 ) {p q : ℝ} (hpq : p.IsConjugateExponent q) :
    a * b ≤ a ^ p / Real.toNnreal p + b ^ q / Real.toNnreal q := by
  nth_rw 0[← Real.coe_to_nnreal p hpq.nonneg]
  nth_rw 0[← Real.coe_to_nnreal q hpq.symm.nonneg]
  exact young_inequality a b hpq.one_lt_nnreal hpq.inv_add_inv_conj_nnreal

end Nnreal

namespace Ennreal

/-- Young's inequality, `ℝ≥0∞` version with real conjugate exponents. -/
theorem young_inequality (a b : ℝ≥0∞) {p q : ℝ} (hpq : p.IsConjugateExponent q) :
    a * b ≤ a ^ p / Ennreal.ofReal p + b ^ q / Ennreal.ofReal q := by
  by_cases' h : a = ⊤ ∨ b = ⊤
  · refine' le_transₓ le_top (le_of_eqₓ _)
    repeat'
      rw [div_eq_mul_inv]
    cases h <;> rw [h] <;> simp [← h, ← hpq.pos, ← hpq.symm.pos]
    
  push_neg  at h
  -- if a ≠ ⊤ and b ≠ ⊤, use the nnreal version: nnreal.young_inequality_real
  rw [← coe_to_nnreal h.left, ← coe_to_nnreal h.right, ← coe_mul, coe_rpow_of_nonneg _ hpq.nonneg,
    coe_rpow_of_nonneg _ hpq.symm.nonneg, Ennreal.ofReal, Ennreal.ofReal, ←
    @coe_div (Real.toNnreal p) _
      (by
        simp [← hpq.pos]),
    ←
    @coe_div (Real.toNnreal q) _
      (by
        simp [← hpq.symm.pos]),
    ← coe_add, coe_le_coe]
  exact Nnreal.young_inequality_real a.to_nnreal b.to_nnreal hpq

end Ennreal

end Young

section HolderMinkowski

/-! ### Hölder's and Minkowski's inequalities -/


namespace Nnreal

private theorem inner_le_Lp_mul_Lp_of_norm_le_one (f g : ι → ℝ≥0 ) {p q : ℝ} (hpq : p.IsConjugateExponent q)
    (hf : (∑ i in s, f i ^ p) ≤ 1) (hg : (∑ i in s, g i ^ q) ≤ 1) : (∑ i in s, f i * g i) ≤ 1 := by
  have hp_ne_zero : Real.toNnreal p ≠ 0 := (zero_lt_one.trans hpq.one_lt_nnreal).Ne.symm
  have hq_ne_zero : Real.toNnreal q ≠ 0 := (zero_lt_one.trans hpq.symm.one_lt_nnreal).Ne.symm
  calc (∑ i in s, f i * g i) ≤ ∑ i in s, f i ^ p / Real.toNnreal p + g i ^ q / Real.toNnreal q :=
      Finset.sum_le_sum fun i his =>
        young_inequality_real (f i) (g i)
          hpq _ = (∑ i in s, f i ^ p) / Real.toNnreal p + (∑ i in s, g i ^ q) / Real.toNnreal q :=
      by
      rw [sum_add_distrib, sum_div, sum_div]_ ≤ 1 / Real.toNnreal p + 1 / Real.toNnreal q := by
      refine' add_le_add _ _
      · rwa [div_le_iff hp_ne_zero, div_mul_cancel _ hp_ne_zero]
        
      · rwa [div_le_iff hq_ne_zero, div_mul_cancel _ hq_ne_zero]
        _ = 1 :=
      hpq.inv_add_inv_conj_nnreal

private theorem inner_le_Lp_mul_Lp_of_norm_eq_zero (f g : ι → ℝ≥0 ) {p q : ℝ} (hpq : p.IsConjugateExponent q)
    (hf : (∑ i in s, f i ^ p) = 0) :
    (∑ i in s, f i * g i) ≤ (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  simp only [← hf, ← hpq.ne_zero, ← one_div, ← sum_eq_zero_iff, ← zero_rpow, ← zero_mul, ← inv_eq_zero, ← Ne.def, ←
    not_false_iff, ← le_zero_iff, ← mul_eq_zero]
  intro i his
  left
  rw [sum_eq_zero_iff] at hf
  exact (rpow_eq_zero_iff.mp (hf i his)).left

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0`-valued functions. -/
theorem inner_le_Lp_mul_Lq (f g : ι → ℝ≥0 ) {p q : ℝ} (hpq : p.IsConjugateExponent q) :
    (∑ i in s, f i * g i) ≤ (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  by_cases' hF_zero : (∑ i in s, f i ^ p) = 0
  · exact inner_le_Lp_mul_Lp_of_norm_eq_zero s f g hpq hF_zero
    
  by_cases' hG_zero : (∑ i in s, g i ^ q) = 0
  · calc (∑ i in s, f i * g i) = ∑ i in s, g i * f i := by
        congr with i
        rw [mul_comm]_ ≤ (∑ i in s, g i ^ q) ^ (1 / q) * (∑ i in s, f i ^ p) ^ (1 / p) :=
        inner_le_Lp_mul_Lp_of_norm_eq_zero s g f hpq.symm
          hG_zero _ = (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) :=
        mul_comm _ _
    
  let f' := fun i => f i / (∑ i in s, f i ^ p) ^ (1 / p)
  let g' := fun i => g i / (∑ i in s, g i ^ q) ^ (1 / q)
  suffices (∑ i in s, f' i * g' i) ≤ 1 by
    simp_rw [f', g', div_mul_div_comm, ← sum_div] at this
    rwa [div_le_iff, one_mulₓ] at this
    refine' mul_ne_zero _ _
    · rw [Ne.def, rpow_eq_zero_iff, not_and_distrib]
      exact Or.inl hF_zero
      
    · rw [Ne.def, rpow_eq_zero_iff, not_and_distrib]
      exact Or.inl hG_zero
      
  refine' inner_le_Lp_mul_Lp_of_norm_le_one s f' g' hpq (le_of_eqₓ _) (le_of_eqₓ _)
  · simp_rw [f', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel hpq.ne_zero, rpow_one, div_self hF_zero]
    
  · simp_rw [g', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel hpq.symm.ne_zero, rpow_one, div_self hG_zero]
    

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `nnreal`-valued
functions. For an alternative version, convenient if the infinite sums are already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_has_sum`. -/
theorem inner_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0 } {p q : ℝ} (hpq : p.IsConjugateExponent q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧ (∑' i, f i * g i) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  have H₁ : ∀ s : Finset ι, (∑ i in s, f i * g i) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
    intro s
    refine' le_transₓ (inner_le_Lp_mul_Lq s f g hpq) (mul_le_mul _ _ bot_le bot_le)
    · rw [Nnreal.rpow_le_rpow_iff (one_div_pos.mpr hpq.pos)]
      exact sum_le_tsum _ (fun _ _ => zero_le _) hf
      
    · rw [Nnreal.rpow_le_rpow_iff (one_div_pos.mpr hpq.symm.pos)]
      exact sum_le_tsum _ (fun _ _ => zero_le _) hg
      
  have bdd : BddAbove (Set.Range fun s => ∑ i in s, f i * g i) := by
    refine' ⟨(∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q), _⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (has_sum_of_is_lub _ (is_lub_csupr bdd)).Summable
  exact ⟨H₂, tsum_le_of_sum_le H₂ H₁⟩

theorem summable_mul_of_Lp_Lq {f g : ι → ℝ≥0 } {p q : ℝ} (hpq : p.IsConjugateExponent q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) : Summable fun i => f i * g i :=
  (inner_le_Lp_mul_Lq_tsum hpq hf hg).1

theorem inner_le_Lp_mul_Lq_tsum' {f g : ι → ℝ≥0 } {p q : ℝ} (hpq : p.IsConjugateExponent q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (∑' i, f i * g i) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (inner_le_Lp_mul_Lq_tsum hpq hf hg).2

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `nnreal`-valued
functions. For an alternative version, convenient if the infinite sums are not already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum`.  -/
theorem inner_le_Lp_mul_Lq_has_sum {f g : ι → ℝ≥0 } {A B : ℝ≥0 } {p q : ℝ} (hpq : p.IsConjugateExponent q)
    (hf : HasSum (fun i => f i ^ p) (A ^ p)) (hg : HasSum (fun i => g i ^ q) (B ^ q)) :
    ∃ C, C ≤ A * B ∧ HasSum (fun i => f i * g i) C := by
  obtain ⟨H₁, H₂⟩ := inner_le_Lp_mul_Lq_tsum hpq hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by
    rw [hf.tsum_eq, rpow_inv_rpow_self hpq.ne_zero]
  have hB : B = (∑' i : ι, g i ^ q) ^ (1 / q) := by
    rw [hg.tsum_eq, rpow_inv_rpow_self hpq.symm.ne_zero]
  refine' ⟨∑' i, f i * g i, _, _⟩
  · simpa [← hA, ← hB] using H₂
    
  · simpa only [← rpow_self_rpow_inv hpq.ne_zero] using H₁.has_sum
    

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ≥0`-valued functions.
-/
theorem rpow_sum_le_const_mul_sum_rpow (f : ι → ℝ≥0 ) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i in s, f i) ^ p ≤ card s ^ (p - 1) * ∑ i in s, f i ^ p := by
  cases' eq_or_lt_of_le hp with hp hp
  · simp [hp]
    
  let q : ℝ := p / (p - 1)
  have hpq : p.is_conjugate_exponent q := by
    rw [Real.is_conjugate_exponent_iff hp]
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [← Nnreal.mul_rpow, Nnreal.rpow_mul, ← hp₁, ← hq, ← one_mulₓ, ← one_rpow, ← rpow_one, ← Pi.one_apply, ←
    sum_const, ← Nat.smul_one_eq_coe] using Nnreal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg

/-- The `L_p` seminorm of a vector `f` is the greatest value of the inner product
`∑ i in s, f i * g i` over functions `g` of `L_q` seminorm less than or equal to one. -/
theorem is_greatest_Lp (f : ι → ℝ≥0 ) {p q : ℝ} (hpq : p.IsConjugateExponent q) :
    IsGreatest ((fun g : ι → ℝ≥0 => ∑ i in s, f i * g i) '' { g | (∑ i in s, g i ^ q) ≤ 1 })
      ((∑ i in s, f i ^ p) ^ (1 / p)) :=
  by
  constructor
  · use fun i => f i ^ p / f i / (∑ i in s, f i ^ p) ^ (1 / q)
    by_cases' hf : (∑ i in s, f i ^ p) = 0
    · simp [← hf, ← hpq.ne_zero, ← hpq.symm.ne_zero]
      
    · have A : p + q - q ≠ 0 := by
        simp [← hpq.ne_zero]
      have B : ∀ y : ℝ≥0 , y * y ^ p / y = y ^ p := by
        refine' fun y => mul_div_cancel_left_of_imp fun h => _
        simpa [← h, ← hpq.ne_zero]
      simp only [← Set.mem_set_of_eq, ← div_rpow, sum_div, rpow_mul, ← div_mul_cancel _ hpq.symm.ne_zero, ← rpow_one, ←
        div_le_iff hf, ← one_mulₓ, ← hpq.mul_eq_add, rpow_sub' _ A, ← _root_.add_sub_cancel, ← le_reflₓ, ← true_andₓ,
        mul_div_assoc, ← B]
      rw [div_eq_iff, ← rpow_add hf, hpq.inv_add_inv_conj, rpow_one]
      simpa [← hpq.symm.ne_zero] using hf
      
    
  · rintro _ ⟨g, hg, rfl⟩
    apply le_transₓ (inner_le_Lp_mul_Lq s f g hpq)
    simpa only [← mul_oneₓ] using mul_le_mul_left' (Nnreal.rpow_le_one hg (le_of_ltₓ hpq.symm.one_div_pos)) _
    

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `nnreal`-valued functions. -/
theorem Lp_add_le (f g : ι → ℝ≥0 ) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤ (∑ i in s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p) := by
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp [← Finset.sum_add_distrib]
    
  have hpq := Real.is_conjugate_exponent_conjugate_exponent hp
  have := is_greatest_Lp s (f + g) hpq
  simp only [← Pi.add_apply, ← add_mulₓ, ← sum_add_distrib] at this
  rcases this.1 with ⟨φ, hφ, H⟩
  rw [← H]
  exact add_le_add ((is_greatest_Lp s f hpq).2 ⟨φ, hφ, rfl⟩) ((is_greatest_Lp s g hpq).2 ⟨φ, hφ, rfl⟩)

/-- Minkowski inequality: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `nnreal`-valued functions. For an alternative version, convenient if the
infinite sums are already expressed as `p`-th powers, see `Lp_add_le_has_sum_of_nonneg`. -/
theorem Lp_add_le_tsum {f g : ι → ℝ≥0 } {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (Summable fun i => (f i + g i) ^ p) ∧
      (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  by
  have pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one hp
  have H₁ : ∀ s : Finset ι, (∑ i in s, (f i + g i) ^ p) ≤ ((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p :=
    by
    intro s
    rw [← Nnreal.rpow_one_div_le_iff Pos]
    refine' le_transₓ (Lp_add_le s f g hp) (add_le_add _ _) <;>
      rw [Nnreal.rpow_le_rpow_iff (one_div_pos.mpr Pos)] <;> refine' sum_le_tsum _ (fun _ _ => zero_le _) _
    exacts[hf, hg]
  have bdd : BddAbove (Set.Range fun s => ∑ i in s, (f i + g i) ^ p) := by
    refine' ⟨((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p, _⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (has_sum_of_is_lub _ (is_lub_csupr bdd)).Summable
  refine' ⟨H₂, _⟩
  rw [Nnreal.rpow_one_div_le_iff Pos]
  refine' tsum_le_of_sum_le H₂ H₁

theorem summable_Lp_add {f g : ι → ℝ≥0 } {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) : Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum hp hf hg).1

theorem Lp_add_le_tsum' {f g : ι → ℝ≥0 } {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum hp hf hg).2

/-- Minkowski inequality: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `nnreal`-valued functions. For an alternative version, convenient if the
infinite sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of_nonneg`.  -/
theorem Lp_add_le_has_sum {f g : ι → ℝ≥0 } {A B : ℝ≥0 } {p : ℝ} (hp : 1 ≤ p) (hf : HasSum (fun i => f i ^ p) (A ^ p))
    (hg : HasSum (fun i => g i ^ p) (B ^ p)) : ∃ C, C ≤ A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by
  have hp' : p ≠ 0 := (lt_of_lt_of_leₓ zero_lt_one hp).ne'
  obtain ⟨H₁, H₂⟩ := Lp_add_le_tsum hp hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by
    rw [hf.tsum_eq, rpow_inv_rpow_self hp']
  have hB : B = (∑' i : ι, g i ^ p) ^ (1 / p) := by
    rw [hg.tsum_eq, rpow_inv_rpow_self hp']
  refine' ⟨(∑' i, (f i + g i) ^ p) ^ (1 / p), _, _⟩
  · simpa [← hA, ← hB] using H₂
    
  · simpa only [← rpow_self_rpow_inv hp'] using H₁.has_sum
    

end Nnreal

namespace Real

variable (f g : ι → ℝ) {p q : ℝ}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : IsConjugateExponent p q) :
    (∑ i in s, f i * g i) ≤ (∑ i in s, abs (f i) ^ p) ^ (1 / p) * (∑ i in s, abs (g i) ^ q) ^ (1 / q) := by
  have :=
    Nnreal.coe_le_coe.2
      (Nnreal.inner_le_Lp_mul_Lq s (fun i => ⟨_, abs_nonneg (f i)⟩) (fun i => ⟨_, abs_nonneg (g i)⟩) hpq)
  push_cast at this
  refine' le_transₓ (sum_le_sum fun i hi => _) this
  simp only [abs_mul, ← le_abs_self]

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ`-valued functions. -/
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 ≤ p) :
    (∑ i in s, abs (f i)) ^ p ≤ card s ^ (p - 1) * ∑ i in s, abs (f i) ^ p := by
  have := Nnreal.coe_le_coe.2 (Nnreal.rpow_sum_le_const_mul_sum_rpow s (fun i => ⟨_, abs_nonneg (f i)⟩) hp)
  push_cast at this
  exact this

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `real`-valued functions. -/
-- for some reason `exact_mod_cast` can't replace this argument
theorem Lp_add_le (hp : 1 ≤ p) :
    (∑ i in s, abs (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i in s, abs (f i) ^ p) ^ (1 / p) + (∑ i in s, abs (g i) ^ p) ^ (1 / p) :=
  by
  have := Nnreal.coe_le_coe.2 (Nnreal.Lp_add_le s (fun i => ⟨_, abs_nonneg (f i)⟩) (fun i => ⟨_, abs_nonneg (g i)⟩) hp)
  push_cast at this
  refine' le_transₓ (rpow_le_rpow _ (sum_le_sum fun i hi => _) _) this <;>
    simp [← sum_nonneg, ← rpow_nonneg_of_nonneg, ← abs_nonneg, ← le_transₓ zero_le_one hp, ← abs_add, ← rpow_le_rpow]

variable {f g}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued nonnegative functions. -/
theorem inner_le_Lp_mul_Lq_of_nonneg (hpq : IsConjugateExponent p q) (hf : ∀, ∀ i ∈ s, ∀, 0 ≤ f i)
    (hg : ∀, ∀ i ∈ s, ∀, 0 ≤ g i) :
    (∑ i in s, f i * g i) ≤ (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  convert inner_le_Lp_mul_Lq s f g hpq using 3 <;>
    apply sum_congr rfl <;> intro i hi <;> simp only [← abs_of_nonneg, ← hf i hi, ← hg i hi]

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `ℝ`-valued functions.
For an alternative version, convenient if the infinite sums are already expressed as `p`-th powers,
see `inner_le_Lp_mul_Lq_has_sum_of_nonneg`. -/
theorem inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.IsConjugateExponent q) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧ (∑' i, f i * g i) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  norm_cast  at *
  exact Nnreal.inner_le_Lp_mul_Lq_tsum hpq hf_sum hg_sum

theorem summable_mul_of_Lp_Lq_of_nonneg (hpq : p.IsConjugateExponent q) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) : Summable fun i => f i * g i :=
  (inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).1

theorem inner_le_Lp_mul_Lq_tsum_of_nonneg' (hpq : p.IsConjugateExponent q) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    (∑' i, f i * g i) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).2

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `nnreal`-valued
functions. For an alternative version, convenient if the infinite sums are not already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum_of_nonneg`.  -/
theorem inner_le_Lp_mul_Lq_has_sum_of_nonneg (hpq : p.IsConjugateExponent q) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hf_sum : HasSum (fun i => f i ^ p) (A ^ p))
    (hg_sum : HasSum (fun i => g i ^ q) (B ^ q)) : ∃ C : ℝ, 0 ≤ C ∧ C ≤ A * B ∧ HasSum (fun i => f i * g i) C := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  lift A to ℝ≥0 using hA
  lift B to ℝ≥0 using hB
  norm_cast  at hf_sum hg_sum
  obtain ⟨C, hC, H⟩ := Nnreal.inner_le_Lp_mul_Lq_has_sum hpq hf_sum hg_sum
  refine' ⟨C, C.prop, hC, _⟩
  norm_cast
  exact H

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with nonnegative `ℝ`-valued
functions. -/
theorem rpow_sum_le_const_mul_sum_rpow_of_nonneg (hp : 1 ≤ p) (hf : ∀, ∀ i ∈ s, ∀, 0 ≤ f i) :
    (∑ i in s, f i) ^ p ≤ card s ^ (p - 1) * ∑ i in s, f i ^ p := by
  convert rpow_sum_le_const_mul_sum_rpow s f hp using 2 <;>
    apply sum_congr rfl <;> intro i hi <;> simp only [← abs_of_nonneg, ← hf i hi]

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ`-valued nonnegative
functions. -/
theorem Lp_add_le_of_nonneg (hp : 1 ≤ p) (hf : ∀, ∀ i ∈ s, ∀, 0 ≤ f i) (hg : ∀, ∀ i ∈ s, ∀, 0 ≤ g i) :
    (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤ (∑ i in s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p) := by
  convert Lp_add_le s f g hp using 2 <;> [skip, congr 1, congr 1] <;>
    apply sum_congr rfl <;> intro i hi <;> simp only [← abs_of_nonneg, ← hf i hi, ← hg i hi, ← add_nonneg]

/-- Minkowski inequality: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `ℝ`-valued functions. For an alternative version, convenient if the infinite
sums are already expressed as `p`-th powers, see `Lp_add_le_has_sum_of_nonneg`. -/
theorem Lp_add_le_tsum_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (Summable fun i => (f i + g i) ^ p) ∧
      (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  norm_cast  at *
  exact Nnreal.Lp_add_le_tsum hp hf_sum hg_sum

theorem summable_Lp_add_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) : Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).1

theorem Lp_add_le_tsum_of_nonneg' (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).2

/-- Minkowski inequality: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `ℝ`-valued functions. For an alternative version, convenient if the infinite
sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of_nonneg`. -/
theorem Lp_add_le_has_sum_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hfA : HasSum (fun i => f i ^ p) (A ^ p)) (hgB : HasSum (fun i => g i ^ p) (B ^ p)) :
    ∃ C, 0 ≤ C ∧ C ≤ A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  lift A to ℝ≥0 using hA
  lift B to ℝ≥0 using hB
  norm_cast  at hfA hgB
  obtain ⟨C, hC₁, hC₂⟩ := Nnreal.Lp_add_le_has_sum hp hfA hgB
  use C
  norm_cast
  exact ⟨zero_le _, hC₁, hC₂⟩

end Real

namespace Ennreal

variable (f g : ι → ℝ≥0∞) {p q : ℝ}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0∞`-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : p.IsConjugateExponent q) :
    (∑ i in s, f i * g i) ≤ (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  by_cases' H : (∑ i in s, f i ^ p) ^ (1 / p) = 0 ∨ (∑ i in s, g i ^ q) ^ (1 / q) = 0
  · replace H : (∀, ∀ i ∈ s, ∀, f i = 0) ∨ ∀, ∀ i ∈ s, ∀, g i = 0
    · simpa [← Ennreal.rpow_eq_zero_iff, ← hpq.pos, ← hpq.symm.pos, ← asymm hpq.pos, ← asymm hpq.symm.pos, ←
        sum_eq_zero_iff_of_nonneg] using H
      
    have : ∀, ∀ i ∈ s, ∀, f i * g i = 0 := fun i hi => by
      cases H <;> simp [← H i hi]
    have : (∑ i in s, f i * g i) = ∑ i in s, 0 := sum_congr rfl this
    simp [← this]
    
  push_neg  at H
  by_cases' H' : (∑ i in s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i in s, g i ^ q) ^ (1 / q) = ⊤
  · cases H' <;> simp [← H', -one_div, ← H]
    
  replace H' : (∀, ∀ i ∈ s, ∀, f i ≠ ⊤) ∧ ∀, ∀ i ∈ s, ∀, g i ≠ ⊤
  · simpa [← Ennreal.rpow_eq_top_iff, ← asymm hpq.pos, ← asymm hpq.symm.pos, ← hpq.pos, ← hpq.symm.pos, ←
      Ennreal.sum_eq_top_iff, ← not_or_distrib] using H'
    
  have :=
    Ennreal.coe_le_coe.2
      (@Nnreal.inner_le_Lp_mul_Lq _ s (fun i => Ennreal.toNnreal (f i)) (fun i => Ennreal.toNnreal (g i)) _ _ hpq)
  simp [Ennreal.coe_rpow_of_nonneg, ← le_of_ltₓ hpq.pos, ← le_of_ltₓ hpq.one_div_pos, ← le_of_ltₓ hpq.symm.pos, ←
    le_of_ltₓ hpq.symm.one_div_pos] at this
  convert this using 1 <;> [skip, congr 2] <;> [skip, skip, simp , skip, simp ] <;>
    · apply Finset.sum_congr rfl fun i hi => _
      simp [← H'.1 i hi, ← H'.2 i hi, -WithZero.coe_mul, ← with_top.coe_mul.symm]
      

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ≥0∞`-valued functions.
-/
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 ≤ p) : (∑ i in s, f i) ^ p ≤ card s ^ (p - 1) * ∑ i in s, f i ^ p := by
  cases' eq_or_lt_of_le hp with hp hp
  · simp [hp]
    
  let q : ℝ := p / (p - 1)
  have hpq : p.is_conjugate_exponent q := by
    rw [Real.is_conjugate_exponent_iff hp]
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [← Ennreal.mul_rpow_of_nonneg _ _ hpq.nonneg, Ennreal.rpow_mul, ← hp₁, ← hq, ← coe_one, ← one_mulₓ, ←
    one_rpow, ← rpow_one, ← Pi.one_apply, ← sum_const, ← Nat.smul_one_eq_coe] using
    Ennreal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ≥0∞` valued nonnegative
functions. -/
theorem Lp_add_le (hp : 1 ≤ p) :
    (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤ (∑ i in s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p) := by
  by_cases' H' : (∑ i in s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i in s, g i ^ p) ^ (1 / p) = ⊤
  · cases H' <;> simp [← H', -one_div]
    
  have pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one hp
  replace H' : (∀, ∀ i ∈ s, ∀, f i ≠ ⊤) ∧ ∀, ∀ i ∈ s, ∀, g i ≠ ⊤
  · simpa [← Ennreal.rpow_eq_top_iff, ← asymm Pos, ← Pos, ← Ennreal.sum_eq_top_iff, ← not_or_distrib] using H'
    
  have :=
    Ennreal.coe_le_coe.2
      (@Nnreal.Lp_add_le _ s (fun i => Ennreal.toNnreal (f i)) (fun i => Ennreal.toNnreal (g i)) _ hp)
  push_cast [Ennreal.coe_rpow_of_nonneg, ← le_of_ltₓ Pos, ← le_of_ltₓ (one_div_pos.2 Pos)] at this
  convert this using 2 <;> [skip, congr 1, congr 1] <;>
    · apply Finset.sum_congr rfl fun i hi => _
      simp [← H'.1 i hi, ← H'.2 i hi]
      

end Ennreal

end HolderMinkowski

