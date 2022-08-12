/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import Mathbin.LinearAlgebra.QuadraticForm.Isometry
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.Data.Real.Sign

/-!
# Real quadratic forms

Sylvester's law of inertia `equivalent_one_neg_one_weighted_sum_squared`:
A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0.

When the real quadratic form is nondegerate we can take the weights to be ±1,
as in `equivalent_one_zero_neg_one_weighted_sum_squared`.

-/


namespace QuadraticForm

open BigOperators

open Real Finset

variable {ι : Type _} [Fintype ι]

/-- The isometry between a weighted sum of squares with weights `u` on the
(non-zero) real numbers and the weighted sum of squares with weights `sign ∘ u`. -/
noncomputable def isometrySignWeightedSumSquares [DecidableEq ι] (w : ι → ℝ) :
    Isometry (weightedSumSquares ℝ w) (weightedSumSquares ℝ (sign ∘ w)) := by
  let u := fun i => if h : w i = 0 then (1 : ℝˣ) else Units.mk0 (w i) h
  have hu' : ∀ i : ι, (sign (u i) * u i) ^ -(1 / 2 : ℝ) ≠ 0 := by
    intro i
    refine' (ne_of_ltₓ (Real.rpow_pos_of_pos (sign_mul_pos_of_ne_zero _ <| Units.ne_zero _) _)).symm
  convert
    (weighted_sum_squares ℝ w).isometryBasisRepr
      ((Pi.basisFun ℝ ι).units_smul fun i => (is_unit_iff_ne_zero.2 <| hu' i).Unit)
  ext1 v
  rw [basis_repr_apply, weighted_sum_squares_apply, weighted_sum_squares_apply]
  refine' sum_congr rfl fun j hj => _
  have hsum :
    (∑ i : ι, v i • ((is_unit_iff_ne_zero.2 <| hu' i).Unit : ℝ) • (Pi.basisFun ℝ ι) i) j =
      v j • (sign (u j) * u j) ^ -(1 / 2 : ℝ) :=
    by
    rw [Finset.sum_apply, sum_eq_single j, Pi.basis_fun_apply, IsUnit.unit_spec, LinearMap.std_basis_apply,
      Pi.smul_apply, Pi.smul_apply, Function.update_same, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_oneₓ]
    intro i _ hij
    rw [Pi.basis_fun_apply, LinearMap.std_basis_apply, Pi.smul_apply, Pi.smul_apply, Function.update_noteq hij.symm,
      Pi.zero_apply, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero]
    intro hj'
    exact False.elim (hj' hj)
  simp_rw [Basis.units_smul_apply]
  erw [hsum]
  simp only [← u, ← Function.comp, ← smul_eq_mul]
  split_ifs
  · simp only [← h, ← zero_smul, ← zero_mul, ← sign_zero]
    
  have hwu : w j = u j := by
    simp only [← u, ← dif_neg h, ← Units.coe_mk0]
  simp only [← hwu, ← Units.coe_mk0]
  suffices
    (u j : ℝ).sign * v j * v j = (sign (u j) * u j) ^ -(1 / 2 : ℝ) * (sign (u j) * u j) ^ -(1 / 2 : ℝ) * u j * v j * v j
    by
    erw [← mul_assoc, this]
    ring
  rw [← Real.rpow_add (sign_mul_pos_of_ne_zero _ <| Units.ne_zero _),
    show -(1 / 2 : ℝ) + -(1 / 2) = -1 by
      ring,
    Real.rpow_neg_one, mul_inv, inv_sign, mul_assoc (sign (u j)) (u j)⁻¹, inv_mul_cancel (Units.ne_zero _), mul_oneₓ]
  infer_instance

/-- **Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1. -/
theorem equivalent_one_neg_one_weighted_sum_squared {M : Type _} [AddCommGroupₓ M] [Module ℝ M] [FiniteDimensional ℝ M]
    (Q : QuadraticForm ℝ M) (hQ : (associated Q).Nondegenerate) :
    ∃ w : Finₓ (FiniteDimensional.finrank ℝ M) → ℝ, (∀ i, w i = -1 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares ℝ w) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares_units_of_nondegenerate' hQ
  ⟨sign ∘ coe ∘ w, fun i => sign_apply_eq_of_ne_zero (w i) (w i).ne_zero,
    ⟨hw₁.trans (isometrySignWeightedSumSquares (coe ∘ w))⟩⟩

/-- **Sylvester's law of inertia**: A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0. -/
theorem equivalent_one_zero_neg_one_weighted_sum_squared {M : Type _} [AddCommGroupₓ M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
    ∃ w : Finₓ (FiniteDimensional.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares ℝ w) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares
  ⟨sign ∘ coe ∘ w, fun i => sign_apply_eq (w i), ⟨hw₁.trans (isometrySignWeightedSumSquares w)⟩⟩

end QuadraticForm

