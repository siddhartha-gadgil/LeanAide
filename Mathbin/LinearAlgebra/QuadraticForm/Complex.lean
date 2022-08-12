/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import Mathbin.LinearAlgebra.QuadraticForm.Isometry
import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# Quadratic forms over the complex numbers

`equivalent_sum_squares`: A nondegenerate quadratic form over the complex numbers is equivalent to
a sum of squares.

-/


namespace QuadraticForm

open BigOperators

open Finset

variable {ι : Type _} [Fintype ι]

/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weighted_sum_squares` with weights 1 or 0. -/
noncomputable def isometrySumSquares [DecidableEq ι] (w' : ι → ℂ) :
    Isometry (weightedSumSquares ℂ w') (weightedSumSquares ℂ (fun i => if w' i = 0 then 0 else 1 : ι → ℂ)) := by
  let w := fun i => if h : w' i = 0 then (1 : Units ℂ) else Units.mk0 (w' i) h
  have hw' : ∀ i : ι, (w i : ℂ) ^ -(1 / 2 : ℂ) ≠ 0 := by
    intro i hi
    exact (w i).ne_zero ((Complex.cpow_eq_zero_iff _ _).1 hi).1
  convert
    (weighted_sum_squares ℂ w').isometryBasisRepr
      ((Pi.basisFun ℂ ι).units_smul fun i => (is_unit_iff_ne_zero.2 <| hw' i).Unit)
  ext1 v
  erw [basis_repr_apply, weighted_sum_squares_apply, weighted_sum_squares_apply]
  refine' sum_congr rfl fun j hj => _
  have hsum :
    (∑ i : ι, v i • ((is_unit_iff_ne_zero.2 <| hw' i).Unit : ℂ) • (Pi.basisFun ℂ ι) i) j = v j • w j ^ -(1 / 2 : ℂ) :=
    by
    rw [Finset.sum_apply, sum_eq_single j, Pi.basis_fun_apply, IsUnit.unit_spec, LinearMap.std_basis_apply,
      Pi.smul_apply, Pi.smul_apply, Function.update_same, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_oneₓ]
    intro i _ hij
    rw [Pi.basis_fun_apply, LinearMap.std_basis_apply, Pi.smul_apply, Pi.smul_apply, Function.update_noteq hij.symm,
      Pi.zero_apply, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero]
    intro hj'
    exact False.elim (hj' hj)
  simp_rw [Basis.units_smul_apply]
  erw [hsum, smul_eq_mul]
  split_ifs
  · simp only [← h, ← zero_smul, ← zero_mul]
    
  have hww' : w' j = w j := by
    simp only [← w, ← dif_neg h, ← Units.coe_mk0]
  simp only [← hww', ← one_mulₓ]
  change v j * v j = ↑(w j) * (v j * ↑(w j) ^ -(1 / 2 : ℂ) * (v j * ↑(w j) ^ -(1 / 2 : ℂ)))
  suffices v j * v j = w j ^ -(1 / 2 : ℂ) * w j ^ -(1 / 2 : ℂ) * w j * v j * v j by
    rw [this]
    ring
  rw [← Complex.cpow_add _ _ (w j).ne_zero,
    show -(1 / 2 : ℂ) + -(1 / 2) = -1 by
      simp [two_mul],
    Complex.cpow_neg_one, inv_mul_cancel (w j).ne_zero, one_mulₓ]

/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
noncomputable def isometrySumSquaresUnits [DecidableEq ι] (w : ι → Units ℂ) :
    Isometry (weightedSumSquares ℂ w) (weightedSumSquares ℂ (1 : ι → ℂ)) := by
  have hw1 : (fun i => if (w i : ℂ) = 0 then 0 else 1 : ι → ℂ) = 1 := by
    ext i : 1
    exact dif_neg (w i).ne_zero
  have := isometry_sum_squares (coe ∘ w)
  rw [hw1] at this
  exact this

/-- A nondegenerate quadratic form on the complex numbers is equivalent to
the sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
theorem equivalent_sum_squares {M : Type _} [AddCommGroupₓ M] [Module ℂ M] [FiniteDimensional ℂ M]
    (Q : QuadraticForm ℂ M) (hQ : (associated Q).Nondegenerate) :
    Equivalent Q (weightedSumSquares ℂ (1 : Finₓ (FiniteDimensional.finrank ℂ M) → ℂ)) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares_units_of_nondegenerate' hQ
  ⟨hw₁.trans (isometrySumSquaresUnits w)⟩

/-- All nondegenerate quadratic forms on the complex numbers are equivalent. -/
theorem complex_equivalent {M : Type _} [AddCommGroupₓ M] [Module ℂ M] [FiniteDimensional ℂ M]
    (Q₁ Q₂ : QuadraticForm ℂ M) (hQ₁ : (associated Q₁).Nondegenerate) (hQ₂ : (associated Q₂).Nondegenerate) :
    Equivalent Q₁ Q₂ :=
  (Q₁.equivalent_sum_squares hQ₁).trans (Q₂.equivalent_sum_squares hQ₂).symm

end QuadraticForm

