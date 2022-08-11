/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Analysis.InnerProductSpace.PiL2
import Mathbin.LinearAlgebra.Orientation

/-!
# Orientations of real inner product spaces.

This file provides definitions and proves lemmas about orientations of real inner product spaces.

## Main definitions

* `orientation.fin_orthonormal_basis` is an orthonormal basis, indexed by `fin n`, with the given
orientation.

-/


noncomputable section

variable {E : Type _} [InnerProductSpace ℝ E]

variable {ι : Type _} [Fintype ι] [DecidableEq ι]

open FiniteDimensional

/-- `basis.adjust_to_orientation`, applied to an orthonormal basis, produces an orthonormal
basis. -/
theorem Orthonormal.orthonormal_adjust_to_orientation [Nonempty ι] {e : Basis ι ℝ E} (h : Orthonormal ℝ e)
    (x : Orientation ℝ E ι) : Orthonormal ℝ (e.adjustToOrientation x) :=
  h.orthonormal_of_forall_eq_or_eq_neg (e.adjust_to_orientation_apply_eq_or_eq_neg x)

/-- An orthonormal basis, indexed by `fin n`, with the given orientation. -/
protected def Orientation.finOrthonormalBasis {n : ℕ} (hn : 0 < n) (h : finrank ℝ E = n)
    (x : Orientation ℝ E (Finₓ n)) : Basis (Finₓ n) ℝ E := by
  have := Finₓ.pos_iff_nonempty.1 hn
  have := finite_dimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E)
  exact (finStdOrthonormalBasis h).toBasis.adjustToOrientation x

/-- `orientation.fin_orthonormal_basis` is orthonormal. -/
protected theorem Orientation.fin_orthonormal_basis_orthonormal {n : ℕ} (hn : 0 < n) (h : finrank ℝ E = n)
    (x : Orientation ℝ E (Finₓ n)) : Orthonormal ℝ (x.finOrthonormalBasis hn h) := by
  have := Finₓ.pos_iff_nonempty.1 hn
  have := finite_dimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E)
  exact
    show Orthonormal ℝ (finStdOrthonormalBasis h).toBasis by
          -- Note sure how to format this
          simp only [← OrthonormalBasis.coe_to_basis, ← OrthonormalBasis.orthonormal].orthonormal_adjust_to_orientation
      _

/-- `orientation.fin_orthonormal_basis` gives a basis with the required orientation. -/
@[simp]
theorem Orientation.fin_orthonormal_basis_orientation {n : ℕ} (hn : 0 < n) (h : finrank ℝ E = n)
    (x : Orientation ℝ E (Finₓ n)) : (x.finOrthonormalBasis hn h).Orientation = x := by
  have := Finₓ.pos_iff_nonempty.1 hn
  exact Basis.orientation_adjust_to_orientation _ _

