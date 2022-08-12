/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import Mathbin.Data.Matrix.Basic

/-!
# Orthogonal

This file contains definitions and properties concerning orthogonality of rows and columns.

## Main results

- `matrix.has_orthogonal_rows`:
  `A.has_orthogonal_rows` means `A` has orthogonal (with respect to `dot_product`) rows.
- `matrix.has_orthogonal_cols`:
  `A.has_orthogonal_cols` means `A` has orthogonal (with respect to `dot_product`) columns.

## Tags

orthogonal
-/


namespace Matrix

variable {α n m : Type _}

variable [Mul α] [AddCommMonoidₓ α]

variable (A : Matrix m n α)

open Matrix

/-- `A.has_orthogonal_rows` means matrix `A` has orthogonal rows (with respect to
`matrix.dot_product`). -/
def HasOrthogonalRows [Fintype n] : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → dotProduct (A i₁) (A i₂) = 0

/-- `A.has_orthogonal_rows` means matrix `A` has orthogonal columns (with respect to
`matrix.dot_product`). -/
def HasOrthogonalCols [Fintype m] : Prop :=
  HasOrthogonalRows Aᵀ

/-- `Aᵀ` has orthogonal rows iff `A` has orthogonal columns. -/
@[simp]
theorem transpose_has_orthogonal_rows_iff_has_orthogonal_cols [Fintype m] :
    Aᵀ.HasOrthogonalRows ↔ A.HasOrthogonalCols :=
  Iff.rfl

/-- `Aᵀ` has orthogonal columns iff `A` has orthogonal rows. -/
@[simp]
theorem transpose_has_orthogonal_cols_iff_has_orthogonal_rows [Fintype n] :
    Aᵀ.HasOrthogonalCols ↔ A.HasOrthogonalRows :=
  Iff.rfl

variable {A}

theorem HasOrthogonalRows.has_orthogonal_cols [Fintype m] (h : Aᵀ.HasOrthogonalRows) : A.HasOrthogonalCols :=
  h

theorem HasOrthogonalCols.transpose_has_orthogonal_rows [Fintype m] (h : A.HasOrthogonalCols) : Aᵀ.HasOrthogonalRows :=
  h

theorem HasOrthogonalCols.has_orthogonal_rows [Fintype n] (h : Aᵀ.HasOrthogonalCols) : A.HasOrthogonalRows :=
  h

theorem HasOrthogonalRows.transpose_has_orthogonal_cols [Fintype n] (h : A.HasOrthogonalRows) : Aᵀ.HasOrthogonalCols :=
  h

end Matrix

