/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.Data.Matrix.Basic

/-!
# Trace of a matrix

This file defines the trace of a matrix, the map sending a matrix to the sum of its diagonal
entries.

See also `linear_algebra.trace` for the trace of an endomorphism.

## Tags

matrix, trace, diagonal

-/


open BigOperators Matrix

namespace Matrix

variable {ι m n p : Type _} {α R S : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

section AddCommMonoidₓ

variable [AddCommMonoidₓ R]

/-- The trace of a square matrix. For more bundled versions, see:
* `matrix.trace_add_monoid_hom`
* `matrix.trace_linear_map`
-/
def trace (A : Matrix n n R) : R :=
  ∑ i, diag A i

variable (n R)

@[simp]
theorem trace_zero : trace (0 : Matrix n n R) = 0 :=
  (Finset.sum_const (0 : R)).trans <| smul_zero _

variable {n R}

@[simp]
theorem trace_add (A B : Matrix n n R) : trace (A + B) = trace A + trace B :=
  Finset.sum_add_distrib

@[simp]
theorem trace_smul [Monoidₓ α] [DistribMulAction α R] (r : α) (A : Matrix n n R) : trace (r • A) = r • trace A :=
  Finset.smul_sum.symm

@[simp]
theorem trace_transpose (A : Matrix n n R) : trace Aᵀ = trace A :=
  rfl

@[simp]
theorem trace_conj_transpose [StarAddMonoid R] (A : Matrix n n R) : trace Aᴴ = star (trace A) :=
  (star_sum _ _).symm

variable (n α R)

/-- `matrix.trace` as an `add_monoid_hom` -/
@[simps]
def traceAddMonoidHom : Matrix n n R →+ R where
  toFun := trace
  map_zero' := trace_zero n R
  map_add' := trace_add

/-- `matrix.trace` as a `linear_map` -/
@[simps]
def traceLinearMap [Semiringₓ α] [Module α R] : Matrix n n R →ₗ[α] R where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

variable {n α R}

@[simp]
theorem trace_list_sum (l : List (Matrix n n R)) : trace l.Sum = (l.map trace).Sum :=
  map_list_sum (traceAddMonoidHom n R) l

@[simp]
theorem trace_multiset_sum (s : Multiset (Matrix n n R)) : trace s.Sum = (s.map trace).Sum :=
  map_multiset_sum (traceAddMonoidHom n R) s

@[simp]
theorem trace_sum (s : Finset ι) (f : ι → Matrix n n R) : trace (∑ i in s, f i) = ∑ i in s, trace (f i) :=
  map_sum (traceAddMonoidHom n R) f s

end AddCommMonoidₓ

section AddCommGroupₓ

variable [AddCommGroupₓ R]

@[simp]
theorem trace_sub (A B : Matrix n n R) : trace (A - B) = trace A - trace B :=
  Finset.sum_sub_distrib

@[simp]
theorem trace_neg (A : Matrix n n R) : trace (-A) = -trace A :=
  Finset.sum_neg_distrib

end AddCommGroupₓ

section One

variable [DecidableEq n] [AddCommMonoidWithOne R]

@[simp]
theorem trace_one : trace (1 : Matrix n n R) = Fintype.card n := by
  simp_rw [trace, diag_one, Pi.one_def, Finset.sum_const, nsmul_one, Finset.card_univ]

end One

section Mul

@[simp]
theorem trace_transpose_mul [AddCommMonoidₓ R] [Mul R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (Aᵀ ⬝ Bᵀ) = trace (A ⬝ B) :=
  Finset.sum_comm

theorem trace_mul_comm [AddCommMonoidₓ R] [CommSemigroupₓ R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (A ⬝ B) = trace (B ⬝ A) := by
  rw [← trace_transpose, ← trace_transpose_mul, transpose_mul]

theorem trace_mul_cycle [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R) (C : Matrix p m R) :
    trace (A ⬝ B ⬝ C) = trace (C ⬝ A ⬝ B) := by
  rw [trace_mul_comm, Matrix.mul_assoc]

theorem trace_mul_cycle' [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R) (C : Matrix p m R) :
    trace (A ⬝ (B ⬝ C)) = trace (C ⬝ (A ⬝ B)) := by
  rw [← Matrix.mul_assoc, trace_mul_comm]

@[simp]
theorem trace_col_mul_row [NonUnitalNonAssocSemiringₓ R] (a b : n → R) : trace (colₓ a ⬝ rowₓ b) = dotProduct a b := by
  simp [← dot_product, ← trace]

end Mul

section Finₓ

variable [AddCommMonoidₓ R]

/-! ### Special cases for `fin n`

While `simp [fin.sum_univ_succ]` can prove these, we include them for convenience and consistency
with `matrix.det_fin_two` etc.
-/


@[simp]
theorem trace_fin_zero (A : Matrix (Finₓ 0) (Finₓ 0) R) : trace A = 0 :=
  rfl

theorem trace_fin_one (A : Matrix (Finₓ 1) (Finₓ 1) R) : trace A = A 0 0 :=
  add_zeroₓ _

theorem trace_fin_two (A : Matrix (Finₓ 2) (Finₓ 2) R) : trace A = A 0 0 + A 1 1 :=
  congr_arg ((· + ·) _) (add_zeroₓ (A 1 1))

theorem trace_fin_three (A : Matrix (Finₓ 3) (Finₓ 3) R) : trace A = A 0 0 + A 1 1 + A 2 2 := by
  rw [← add_zeroₓ (A 2 2), add_assocₓ]
  rfl

end Finₓ

end Matrix

