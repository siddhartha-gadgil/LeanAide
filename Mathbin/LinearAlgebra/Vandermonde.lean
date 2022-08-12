/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.BigOperators.Fin
import Mathbin.Algebra.GeomSum
import Mathbin.GroupTheory.Perm.Fin
import Mathbin.LinearAlgebra.Matrix.Determinant

/-!
# Vandermonde matrix

This file defines the `vandermonde` matrix and gives its determinant.

## Main definitions

 - `vandermonde v`: a square matrix with the `i, j`th entry equal to `v i ^ j`.

## Main results

 - `det_vandermonde`: `det (vandermonde v)` is the product of `v i - v j`, where
   `(i, j)` ranges over the unordered pairs.
-/


variable {R : Type _} [CommRingₓ R]

open Equivₓ Finset

open BigOperators Matrix

namespace Matrix

/-- `vandermonde v` is the square matrix with `i`th row equal to `1, v i, v i ^ 2, v i ^ 3, ...`.
-/
def vandermonde {n : ℕ} (v : Finₓ n → R) : Matrix (Finₓ n) (Finₓ n) R := fun i j => v i ^ (j : ℕ)

@[simp]
theorem vandermonde_apply {n : ℕ} (v : Finₓ n → R) (i j) : vandermonde v i j = v i ^ (j : ℕ) :=
  rfl

@[simp]
theorem vandermonde_cons {n : ℕ} (v0 : R) (v : Finₓ n → R) :
    vandermonde (Finₓ.cons v0 v : Finₓ n.succ → R) =
      Finₓ.cons (fun j => v0 ^ (j : ℕ)) fun i => Finₓ.cons 1 fun j => v i * vandermonde v i j :=
  by
  ext i j
  refine'
    Finₓ.cases
      (by
        simp )
      (fun i => _) i
  refine'
    Finₓ.cases
      (by
        simp )
      (fun j => _) j
  simp [← pow_succₓ]

theorem vandermonde_succ {n : ℕ} (v : Finₓ n.succ → R) :
    vandermonde v =
      Finₓ.cons (fun j => v 0 ^ (j : ℕ)) fun i => Finₓ.cons 1 fun j => v i.succ * vandermonde (Finₓ.tail v) i j :=
  by
  conv_lhs => rw [← Finₓ.cons_self_tail v, vandermonde_cons]
  simp only [← Finₓ.tail]

theorem vandermonde_mul_vandermonde_transpose {n : ℕ} (v w : Finₓ n → R) (i j) :
    (vandermonde v ⬝ (vandermonde w)ᵀ) i j = ∑ k : Finₓ n, (v i * w j) ^ (k : ℕ) := by
  simp only [← vandermonde_apply, ← Matrix.mul_apply, ← Matrix.transpose_apply, ← mul_powₓ]

theorem vandermonde_transpose_mul_vandermonde {n : ℕ} (v : Finₓ n → R) (i j) :
    ((vandermonde v)ᵀ ⬝ vandermonde v) i j = ∑ k : Finₓ n, v k ^ (i + j : ℕ) := by
  simp only [← vandermonde_apply, ← Matrix.mul_apply, ← Matrix.transpose_apply, ← pow_addₓ]

theorem det_vandermonde {n : ℕ} (v : Finₓ n → R) : det (vandermonde v) = ∏ i : Finₓ n, ∏ j in ioi i, v j - v i := by
  unfold vandermonde
  induction' n with n ih
  · exact det_eq_one_of_card_eq_zero (Fintype.card_fin 0)
    
  calc
    det (of fun i j : Finₓ n.succ => v i ^ (j : ℕ)) =
        det
          (of fun i j : Finₓ n.succ =>
            Matrix.vecCons (v 0 ^ (j : ℕ)) (fun i => v (Finₓ.succ i) ^ (j : ℕ) - v 0 ^ (j : ℕ)) i) :=
      det_eq_of_forall_row_eq_smul_add_const (Matrix.vecCons 0 1) 0 (Finₓ.cons_zero _ _)
        _ _ =
        det
          (of fun i j : Finₓ n =>
            Matrix.vecCons (v 0 ^ (j.succ : ℕ)) (fun i : Finₓ n => v (Finₓ.succ i) ^ (j.succ : ℕ) - v 0 ^ (j.succ : ℕ))
              (Finₓ.succAbove 0 i)) :=
      by
      simp_rw [det_succ_column_zero, Finₓ.sum_univ_succ, of_apply, Matrix.cons_val_zero, minor, of_apply,
        Matrix.cons_val_succ, Finₓ.coe_zero, pow_zeroₓ, one_mulₓ, sub_self, mul_zero, zero_mul, Finset.sum_const_zero,
        add_zeroₓ]_ =
        det
          (of fun i j : Finₓ n =>
            (v (Finₓ.succ i) - v 0) * ∑ k in Finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ) :
            Matrix _ _ R) :=
      by
      congr
      ext i j
      rw [Finₓ.succ_above_zero, Matrix.cons_val_succ, Finₓ.coe_succ, mul_comm]
      exact
        (geom_sum₂_mul (v i.succ) (v 0)
            (j + 1 :
              ℕ)).symm _ =
        (∏ i : Finₓ n, v (Finₓ.succ i) - v 0) *
          det fun i j : Finₓ n => ∑ k in Finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ) :=
      det_mul_column (fun i => v (Finₓ.succ i) - v 0)
        _ _ = (∏ i : Finₓ n, v (Finₓ.succ i) - v 0) * det fun i j : Finₓ n => v (Finₓ.succ i) ^ (j : ℕ) :=
      congr_arg ((· * ·) _) _ _ = ∏ i : Finₓ n.succ, ∏ j in Ioi i, v j - v i := by
      simp_rw [ih (v ∘ Finₓ.succ), Finₓ.prod_univ_succ, Finₓ.prod_Ioi_zero, Finₓ.prod_Ioi_succ]
  · intro i j
    simp_rw [of_apply]
    rw [Matrix.cons_val_zero]
    refine' Finₓ.cases _ (fun i => _) i
    · simp
      
    rw [Matrix.cons_val_succ, Matrix.cons_val_succ, Pi.one_apply]
    ring
    
  · cases n
    · simp only [← det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
      
    apply det_eq_of_forall_col_eq_smul_add_pred fun i => v 0
    · intro j
      simp
      
    · intro i j
      simp only [← smul_eq_mul, ← Pi.add_apply, ← Finₓ.coe_succ, ← Finₓ.coe_cast_succ, ← Pi.smul_apply]
      rw [Finset.sum_range_succ, add_commₓ, tsub_self, pow_zeroₓ, mul_oneₓ, Finset.mul_sum]
      congr 1
      refine' Finset.sum_congr rfl fun i' hi' => _
      rw [mul_left_commₓ (v 0), Nat.succ_subₓ, pow_succₓ]
      exact nat.lt_succ_iff.mp (finset.mem_range.mp hi')
      
    

theorem det_vandermonde_eq_zero_iff [IsDomain R] {n : ℕ} {v : Finₓ n → R} :
    det (vandermonde v) = 0 ↔ ∃ i j : Finₓ n, v i = v j ∧ i ≠ j := by
  constructor
  · simp only [← det_vandermonde v, ← Finset.prod_eq_zero_iff, ← sub_eq_zero, ← forall_exists_index]
    exact fun i _ j h₁ h₂ => ⟨j, i, h₂, (mem_Ioi.mp h₁).ne'⟩
    
  · simp only [← Ne.def, ← forall_exists_index, ← and_imp]
    refine' fun i j h₁ h₂ => Matrix.det_zero_of_row_eq h₂ (funext fun k => _)
    rw [vandermonde_apply, vandermonde_apply, h₁]
    

theorem det_vandermonde_ne_zero_iff [IsDomain R] {n : ℕ} {v : Finₓ n → R} :
    det (vandermonde v) ≠ 0 ↔ Function.Injective v := by
  simpa only [← det_vandermonde_eq_zero_iff, ← Ne.def, ← not_exists, ← not_and, ← not_not]

end Matrix

