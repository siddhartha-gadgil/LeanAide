/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.Associated
import Mathbin.Algebra.Regular.Basic
import Mathbin.LinearAlgebra.Matrix.MvPolynomial
import Mathbin.LinearAlgebra.Matrix.Polynomial
import Mathbin.RingTheory.Polynomial.Basic
import Mathbin.Tactic.Linarith.Default
import Mathbin.Tactic.RingExp

/-!
# Cramer's rule and adjugate matrices

The adjugate matrix is the transpose of the cofactor matrix.
It is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.update_column i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the determinants of each minor of `A`.
Instead of defining a minor to be `A` with row `i` and column `j` deleted, we
replace the `i`th row of `A` with the `j`th basis vector; this has the same
determinant as the minor but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`.

## Main definitions

 * `matrix.cramer A b`: the vector output by Cramer's rule on `A` and `b`.
 * `matrix.adjugate A`: the adjugate (or classical adjoint) of the matrix `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

cramer, cramer's rule, adjugate
-/


namespace Matrix

universe u v

variable {n : Type u} [DecidableEq n] [Fintype n] {α : Type v} [CommRingₓ α]

open Matrix BigOperators Polynomial

open Equivₓ Equivₓ.Perm Finset

section Cramer

/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramer_map`.
  After defining `cramer_map` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/


variable (A : Matrix n n α) (b : n → α)

/-- `cramer_map A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer_map A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer_map A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer_map` is well-defined but not necessarily useful.
-/
def cramerMap (i : n) : α :=
  (A.updateColumn i b).det

theorem cramer_map_is_linear (i : n) : IsLinearMap α fun b => cramerMap A b i :=
  { map_add := det_update_column_add _ _, map_smul := det_update_column_smul _ _ }

theorem cramer_is_linear : IsLinearMap α (cramerMap A) := by
  constructor <;> intros <;> ext i
  · apply (cramer_map_is_linear A i).1
    
  · apply (cramer_map_is_linear A i).2
    

/-- `cramer A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer` is well-defined but not necessarily useful.
 -/
def cramer (A : Matrix n n α) : (n → α) →ₗ[α] n → α :=
  IsLinearMap.mk' (cramerMap A) (cramer_is_linear A)

theorem cramer_apply (i : n) : cramer A b i = (A.updateColumn i b).det :=
  rfl

theorem cramer_transpose_apply (i : n) : cramer Aᵀ b i = (A.updateRow i b).det := by
  rw [cramer_apply, update_column_transpose, det_transpose]

theorem cramer_transpose_row_self (i : n) : Aᵀ.cramer (A i) = Pi.single i A.det := by
  ext j
  rw [cramer_apply, Pi.single_apply]
  split_ifs with h
  · -- i = j: this entry should be `A.det`
    subst h
    simp only [← update_column_transpose, ← det_transpose, ← update_row, ← Function.update_eq_self]
    
  · -- i ≠ j: this entry should be 0
    rw [update_column_transpose, det_transpose]
    apply det_zero_of_row_eq h
    rw [update_row_self, update_row_ne (Ne.symm h)]
    

theorem cramer_row_self (i : n) (h : ∀ j, b j = A j i) : A.cramer b = Pi.single i A.det := by
  rw [← transpose_transpose A, det_transpose]
  convert cramer_transpose_row_self Aᵀ i
  exact funext h

@[simp]
theorem cramer_one : cramer (1 : Matrix n n α) = 1 := by
  ext i j
  convert congr_fun (cramer_row_self (1 : Matrix n n α) (Pi.single i 1) i _) j
  · simp
    
  · intro j
    rw [Matrix.one_eq_pi_single, Pi.single_comm]
    

theorem cramer_smul (r : α) (A : Matrix n n α) : cramer (r • A) = r ^ (Fintype.card n - 1) • cramer A :=
  LinearMap.ext fun b => funext fun _ => det_update_column_smul' _ _ _ _

@[simp]
theorem cramer_subsingleton_apply [Subsingleton n] (A : Matrix n n α) (b : n → α) (i : n) : cramer A b i = b i := by
  rw [cramer_apply, det_eq_elem_of_subsingleton _ i, update_column_self]

theorem cramer_zero [Nontrivial n] : cramer (0 : Matrix n n α) = 0 := by
  ext i j
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  intro j''
  simp [← update_column_ne hj']

/-- Use linearity of `cramer` to take it out of a summation. -/
theorem sum_cramer {β} (s : Finset β) (f : β → n → α) : (∑ x in s, cramer A (f x)) = cramer A (∑ x in s, f x) :=
  (LinearMap.map_sum (cramer A)).symm

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
theorem sum_cramer_apply {β} (s : Finset β) (f : n → β → α) (i : n) :
    (∑ x in s, cramer A (fun j => f j x) i) = cramer A (fun j : n => ∑ x in s, f j x) i :=
  calc
    (∑ x in s, cramer A (fun j => f j x) i) = (∑ x in s, cramer A fun j => f j x) i := (Finset.sum_apply i s _).symm
    _ = cramer A (fun j : n => ∑ x in s, f j x) i := by
      rw [sum_cramer, cramer_apply]
      congr with j
      apply Finset.sum_apply
    

end Cramer

section Adjugate

/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring.
-/


/-- The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking the determinant of minors,
  i.e. the matrix with a row and column removed.
  However, the proof of `mul_adjugate` becomes a lot easier if we define the
  minor as replacing a column with a basis vector, since it allows us to use
  facts about the `cramer` map.
-/
def adjugate (A : Matrix n n α) : Matrix n n α := fun i => cramer Aᵀ (Pi.single i 1)

theorem adjugate_def (A : Matrix n n α) : adjugate A = fun i => cramer Aᵀ (Pi.single i 1) :=
  rfl

theorem adjugate_apply (A : Matrix n n α) (i j : n) : adjugate A i j = (A.updateRow j (Pi.single i 1)).det := by
  rw [adjugate_def]
  simp only
  rw [cramer_apply, update_column_transpose, det_transpose]

theorem adjugate_transpose (A : Matrix n n α) : (adjugate A)ᵀ = adjugate Aᵀ := by
  ext i j
  rw [transpose_apply, adjugate_apply, adjugate_apply, update_row_transpose, det_transpose]
  rw [det_apply', det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  by_cases' i = σ j
  · -- Everything except `(i , j)` (= `(σ j , j)`) is given by A, and the rest is a single `1`.
      congr <;>
      ext j'
    subst h
    have : σ j' = σ j ↔ j' = j := σ.injective.eq_iff
    rw [update_row_apply, update_column_apply]
    simp_rw [this]
    rw [← dite_eq_ite, ← dite_eq_ite]
    congr 1 with rfl
    rw [Pi.single_eq_same, Pi.single_eq_same]
    
  · -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : (∏ j' : n, update_column A j (Pi.single i 1) (σ j') j') = 0 := by
      apply prod_eq_zero (mem_univ j)
      rw [update_column_self, Pi.single_eq_of_ne' h]
    rw [this]
    apply prod_eq_zero (mem_univ (σ⁻¹ i))
    erw [apply_symm_apply σ i, update_row_self]
    apply Pi.single_eq_of_ne
    intro h'
    exact h ((symm_apply_eq σ).mp h')
    

/-- Since the map `b ↦ cramer A b` is linear in `b`, it must be multiplication by some matrix. This
matrix is `A.adjugate`. -/
theorem cramer_eq_adjugate_mul_vec (A : Matrix n n α) (b : n → α) : cramer A b = A.adjugate.mulVec b := by
  nth_rw 1[← A.transpose_transpose]
  rw [← adjugate_transpose, adjugate_def]
  have : b = ∑ i, b i • Pi.single i 1 := by
    refine' (pi_eq_sum_univ b).trans _
    congr with j
    simp [← Pi.single_apply, ← eq_comm]
  nth_rw 0[this]
  ext k
  simp [← mul_vec, ← dot_product, ← mul_comm]

theorem mul_adjugate_apply (A : Matrix n n α) (i j k) : A i k * adjugate A k j = cramer Aᵀ (Pi.single k (A i k)) j := by
  erw [← smul_eq_mul, ← Pi.smul_apply, ← LinearMap.map_smul, ← Pi.single_smul', smul_eq_mul, mul_oneₓ]

theorem mul_adjugate (A : Matrix n n α) : A ⬝ adjugate A = A.det • 1 := by
  ext i j
  rw [mul_apply, Pi.smul_apply, Pi.smul_apply, one_apply, smul_eq_mul, mul_boole]
  simp [← mul_adjugate_apply, ← sum_cramer_apply, ← cramer_transpose_row_self, ← Pi.single_apply, ← eq_comm]

theorem adjugate_mul (A : Matrix n n α) : adjugate A ⬝ A = A.det • 1 :=
  calc
    adjugate A ⬝ A = (Aᵀ ⬝ adjugate Aᵀ)ᵀ := by
      rw [← adjugate_transpose, ← transpose_mul, transpose_transpose]
    _ = A.det • 1 := by
      rw [mul_adjugate Aᵀ, det_transpose, transpose_smul, transpose_one]
    

theorem adjugate_smul (r : α) (A : Matrix n n α) : adjugate (r • A) = r ^ (Fintype.card n - 1) • adjugate A := by
  rw [adjugate, adjugate, transpose_smul, cramer_smul]
  rfl

/-- A stronger form of **Cramer's rule** that allows us to solve some instances of `A ⬝ x = b` even
if the determinant is not a unit. A sufficient (but still not necessary) condition is that `A.det`
divides `b`. -/
@[simp]
theorem mul_vec_cramer (A : Matrix n n α) (b : n → α) : A.mulVec (cramer A b) = A.det • b := by
  rw [cramer_eq_adjugate_mul_vec, mul_vec_mul_vec, mul_adjugate, smul_mul_vec_assoc, one_mul_vec]

theorem adjugate_subsingleton [Subsingleton n] (A : Matrix n n α) : adjugate A = 1 := by
  ext i j
  simp [← Subsingleton.elimₓ i j, ← adjugate_apply, ← det_eq_elem_of_subsingleton _ i]

theorem adjugate_eq_one_of_card_eq_one {A : Matrix n n α} (h : Fintype.card n = 1) : adjugate A = 1 := by
  have : Subsingleton n := fintype.card_le_one_iff_subsingleton.mp h.le
  exact adjugate_subsingleton _

@[simp]
theorem adjugate_zero [Nontrivial n] : adjugate (0 : Matrix n n α) = 0 := by
  ext i j
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  intro j''
  simp [← update_column_ne hj']

@[simp]
theorem adjugate_one : adjugate (1 : Matrix n n α) = 1 := by
  ext
  simp [← adjugate_def, ← Matrix.one_apply, ← Pi.single_apply, ← eq_comm]

@[simp]
theorem adjugate_diagonal (v : n → α) : adjugate (diagonalₓ v) = diagonalₓ fun i => ∏ j in Finset.univ.erase i, v j :=
  by
  ext
  simp only [← adjugate_def, ← cramer_apply, ← diagonal_transpose]
  obtain rfl | hij := eq_or_ne i j
  · rw [diagonal_apply_eq, diagonal_update_column_single, det_diagonal, prod_update_of_mem (Finset.mem_univ _),
      sdiff_singleton_eq_erase, one_mulₓ]
    
  · rw [diagonal_apply_ne _ hij]
    refine' det_eq_zero_of_row_eq_zero j fun k => _
    obtain rfl | hjk := eq_or_ne k j
    · rw [update_column_self, Pi.single_eq_of_ne' hij]
      
    · rw [update_column_ne hjk, diagonal_apply_ne' _ hjk]
      
    

theorem _root_.ring_hom.map_adjugate {R S : Type _} [CommRingₓ R] [CommRingₓ S] (f : R →+* S) (M : Matrix n n R) :
    f.mapMatrix M.adjugate = Matrix.adjugate (f.mapMatrix M) := by
  ext i k
  have : Pi.single i (1 : S) = f ∘ Pi.single i 1 := by
    rw [← f.map_one]
    exact Pi.single_op (fun i => f) (fun i => f.map_zero) i (1 : R)
  rw [adjugate_apply, RingHom.map_matrix_apply, map_apply, RingHom.map_matrix_apply, this, ← map_update_row, ←
    RingHom.map_matrix_apply, ← RingHom.map_det, ← adjugate_apply]

theorem _root_.alg_hom.map_adjugate {R A B : Type _} [CommSemiringₓ R] [CommRingₓ A] [CommRingₓ B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (M : Matrix n n A) : f.mapMatrix M.adjugate = Matrix.adjugate (f.mapMatrix M) :=
  f.toRingHom.map_adjugate _

theorem det_adjugate (A : Matrix n n α) : (adjugate A).det = A.det ^ (Fintype.card n - 1) := by
  -- get rid of the `- 1`
  cases' (Fintype.card n).eq_zero_or_pos with h_card h_card
  · have : IsEmpty n := fintype.card_eq_zero_iff.mp h_card
    rw [h_card, Nat.zero_sub, pow_zeroₓ, adjugate_subsingleton, det_one]
    
  replace h_card := tsub_add_cancel_of_le h_card.nat_succ_le
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mv_polynomial_X n n ℤ
  suffices A'.adjugate.det = A'.det ^ (Fintype.card n - 1) by
    rw [← mv_polynomial_X_map_matrix_aeval ℤ A, ← AlgHom.map_adjugate, ← AlgHom.map_det, ← AlgHom.map_det, ←
      AlgHom.map_pow, this]
  apply mul_left_cancel₀ (show A'.det ≠ 0 from det_mv_polynomial_X_ne_zero n ℤ)
  calc A'.det * A'.adjugate.det = (A' ⬝ adjugate A').det := (det_mul _ _).symm _ = A'.det ^ Fintype.card n := by
      rw [mul_adjugate, det_smul, det_one, mul_oneₓ]_ = A'.det * A'.det ^ (Fintype.card n - 1) := by
      rw [← pow_succₓ, h_card]

@[simp]
theorem adjugate_fin_zero (A : Matrix (Finₓ 0) (Finₓ 0) α) : adjugate A = 0 :=
  @Subsingleton.elimₓ _ Matrix.subsingleton_of_empty_left _ _

@[simp]
theorem adjugate_fin_one (A : Matrix (Finₓ 1) (Finₓ 1) α) : adjugate A = 1 :=
  adjugate_subsingleton A

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem adjugate_fin_two (A : Matrix (Finₓ 2) (Finₓ 2) α) :
    adjugate A =
      «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  by
  ext i j
  rw [adjugate_apply, det_fin_two]
  fin_cases i with [0, 1] <;>
    fin_cases j with [0, 1] <;>
      simp only [← Nat.one_ne_zero, ← one_mulₓ, ← Finₓ.one_eq_zero_iff, ← Pi.single_eq_same, ← zero_mul, ←
        Finₓ.zero_eq_one_iff, ← sub_zero, ← Pi.single_eq_of_ne, ← Ne.def, ← not_false_iff, ← update_row_self, ←
        update_row_ne, ← cons_val_zero, ← mul_zero, ← mul_oneₓ, ← zero_sub, ← cons_val_one, ← head_cons, ← of_apply]

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
@[simp]
theorem adjugate_fin_two_of (a b c d : α) :
    adjugate
        («expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation") =
      «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  adjugate_fin_two _

theorem adjugate_conj_transpose [StarRing α] (A : Matrix n n α) : A.adjugateᴴ = adjugate Aᴴ := by
  dsimp' only [← conj_transpose]
  have : Aᵀ.adjugate.map star = adjugate (Aᵀ.map star) := (starRingEnd α).map_adjugate Aᵀ
  rw [A.adjugate_transpose, this]

theorem is_regular_of_is_left_regular_det {A : Matrix n n α} (hA : IsLeftRegular A.det) : IsRegular A := by
  constructor
  · intro B C h
    refine' hA.matrix _
    rw [← Matrix.one_mul B, ← Matrix.one_mul C, ← Matrix.smul_mul, ← Matrix.smul_mul, ← adjugate_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, ← mul_eq_mul A, h, mul_eq_mul]
    
  · intro B C h
    simp only [← mul_eq_mul] at h
    refine' hA.matrix _
    rw [← Matrix.mul_one B, ← Matrix.mul_one C, ← Matrix.mul_smul, ← Matrix.mul_smul, ← mul_adjugate, ←
      Matrix.mul_assoc, ← Matrix.mul_assoc, h]
    

theorem adjugate_mul_distrib_aux (A B : Matrix n n α) (hA : IsLeftRegular A.det) (hB : IsLeftRegular B.det) :
    adjugate (A ⬝ B) = adjugate B ⬝ adjugate A := by
  have hAB : IsLeftRegular (A ⬝ B).det := by
    rw [det_mul]
    exact hA.mul hB
  refine' (is_regular_of_is_left_regular_det hAB).left _
  rw [mul_eq_mul, mul_adjugate, mul_eq_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B, mul_adjugate, smul_mul,
    Matrix.one_mul, mul_smul, mul_adjugate, smul_smul, mul_comm, ← det_mul]

/-- Proof follows from "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3
-/
theorem adjugate_mul_distrib (A B : Matrix n n α) : adjugate (A ⬝ B) = adjugate B ⬝ adjugate A := by
  let g : Matrix n n α → Matrix n n α[X] := fun M => M.map Polynomial.c + (Polynomial.x : α[X]) • 1
  let f' : Matrix n n α[X] →+* Matrix n n α := (Polynomial.evalRingHom 0).mapMatrix
  have f'_inv : ∀ M, f' (g M) = M := by
    intro
    ext
    simp [← f', ← g]
  have f'_adj : ∀ M : Matrix n n α, f' (adjugate (g M)) = adjugate M := by
    intro
    rw [RingHom.map_adjugate, f'_inv]
  have f'_g_mul : ∀ M N : Matrix n n α, f' (g M ⬝ g N) = M ⬝ N := by
    intros
    rw [← mul_eq_mul, RingHom.map_mul, f'_inv, f'_inv, mul_eq_mul]
  have hu : ∀ M : Matrix n n α, IsRegular (g M).det := by
    intro M
    refine' Polynomial.Monic.is_regular _
    simp only [← g, ← Polynomial.Monic.def, Polynomial.leading_coeff_det_X_one_add_C M, ← add_commₓ]
  rw [← f'_adj, ← f'_adj, ← f'_adj, ← mul_eq_mul (f' (adjugate (g B))), ← f'.map_mul, mul_eq_mul, ←
    adjugate_mul_distrib_aux _ _ (hu A).left (hu B).left, RingHom.map_adjugate, RingHom.map_adjugate, f'_inv, f'_g_mul]

@[simp]
theorem adjugate_pow (A : Matrix n n α) (k : ℕ) : adjugate (A ^ k) = adjugate A ^ k := by
  induction' k with k IH
  · simp
    
  · rw [pow_succ'ₓ, mul_eq_mul, adjugate_mul_distrib, IH, ← mul_eq_mul, pow_succₓ]
    

theorem det_smul_adjugate_adjugate (A : Matrix n n α) :
    det A • adjugate (adjugate A) = det A ^ (Fintype.card n - 1) • A := by
  have : A ⬝ (A.adjugate ⬝ A.adjugate.adjugate) = A ⬝ (A.det ^ (Fintype.card n - 1) • 1) := by
    rw [← adjugate_mul_distrib, adjugate_mul, adjugate_smul, adjugate_one]
  rwa [← Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at this

/-- Note that this is not true for `fintype.card n = 1` since `1 - 2 = 0` and not `-1`. -/
theorem adjugate_adjugate (A : Matrix n n α) (h : Fintype.card n ≠ 1) :
    adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A := by
  -- get rid of the `- 2`
  cases' h_card : Fintype.card n with n'
  · have : IsEmpty n := fintype.card_eq_zero_iff.mp h_card
    exact @Subsingleton.elimₓ _ Matrix.subsingleton_of_empty_left _ _
    
  cases n'
  · exact (h h_card).elim
    
  rw [← h_card]
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mv_polynomial_X n n ℤ
  suffices adjugate (adjugate A') = det A' ^ (Fintype.card n - 2) • A' by
    rw [← mv_polynomial_X_map_matrix_aeval ℤ A, ← AlgHom.map_adjugate, ← AlgHom.map_adjugate, this, ← AlgHom.map_det, ←
      AlgHom.map_pow, AlgHom.map_matrix_apply, AlgHom.map_matrix_apply, Matrix.map_smul' _ _ _ (_root_.map_mul _)]
  have h_card' : Fintype.card n - 2 + 1 = Fintype.card n - 1 := by
    simp [← h_card]
  have is_reg : IsSmulRegular (MvPolynomial (n × n) ℤ) (det A') := fun x y =>
    mul_left_cancel₀ (det_mv_polynomial_X_ne_zero n ℤ)
  apply is_reg.matrix
  rw [smul_smul, ← pow_succₓ, h_card', det_smul_adjugate_adjugate]

/-- A weaker version of `matrix.adjugate_adjugate` that uses `nontrivial`. -/
theorem adjugate_adjugate' (A : Matrix n n α) [Nontrivial n] :
    adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A :=
  adjugate_adjugate _ <| Fintype.one_lt_card.ne'

end Adjugate

end Matrix

