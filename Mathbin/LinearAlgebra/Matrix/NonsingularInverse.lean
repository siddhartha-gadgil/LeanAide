/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baanen, Lu-Ming Zhang
-/
import Mathbin.Algebra.Regular.Smul
import Mathbin.LinearAlgebra.Matrix.Adjugate
import Mathbin.LinearAlgebra.Matrix.Polynomial

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible determinant.

For matrices that are not square or not of full rank, there is a more general notion of
pseudoinverses which we do not consider here.

The definition of inverse used in this file is the adjugate divided by the determinant.
We show that dividing the adjugate by `det A` (if possible), giving a matrix `A⁻¹` (`nonsing_inv`),
will result in a multiplicative inverse to `A`.

Note that there are at least three different inverses in mathlib:

* `A⁻¹` (`has_inv.inv`): alone, this satisfies no properties, although it is usually used in
  conjunction with `group` or `group_with_zero`. On matrices, this is defined to be zero when no
  inverse exists.
* `⅟A` (`inv_of`): this is only available in the presence of `[invertible A]`, which guarantees an
  inverse exists.
* `ring.inverse A`: this is defined on any `monoid_with_zero`, and just like `⁻¹` on matrices, is
  defined to be zero when no inverse exists.

We start by working with `invertible`, and show the main results:

* `matrix.invertible_of_det_invertible`
* `matrix.det_invertible_of_invertible`
* `matrix.is_unit_iff_is_unit_det`
* `matrix.mul_eq_one_comm`

After this we define `matrix.has_inv` and show it matches `⅟A` and `ring.inverse A`.
The rest of the results in the file are then about `A⁻¹`

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/


namespace Matrix

universe u u' v

variable {m : Type u} {n : Type u'} {α : Type v}

open Matrix BigOperators

open Equivₓ Equivₓ.Perm Finset

/-! ### Matrices are `invertible` iff their determinants are -/


section Invertible

variable [Fintype n] [DecidableEq n] [CommRingₓ α]

/-- A copy of `inv_of_mul_self` using `⬝` not `*`. -/
protected theorem inv_of_mul_self (A : Matrix n n α) [Invertible A] : ⅟ A ⬝ A = 1 :=
  inv_of_mul_self A

/-- A copy of `mul_inv_of_self` using `⬝` not `*`. -/
protected theorem mul_inv_of_self (A : Matrix n n α) [Invertible A] : A ⬝ ⅟ A = 1 :=
  mul_inv_of_self A

/-- A copy of `inv_of_mul_self_assoc` using `⬝` not `*`. -/
protected theorem inv_of_mul_self_assoc (A : Matrix n n α) (B : Matrix n m α) [Invertible A] : ⅟ A ⬝ (A ⬝ B) = B := by
  rw [← Matrix.mul_assoc, Matrix.inv_of_mul_self, Matrix.one_mul]

/-- A copy of `mul_inv_of_self_assoc` using `⬝` not `*`. -/
protected theorem mul_inv_of_self_assoc (A : Matrix n n α) (B : Matrix n m α) [Invertible A] : A ⬝ (⅟ A ⬝ B) = B := by
  rw [← Matrix.mul_assoc, Matrix.mul_inv_of_self, Matrix.one_mul]

/-- A copy of `mul_inv_of_mul_self_cancel` using `⬝` not `*`. -/
protected theorem mul_inv_of_mul_self_cancel (A : Matrix m n α) (B : Matrix n n α) [Invertible B] : A ⬝ ⅟ B ⬝ B = A :=
  by
  rw [Matrix.mul_assoc, Matrix.inv_of_mul_self, Matrix.mul_one]

/-- A copy of `mul_mul_inv_of_self_cancel` using `⬝` not `*`. -/
protected theorem mul_mul_inv_of_self_cancel (A : Matrix m n α) (B : Matrix n n α) [Invertible B] : A ⬝ B ⬝ ⅟ B = A :=
  by
  rw [Matrix.mul_assoc, Matrix.mul_inv_of_self, Matrix.mul_one]

variable (A : Matrix n n α) (B : Matrix n n α)

/-- If `A.det` has a constructive inverse, produce one for `A`. -/
def invertibleOfDetInvertible [Invertible A.det] : Invertible A where
  invOf := ⅟ A.det • A.adjugate
  mul_inv_of_self := by
    rw [mul_smul_comm, Matrix.mul_eq_mul, mul_adjugate, smul_smul, inv_of_mul_self, one_smul]
  inv_of_mul_self := by
    rw [smul_mul_assoc, Matrix.mul_eq_mul, adjugate_mul, smul_smul, inv_of_mul_self, one_smul]

theorem inv_of_eq [Invertible A.det] [Invertible A] : ⅟ A = ⅟ A.det • A.adjugate := by
  let this := invertible_of_det_invertible A
  convert (rfl : ⅟ A = _)

/-- `A.det` is invertible if `A` has a left inverse. -/
def detInvertibleOfLeftInverse (h : B ⬝ A = 1) : Invertible A.det where
  invOf := B.det
  mul_inv_of_self := by
    rw [mul_comm, ← det_mul, h, det_one]
  inv_of_mul_self := by
    rw [← det_mul, h, det_one]

/-- `A.det` is invertible if `A` has a right inverse. -/
def detInvertibleOfRightInverse (h : A ⬝ B = 1) : Invertible A.det where
  invOf := B.det
  mul_inv_of_self := by
    rw [← det_mul, h, det_one]
  inv_of_mul_self := by
    rw [mul_comm, ← det_mul, h, det_one]

/-- If `A` has a constructive inverse, produce one for `A.det`. -/
def detInvertibleOfInvertible [Invertible A] : Invertible A.det :=
  detInvertibleOfLeftInverse A (⅟ A) (inv_of_mul_self _)

theorem det_inv_of [Invertible A] [Invertible A.det] : (⅟ A).det = ⅟ A.det := by
  let this := det_invertible_of_invertible A
  convert (rfl : _ = ⅟ A.det)

/-- Together `matrix.det_invertible_of_invertible` and `matrix.invertible_of_det_invertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def invertibleEquivDetInvertible : Invertible A ≃ Invertible A.det where
  toFun := @detInvertibleOfInvertible _ _ _ _ _ A
  invFun := @invertibleOfDetInvertible _ _ _ _ _ A
  left_inv := fun _ => Subsingleton.elimₓ _ _
  right_inv := fun _ => Subsingleton.elimₓ _ _

variable {A B}

theorem mul_eq_one_comm : A ⬝ B = 1 ↔ B ⬝ A = 1 :=
  suffices ∀ A B, A ⬝ B = 1 → B ⬝ A = 1 from ⟨this A B, this B A⟩
  fun A B h => by
  let this : Invertible B.det := det_invertible_of_left_inverse _ _ h
  let this : Invertible B := invertible_of_det_invertible B
  calc B ⬝ A = B ⬝ A ⬝ (B ⬝ ⅟ B) := by
      rw [Matrix.mul_inv_of_self, Matrix.mul_one]_ = B ⬝ (A ⬝ B ⬝ ⅟ B) := by
      simp only [← Matrix.mul_assoc]_ = B ⬝ ⅟ B := by
      rw [h, Matrix.one_mul]_ = 1 := Matrix.mul_inv_of_self B

variable (A B)

/-- We can construct an instance of invertible A if A has a left inverse. -/
def invertibleOfLeftInverse (h : B ⬝ A = 1) : Invertible A :=
  ⟨B, h, mul_eq_one_comm.mp h⟩

/-- We can construct an instance of invertible A if A has a right inverse. -/
def invertibleOfRightInverse (h : A ⬝ B = 1) : Invertible A :=
  ⟨B, mul_eq_one_comm.mp h, h⟩

/-- Given a proof that `A.det` has a constructive inverse, lift `A` to `(matrix n n α)ˣ`-/
def unitOfDetInvertible [Invertible A.det] : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ A (invertibleOfDetInvertible A)

/-- When lowered to a prop, `matrix.invertible_equiv_det_invertible` forms an `iff`. -/
theorem is_unit_iff_is_unit_det : IsUnit A ↔ IsUnit A.det := by
  simp only [nonempty_invertible_iff_is_unit, ← (invertible_equiv_det_invertible A).nonempty_congr]

/-! #### Variants of the statements above with `is_unit`-/


theorem is_unit_det_of_invertible [Invertible A] : IsUnit A.det :=
  @is_unit_of_invertible _ _ _ (detInvertibleOfInvertible A)

variable {A B}

theorem is_unit_det_of_left_inverse (h : B ⬝ A = 1) : IsUnit A.det :=
  @is_unit_of_invertible _ _ _ (detInvertibleOfLeftInverse _ _ h)

theorem is_unit_det_of_right_inverse (h : A ⬝ B = 1) : IsUnit A.det :=
  @is_unit_of_invertible _ _ _ (detInvertibleOfRightInverse _ _ h)

theorem det_ne_zero_of_left_inverse [Nontrivial α] (h : B ⬝ A = 1) : A.det ≠ 0 :=
  (is_unit_det_of_left_inverse h).ne_zero

theorem det_ne_zero_of_right_inverse [Nontrivial α] (h : A ⬝ B = 1) : A.det ≠ 0 :=
  (is_unit_det_of_right_inverse h).ne_zero

end Invertible

variable [Fintype n] [DecidableEq n] [CommRingₓ α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem is_unit_det_transpose (h : IsUnit A.det) : IsUnit Aᵀ.det := by
  rw [det_transpose]
  exact h

/-! ### A noncomputable `has_inv` instance  -/


/-- The inverse of a square matrix, when it is invertible (and zero otherwise).-/
noncomputable instance : Inv (Matrix n n α) :=
  ⟨fun A => Ring.inverse A.det • A.adjugate⟩

theorem inv_def (A : Matrix n n α) : A⁻¹ = Ring.inverse A.det • A.adjugate :=
  rfl

theorem nonsing_inv_apply_not_is_unit (h : ¬IsUnit A.det) : A⁻¹ = 0 := by
  rw [inv_def, Ring.inverse_non_unit _ h, zero_smul]

theorem nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (↑h.Unit⁻¹ : α) • A.adjugate := by
  rw [inv_def, ← Ring.inverse_unit h.unit, IsUnit.unit_spec]

/-- The nonsingular inverse is the same as `inv_of` when `A` is invertible. -/
@[simp]
theorem inv_of_eq_nonsing_inv [Invertible A] : ⅟ A = A⁻¹ := by
  let this := det_invertible_of_invertible A
  rw [inv_def, Ringₓ.inverse_invertible, inv_of_eq]

/-- Coercing the result of `units.has_inv` is the same as coercing first and applying the
nonsingular inverse. -/
@[simp, norm_cast]
theorem coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ : Matrix n n α) := by
  let this := A.invertible
  rw [← inv_of_eq_nonsing_inv, inv_of_units]

/-- The nonsingular inverse is the same as the general `ring.inverse`. -/
theorem nonsing_inv_eq_ring_inverse : A⁻¹ = Ring.inverse A := by
  by_cases' h_det : IsUnit A.det
  · cases (A.is_unit_iff_is_unit_det.mpr h_det).nonempty_invertible
    rw [← inv_of_eq_nonsing_inv, Ringₓ.inverse_invertible]
    
  · have h := mt A.is_unit_iff_is_unit_det.mp h_det
    rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_is_unit A h_det]
    

theorem transpose_nonsing_inv : A⁻¹ᵀ = Aᵀ⁻¹ := by
  rw [inv_def, inv_def, transpose_smul, det_transpose, adjugate_transpose]

theorem conj_transpose_nonsing_inv [StarRing α] : A⁻¹ᴴ = Aᴴ⁻¹ := by
  rw [inv_def, inv_def, conj_transpose_smul, det_conj_transpose, adjugate_conj_transpose, Ringₓ.inverse_star]

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp]
theorem mul_nonsing_inv (h : IsUnit A.det) : A ⬝ A⁻¹ = 1 := by
  cases (A.is_unit_iff_is_unit_det.mpr h).nonempty_invertible
  rw [← inv_of_eq_nonsing_inv, Matrix.mul_inv_of_self]

/-- The `nonsing_inv` of `A` is a left inverse. -/
@[simp]
theorem nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ ⬝ A = 1 := by
  cases (A.is_unit_iff_is_unit_det.mpr h).nonempty_invertible
  rw [← inv_of_eq_nonsing_inv, Matrix.inv_of_mul_self]

@[simp]
theorem mul_nonsing_inv_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B ⬝ A ⬝ A⁻¹ = B := by
  simp [← Matrix.mul_assoc, ← mul_nonsing_inv A h]

@[simp]
theorem mul_nonsing_inv_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A ⬝ (A⁻¹ ⬝ B) = B := by
  simp [Matrix.mul_assoc, ← mul_nonsing_inv A h]

@[simp]
theorem nonsing_inv_mul_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B ⬝ A⁻¹ ⬝ A = B := by
  simp [← Matrix.mul_assoc, ← nonsing_inv_mul A h]

@[simp]
theorem nonsing_inv_mul_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A⁻¹ ⬝ (A ⬝ B) = B := by
  simp [Matrix.mul_assoc, ← nonsing_inv_mul A h]

@[simp]
theorem mul_inv_of_invertible [Invertible A] : A ⬝ A⁻¹ = 1 :=
  mul_nonsing_inv A (is_unit_det_of_invertible A)

@[simp]
theorem inv_mul_of_invertible [Invertible A] : A⁻¹ ⬝ A = 1 :=
  nonsing_inv_mul A (is_unit_det_of_invertible A)

@[simp]
theorem mul_inv_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B ⬝ A ⬝ A⁻¹ = B :=
  mul_nonsing_inv_cancel_right A B (is_unit_det_of_invertible A)

@[simp]
theorem mul_inv_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A ⬝ (A⁻¹ ⬝ B) = B :=
  mul_nonsing_inv_cancel_left A B (is_unit_det_of_invertible A)

@[simp]
theorem inv_mul_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B ⬝ A⁻¹ ⬝ A = B :=
  nonsing_inv_mul_cancel_right A B (is_unit_det_of_invertible A)

@[simp]
theorem inv_mul_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A⁻¹ ⬝ (A ⬝ B) = B :=
  nonsing_inv_mul_cancel_left A B (is_unit_det_of_invertible A)

theorem nonsing_inv_cancel_or_zero : A⁻¹ ⬝ A = 1 ∧ A ⬝ A⁻¹ = 1 ∨ A⁻¹ = 0 := by
  by_cases' h : IsUnit A.det
  · exact Or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩
    
  · exact Or.inr (nonsing_inv_apply_not_is_unit _ h)
    

theorem det_nonsing_inv_mul_det (h : IsUnit A.det) : A⁻¹.det * A.det = 1 := by
  rw [← det_mul, A.nonsing_inv_mul h, det_one]

@[simp]
theorem det_nonsing_inv : A⁻¹.det = Ring.inverse A.det := by
  by_cases' h : IsUnit A.det
  · cases h.nonempty_invertible
    let this := invertible_of_det_invertible A
    rw [Ringₓ.inverse_invertible, ← inv_of_eq_nonsing_inv, det_inv_of]
    
  cases is_empty_or_nonempty n
  · rw [det_is_empty, det_is_empty, Ring.inverse_one]
    
  · rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_is_unit _ h, det_zero ‹_›]
    

theorem is_unit_nonsing_inv_det (h : IsUnit A.det) : IsUnit A⁻¹.det :=
  is_unit_of_mul_eq_one _ _ (A.det_nonsing_inv_mul_det h)

@[simp]
theorem nonsing_inv_nonsing_inv (h : IsUnit A.det) : A⁻¹⁻¹ = A :=
  calc
    A⁻¹⁻¹ = 1 ⬝ A⁻¹⁻¹ := by
      rw [Matrix.one_mul]
    _ = A ⬝ A⁻¹ ⬝ A⁻¹⁻¹ := by
      rw [A.mul_nonsing_inv h]
    _ = A := by
      rw [Matrix.mul_assoc, A⁻¹.mul_nonsing_inv (A.is_unit_nonsing_inv_det h), Matrix.mul_one]
    

theorem is_unit_nonsing_inv_det_iff {A : Matrix n n α} : IsUnit A⁻¹.det ↔ IsUnit A.det := by
  rw [Matrix.det_nonsing_inv, is_unit_ring_inverse]

/-- A version of `matrix.invertible_of_det_invertible` with the inverse defeq to `A⁻¹` that is
therefore noncomputable. -/
-- `is_unit.invertible` lifts the proposition `is_unit A` to a constructive inverse of `A`.
noncomputable def invertibleOfIsUnitDet (h : IsUnit A.det) : Invertible A :=
  ⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

/-- A version of `matrix.units_of_det_invertible` with the inverse defeq to `A⁻¹` that is therefore
noncomputable. -/
noncomputable def nonsingInvUnit (h : IsUnit A.det) : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ _ (invertibleOfIsUnitDet A h)

theorem unit_of_det_invertible_eq_nonsing_inv_unit [Invertible A.det] :
    unitOfDetInvertible A = nonsingInvUnit A (is_unit_of_invertible _) := by
  ext
  rfl

variable {A} {B}

/-- If matrix A is left invertible, then its inverse equals its left inverse. -/
theorem inv_eq_left_inv (h : B ⬝ A = 1) : A⁻¹ = B := by
  let this := invertible_of_left_inverse _ _ h
  exact inv_of_eq_nonsing_inv A ▸ inv_of_eq_left_inv h

/-- If matrix A is right invertible, then its inverse equals its right inverse. -/
theorem inv_eq_right_inv (h : A ⬝ B = 1) : A⁻¹ = B :=
  inv_eq_left_inv (mul_eq_one_comm.2 h)

section InvEqInv

variable {C : Matrix n n α}

/-- The left inverse of matrix A is unique when existing. -/
theorem left_inv_eq_left_inv (h : B ⬝ A = 1) (g : C ⬝ A = 1) : B = C := by
  rw [← inv_eq_left_inv h, ← inv_eq_left_inv g]

/-- The right inverse of matrix A is unique when existing. -/
theorem right_inv_eq_right_inv (h : A ⬝ B = 1) (g : A ⬝ C = 1) : B = C := by
  rw [← inv_eq_right_inv h, ← inv_eq_right_inv g]

/-- The right inverse of matrix A equals the left inverse of A when they exist. -/
theorem right_inv_eq_left_inv (h : A ⬝ B = 1) (g : C ⬝ A = 1) : B = C := by
  rw [← inv_eq_right_inv h, ← inv_eq_left_inv g]

theorem inv_inj (h : A⁻¹ = B⁻¹) (h' : IsUnit A.det) : A = B := by
  refine' left_inv_eq_left_inv (mul_nonsing_inv _ h') _
  rw [h]
  refine' mul_nonsing_inv _ _
  rwa [← is_unit_nonsing_inv_det_iff, ← h, is_unit_nonsing_inv_det_iff]

end InvEqInv

variable (A)

@[simp]
theorem inv_zero : (0 : Matrix n n α)⁻¹ = 0 := by
  cases' subsingleton_or_nontrivial α with ht ht
  · simp
    
  cases' (Fintype.card n).zero_le.eq_or_lt with hc hc
  · rw [eq_comm, Fintype.card_eq_zero_iff] at hc
    have := hc
    ext i
    exact (IsEmpty.false i).elim
    
  · have hn : Nonempty n := fintype.card_pos_iff.mp hc
    refine' nonsing_inv_apply_not_is_unit _ _
    simp [← hn]
    

@[simp]
theorem inv_one : (1 : Matrix n n α)⁻¹ = 1 :=
  inv_eq_left_inv
    (by
      simp )

theorem inv_smul (k : α) [Invertible k] (h : IsUnit A.det) : (k • A)⁻¹ = ⅟ k • A⁻¹ :=
  inv_eq_left_inv
    (by
      simp [← h, ← smul_smul])

theorem inv_smul' (k : αˣ) (h : IsUnit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹ :=
  inv_eq_left_inv
    (by
      simp [← h, ← smul_smul])

theorem inv_adjugate (A : Matrix n n α) (h : IsUnit A.det) : (adjugate A)⁻¹ = h.Unit⁻¹ • A := by
  refine' inv_eq_left_inv _
  rw [smul_mul, mul_adjugate, Units.smul_def, smul_smul, h.coe_inv_mul, one_smul]

/-- `diagonal v` is invertible if `v` is -/
def diagonalInvertible {α} [NonAssocSemiringₓ α] (v : n → α) [Invertible v] : Invertible (diagonalₓ v) :=
  Invertible.map (diagonalRingHom n α) v

theorem inv_of_diagonal_eq {α} [Semiringₓ α] (v : n → α) [Invertible v] [Invertible (diagonalₓ v)] :
    ⅟ (diagonalₓ v) = diagonalₓ (⅟ v) := by
  let this := diagonal_invertible v
  convert (rfl : ⅟ (diagonal v) = _)

/-- `v` is invertible if `diagonal v` is -/
def invertibleOfDiagonalInvertible (v : n → α) [Invertible (diagonalₓ v)] : Invertible v where
  invOf := diag (⅟ (diagonalₓ v))
  inv_of_mul_self :=
    funext fun i => by
      let this : Invertible (diagonal v).det := det_invertible_of_invertible _
      rw [inv_of_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      dsimp'
      rw [mul_assoc, prod_erase_mul _ _ (Finset.mem_univ _), ← det_diagonal]
      exact mul_inv_of_self _
  mul_inv_of_self :=
    funext fun i => by
      let this : Invertible (diagonal v).det := det_invertible_of_invertible _
      rw [inv_of_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      dsimp'
      rw [mul_left_commₓ, mul_prod_erase _ _ (Finset.mem_univ _), ← det_diagonal]
      exact mul_inv_of_self _

/-- Together `matrix.diagonal_invertible` and `matrix.invertible_of_diagonal_invertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def diagonalInvertibleEquivInvertible (v : n → α) : Invertible (diagonalₓ v) ≃ Invertible v where
  toFun := @invertibleOfDiagonalInvertible _ _ _ _ _ _
  invFun := @diagonalInvertible _ _ _ _ _ _
  left_inv := fun _ => Subsingleton.elimₓ _ _
  right_inv := fun _ => Subsingleton.elimₓ _ _

/-- When lowered to a prop, `matrix.diagonal_invertible_equiv_invertible` forms an `iff`. -/
@[simp]
theorem is_unit_diagonal {v : n → α} : IsUnit (diagonalₓ v) ↔ IsUnit v := by
  simp only [nonempty_invertible_iff_is_unit, ← (diagonal_invertible_equiv_invertible v).nonempty_congr]

theorem inv_diagonal (v : n → α) : (diagonalₓ v)⁻¹ = diagonalₓ (Ring.inverse v) := by
  rw [nonsing_inv_eq_ring_inverse]
  by_cases' h : IsUnit v
  · have := is_unit_diagonal.mpr h
    cases this.nonempty_invertible
    cases h.nonempty_invertible
    rw [Ringₓ.inverse_invertible, Ringₓ.inverse_invertible, inv_of_diagonal_eq]
    
  · have := is_unit_diagonal.not.mpr h
    rw [Ring.inverse_non_unit _ h, Pi.zero_def, diagonal_zero, Ring.inverse_non_unit _ this]
    

@[simp]
theorem inv_inv_inv (A : Matrix n n α) : A⁻¹⁻¹⁻¹ = A⁻¹ := by
  by_cases' h : IsUnit A.det
  · rw [nonsing_inv_nonsing_inv _ h]
    
  · simp [← nonsing_inv_apply_not_is_unit _ h]
    

theorem mul_inv_rev (A B : Matrix n n α) : (A ⬝ B)⁻¹ = B⁻¹ ⬝ A⁻¹ := by
  simp only [← inv_def]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, det_mul, adjugate_mul_distrib, Ring.mul_inverse_rev]

/-- A version of `list.prod_inv_reverse` for `matrix.has_inv`. -/
theorem list_prod_inv_reverse : ∀ l : List (Matrix n n α), l.Prod⁻¹ = (l.reverse.map Inv.inv).Prod
  | [] => by
    rw [List.reverse_nil, List.map_nil, List.prod_nil, inv_one]
  | A :: Xs => by
    rw [List.reverse_cons', List.map_concat, List.prod_concat, List.prod_cons, Matrix.mul_eq_mul, Matrix.mul_eq_mul,
      mul_inv_rev, list_prod_inv_reverse]

/-- One form of **Cramer's rule**. See `matrix.mul_vec_cramer` for a stronger form. -/
@[simp]
theorem det_smul_inv_mul_vec_eq_cramer (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
    A.det • A⁻¹.mulVec b = cramer A b := by
  rw [cramer_eq_adjugate_mul_vec, A.nonsing_inv_apply h, ← smul_mul_vec_assoc, smul_smul, h.mul_coe_inv, one_smul]

/-- One form of **Cramer's rule**. See `matrix.mul_vec_cramer` for a stronger form. -/
@[simp]
theorem det_smul_inv_vec_mul_eq_cramer_transpose (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
    A.det • A⁻¹.vecMul b = cramer Aᵀ b := by
  rw [← A⁻¹.transpose_transpose, vec_mul_transpose, transpose_nonsing_inv, ← det_transpose,
    Aᵀ.det_smul_inv_mul_vec_eq_cramer _ (is_unit_det_transpose A h)]

/-! ### More results about determinants -/


section Det

variable [Fintype m] [DecidableEq m]

/-- A variant of `matrix.det_units_conj`. -/
theorem det_conj {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) : det (M ⬝ N ⬝ M⁻¹) = det N := by
  rw [← h.unit_spec, ← coe_units_inv, det_units_conj]

/-- A variant of `matrix.det_units_conj'`. -/
theorem det_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) : det (M⁻¹ ⬝ N ⬝ M) = det N := by
  rw [← h.unit_spec, ← coe_units_inv, det_units_conj']

/-- Determinant of a 2×2 block matrix, expanded around an invertible top left element in terms of
the Schur complement. -/
theorem det_from_blocks₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) [Invertible A] :
    (Matrix.fromBlocks A B C D).det = det A * det (D - C ⬝ ⅟ A ⬝ B) := by
  have :
    from_blocks A B C D =
      from_blocks 1 0 (C ⬝ ⅟ A) 1 ⬝ from_blocks A 0 0 (D - C ⬝ ⅟ A ⬝ B) ⬝ from_blocks 1 (⅟ A ⬝ B) 0 1 :=
    by
    simp only [← from_blocks_multiply, ← Matrix.mul_zero, ← Matrix.zero_mul, ← add_zeroₓ, ← zero_addₓ, ← Matrix.one_mul,
      ← Matrix.mul_one, ← Matrix.inv_of_mul_self, ← Matrix.mul_inv_of_self_assoc, ← Matrix.mul_inv_of_mul_self_cancel, ←
      Matrix.mul_assoc, ← add_sub_cancel'_right]
  rw [this, det_mul, det_mul, det_from_blocks_zero₂₁, det_from_blocks_zero₂₁, det_from_blocks_zero₁₂, det_one, det_one,
    one_mulₓ, one_mulₓ, mul_oneₓ]

@[simp]
theorem det_from_blocks_one₁₁ (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) :
    (Matrix.fromBlocks 1 B C D).det = det (D - C ⬝ B) := by
  have : Invertible (1 : Matrix m m α) := invertibleOne
  rw [det_from_blocks₁₁, inv_of_one, Matrix.mul_one, det_one, one_mulₓ]

/-- Determinant of a 2×2 block matrix, expanded around an invertible bottom right element in terms
of the Schur complement. -/
theorem det_from_blocks₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) [Invertible D] :
    (Matrix.fromBlocks A B C D).det = det D * det (A - B ⬝ ⅟ D ⬝ C) := by
  have : from_blocks A B C D = (from_blocks D C B A).minor (sum_comm _ _) (sum_comm _ _) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [this, det_minor_equiv_self, det_from_blocks₁₁]

@[simp]
theorem det_from_blocks_one₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) :
    (Matrix.fromBlocks A B C 1).det = det (A - B ⬝ C) := by
  have : Invertible (1 : Matrix n n α) := invertibleOne
  rw [det_from_blocks₂₂, inv_of_one, Matrix.mul_one, det_one, one_mulₓ]

/-- The **Weinstein–Aronszajn identity**. Note the `1` on the LHS is of shape m×m, while the `1` on
the RHS is of shape n×n. -/
theorem det_one_add_mul_comm (A : Matrix m n α) (B : Matrix n m α) : det (1 + A ⬝ B) = det (1 + B ⬝ A) :=
  calc
    det (1 + A ⬝ B) = det (fromBlocks 1 (-A) B 1) := by
      rw [det_from_blocks_one₂₂, Matrix.neg_mul, sub_neg_eq_add]
    _ = det (1 + B ⬝ A) := by
      rw [det_from_blocks_one₁₁, Matrix.mul_neg, sub_neg_eq_add]
    

/-- Alternate statement of the **Weinstein–Aronszajn identity** -/
theorem det_mul_add_one_comm (A : Matrix m n α) (B : Matrix n m α) : det (A ⬝ B + 1) = det (B ⬝ A + 1) := by
  rw [add_commₓ, det_one_add_mul_comm, add_commₓ]

theorem det_one_sub_mul_comm (A : Matrix m n α) (B : Matrix n m α) : det (1 - A ⬝ B) = det (1 - B ⬝ A) := by
  rw [sub_eq_add_neg, ← Matrix.neg_mul, det_one_add_mul_comm, Matrix.mul_neg, ← sub_eq_add_neg]

/-- A special case of the **Matrix determinant lemma** for when `A = I`.

TODO: show this more generally. -/
theorem det_one_add_col_mul_row (u v : m → α) : det (1 + colₓ u ⬝ rowₓ v) = 1 + v ⬝ᵥ u := by
  rw [det_one_add_mul_comm, det_unique, Pi.add_apply, Pi.add_apply, Matrix.one_apply_eq, Matrix.row_mul_col_apply]

end Det

end Matrix

