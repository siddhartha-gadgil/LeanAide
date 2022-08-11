/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Tim Baanen
-/
import Mathbin.Data.Matrix.Pequiv
import Mathbin.Data.Matrix.Block
import Mathbin.Data.Matrix.Notation
import Mathbin.Data.Fintype.Card
import Mathbin.GroupTheory.Perm.Fin
import Mathbin.GroupTheory.Perm.Sign
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Tactic.Ring
import Mathbin.LinearAlgebra.Alternating
import Mathbin.LinearAlgebra.Pi

/-!
# Determinant of a matrix

This file defines the determinant of a matrix, `matrix.det`, and its essential properties.

## Main definitions

 - `matrix.det`: the determinant of a square matrix, as a sum over permutations
 - `matrix.det_row_alternating`: the determinant, as an `alternating_map` in the rows of the matrix

## Main results

 - `det_mul`: the determinant of `A ⬝ B` is the product of determinants
 - `det_zero_of_row_eq`: the determinant is zero if there is a repeated row
 - `det_block_diagonal`: the determinant of a block diagonal matrix is a product
   of the blocks' determinants

## Implementation notes

It is possible to configure `simp` to compute determinants. See the file
`test/matrix.lean` for some examples.

-/


universe u v w z

open Equivₓ Equivₓ.Perm Finset Function

namespace Matrix

open Matrix BigOperators

variable {m n : Type _} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRingₓ R]

-- mathport name: «exprε »
local notation "ε" σ:arg => ((sign σ : ℤ) : R)

/-- `det` is an `alternating_map` in the rows of the matrix. -/
def detRowAlternating : AlternatingMap R (n → R) R n :=
  ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj).alternatization

/-- The determinant of a matrix given by the Leibniz formula. -/
abbrev det (M : Matrix n n R) : R :=
  detRowAlternating M

theorem det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, σ.sign • ∏ i, M (σ i) i :=
  MultilinearMap.alternatization_apply _ M

-- This is what the old definition was. We use it to avoid having to change the old proofs below
theorem det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n, ε σ * ∏ i, M (σ i) i := by
  simp [← det_apply, ← Units.smul_def]

@[simp]
theorem det_diagonal {d : n → R} : det (diagonalₓ d) = ∏ i, d i := by
  rw [det_apply']
  refine' (Finset.sum_eq_single 1 _ _).trans _
  · intro σ h1 h2
    cases' not_forall.1 (mt Equivₓ.ext h2) with x h3
    convert mul_zero _
    apply Finset.prod_eq_zero
    · change x ∈ _
      simp
      
    exact if_neg h3
    
  · simp
    
  · simp
    

@[simp]
theorem det_zero (h : Nonempty n) : det (0 : Matrix n n R) = 0 :=
  (detRowAlternating : AlternatingMap R (n → R) R n).map_zero

@[simp]
theorem det_one : det (1 : Matrix n n R) = 1 := by
  rw [← diagonal_one] <;> simp [-diagonal_one]

theorem det_is_empty [IsEmpty n] {A : Matrix n n R} : det A = 1 := by
  simp [← det_apply]

@[simp]
theorem coe_det_is_empty [IsEmpty n] : (det : Matrix n n R → R) = Function.const _ 1 := by
  ext
  exact det_is_empty

theorem det_eq_one_of_card_eq_zero {A : Matrix n n R} (h : Fintype.card n = 0) : det A = 1 := by
  have : IsEmpty n := fintype.card_eq_zero_iff.mp h
  exact det_is_empty

/-- If `n` has only one element, the determinant of an `n` by `n` matrix is just that element.
Although `unique` implies `decidable_eq` and `fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
theorem det_unique {n : Type _} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) : det A = A default default :=
  by
  simp [← det_apply, ← univ_unique]

theorem det_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) : det A = A k k := by
  convert det_unique _
  exact uniqueOfSubsingleton k

theorem det_eq_elem_of_card_eq_one {A : Matrix n n R} (h : Fintype.card n = 1) (k : n) : det A = A k k := by
  have : Subsingleton n := fintype.card_le_one_iff_subsingleton.mp h.le
  exact det_eq_elem_of_subsingleton _ _

theorem det_mul_aux {M N : Matrix n n R} {p : n → n} (H : ¬Bijective p) :
    (∑ σ : Perm n, ε σ * ∏ x, M (σ x) (p x) * N (p x) x) = 0 := by
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    rw [← Fintype.injective_iff_bijective, injective] at H
    push_neg  at H
    exact H
  exact
    sum_involution (fun σ _ => σ * swap i j)
      (fun σ _ => by
        have : (∏ x, M (σ x) (p x)) = ∏ x, M ((σ * swap i j) x) (p x) :=
          Fintype.prod_equiv (swap i j) _ _
            (by
              simp [← apply_swap_eq_self hpij])
        simp [← this, ← sign_swap hij, ← prod_mul_distrib])
      (fun σ _ _ => (not_congr mul_swap_eq_iff).mpr hij) (fun _ _ => mem_univ _) fun σ _ => mul_swap_involutive i j σ

@[simp]
theorem det_mul (M N : Matrix n n R) : det (M ⬝ N) = det M * det N :=
  calc
    det (M ⬝ N) = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [← det_apply', ← mul_apply, ← prod_univ_sum, ← mul_sum, ← Fintype.pi_finset_univ] <;>
        rw [Finset.sum_comm]
    _ = ∑ p in (@univ (n → n) _).filter Bijective, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i :=
      Eq.symm <|
        sum_subset (filter_subset _ _) fun f _ hbij =>
          det_mul_aux <| by
            simpa only [← true_andₓ, ← mem_filter, ← mem_univ] using hbij
    _ = ∑ τ : Perm n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i :=
      sum_bij (fun p h => Equivₓ.ofBijective p (mem_filter.1 h).2) (fun _ _ => mem_univ _) (fun _ _ => rfl)
        (fun _ _ _ _ h => by
          injection h)
        fun b _ => ⟨b, mem_filter.2 ⟨mem_univ _, b.Bijective⟩, coe_fn_injective rfl⟩
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * ∏ j, M (τ j) (σ j) := by
      simp only [← mul_comm, ← mul_left_commₓ, ← prod_mul_distrib, ← mul_assoc]
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i :=
      sum_congr rfl fun σ _ =>
        Fintype.sum_equiv (Equivₓ.mulRight σ⁻¹) _ _ fun τ => by
          have : (∏ j, M (τ j) (σ j)) = ∏ j, M ((τ * σ⁻¹) j) j := by
            rw [← (σ⁻¹ : _ ≃ _).prod_comp]
            simp only [← Equivₓ.Perm.coe_mul, ← apply_inv_self]
          have h : ε σ * ε(τ * σ⁻¹) = ε τ :=
            calc
              ε σ * ε(τ * σ⁻¹) = ε(τ * σ⁻¹ * σ) := by
                rw [mul_comm, sign_mul (τ * σ⁻¹)]
                simp only [← Int.cast_mul, ← Units.coe_mul]
              _ = ε τ := by
                simp only [← inv_mul_cancel_right]
              
          simp_rw [Equivₓ.coe_mul_right, h]
          simp only [← this]
    _ = det M * det N := by
      simp only [← det_apply', ← Finset.mul_sum, ← mul_comm, ← mul_left_commₓ]
    

/-- The determinant of a matrix, as a monoid homomorphism. -/
def detMonoidHom : Matrix n n R →* R where
  toFun := det
  map_one' := det_one
  map_mul' := det_mul

@[simp]
theorem coe_det_monoid_hom : (detMonoidHom : Matrix n n R → R) = det :=
  rfl

/-- On square matrices, `mul_comm` applies under `det`. -/
theorem det_mul_comm (M N : Matrix m m R) : det (M ⬝ N) = det (N ⬝ M) := by
  rw [det_mul, det_mul, mul_comm]

/-- On square matrices, `mul_left_comm` applies under `det`. -/
theorem det_mul_left_comm (M N P : Matrix m m R) : det (M ⬝ (N ⬝ P)) = det (N ⬝ (M ⬝ P)) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, det_mul, det_mul_comm M N, ← det_mul]

/-- On square matrices, `mul_right_comm` applies under `det`. -/
theorem det_mul_right_comm (M N P : Matrix m m R) : det (M ⬝ N ⬝ P) = det (M ⬝ P ⬝ N) := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, det_mul, det_mul_comm N P, ← det_mul]

theorem det_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) : det (↑M ⬝ N ⬝ ↑M⁻¹ : Matrix m m R) = det N := by
  rw [det_mul_right_comm, ← mul_eq_mul, ← mul_eq_mul, Units.mul_inv, one_mulₓ]

theorem det_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) : det (↑M⁻¹ ⬝ N ⬝ ↑M : Matrix m m R) = det N :=
  det_units_conj M⁻¹ N

/-- Transposing a matrix preserves the determinant. -/
@[simp]
theorem det_transpose (M : Matrix n n R) : Mᵀ.det = M.det := by
  rw [det_apply', det_apply']
  refine' Fintype.sum_bijective _ inv_involutive.bijective _ _ _
  intro σ
  rw [sign_inv]
  congr 1
  apply Fintype.prod_equiv σ
  intros
  simp

/-- Permuting the columns changes the sign of the determinant. -/
theorem det_permute (σ : Perm n) (M : Matrix n n R) : (Matrix.det fun i => M (σ i)) = σ.sign * M.det :=
  ((detRowAlternating : AlternatingMap R (n → R) R n).map_perm M σ).trans
    (by
      simp [← Units.smul_def])

/-- Permuting rows and columns with the same equivalence has no effect. -/
@[simp]
theorem det_minor_equiv_self (e : n ≃ m) (A : Matrix m m R) : det (A.minor e e) = det A := by
  rw [det_apply', det_apply']
  apply Fintype.sum_equiv (Equivₓ.permCongr e)
  intro σ
  rw [Equivₓ.Perm.sign_perm_congr e σ]
  congr 1
  apply Fintype.prod_equiv e
  intro i
  rw [Equivₓ.perm_congr_apply, Equivₓ.symm_apply_apply, minor_apply]

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`; this one is unsuitable because
`matrix.reindex_apply` unfolds `reindex` first.
-/
theorem det_reindex_self (e : m ≃ n) (A : Matrix m m R) : det (reindex e e A) = det A :=
  det_minor_equiv_self e.symm A

/-- The determinant of a permutation matrix equals its sign. -/
@[simp]
theorem det_permutation (σ : Perm n) : Matrix.det (σ.toPequiv.toMatrix : Matrix n n R) = σ.sign := by
  rw [← Matrix.mul_one (σ.to_pequiv.to_matrix : Matrix n n R), Pequiv.to_pequiv_mul_matrix, det_permute, det_one,
    mul_oneₓ]

theorem det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^ Fintype.card n * det A :=
  calc
    det (c • A) = det (Matrix.mul (diagonalₓ fun _ => c) A) := by
      rw [smul_eq_diagonal_mul]
    _ = det (diagonalₓ fun _ => c) * det A := det_mul _ _
    _ = c ^ Fintype.card n * det A := by
      simp [← card_univ]
    

@[simp]
theorem det_smul_of_tower {α} [Monoidₓ α] [DistribMulAction α R] [IsScalarTower α R R] [SmulCommClass α R R] (c : α)
    (A : Matrix n n R) : det (c • A) = c ^ Fintype.card n • det A := by
  rw [← smul_one_smul R c A, det_smul, smul_pow, one_pow, smul_mul_assoc, one_mulₓ]

theorem det_neg (A : Matrix n n R) : det (-A) = -1 ^ Fintype.card n * det A := by
  rw [← det_smul, neg_one_smul]

/-- A variant of `matrix.det_neg` with scalar multiplication by `units ℤ` instead of multiplication
by `R`. -/
theorem det_neg_eq_smul (A : Matrix n n R) : det (-A) = (-1 : Units ℤ) ^ Fintype.card n • det A := by
  rw [← det_smul_of_tower, Units.neg_smul, one_smul]

/-- Multiplying each row by a fixed `v i` multiplies the determinant by
the product of the `v`s. -/
theorem det_mul_row (v : n → R) (A : Matrix n n R) : det (of fun i j => v j * A i j) = (∏ i, v i) * det A :=
  calc
    det (of fun i j => v j * A i j) = det (A ⬝ diagonalₓ v) :=
      congr_arg det <| by
        ext
        simp [← mul_comm]
    _ = (∏ i, v i) * det A := by
      rw [det_mul, det_diagonal, mul_comm]
    

/-- Multiplying each column by a fixed `v j` multiplies the determinant by
the product of the `v`s. -/
theorem det_mul_column (v : n → R) (A : Matrix n n R) : det (of fun i j => v i * A i j) = (∏ i, v i) * det A :=
  MultilinearMap.map_smul_univ _ v A

@[simp]
theorem det_pow (M : Matrix m m R) (n : ℕ) : det (M ^ n) = det M ^ n :=
  (detMonoidHom : Matrix m m R →* R).map_pow M n

section HomMap

variable {S : Type w} [CommRingₓ S]

theorem _root_.ring_hom.map_det (f : R →+* S) (M : Matrix n n R) : f M.det = Matrix.det (f.mapMatrix M) := by
  simp [← Matrix.det_apply', ← f.map_sum, ← f.map_prod]

theorem _root_.ring_equiv.map_det (f : R ≃+* S) (M : Matrix n n R) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toRingHom.map_det _

theorem _root_.alg_hom.map_det [Algebra R S] {T : Type z} [CommRingₓ T] [Algebra R T] (f : S →ₐ[R] T)
    (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toRingHom.map_det _

theorem _root_.alg_equiv.map_det [Algebra R S] {T : Type z} [CommRingₓ T] [Algebra R T] (f : S ≃ₐ[R] T)
    (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toAlgHom.map_det _

end HomMap

@[simp]
theorem det_conj_transpose [StarRing R] (M : Matrix m m R) : det Mᴴ = star (det M) :=
  ((starRingEnd R).map_det _).symm.trans <| congr_arg star M.det_transpose

section DetZero

/-!
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/


theorem det_eq_zero_of_row_eq_zero {A : Matrix n n R} (i : n) (h : ∀ j, A i j = 0) : det A = 0 :=
  (detRowAlternating : AlternatingMap R (n → R) R n).map_coord_zero i (funext h)

theorem det_eq_zero_of_column_eq_zero {A : Matrix n n R} (j : n) (h : ∀ i, A i j = 0) : det A = 0 := by
  rw [← det_transpose]
  exact det_eq_zero_of_row_eq_zero j h

variable {M : Matrix n n R} {i j : n}

/-- If a matrix has a repeated row, the determinant will be zero. -/
theorem det_zero_of_row_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
  (detRowAlternating : AlternatingMap R (n → R) R n).map_eq_zero_of_eq M hij i_ne_j

/-- If a matrix has a repeated column, the determinant will be zero. -/
theorem det_zero_of_column_eq (i_ne_j : i ≠ j) (hij : ∀ k, M k i = M k j) : M.det = 0 := by
  rw [← det_transpose, det_zero_of_row_eq i_ne_j]
  exact funext hij

end DetZero

theorem det_update_row_add (M : Matrix n n R) (j : n) (u v : n → R) :
    det (updateRow M j <| u + v) = det (updateRow M j u) + det (updateRow M j v) :=
  (detRowAlternating : AlternatingMap R (n → R) R n).map_add M j u v

theorem det_update_column_add (M : Matrix n n R) (j : n) (u v : n → R) :
    det (updateColumn M j <| u + v) = det (updateColumn M j u) + det (updateColumn M j v) := by
  rw [← det_transpose, ← update_row_transpose, det_update_row_add]
  simp [← update_row_transpose, ← det_transpose]

theorem det_update_row_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateRow M j <| s • u) = s * det (updateRow M j u) :=
  (detRowAlternating : AlternatingMap R (n → R) R n).map_smul M j s u

theorem det_update_column_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateColumn M j <| s • u) = s * det (updateColumn M j u) := by
  rw [← det_transpose, ← update_row_transpose, det_update_row_smul]
  simp [← update_row_transpose, ← det_transpose]

theorem det_update_row_smul' (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateRow (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateRow M j u) :=
  MultilinearMap.map_update_smul _ M j s u

theorem det_update_column_smul' (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateColumn (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateColumn M j u) := by
  rw [← det_transpose, ← update_row_transpose, transpose_smul, det_update_row_smul']
  simp [← update_row_transpose, ← det_transpose]

section DetEq

/-! ### `det_eq` section

Lemmas showing the determinant is invariant under a variety of operations.
-/


theorem det_eq_of_eq_mul_det_one {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1) (hA : A = B ⬝ C) :
    det A = det B :=
  calc
    det A = det (B ⬝ C) := congr_arg _ hA
    _ = det B * det C := det_mul _ _
    _ = det B := by
      rw [hC, mul_oneₓ]
    

theorem det_eq_of_eq_det_one_mul {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1) (hA : A = C ⬝ B) :
    det A = det B :=
  calc
    det A = det (C ⬝ B) := congr_arg _ hA
    _ = det C * det B := det_mul _ _
    _ = det B := by
      rw [hC, one_mulₓ]
    

theorem det_update_row_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) : det (updateRow A i (A i + A j)) = det A :=
  by
  simp [← det_update_row_add, ← det_zero_of_row_eq hij (update_row_self.trans (update_row_ne hij.symm).symm)]

theorem det_update_column_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    det (updateColumn A i fun k => A k i + A k j) = det A := by
  rw [← det_transpose, ← update_row_transpose, ← det_transpose A]
  exact det_update_row_add_self Aᵀ hij

theorem det_update_row_add_smul_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
    det (updateRow A i (A i + c • A j)) = det A := by
  simp [← det_update_row_add, ← det_update_row_smul, ←
    det_zero_of_row_eq hij (update_row_self.trans (update_row_ne hij.symm).symm)]

theorem det_update_column_add_smul_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
    det (updateColumn A i fun k => A k i + c • A k j) = det A := by
  rw [← det_transpose, ← update_row_transpose, ← det_transpose A]
  exact det_update_row_add_smul_self Aᵀ hij c

theorem det_eq_of_forall_row_eq_smul_add_const_aux {A B : Matrix n n R} {s : Finset n} :
    ∀ (c : n → R) (hs : ∀ i, i ∉ s → c i = 0) (k : n) (hk : k ∉ s) (A_eq : ∀ i j, A i j = B i j + c i * B k j),
      det A = det B :=
  by
  revert B
  refine' s.induction_on _ _
  · intro A c hs k hk A_eq
    have : ∀ i, c i = 0 := by
      intro i
      specialize hs i
      contrapose! hs
      simp [← hs]
    congr
    ext i j
    rw [A_eq, this, zero_mul, add_zeroₓ]
    
  · intro i s hi ih B c hs k hk A_eq
    have hAi : A i = B i + c i • B k := funext (A_eq i)
    rw [@ih (update_row B i (A i)) (Function.update c i 0), hAi, det_update_row_add_smul_self]
    · exact mt (fun h => show k ∈ insert i s from h ▸ Finset.mem_insert_self _ _) hk
      
    · intro i' hi'
      rw [Function.update_apply]
      split_ifs with hi'i
      · rfl
        
      · exact hs i' fun h => hi' ((finset.mem_insert.mp h).resolve_left hi'i)
        
      
    · exact fun h => hk (Finset.mem_insert_of_mem h)
      
    · intro i' j'
      rw [update_row_apply, Function.update_apply]
      split_ifs with hi'i
      · simp [← hi'i]
        
      rw [A_eq, update_row_ne fun h : k = i => hk <| h ▸ Finset.mem_insert_self k s]
      
    

/-- If you add multiples of row `B k` to other rows, the determinant doesn't change. -/
theorem det_eq_of_forall_row_eq_smul_add_const {A B : Matrix n n R} (c : n → R) (k : n) (hk : c k = 0)
    (A_eq : ∀ i j, A i j = B i j + c i * B k j) : det A = det B :=
  det_eq_of_forall_row_eq_smul_add_const_aux c
    (fun i =>
      not_imp_comm.mp fun hi =>
        Finset.mem_erase.mpr ⟨mt (fun h : i = k => show c i = 0 from h.symm ▸ hk) hi, Finset.mem_univ i⟩)
    k (Finset.not_mem_erase k Finset.univ) A_eq

theorem det_eq_of_forall_row_eq_smul_add_pred_aux {n : ℕ} (k : Finₓ (n + 1)) :
    ∀ (c : Finₓ n → R) (hc : ∀ i : Finₓ n, k < i.succ → c i = 0) {M N : Matrix (Finₓ n.succ) (Finₓ n.succ) R}
      (h0 : ∀ j, M 0 j = N 0 j) (hsucc : ∀ (i : Finₓ n) (j), M i.succ j = N i.succ j + c i * M i.cast_succ j),
      det M = det N :=
  by
  refine' Finₓ.induction _ (fun k ih => _) k <;> intro c hc M N h0 hsucc
  · congr
    ext i j
    refine' Finₓ.cases (h0 j) (fun i => _) i
    rw [hsucc, hc i (Finₓ.succ_pos _), zero_mul, add_zeroₓ]
    
  set M' := update_row M k.succ (N k.succ) with hM'
  have hM : M = update_row M' k.succ (M' k.succ + c k • M k.cast_succ) := by
    ext i j
    by_cases' hi : i = k.succ
    · simp [← hi, ← hM', ← hsucc, ← update_row_self]
      
    rw [update_row_ne hi, hM', update_row_ne hi]
  have k_ne_succ : k.cast_succ ≠ k.succ := (Finₓ.cast_succ_lt_succ k).Ne
  have M_k : M k.cast_succ = M' k.cast_succ := (update_row_ne k_ne_succ).symm
  rw [hM, M_k, det_update_row_add_smul_self M' k_ne_succ.symm, ih (Function.update c k 0)]
  · intro i hi
    rw [Finₓ.lt_iff_coe_lt_coe, Finₓ.coe_cast_succ, Finₓ.coe_succ, Nat.lt_succ_iffₓ] at hi
    rw [Function.update_apply]
    split_ifs with hik
    · rfl
      
    exact hc _ (fin.succ_lt_succ_iff.mpr (lt_of_le_of_neₓ hi (Ne.symm hik)))
    
  · rwa [hM', update_row_ne (Finₓ.succ_ne_zero _).symm]
    
  intro i j
  rw [Function.update_apply]
  split_ifs with hik
  · rw [zero_mul, add_zeroₓ, hM', hik, update_row_self]
    
  rw [hM', update_row_ne ((Finₓ.succ_injective _).Ne hik), hsucc]
  by_cases' hik2 : k < i
  · simp [← hc i (fin.succ_lt_succ_iff.mpr hik2)]
    
  rw [update_row_ne]
  apply ne_of_ltₓ
  rwa [Finₓ.lt_iff_coe_lt_coe, Finₓ.coe_cast_succ, Finₓ.coe_succ, Nat.lt_succ_iffₓ, ← not_ltₓ]

/-- If you add multiples of previous rows to the next row, the determinant doesn't change. -/
theorem det_eq_of_forall_row_eq_smul_add_pred {n : ℕ} {A B : Matrix (Finₓ (n + 1)) (Finₓ (n + 1)) R} (c : Finₓ n → R)
    (A_zero : ∀ j, A 0 j = B 0 j) (A_succ : ∀ (i : Finₓ n) (j), A i.succ j = B i.succ j + c i * A i.cast_succ j) :
    det A = det B :=
  det_eq_of_forall_row_eq_smul_add_pred_aux (Finₓ.last _) c (fun i hi => absurd hi (not_lt_of_geₓ (Finₓ.le_last _)))
    A_zero A_succ

/-- If you add multiples of previous columns to the next columns, the determinant doesn't change. -/
theorem det_eq_of_forall_col_eq_smul_add_pred {n : ℕ} {A B : Matrix (Finₓ (n + 1)) (Finₓ (n + 1)) R} (c : Finₓ n → R)
    (A_zero : ∀ i, A i 0 = B i 0) (A_succ : ∀ (i) (j : Finₓ n), A i j.succ = B i j.succ + c j * A i j.cast_succ) :
    det A = det B := by
  rw [← det_transpose A, ← det_transpose B]
  exact det_eq_of_forall_row_eq_smul_add_pred c A_zero fun i j => A_succ j i

end DetEq

@[simp]
theorem det_block_diagonal {o : Type _} [Fintype o] [DecidableEq o] (M : o → Matrix n n R) :
    (blockDiagonalₓ M).det = ∏ k, (M k).det := by
  -- Rewrite the determinants as a sum over permutations.
  simp_rw [det_apply']
  -- The right hand side is a product of sums, rewrite it as a sum of products.
  rw [Finset.prod_sum]
  simp_rw [Finset.mem_univ, Finset.prod_attach_univ, Finset.univ_pi_univ]
  -- We claim that the only permutations contributing to the sum are those that
  -- preserve their second component.
  let preserving_snd : Finset (Equivₓ.Perm (n × o)) := finset.univ.filter fun σ => ∀ x, (σ x).snd = x.snd
  have mem_preserving_snd : ∀ {σ : Equivₓ.Perm (n × o)}, σ ∈ preserving_snd ↔ ∀ x, (σ x).snd = x.snd := fun σ =>
    finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  rw [← Finset.sum_subset (Finset.subset_univ preserving_snd) _]
  -- And that these are in bijection with `o → equiv.perm m`.
  rw
    [(Finset.sum_bij
        (fun (σ : ∀ k : o, k ∈ Finset.univ → Equivₓ.Perm n) _ => prod_congr_left fun k => σ k (Finset.mem_univ k)) _ _ _
        _).symm]
  · intro σ _
    rw [mem_preserving_snd]
    rintro ⟨k, x⟩
    simp only [← prod_congr_left_apply]
    
  · intro σ _
    rw [Finset.prod_mul_distrib, ← Finset.univ_product_univ, Finset.prod_product_right]
    simp only [← sign_prod_congr_left, ← Units.coe_prod, ← Int.cast_prod, ← block_diagonal_apply_eq, ←
      prod_congr_left_apply]
    
  · intro σ σ' _ _ eq
    ext x hx k
    simp only at eq
    have :
      ∀ k x,
        prod_congr_left (fun k => σ k (Finset.mem_univ _)) (k, x) =
          prod_congr_left (fun k => σ' k (Finset.mem_univ _)) (k, x) :=
      fun k x => by
      rw [Eq]
    simp only [← prod_congr_left_apply, ← Prod.mk.inj_iff] at this
    exact (this k x).1
    
  · intro σ hσ
    rw [mem_preserving_snd] at hσ
    have hσ' : ∀ x, (σ⁻¹ x).snd = x.snd := by
      intro x
      conv_rhs => rw [← perm.apply_inv_self σ x, hσ]
    have mk_apply_eq : ∀ k x, ((σ (x, k)).fst, k) = σ (x, k) := by
      intro k x
      ext
      · simp only
        
      · simp only [← hσ]
        
    have mk_inv_apply_eq : ∀ k x, ((σ⁻¹ (x, k)).fst, k) = σ⁻¹ (x, k) := by
      intro k x
      conv_lhs => rw [← perm.apply_inv_self σ (x, k)]
      ext
      · simp only [← apply_inv_self]
        
      · simp only [← hσ']
        
    refine' ⟨fun k _ => ⟨fun x => (σ (x, k)).fst, fun x => (σ⁻¹ (x, k)).fst, _, _⟩, _, _⟩
    · intro x
      simp only [← mk_apply_eq, ← inv_apply_self]
      
    · intro x
      simp only [← mk_inv_apply_eq, ← apply_inv_self]
      
    · apply Finset.mem_univ
      
    · ext ⟨k, x⟩
      · simp only [← coe_fn_mk, ← prod_congr_left_apply]
        
      · simp only [← prod_congr_left_apply, ← hσ]
        
      
    
  · intro σ _ hσ
    rw [mem_preserving_snd] at hσ
    obtain ⟨⟨k, x⟩, hkx⟩ := not_forall.mp hσ
    rw [Finset.prod_eq_zero (Finset.mem_univ (k, x)), mul_zero]
    rw [← @Prod.mk.eta _ _ (σ (k, x)), block_diagonal_apply_ne]
    exact hkx
    

/-- The determinant of a 2×2 block matrix with the lower-left block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`matrix.det_of_upper_triangular`. -/
@[simp]
theorem det_from_blocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).det = A.det * D.det := by
  classical
  simp_rw [det_apply']
  convert (sum_subset (subset_univ ((sum_congr_hom m n).range : Set (perm (Sum m n))).toFinset) _).symm
  rw [sum_mul_sum]
  simp_rw [univ_product_univ]
  rw [(sum_bij (fun (σ : perm m × perm n) _ => Equivₓ.sumCongr σ.fst σ.snd) _ _ _ _).symm]
  · intro σ₁₂ h
    simp only
    erw [Set.mem_to_finset, MonoidHom.mem_range]
    use σ₁₂
    simp only [← sum_congr_hom_apply]
    
  · simp only [← forall_prop_of_true, ← Prod.forall, ← mem_univ]
    intro σ₁ σ₂
    rw [Fintype.prod_sum_type]
    simp_rw [Equivₓ.sum_congr_apply, Sum.map_inr, Sum.map_inl, from_blocks_apply₁₁, from_blocks_apply₂₂]
    rw [mul_mul_mul_commₓ]
    congr
    rw [sign_sum_congr, Units.coe_mul, Int.cast_mul]
    
  · intro σ₁ σ₂ h₁ h₂
    dsimp' only
    intro h
    have h2 : ∀ x, perm.sum_congr σ₁.fst σ₁.snd x = perm.sum_congr σ₂.fst σ₂.snd x := by
      intro x
      exact congr_fun (congr_arg to_fun h) x
    simp only [← Sum.map_inr, ← Sum.map_inl, ← perm.sum_congr_apply, ← Sum.forall] at h2
    ext
    · exact h2.left x
      
    · exact h2.right x
      
    
  · intro σ hσ
    erw [Set.mem_to_finset, MonoidHom.mem_range] at hσ
    obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
    use σ₁₂
    rw [← hσ₁₂]
    simp
    
  · intro σ hσ hσn
    have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
      by_contra
      rw [Set.mem_to_finset] at hσn
      apply absurd (mem_sum_congr_hom_range_of_perm_maps_to_inl _) hσn
      rintro x ⟨a, ha⟩
      rw [← ha]
      exact h a
    obtain ⟨a, ha⟩ := not_forall.mp h1
    cases' hx : σ (Sum.inl a) with a2 b
    · have hn := (not_exists.mp ha) a2
      exact absurd hx.symm hn
      
    · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a)), mul_zero]
      rw [hx, from_blocks_apply₂₁]
      rfl
      
    

/-- The determinant of a 2×2 block matrix with the upper-right block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`matrix.det_of_lower_triangular`. -/
@[simp]
theorem det_from_blocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R) (D : Matrix n n R) :
    (Matrix.fromBlocks A 0 C D).det = A.det * D.det := by
  rw [← det_transpose, from_blocks_transpose, transpose_zero, det_from_blocks_zero₂₁, det_transpose, det_transpose]

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column 0. -/
theorem det_succ_column_zero {n : ℕ} (A : Matrix (Finₓ n.succ) (Finₓ n.succ) R) :
    det A = ∑ i : Finₓ n.succ, -1 ^ (i : ℕ) * A i 0 * det (A.minor i.succAbove Finₓ.succ) := by
  rw [Matrix.det_apply, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [← Finset.sum_map, ← Equivₓ.to_embedding_apply, ← Finset.sum_product, ← Matrix.minor]
  refine' Finset.sum_congr rfl fun i _ => Finₓ.cases _ (fun i => _) i
  · simp only [← Finₓ.prod_univ_succ, ← Matrix.det_apply, ← Finset.mul_sum, ← Equivₓ.Perm.decompose_fin_symm_apply_zero,
      ← Finₓ.coe_zero, ← one_mulₓ, ← Equivₓ.Perm.decomposeFin.symm_sign, ← Equivₓ.swap_self, ← if_true, ← id.def, ←
      eq_self_iff_true, ← Equivₓ.Perm.decompose_fin_symm_apply_succ, ← Finₓ.succ_above_zero, ← Equivₓ.coe_refl, ←
      pow_zeroₓ, ← mul_smul_comm, ← of_apply]
    
  -- `univ_perm_fin_succ` gives a different embedding of `perm (fin n)` into
  -- `perm (fin n.succ)` than the determinant of the submatrix we want,
  -- permute `A` so that we get the correct one.
  have : (-1 : R) ^ (i : ℕ) = i.cycle_range.sign := by
    simp [← Finₓ.sign_cycle_range]
  rw [Finₓ.coe_succ, pow_succₓ, this, mul_assoc, mul_assoc, mul_left_commₓ ↑(Equivₓ.Perm.sign _), ← det_permute,
    Matrix.det_apply, Finset.mul_sum, Finset.mul_sum]
  -- now we just need to move the corresponding parts to the same place
  refine' Finset.sum_congr rfl fun σ _ => _
  rw [Equivₓ.Perm.decomposeFin.symm_sign, if_neg (Finₓ.succ_ne_zero i)]
  calc
    ((-1 * σ.sign : ℤ) • ∏ i', A (equiv.perm.decompose_fin.symm (Finₓ.succ i, σ) i') i') =
        (-1 * σ.sign : ℤ) •
          (A (Finₓ.succ i) 0 * ∏ i', A ((Finₓ.succ i).succAbove (Finₓ.cycleRange i (σ i'))) i'.succ) :=
      by
      simp only [← Finₓ.prod_univ_succ, ← Finₓ.succ_above_cycle_range, ← Equivₓ.Perm.decompose_fin_symm_apply_zero, ←
        Equivₓ.Perm.decompose_fin_symm_apply_succ]_ =
        -1 *
          (A (Finₓ.succ i) 0 * (σ.sign : ℤ) • ∏ i', A ((Finₓ.succ i).succAbove (Finₓ.cycleRange i (σ i'))) i'.succ) :=
      by
      simp only [← mul_assoc, ← mul_comm, ← _root_.neg_mul, ← one_mulₓ, ← zsmul_eq_mul, ← neg_inj, ← neg_smul, ←
        Finₓ.succ_above_cycle_range]

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row 0. -/
theorem det_succ_row_zero {n : ℕ} (A : Matrix (Finₓ n.succ) (Finₓ n.succ) R) :
    det A = ∑ j : Finₓ n.succ, -1 ^ (j : ℕ) * A 0 j * det (A.minor Finₓ.succ j.succAbove) := by
  rw [← det_transpose A, det_succ_column_zero]
  refine' Finset.sum_congr rfl fun i _ => _
  rw [← det_transpose]
  simp only [← transpose_apply, ← transpose_minor, ← transpose_transpose]

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row `i`. -/
theorem det_succ_row {n : ℕ} (A : Matrix (Finₓ n.succ) (Finₓ n.succ) R) (i : Finₓ n.succ) :
    det A = ∑ j : Finₓ n.succ, -1 ^ (i + j : ℕ) * A i j * det (A.minor i.succAbove j.succAbove) := by
  simp_rw [pow_addₓ, mul_assoc, ← mul_sum]
  have : det A = (-1 : R) ^ (i : ℕ) * i.cycle_range⁻¹.sign * det A := by
    calc det A = ↑((-1 : ℤˣ) ^ (i : ℕ) * (-1 : ℤˣ) ^ (i : ℕ) : ℤˣ) * det A := by
        simp _ = (-1 : R) ^ (i : ℕ) * i.cycle_range⁻¹.sign * det A := by
        simp [-Int.units_mul_self]
  rw [this, mul_assoc]
  congr
  rw [← det_permute, det_succ_row_zero]
  refine' Finset.sum_congr rfl fun j _ => _
  rw [mul_assoc, Matrix.minor, Matrix.minor]
  congr
  · rw [Equivₓ.Perm.inv_def, Finₓ.cycle_range_symm_zero]
    
  · ext i' j'
    rw [Equivₓ.Perm.inv_def, Finₓ.cycle_range_symm_succ]
    

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column `j`. -/
theorem det_succ_column {n : ℕ} (A : Matrix (Finₓ n.succ) (Finₓ n.succ) R) (j : Finₓ n.succ) :
    det A = ∑ i : Finₓ n.succ, -1 ^ (i + j : ℕ) * A i j * det (A.minor i.succAbove j.succAbove) := by
  rw [← det_transpose, det_succ_row _ j]
  refine' Finset.sum_congr rfl fun i _ => _
  rw [add_commₓ, ← det_transpose, transpose_apply, transpose_minor, transpose_transpose]

/-- Determinant of 0x0 matrix -/
@[simp]
theorem det_fin_zero {A : Matrix (Finₓ 0) (Finₓ 0) R} : det A = 1 :=
  det_is_empty

/-- Determinant of 1x1 matrix -/
theorem det_fin_one (A : Matrix (Finₓ 1) (Finₓ 1) R) : det A = A 0 0 :=
  det_unique A

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem det_fin_one_of (a : R) :
    det («expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation") =
      a :=
  det_fin_one _

/-- Determinant of 2x2 matrix -/
theorem det_fin_two (A : Matrix (Finₓ 2) (Finₓ 2) R) : det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  simp [← Matrix.det_succ_row_zero, ← Finₓ.sum_univ_succ]
  ring

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
@[simp]
theorem det_fin_two_of (a b c d : R) :
    Matrix.det
        («expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation") =
      a * d - b * c :=
  det_fin_two _

/-- Determinant of 3x3 matrix -/
theorem det_fin_three (A : Matrix (Finₓ 3) (Finₓ 3) R) :
    det A =
      A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0 +
          A 0 2 * A 1 0 * A 2 1 -
        A 0 2 * A 1 1 * A 2 0 :=
  by
  simp [← Matrix.det_succ_row_zero, ← Finₓ.sum_univ_succ]
  ring

end Matrix

