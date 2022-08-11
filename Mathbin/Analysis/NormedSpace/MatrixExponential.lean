/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Analysis.NormedSpace.Exponential
import Mathbin.Analysis.Matrix
import Mathbin.LinearAlgebra.Matrix.Zpow
import Mathbin.Topology.UniformSpace.Matrix

/-!
# Lemmas about the matrix exponential

In this file, we provide results about `exp` on `matrix`s over a topological or normed algebra.
Note that generic results over all topological spaces such as `exp_zero` can be used on matrices
without issue, so are not repeated here. The topological results specific to matrices are:

* `matrix.exp_transpose`
* `matrix.exp_conj_transpose`
* `matrix.exp_diagonal`
* `matrix.exp_block_diagonal`
* `matrix.exp_block_diagonal'`

Lemmas like `exp_add_of_commute` require a canonical norm on the type; while there are multiple
sensible choices for the norm of a `matrix` (`matrix.normed_group`, `matrix.frobenius_normed_group`,
`matrix.linfty_op_normed_group`), none of them are canonical. In an application where a particular
norm is chosen using `local attribute [instance]`, then the usual lemmas about `exp` are fine. When
choosing a norm is undesirable, the results in this file can be used.

In this file, we copy across the lemmas about `exp`, but hide the requirement for a norm inside the
proof.

* `matrix.exp_add_of_commute`
* `matrix.exp_sum_of_commute`
* `matrix.exp_nsmul`
* `matrix.is_unit_exp`
* `matrix.exp_units_conj`
* `matrix.exp_units_conj'`

Additionally, we prove some results about `matrix.has_inv` and `matrix.div_inv_monoid`, as the
results for general rings are instead stated about `ring.inverse`:

* `matrix.exp_neg`
* `matrix.exp_zsmul`
* `matrix.exp_conj`
* `matrix.exp_conj'`

## Implementation notes

This file runs into some sharp edges on typeclass search in lean 3, especially regarding pi types.
To work around this, we copy a handful of instances for when lean can't find them by itself.
Hopefully we will be able to remove these in Lean 4.

## TODO

* Show that `matrix.det (exp 𝕂 A) = exp 𝕂 (matrix.trace A)`

## References

* https://en.wikipedia.org/wiki/Matrix_exponential
-/


open Matrix BigOperators

section HacksForPiInstanceSearch

/-- A special case of `pi.topological_ring` for when `R` is not dependently typed. -/
instance Function.topological_ring (I : Type _) (R : Type _) [NonUnitalRing R] [TopologicalSpace R]
    [TopologicalRing R] : TopologicalRing (I → R) :=
  Pi.topological_ring

/-- A special case of `function.algebra` for when A is a `ring` not a `semiring` -/
instance Function.algebraRing (I : Type _) {R : Type _} (A : Type _) [CommSemiringₓ R] [Ringₓ A] [Algebra R A] :
    Algebra R (I → A) :=
  Pi.algebra _ _

/-- A special case of `pi.algebra` for when `f = λ i, matrix (m i) (m i) A`. -/
instance Pi.matrixAlgebra (I R A : Type _) (m : I → Type _) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] : Algebra R (∀ i, Matrix (m i) (m i) A) :=
  @Pi.algebra I R (fun i => Matrix (m i) (m i) A) _ _ fun i => Matrix.algebra

/-- A special case of `pi.topological_ring` for when `f = λ i, matrix (m i) (m i) A`. -/
instance Pi.matrix_topological_ring (I A : Type _) (m : I → Type _) [Ringₓ A] [TopologicalSpace A] [TopologicalRing A]
    [∀ i, Fintype (m i)] : TopologicalRing (∀ i, Matrix (m i) (m i) A) :=
  @Pi.topological_ring _ (fun i => Matrix (m i) (m i) A) _ _ fun i => Matrix.topological_ring

end HacksForPiInstanceSearch

variable (𝕂 : Type _) {m n p : Type _} {n' : m → Type _} {𝔸 : Type _}

namespace Matrix

section Topological

section Ringₓ

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [∀ i, Fintype (n' i)] [∀ i, DecidableEq (n' i)]
  [Field 𝕂] [Ringₓ 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸] [Algebra 𝕂 𝔸] [T2Space 𝔸]

theorem exp_diagonal (v : m → 𝔸) : exp 𝕂 (diagonalₓ v) = diagonalₓ (exp 𝕂 v) := by
  simp_rw [exp_eq_tsum, diagonal_pow, ← diagonal_smul, ← diagonal_tsum]

theorem exp_block_diagonal (v : m → Matrix n n 𝔸) : exp 𝕂 (blockDiagonalₓ v) = blockDiagonalₓ (exp 𝕂 v) := by
  simp_rw [exp_eq_tsum, ← block_diagonal_pow, ← block_diagonal_smul, ← block_diagonal_tsum]

theorem exp_block_diagonal' (v : ∀ i, Matrix (n' i) (n' i) 𝔸) : exp 𝕂 (blockDiagonal'ₓ v) = blockDiagonal'ₓ (exp 𝕂 v) :=
  by
  simp_rw [exp_eq_tsum, ← block_diagonal'_pow, ← block_diagonal'_smul, ← block_diagonal'_tsum]

theorem exp_conj_transpose [StarRing 𝔸] [HasContinuousStar 𝔸] (A : Matrix m m 𝔸) : exp 𝕂 Aᴴ = (exp 𝕂 A)ᴴ :=
  (star_exp A).symm

end Ringₓ

section CommRingₓ

variable [Fintype m] [DecidableEq m] [Field 𝕂] [CommRingₓ 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸] [Algebra 𝕂 𝔸]
  [T2Space 𝔸]

theorem exp_transpose (A : Matrix m m 𝔸) : exp 𝕂 Aᵀ = (exp 𝕂 A)ᵀ := by
  simp_rw [exp_eq_tsum, transpose_tsum, transpose_smul, transpose_pow]

end CommRingₓ

end Topological

section Normed

variable [IsROrC 𝕂] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [∀ i, Fintype (n' i)]
  [∀ i, DecidableEq (n' i)] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

theorem exp_add_of_commute (A B : Matrix m m 𝔸) (h : Commute A B) : exp 𝕂 (A + B) = exp 𝕂 A ⬝ exp 𝕂 B := by
  let this : SemiNormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_add_of_commute h

theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → Matrix m m 𝔸)
    (h : ∀, ∀ i ∈ s, ∀, ∀ j ∈ s, ∀, Commute (f i) (f j)) :
    exp 𝕂 (∑ i in s, f i) = s.noncommProd (fun i => exp 𝕂 (f i)) fun i hi j hj => (h i hi j hj).exp 𝕂 := by
  let this : SemiNormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_sum_of_commute s f h

theorem exp_nsmul (n : ℕ) (A : Matrix m m 𝔸) : exp 𝕂 (n • A) = exp 𝕂 A ^ n := by
  let this : SemiNormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_nsmul n A

theorem is_unit_exp (A : Matrix m m 𝔸) : IsUnit (exp 𝕂 A) := by
  let this : SemiNormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact is_unit_exp _ A

theorem exp_units_conj (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp 𝕂 (↑U ⬝ A ⬝ ↑U⁻¹ : Matrix m m 𝔸) = ↑U ⬝ exp 𝕂 A ⬝ ↑U⁻¹ := by
  let this : SemiNormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_units_conj _ U A

theorem exp_units_conj' (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp 𝕂 (↑U⁻¹ ⬝ A ⬝ U : Matrix m m 𝔸) = ↑U⁻¹ ⬝ exp 𝕂 A ⬝ U :=
  exp_units_conj 𝕂 U⁻¹ A

end Normed

section NormedComm

variable [IsROrC 𝕂] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [∀ i, Fintype (n' i)]
  [∀ i, DecidableEq (n' i)] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

theorem exp_neg (A : Matrix m m 𝔸) : exp 𝕂 (-A) = (exp 𝕂 A)⁻¹ := by
  rw [nonsing_inv_eq_ring_inverse]
  let this : SemiNormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact (Ringₓ.inverse_exp _ A).symm

theorem exp_zsmul (z : ℤ) (A : Matrix m m 𝔸) : exp 𝕂 (z • A) = exp 𝕂 A ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg
  · rw [zpow_coe_nat, coe_nat_zsmul, exp_nsmul]
    
  · have : IsUnit (exp 𝕂 A).det := (Matrix.is_unit_iff_is_unit_det _).mp (is_unit_exp _ _)
    rw [Matrix.zpow_neg this, zpow_coe_nat, neg_smul, exp_neg, coe_nat_zsmul, exp_nsmul]
    

theorem exp_conj (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) : exp 𝕂 (U ⬝ A ⬝ U⁻¹) = U ⬝ exp 𝕂 A ⬝ U⁻¹ :=
  let ⟨u, hu⟩ := hy
  hu ▸ by
    simpa only [← Matrix.coe_units_inv] using exp_units_conj 𝕂 u A

theorem exp_conj' (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) : exp 𝕂 (U⁻¹ ⬝ A ⬝ U) = U⁻¹ ⬝ exp 𝕂 A ⬝ U :=
  let ⟨u, hu⟩ := hy
  hu ▸ by
    simpa only [← Matrix.coe_units_inv] using exp_units_conj' 𝕂 u A

end NormedComm

end Matrix

