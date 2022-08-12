/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.LinearAlgebra.Matrix.Determinant

/-!
# Changing the index type of a matrix

This file concerns the map `matrix.reindex`, mapping a `m` by `n` matrix
to an `m'` by `n'` matrix, as long as `m ≃ m'` and `n ≃ n'`.

## Main definitions

* `matrix.reindex_linear_equiv R A`: `matrix.reindex` is an `R`-linear equivalence between
  `A`-matrices.
* `matrix.reindex_alg_equiv R`: `matrix.reindex` is an `R`-algebra equivalence between `R`-matrices.

## Tags

matrix, reindex

-/


namespace Matrix

open Equivₓ

open Matrix

variable {l m n o : Type _} {l' m' n' o' : Type _} {m'' n'' : Type _}

variable (R A : Type _)

section AddCommMonoidₓ

variable [Semiringₓ R] [AddCommMonoidₓ A] [Module R A]

/-- The natural map that reindexes a matrix's rows and columns with equivalent types,
`matrix.reindex`, is a linear equivalence. -/
def reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n A ≃ₗ[R] Matrix m' n' A :=
  { reindex eₘ eₙ with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[simp]
theorem reindex_linear_equiv_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A) :
    reindexLinearEquiv R A eₘ eₙ M = reindex eₘ eₙ M :=
  rfl

@[simp]
theorem reindex_linear_equiv_symm (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexLinearEquiv R A eₘ eₙ).symm = reindexLinearEquiv R A eₘ.symm eₙ.symm :=
  rfl

@[simp]
theorem reindex_linear_equiv_refl_refl :
    reindexLinearEquiv R A (Equivₓ.refl m) (Equivₓ.refl n) = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun _ => rfl

theorem reindex_linear_equiv_trans (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    (reindexLinearEquiv R A e₁ e₂).trans (reindexLinearEquiv R A e₁' e₂') =
      (reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') : _ ≃ₗ[R] _) :=
  by
  ext
  rfl

theorem reindex_linear_equiv_comp (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    reindexLinearEquiv R A e₁' e₂' ∘ reindexLinearEquiv R A e₁ e₂ =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') :=
  by
  rw [← reindex_linear_equiv_trans]
  rfl

theorem reindex_linear_equiv_comp_apply (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
    (M : Matrix m n A) :
    (reindexLinearEquiv R A e₁' e₂') (reindexLinearEquiv R A e₁ e₂ M) =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') M :=
  minor_minor _ _ _ _ _

theorem reindex_linear_equiv_one [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m') :
    reindexLinearEquiv R A e e (1 : Matrix m m A) = 1 :=
  minor_one_equiv e.symm

end AddCommMonoidₓ

section Semiringₓ

variable [Semiringₓ R] [Semiringₓ A] [Module R A]

theorem reindex_linear_equiv_mul [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o') (M : Matrix m n A)
    (N : Matrix n o A) :
    reindexLinearEquiv R A eₘ eₙ M ⬝ reindexLinearEquiv R A eₙ eₒ N = reindexLinearEquiv R A eₘ eₒ (M ⬝ N) :=
  minor_mul_equiv M N _ _ _

theorem mul_reindex_linear_equiv_one [Fintype n] [Fintype o] [DecidableEq o] (e₁ : o ≃ n) (e₂ : o ≃ n')
    (M : Matrix m n A) :
    M.mul (reindexLinearEquiv R A e₁ e₂ 1) = reindexLinearEquiv R A (Equivₓ.refl m) (e₁.symm.trans e₂) M :=
  mul_minor_one _ _ _

end Semiringₓ

section Algebra

variable [CommSemiringₓ R] [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]

/-- For square matrices with coefficients in commutative semirings, the natural map that reindexes
a matrix's rows and columns with equivalent types, `matrix.reindex`, is an equivalence of algebras.
-/
def reindexAlgEquiv (e : m ≃ n) : Matrix m m R ≃ₐ[R] Matrix n n R :=
  { reindexLinearEquiv R R e e with toFun := reindex e e,
    map_mul' := fun a b => (reindex_linear_equiv_mul R R e e e a b).symm,
    commutes' := fun r => by
      simp [← algebraMap, ← Algebra.toRingHom, ← minor_smul] }

@[simp]
theorem reindex_alg_equiv_apply (e : m ≃ n) (M : Matrix m m R) : reindexAlgEquiv R e M = reindex e e M :=
  rfl

@[simp]
theorem reindex_alg_equiv_symm (e : m ≃ n) : (reindexAlgEquiv R e).symm = reindexAlgEquiv R e.symm :=
  rfl

@[simp]
theorem reindex_alg_equiv_refl : reindexAlgEquiv R (Equivₓ.refl m) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => rfl

theorem reindex_alg_equiv_mul (e : m ≃ n) (M : Matrix m m R) (N : Matrix m m R) :
    reindexAlgEquiv R e (M ⬝ N) = reindexAlgEquiv R e M ⬝ reindexAlgEquiv R e N :=
  (reindexAlgEquiv R e).map_mul M N

end Algebra

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`.
-/
theorem det_reindex_linear_equiv_self [CommRingₓ R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (M : Matrix m m R) : det (reindexLinearEquiv R R e e M) = det M :=
  det_reindex_self e M

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`.
-/
theorem det_reindex_alg_equiv [CommRingₓ R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (A : Matrix m m R) : det (reindexAlgEquiv R e A) = det A :=
  det_reindex_self e A

end Matrix

