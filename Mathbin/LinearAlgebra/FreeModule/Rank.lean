/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.LinearAlgebra.FreeModule.Basic
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!

# Rank of free modules

This is a basic API for the rank of free modules.

-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

open TensorProduct DirectSum BigOperators Cardinal

open Cardinal

namespace Module.Free

section Ringₓ

variable [Ringₓ R] [StrongRankCondition R]

variable [AddCommGroupₓ M] [Module R M] [Module.Free R M]

variable [AddCommGroupₓ N] [Module R N] [Module.Free R N]

/-- The rank of a free module `M` over `R` is the cardinality of `choose_basis_index R M`. -/
theorem rank_eq_card_choose_basis_index : Module.rank R M = # (ChooseBasisIndex R M) :=
  (chooseBasis R M).mk_eq_dim''.symm

/-- The rank of `(ι →₀ R)` is `(# ι).lift`. -/
@[simp]
theorem rank_finsupp {ι : Type v} : Module.rank R (ι →₀ R) = (# ι).lift := by
  simpa [← lift_id', ← lift_umax] using (Basis.of_repr (LinearEquiv.refl _ (ι →₀ R))).mk_eq_dim.symm

/-- If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`. -/
theorem rank_finsupp' {ι : Type u} : Module.rank R (ι →₀ R) = # ι := by
  simp

/-- The rank of `M × N` is `(module.rank R M).lift + (module.rank R N).lift`. -/
@[simp]
theorem rank_prod : Module.rank R (M × N) = lift.{w, v} (Module.rank R M) + lift.{v, w} (Module.rank R N) := by
  simpa [← rank_eq_card_choose_basis_index R M, ← rank_eq_card_choose_basis_index R N, ← lift_umax, ← lift_umax'] using
    ((choose_basis R M).Prod (choose_basis R N)).mk_eq_dim.symm

/-- If `M` and `N` lie in the same universe, the rank of `M × N` is
  `(module.rank R M) + (module.rank R N)`. -/
theorem rank_prod' (N : Type v) [AddCommGroupₓ N] [Module R N] [Module.Free R N] :
    Module.rank R (M × N) = Module.rank R M + Module.rank R N := by
  simp

/-- The rank of the direct sum is the sum of the ranks. -/
@[simp]
theorem rank_direct_sum {ι : Type v} (M : ι → Type w) [∀ i : ι, AddCommGroupₓ (M i)] [∀ i : ι, Module R (M i)]
    [∀ i : ι, Module.Free R (M i)] : Module.rank R (⨁ i, M i) = Cardinal.sum fun i => Module.rank R (M i) := by
  let B := fun i => choose_basis R (M i)
  let b : Basis _ R (⨁ i, M i) := Dfinsupp.basis fun i => B i
  simp [b.mk_eq_dim'', ← fun i => (B i).mk_eq_dim'']

/-- The rank of a finite product is the sum of the ranks. -/
@[simp]
theorem rank_pi_fintype {ι : Type v} [Fintype ι] {M : ι → Type w} [∀ i : ι, AddCommGroupₓ (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] :
    Module.rank R (∀ i, M i) = Cardinal.sum fun i => Module.rank R (M i) := by
  rw [← (DirectSum.linearEquivFunOnFintype _ _ M).dim_eq, rank_direct_sum]

/-- If `m` and `n` are `fintype`, the rank of `m × n` matrices is `(# m).lift * (# n).lift`. -/
@[simp]
theorem rank_matrix (m : Type v) (n : Type w) [Fintype m] [Fintype n] :
    Module.rank R (Matrix m n R) = lift.{max v w u, v} (# m) * lift.{max v w u, w} (# n) := by
  have h := (Matrix.stdBasis R m n).mk_eq_dim
  rw [← lift_lift.{max v w u, max v w}, lift_inj] at h
  simpa using h.symm

/-- If `m` and `n` are `fintype` that lie in the same universe, the rank of `m × n` matrices is
  `(# n * # m).lift`. -/
@[simp]
theorem rank_matrix' (m n : Type v) [Fintype m] [Fintype n] : Module.rank R (Matrix m n R) = (# m * # n).lift := by
  rw [rank_matrix, lift_mul, lift_umax]

/-- If `m` and `n` are `fintype` that lie in the same universe as `R`, the rank of `m × n` matrices
  is `# m * # n`. -/
@[simp]
theorem rank_matrix'' (m n : Type u) [Fintype m] [Fintype n] : Module.rank R (Matrix m n R) = # m * # n := by
  simp

end Ringₓ

section CommRingₓ

variable [CommRingₓ R] [StrongRankCondition R]

variable [AddCommGroupₓ M] [Module R M] [Module.Free R M]

variable [AddCommGroupₓ N] [Module R N] [Module.Free R N]

/-- The rank of `M ⊗[R] N` is `(module.rank R M).lift * (module.rank R N).lift`. -/
@[simp]
theorem rank_tensor_product :
    Module.rank R (M ⊗[R] N) = lift.{w, v} (Module.rank R M) * lift.{v, w} (Module.rank R N) := by
  let ιM := choose_basis_index R M
  let ιN := choose_basis_index R N
  have h₁ := LinearEquiv.lift_dim_eq (TensorProduct.congr (reprₓ R M) (reprₓ R N))
  let b : Basis (ιM × ιN) R (_ →₀ R) := Finsupp.basisSingleOne
  rw [LinearEquiv.dim_eq (finsuppTensorFinsupp' R ιM ιN), ← b.mk_eq_dim, mk_prod] at h₁
  rw [lift_inj.1 h₁, rank_eq_card_choose_basis_index R M, rank_eq_card_choose_basis_index R N]

/-- If `M` and `N` lie in the same universe, the rank of `M ⊗[R] N` is
  `(module.rank R M) * (module.rank R N)`. -/
theorem rank_tensor_product' (N : Type v) [AddCommGroupₓ N] [Module R N] [Module.Free R N] :
    Module.rank R (M ⊗[R] N) = Module.rank R M * Module.rank R N := by
  simp

end CommRingₓ

end Module.Free

