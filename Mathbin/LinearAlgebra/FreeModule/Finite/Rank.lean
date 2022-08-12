/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.LinearAlgebra.FreeModule.Rank
import Mathbin.LinearAlgebra.FreeModule.Finite.Basic

/-!

# Rank of finite free modules

This is a basic API for the rank of finite free modules.

-/


--TODO: `linear_algebra/finite_dimensional` should import this file, and a lot of results should
--be moved here.
universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

open TensorProduct DirectSum BigOperators Cardinal

open Cardinal FiniteDimensional Fintype

namespace Module.Free

section Ringₓ

variable [Ringₓ R] [StrongRankCondition R]

variable [AddCommGroupₓ M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroupₓ N] [Module R N] [Module.Free R N] [Module.Finite R N]

/-- The rank of a finite and free module is finite. -/
theorem rank_lt_aleph_0 : Module.rank R M < ℵ₀ := by
  let this := nontrivial_of_invariant_basis_number R
  rw [← (choose_basis R M).mk_eq_dim'', lt_aleph_0_iff_fintype]
  exact Nonempty.intro inferInstance

/-- If `M` is finite and free, `finrank M = rank M`. -/
@[simp]
theorem finrank_eq_rank : ↑(finrank R M) = Module.rank R M := by
  rw [finrank, cast_to_nat_of_lt_aleph_0 (rank_lt_aleph_0 R M)]

/-- The finrank of a free module `M` over `R` is the cardinality of `choose_basis_index R M`. -/
theorem finrank_eq_card_choose_basis_index :
    finrank R M =
      @card (ChooseBasisIndex R M) (@ChooseBasisIndex.fintype R M _ _ _ _ (nontrivial_of_invariant_basis_number R) _) :=
  by
  let this := nontrivial_of_invariant_basis_number R
  simp [← finrank, ← rank_eq_card_choose_basis_index]

/-- The finrank of `(ι →₀ R)` is `fintype.card ι`. -/
@[simp]
theorem finrank_finsupp {ι : Type v} [Fintype ι] : finrank R (ι →₀ R) = card ι := by
  rw [finrank, rank_finsupp, ← mk_to_nat_eq_card, to_nat_lift]

/-- The finrank of `(ι → R)` is `fintype.card ι`. -/
theorem finrank_pi {ι : Type v} [Fintype ι] : finrank R (ι → R) = card ι := by
  simp [← finrank]

/-- The finrank of the direct sum is the sum of the finranks. -/
@[simp]
theorem finrank_direct_sum {ι : Type v} [Fintype ι] (M : ι → Type w) [∀ i : ι, AddCommGroupₓ (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (⨁ i, M i) = ∑ i, finrank R (M i) := by
  let this := nontrivial_of_invariant_basis_number R
  simp only [← finrank, ← fun i => rank_eq_card_choose_basis_index R (M i), ← rank_direct_sum, mk_sigma, ←
    mk_to_nat_eq_card, ← card_sigma]

/-- The finrank of `M × N` is `(finrank R M) + (finrank R N)`. -/
@[simp]
theorem finrank_prod : finrank R (M × N) = finrank R M + finrank R N := by
  simp [← finrank, ← rank_lt_aleph_0 R M, ← rank_lt_aleph_0 R N]

/-- The finrank of a finite product is the sum of the finranks. -/
--TODO: this should follow from `linear_equiv.finrank_eq`, that is over a field.
theorem finrank_pi_fintype {ι : Type v} [Fintype ι] {M : ι → Type w} [∀ i : ι, AddCommGroupₓ (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (∀ i, M i) = ∑ i, finrank R (M i) := by
  let this := nontrivial_of_invariant_basis_number R
  simp only [← finrank, ← fun i => rank_eq_card_choose_basis_index R (M i), ← rank_pi_fintype, mk_sigma, ←
    mk_to_nat_eq_card, ← card_sigma]

/-- If `m` and `n` are `fintype`, the finrank of `m × n` matrices is
  `(fintype.card m) * (fintype.card n)`. -/
theorem finrank_matrix (m n : Type v) [Fintype m] [Fintype n] : finrank R (Matrix m n R) = card m * card n := by
  simp [← finrank]

end Ringₓ

section CommRingₓ

variable [CommRingₓ R] [StrongRankCondition R]

variable [AddCommGroupₓ M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroupₓ N] [Module R N] [Module.Free R N] [Module.Finite R N]

/-- The finrank of `M →ₗ[R] N` is `(finrank R M) * (finrank R N)`. -/
--TODO: this should follow from `linear_equiv.finrank_eq`, that is over a field.
theorem finrank_linear_hom : finrank R (M →ₗ[R] N) = finrank R M * finrank R N := by
  classical
  let this := nontrivial_of_invariant_basis_number R
  have h := LinearMap.toMatrix (choose_basis R M) (choose_basis R N)
  let b := (Matrix.stdBasis _ _ _).map h.symm
  rw [finrank, dim_eq_card_basis b, ← mk_fintype, mk_to_nat_eq_card, finrank, finrank, rank_eq_card_choose_basis_index,
    rank_eq_card_choose_basis_index, mk_to_nat_eq_card, mk_to_nat_eq_card, card_prod, mul_comm]

/-- The finrank of `M ⊗[R] N` is `(finrank R M) * (finrank R N)`. -/
@[simp]
theorem finrank_tensor_product (M : Type v) (N : Type w) [AddCommGroupₓ M] [Module R M] [Module.Free R M]
    [AddCommGroupₓ N] [Module R N] [Module.Free R N] : finrank R (M ⊗[R] N) = finrank R M * finrank R N := by
  simp [← finrank]

end CommRingₓ

end Module.Free

