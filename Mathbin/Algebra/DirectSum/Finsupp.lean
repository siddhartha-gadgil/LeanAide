/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Algebra.DirectSum.Module
import Mathbin.Data.Finsupp.ToDfinsupp

/-!
# Results on direct sums and finitely supported functions.

1. The linear equivalence between finitely supported functions `ι →₀ M` and
the direct sum of copies of `M` indexed by `ι`.
-/


universe u v w

noncomputable section

open DirectSum

open LinearMap Submodule

variable {R : Type u} {M : Type v} [Ringₓ R] [AddCommGroupₓ M] [Module R M]

section finsuppLequivDirectSum

variable (R M) (ι : Type _) [DecidableEq ι]

/-- The finitely supported functions `ι →₀ M` are in linear equivalence with the direct sum of
copies of M indexed by ι. -/
def finsuppLequivDirectSum : (ι →₀ M) ≃ₗ[R] ⨁ i : ι, M :=
  have : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  finsuppLequivDfinsupp R

@[simp]
theorem finsupp_lequiv_direct_sum_single (i : ι) (m : M) :
    finsuppLequivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i m :=
  Finsupp.to_dfinsupp_single i m

@[simp]
theorem finsupp_lequiv_direct_sum_symm_lof (i : ι) (m : M) :
    (finsuppLequivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsupp.single i m := by
  let this : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  exact Dfinsupp.to_finsupp_single i m

end finsuppLequivDirectSum

