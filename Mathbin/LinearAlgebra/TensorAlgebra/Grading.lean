/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.TensorAlgebra.Basic
import Mathbin.RingTheory.GradedAlgebra.Basic

/-!
# Results about the grading structure of the tensor algebra

The main result is `tensor_algebra.graded_algebra`, which says that the tensor algebra is a
ℕ-graded algebra.
-/


namespace TensorAlgebra

variable {R M : Type _} [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

open DirectSum

variable (R M)

/-- A version of `tensor_algebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `tensor_algebra.graded_algebra`. -/
def GradedAlgebra.ι : M →ₗ[R] ⨁ i : ℕ, ↥((ι R : M →ₗ[_] _).range ^ i) :=
  DirectSum.lof R ℕ (fun i => ↥((ι R : M →ₗ[_] _).range ^ i)) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by
      simpa only [← pow_oneₓ] using LinearMap.mem_range_self _ m

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun i => ↥((ι R : M →ₗ[_] _).range ^ i)) 1
        ⟨ι R m, by
          simpa only [← pow_oneₓ] using LinearMap.mem_range_self _ m⟩ :=
  rfl

variable {R M}

/-- The tensor algebra is graded by the powers of the submodule `(tensor_algebra.ι R).range`. -/
instance gradedAlgebra : GradedAlgebra ((· ^ ·) (ι R : M →ₗ[R] TensorAlgebra R M).range : ℕ → Submodule R _) :=
  GradedAlgebra.ofAlgHom _ (lift R <| GradedAlgebra.ι R M)
    (by
      ext m
      dsimp' only [← LinearMap.comp_apply, ← AlgHom.to_linear_map_apply, ← AlgHom.comp_apply, ← AlgHom.id_apply]
      rw [lift_ι_apply, graded_algebra.ι_apply R M, DirectSum.coe_alg_hom_of, Subtype.coe_mk])
    fun i x => by
    cases' x with x hx
    dsimp' only [← Subtype.coe_mk, ← DirectSum.lof_eq_of]
    refine' Submodule.pow_induction_on_left' _ (fun r => _) (fun x y i hx hy ihx ihy => _) (fun m hm i x hx ih => _) hx
    · rw [AlgHom.commutes, DirectSum.algebra_map_apply]
      rfl
      
    · rw [AlgHom.map_add, ihx, ihy, ← map_add]
      rfl
      
    · obtain ⟨_, rfl⟩ := hm
      rw [AlgHom.map_mul, ih, lift_ι_apply, graded_algebra.ι_apply R M, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_graded_monoid_eq (Sigma.subtype_ext (add_commₓ _ _) rfl)
      

end TensorAlgebra

