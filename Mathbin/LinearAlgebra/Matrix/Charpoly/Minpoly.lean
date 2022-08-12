/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import Mathbin.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.RingTheory.PowerBasis

/-!
# The minimal polynomial divides the characteristic polynomial of a matrix.
-/


noncomputable section

universe u v

open Polynomial Matrix

variable {R : Type u} [CommRingₓ R]

variable {n : Type v} [DecidableEq n] [Fintype n]

open Finset

variable {M : Matrix n n R}

namespace Matrix

theorem is_integral : IsIntegral R M :=
  ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

theorem minpoly_dvd_charpoly {K : Type _} [Field K] (M : Matrix n n K) : minpoly K M ∣ M.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly M)

end Matrix

section PowerBasis

open Algebra

/-- The characteristic polynomial of the map `λ x, a * x` is the minimal polynomial of `a`.

In combination with `det_eq_sign_charpoly_coeff` or `trace_eq_neg_charpoly_coeff`
and a bit of rewriting, this will allow us to conclude the
field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.
-/
theorem charpoly_left_mul_matrix {K S : Type _} [Field K] [CommRingₓ S] [Algebra K S] (h : PowerBasis K S) :
    (leftMulMatrix h.Basis h.gen).charpoly = minpoly K h.gen := by
  apply minpoly.unique
  · apply Matrix.charpoly_monic
    
  · apply (injective_iff_map_eq_zero (left_mul_matrix _)).mp (left_mul_matrix_injective h.basis)
    rw [← Polynomial.aeval_alg_hom_apply, aeval_self_charpoly]
    
  · intro q q_monic root_q
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin, degree_eq_nat_degree q_monic.ne_zero]
    apply with_bot.some_le_some.mpr
    exact h.dim_le_nat_degree_of_root q_monic.ne_zero root_q
    

end PowerBasis

