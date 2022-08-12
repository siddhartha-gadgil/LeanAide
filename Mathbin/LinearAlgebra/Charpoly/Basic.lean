/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.LinearAlgebra.FreeModule.Finite.Basic
import Mathbin.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathbin.FieldTheory.Minpoly

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a finite and
free `R`-module. The proof that `f.charpoly` is the characteristic polynomial of the matrix of `f`
in any basis is in `linear_algebra/charpoly/to_matrix`.

## Main definition

* `linear_map.charpoly f` : the characteristic polynomial of `f : M →ₗ[R] M`.

-/


universe u v w

variable {R : Type u} {M : Type v} [CommRingₓ R] [Nontrivial R]

variable [AddCommGroupₓ M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

open Classical Matrix Polynomial

noncomputable section

open Module.Free Polynomial Matrix

namespace LinearMap

section Basic

/-- The characteristic polynomial of `f : M →ₗ[R] M`. -/
def charpoly : R[X] :=
  (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly

theorem charpoly_def : f.charpoly = (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly :=
  rfl

end Basic

section Coeff

theorem charpoly_monic : f.charpoly.Monic :=
  charpoly_monic _

end Coeff

section CayleyHamilton

/-- The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a linear map, applied
to the linear map itself, is zero.

See `matrix.aeval_self_charpoly` for the equivalent statement about matrices. -/
theorem aeval_self_charpoly : aeval f f.charpoly = 0 := by
  apply (LinearEquiv.map_eq_zero_iff (algEquivMatrix _).toLinearEquiv).1
  rw [AlgEquiv.to_linear_equiv_apply, ← AlgEquiv.coe_alg_hom, ← Polynomial.aeval_alg_hom_apply _ _ _, charpoly_def]
  exact aeval_self_charpoly _

theorem is_integral : IsIntegral R f :=
  ⟨f.charpoly, ⟨charpoly_monic f, aeval_self_charpoly f⟩⟩

theorem minpoly_dvd_charpoly {K : Type u} {M : Type v} [Field K] [AddCommGroupₓ M] [Module K M] [FiniteDimensional K M]
    (f : M →ₗ[K] M) : minpoly K f ∣ f.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly f)

/-- Any endomorphism polynomial `p` is equivalent under evaluation to `p %ₘ f.charpoly`; that is,
`p` is equivalent to a polynomial with degree less than the dimension of the module. -/
theorem aeval_eq_aeval_mod_charpoly (p : R[X]) : aeval f p = aeval f (p %ₘ f.charpoly) :=
  (aeval_mod_by_monic_eq_self_of_root f.charpoly_monic f.aeval_self_charpoly).symm

/-- Any endomorphism power can be computed as the sum of endomorphism powers less than the
dimension of the module. -/
theorem pow_eq_aeval_mod_charpoly (k : ℕ) : f ^ k = aeval f (X ^ k %ₘ f.charpoly) := by
  rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

variable {f}

theorem minpoly_coeff_zero_of_injective (hf : Function.Injective f) : (minpoly R f).coeff 0 ≠ 0 := by
  intro h
  obtain ⟨P, hP⟩ := X_dvd_iff.2 h
  have hdegP : P.degree < (minpoly R f).degree := by
    rw [hP, mul_comm]
    refine' degree_lt_degree_mul_X fun h => _
    rw [h, mul_zero] at hP
    exact minpoly.ne_zero (IsIntegral f) hP
  have hPmonic : P.monic := by
    suffices (minpoly R f).Monic by
      rwa [monic.def, hP, mul_comm, leading_coeff_mul_X, ← monic.def] at this
    exact minpoly.monic (IsIntegral f)
  have hzero : aeval f (minpoly R f) = 0 := minpoly.aeval _ _
  simp only [← hP, ← mul_eq_comp, ← ext_iff, ← hf, ← aeval_X, ← map_eq_zero_iff, ← coe_comp, ← AlgHom.map_mul, ←
    zero_apply] at hzero
  exact not_leₓ.2 hdegP (minpoly.min _ _ hPmonic (ext hzero))

end CayleyHamilton

end LinearMap

