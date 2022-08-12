/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathbin.Data.MvPolynomial.Monad

/-!
## Expand multivariate polynomials

Given a multivariate polynomial `φ`, one may replace every occurence of `X i` by `X i ^ n`,
for some natural number `n`.
This operation is called `mv_polynomial.expand` and it is an algebra homomorphism.

### Main declaration

* `mv_polynomial.expand`: expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/


open BigOperators

namespace MvPolynomial

variable {σ τ R S : Type _} [CommSemiringₓ R] [CommSemiringₓ S]

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `polynomial.expand`. -/
noncomputable def expand (p : ℕ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  { (eval₂Hom c fun i => x i ^ p : MvPolynomial σ R →+* MvPolynomial σ R) with commutes' := fun r => eval₂_hom_C _ _ _ }

@[simp]
theorem expand_C (p : ℕ) (r : R) : expand p (c r : MvPolynomial σ R) = c r :=
  eval₂_hom_C _ _ _

@[simp]
theorem expand_X (p : ℕ) (i : σ) : expand p (x i : MvPolynomial σ R) = x i ^ p :=
  eval₂_hom_X' _ _ _

@[simp]
theorem expand_monomial (p : ℕ) (d : σ →₀ ℕ) (r : R) :
    expand p (monomial d r) = c r * ∏ i in d.support, (x i ^ p) ^ d i :=
  bind₁_monomial _ _ _

theorem expand_one_apply (f : MvPolynomial σ R) : expand 1 f = f := by
  simp only [← expand, ← bind₁_X_left, ← AlgHom.id_apply, ← RingHom.to_fun_eq_coe, ← eval₂_hom_C_left, ←
    AlgHom.coe_to_ring_hom, ← pow_oneₓ, ← AlgHom.coe_mk]

@[simp]
theorem expand_one : expand 1 = AlgHom.id R (MvPolynomial σ R) := by
  ext1 f
  rw [expand_one_apply, AlgHom.id_apply]

theorem expand_comp_bind₁ (p : ℕ) (f : σ → MvPolynomial τ R) :
    (expand p).comp (bind₁ f) = bind₁ fun i => expand p (f i) := by
  apply alg_hom_ext
  intro i
  simp only [← AlgHom.comp_apply, ← bind₁_X_right]

theorem expand_bind₁ (p : ℕ) (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    expand p (bind₁ f φ) = bind₁ (fun i => expand p (f i)) φ := by
  rw [← AlgHom.comp_apply, expand_comp_bind₁]

@[simp]
theorem map_expand (f : R →+* S) (p : ℕ) (φ : MvPolynomial σ R) : map f (expand p φ) = expand p (map f φ) := by
  simp [← expand, ← map_bind₁]

@[simp]
theorem rename_expand (f : σ → τ) (p : ℕ) (φ : MvPolynomial σ R) : rename f (expand p φ) = expand p (rename f φ) := by
  simp [← expand, ← bind₁_rename, ← rename_bind₁]

@[simp]
theorem rename_comp_expand (f : σ → τ) (p : ℕ) :
    (rename f).comp (expand p) = (expand p).comp (rename f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) := by
  ext1 φ
  simp only [← rename_expand, ← AlgHom.comp_apply]

end MvPolynomial

