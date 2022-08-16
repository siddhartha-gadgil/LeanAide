/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Data.MvPolynomial.Rename

/-!
# `comap` operation on `mv_polynomial`

This file defines the `comap` function on `mv_polynomial`.

`mv_polynomial.comap` is a low-tech example of a map of "algebraic varieties," modulo the fact that
`mathlib` does not yet define varieties.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

-/


namespace MvPolynomial

variable {σ : Type _} {τ : Type _} {υ : Type _} {R : Type _} [CommSemiringₓ R]

/-- Given an algebra hom `f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R`
and a variable evaluation `v : τ → R`,
`comap f v` produces a variable evaluation `σ → R`.
-/
noncomputable def comap (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) : (τ → R) → σ → R := fun x i => aeval x (f (x i))

@[simp]
theorem comap_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (x : τ → R) (i : σ) :
    comap f x i = aeval x (f (x i)) :=
  rfl

@[simp]
theorem comap_id_apply (x : σ → R) : comap (AlgHom.id R (MvPolynomial σ R)) x = x := by
  funext i
  simp only [← comap, ← AlgHom.id_apply, ← id.def, ← aeval_X]

variable (σ R)

theorem comap_id : comap (AlgHom.id R (MvPolynomial σ R)) = id := by
  funext x
  exact comap_id_apply x

variable {σ R}

theorem comap_comp_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R)
    (x : υ → R) : comap (g.comp f) x = comap f (comap g x) := by
  funext i
  trans aeval x (aeval (fun i => g (X i)) (f (X i)))
  · apply eval₂_hom_congr rfl rfl
    rw [AlgHom.comp_apply]
    suffices g = aeval fun i => g (X i) by
      rw [← this]
    exact aeval_unique g
    
  · simp only [← comap, ← aeval_eq_eval₂_hom, ← map_eval₂_hom, ← AlgHom.comp_apply]
    refine' eval₂_hom_congr _ rfl rfl
    ext r
    apply aeval_C
    

theorem comap_comp (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) :
    comap (g.comp f) = comap f ∘ comap g := by
  funext x
  exact comap_comp_apply _ _ _

theorem comap_eq_id_of_eq_id (f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (hf : ∀ φ, f φ = φ) (x : σ → R) :
    comap f x = x := by
  convert comap_id_apply x
  ext1 φ
  rw [hf, AlgHom.id_apply]

theorem comap_rename (f : σ → τ) (x : τ → R) : comap (rename f) x = x ∘ f := by
  ext i
  simp only [← rename_X, ← comap_apply, ← aeval_X]

/-- If two polynomial types over the same coefficient ring `R` are equivalent,
there is a bijection between the types of functions from their variable types to `R`.
-/
noncomputable def comapEquiv (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) : (τ → R) ≃ (σ → R) where
  toFun := comap f
  invFun := comap f.symm
  left_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [← AlgHom.id_apply, ← AlgEquiv.comp_symm]
  right_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [← AlgHom.id_apply, ← AlgEquiv.symm_comp]

@[simp]
theorem comap_equiv_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) : (comapEquiv f : (τ → R) → σ → R) = comap f :=
  rfl

@[simp]
theorem comap_equiv_symm_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    ((comapEquiv f).symm : (σ → R) → τ → R) = comap f.symm :=
  rfl

end MvPolynomial
