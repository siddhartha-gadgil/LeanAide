/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Data.W.Cardinal
import Mathbin.Data.MvPolynomial.Basic

/-!
# Cardinality of Polynomial Ring

The main result in this file is `mv_polynomial.cardinal_mk_le_max`, which says that
the cardinality of `mv_polynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ℵ₀`.

-/


universe u

/-
The definitions `mv_polynomial_fun` and `arity` are motivated by defining the following
inductive type as a `W_type` in order to be able to use theorems about the cardinality
of `W_type`.

inductive mv_polynomial_term (σ R : Type u) : Type u
| of_ring : R → mv_polynomial_term
| X : σ → mv_polynomial_term
| add : mv_polynomial_term → mv_polynomial_term → mv_polynomial_term
| mul : mv_polynomial_term → mv_polynomial_term → mv_polynomial_term

`W_type (arity σ R)` is isomorphic to the above type.
-/
open Cardinal

open Cardinal

/-- A type used to prove theorems about the cardinality of `mv_polynomial σ R`. The
`W_type (arity σ R)` has a constant for every element of `R` and `σ` and two binary functions. -/
private def mv_polynomial_fun (σ R : Type u) : Type u :=
  Sum R (Sum σ (ULift.{u} Bool))

variable (σ R : Type u)

/-- A function used to prove theorems about the cardinality of `mv_polynomial σ R`.
  The type ``W_type (arity σ R)` has a constant for every element of `R` and `σ` and two binary
  functions. -/
private def arity : MvPolynomialFun σ R → Type u
  | Sum.inl _ => Pempty
  | Sum.inr (Sum.inl _) => Pempty
  | Sum.inr (Sum.inr ⟨ff⟩) => ULift Bool
  | Sum.inr (Sum.inr ⟨tt⟩) => ULift Bool

private def arity_fintype (x : MvPolynomialFun σ R) : Fintype (Arity σ R x) := by
  rcases x with (x | x | ⟨_ | _⟩) <;> dsimp' [← arity] <;> infer_instance

attribute [local instance] arity_fintype

variable {σ R}

variable [CommSemiringₓ R]

/-- The surjection from `W_type (arity σ R)` into `mv_polynomial σ R`. -/
private noncomputable def to_mv_polynomial : WType (Arity σ R) → MvPolynomial σ R
  | ⟨Sum.inl r, _⟩ => MvPolynomial.c r
  | ⟨Sum.inr (Sum.inl i), _⟩ => MvPolynomial.x i
  | ⟨Sum.inr (Sum.inr ⟨ff⟩), f⟩ => to_mv_polynomial (f (ULift.up true)) * to_mv_polynomial (f (ULift.up false))
  | ⟨Sum.inr (Sum.inr ⟨tt⟩), f⟩ => to_mv_polynomial (f (ULift.up true)) + to_mv_polynomial (f (ULift.up false))

private theorem to_mv_polynomial_surjective : Function.Surjective (@toMvPolynomial σ R _) := by
  intro p
  induction' p using MvPolynomial.induction_on with x p₁ p₂ ih₁ ih₂ p i ih
  · exact ⟨WType.mk (Sum.inl x) Pempty.elimₓ, rfl⟩
    
  · rcases ih₁ with ⟨w₁, rfl⟩
    rcases ih₂ with ⟨w₂, rfl⟩
    exact
      ⟨WType.mk (Sum.inr (Sum.inr ⟨tt⟩)) fun x => cond x.down w₁ w₂, by
        simp [← to_mv_polynomial]⟩
    
  · rcases ih with ⟨w, rfl⟩
    exact
      ⟨WType.mk (Sum.inr (Sum.inr ⟨ff⟩)) fun x => cond x.down w (WType.mk (Sum.inr (Sum.inl i)) Pempty.elimₓ), by
        simp [← to_mv_polynomial]⟩
    

private theorem cardinal_mv_polynomial_fun_le : # (MvPolynomialFun σ R) ≤ max (max (# R) (# σ)) ℵ₀ :=
  calc
    # (MvPolynomialFun σ R) = # R + # σ + # (ULift Bool) := by
      dsimp' [← mv_polynomial_fun] <;> simp only [add_def, ← add_assocₓ, ← Cardinal.mk_ulift]
    _ ≤ max (max (# R + # σ) (# (ULift Bool))) ℵ₀ := add_le_max _ _
    _ ≤ max (max (max (max (# R) (# σ)) ℵ₀) (# (ULift Bool))) ℵ₀ :=
      max_le_max (max_le_max (add_le_max _ _) le_rfl) le_rfl
    _ ≤ _ := by
      simp only [← max_commₓ ℵ₀, ← max_assocₓ, ← max_left_commₓ ℵ₀, ← max_selfₓ, ←
        max_eq_leftₓ (lt_aleph_0_of_finite (ULift.{u} Bool)).le]
    

namespace MvPolynomial

/-- The cardinality of the multivariate polynomial ring, `mv_polynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀` -/
theorem cardinal_mk_le_max {σ R : Type u} [CommSemiringₓ R] : # (MvPolynomial σ R) ≤ max (max (# R) (# σ)) ℵ₀ :=
  calc
    # (MvPolynomial σ R) ≤ # (WType (Arity σ R)) := Cardinal.mk_le_of_surjective to_mv_polynomial_surjective
    _ ≤ max (# (MvPolynomialFun σ R)) ℵ₀ := WType.cardinal_mk_le_max_aleph_0_of_finite
    _ ≤ _ := max_le_max cardinal_mv_polynomial_fun_le le_rfl
    _ ≤ _ := by
      simp only [← max_assocₓ, ← max_selfₓ]
    

end MvPolynomial

