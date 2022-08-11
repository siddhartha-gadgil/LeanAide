/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Algebra.Tower
import Mathbin.Data.Polynomial.AlgebraMap

/-!
# Algebra towers for polynomial

This file proves some basic results about the algebra tower structure for the type `polynomial R`.

This structure itself is provided elsewhere as `polynomial.is_scalar_tower`
-/


universe u v w u₁

open Polynomial

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace IsScalarTower

section Semiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ S] [Semiringₓ A] [Semiringₓ B]

variable [Algebra R S] [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

variable (R S A) {B}

theorem aeval_apply (x : A) (p : R[X]) :
    Polynomial.aeval x p = Polynomial.aeval x (Polynomial.map (algebraMap R S) p) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, algebra_map_eq R S A]

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ A] [Semiringₓ B]

variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

theorem algebra_map_aeval (x : A) (p : R[X]) :
    algebraMap A B (Polynomial.aeval x p) = Polynomial.aeval (algebraMap A B x) p := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, ← IsScalarTower.algebra_map_eq]

theorem aeval_eq_zero_of_aeval_algebra_map_eq_zero {x : A} {p : R[X]} (h : Function.Injective (algebraMap A B))
    (hp : Polynomial.aeval (algebraMap A B x) p = 0) : Polynomial.aeval x p = 0 := by
  rw [← algebra_map_aeval, ← (algebraMap A B).map_zero] at hp
  exact h hp

theorem aeval_eq_zero_of_aeval_algebra_map_eq_zero_field {R A B : Type _} [CommSemiringₓ R] [Field A] [CommSemiringₓ B]
    [Nontrivial B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] {x : A} {p : R[X]}
    (h : Polynomial.aeval (algebraMap A B x) p = 0) : Polynomial.aeval x p = 0 :=
  aeval_eq_zero_of_aeval_algebra_map_eq_zero R A B (algebraMap A B).Injective h

end CommSemiringₓ

end IsScalarTower

namespace Subalgebra

open IsScalarTower

section CommSemiringₓ

variable (R) {S A} [CommSemiringₓ R] [CommSemiringₓ S] [CommSemiringₓ A]

variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

@[simp]
theorem aeval_coe {S : Subalgebra R A} {x : S} {p : R[X]} : Polynomial.aeval (x : A) p = Polynomial.aeval x p :=
  (algebra_map_aeval R S A x p).symm

end CommSemiringₓ

end Subalgebra

