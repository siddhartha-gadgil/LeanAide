/-
Copyright (c) 2021 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Eric Wieser
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.Algebra.FreeAlgebra

/-!
# Characteristics of algebras

In this file we describe the characteristic of `R`-algebras.

In particular we are interested in the characteristic of free algebras over `R`
and the fraction field `fraction_ring R`.


## Main results

- `char_p_of_injective_algebra_map` If `R →+* A` is an injective algebra map
  then `A` has the same characteristic as `R`.

Instances constructed from this result:
- Any `free_algebra R X` has the same characteristic as `R`.
- The `fraction_ring R` of an integral domain `R` has the same characteristic as `R`.

-/


/-- If the algebra map `R →+* A` is injective then `A` has the same characteristic as `R`. -/
theorem char_p_of_injective_algebra_map {R A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (p : ℕ) [CharP R p] : CharP A p :=
  { cast_eq_zero_iff := fun x => by
      rw [← CharP.cast_eq_zero_iff R p x]
      change algebraMap ℕ A x = 0 ↔ algebraMap ℕ R x = 0
      rw [IsScalarTower.algebra_map_apply ℕ R A x]
      refine' Iff.trans _ h.eq_iff
      rw [RingHom.map_zero] }

theorem char_p_of_injective_algebra_map' (R A : Type _) [Field R] [Semiringₓ A] [Algebra R A] [Nontrivial A] (p : ℕ)
    [CharP R p] : CharP A p :=
  char_p_of_injective_algebra_map (algebraMap R A).Injective p

/-- If the algebra map `R →+* A` is injective and `R` has characteristic zero then so does `A`. -/
theorem char_zero_of_injective_algebra_map {R A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A :=
  { cast_injective := fun x y hxy => by
      change algebraMap ℕ A x = algebraMap ℕ A y at hxy
      rw [IsScalarTower.algebra_map_apply ℕ R A x] at hxy
      rw [IsScalarTower.algebra_map_apply ℕ R A y] at hxy
      exact CharZero.cast_injective (h hxy) }

-- `char_p.char_p_to_char_zero A _ (char_p_of_injective_algebra_map h 0)` does not work
-- here as it would require `ring A`.
section

variable (K L : Type _) [Field K] [CommSemiringₓ L] [Nontrivial L] [Algebra K L]

theorem Algebra.char_p_iff (p : ℕ) : CharP K p ↔ CharP L p :=
  (algebraMap K L).char_p_iff_char_p p

end

namespace FreeAlgebra

variable {R X : Type _} [CommSemiringₓ R] (p : ℕ)

/-- If `R` has characteristic `p`, then so does `free_algebra R X`. -/
instance char_p [CharP R p] : CharP (FreeAlgebra R X) p :=
  char_p_of_injective_algebra_map FreeAlgebra.algebra_map_left_inverse.Injective p

/-- If `R` has characteristic `0`, then so does `free_algebra R X`. -/
instance char_zero [CharZero R] : CharZero (FreeAlgebra R X) :=
  char_zero_of_injective_algebra_map FreeAlgebra.algebra_map_left_inverse.Injective

end FreeAlgebra

namespace IsFractionRing

variable (R : Type _) {K : Type _} [CommRingₓ R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (p : ℕ)

/-- If `R` has characteristic `p`, then so does Frac(R). -/
theorem char_p_of_is_fraction_ring [CharP R p] : CharP K p :=
  char_p_of_injective_algebra_map (IsFractionRing.injective R K) p

/-- If `R` has characteristic `0`, then so does Frac(R). -/
theorem char_zero_of_is_fraction_ring [CharZero R] : CharZero K :=
  @CharP.char_p_to_char_zero K _ (char_p_of_is_fraction_ring R 0)

variable [IsDomain R]

/-- If `R` has characteristic `p`, then so does `fraction_ring R`. -/
instance char_p [CharP R p] : CharP (FractionRing R) p :=
  char_p_of_is_fraction_ring R p

/-- If `R` has characteristic `0`, then so does `fraction_ring R`. -/
instance char_zero [CharZero R] : CharZero (FractionRing R) :=
  char_zero_of_is_fraction_ring R

end IsFractionRing

