/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathbin.Data.Polynomial.Taylor
import Mathbin.FieldTheory.Ratfunc
import Mathbin.RingTheory.LaurentSeries

/-!
# Laurent expansions of rational functions

## Main declarations

* `ratfunc.laurent`: the Laurent expansion of the rational function `f` at `r`, as an `alg_hom`.
* `ratfunc.laurent_injective`: the Laurent expansion at `r` is unique

## Implementation details

Implemented as the quotient of two Taylor expansions, over domains.
An auxiliary definition is provided first to make the construction of the `alg_hom` easier,
  which works on `comm_ring` which are not necessarily domains.
-/


universe u

namespace Ratfunc

noncomputable section

open Polynomial

open Classical nonZeroDivisors Polynomial

variable {R : Type u} [CommRingₓ R] [hdomain : IsDomain R] (r s : R) (p q : R[X]) (f : Ratfunc R)

theorem taylor_mem_non_zero_divisors (hp : p ∈ R[X]⁰) : taylor r p ∈ R[X]⁰ := by
  rw [mem_non_zero_divisors_iff]
  intro x hx
  have : x = taylor (r - r) x := by
    simp
  rwa [this, sub_eq_add_neg, ← taylor_taylor, ← taylor_mul, LinearMap.map_eq_zero_iff _ (taylor_injective _),
    mul_right_mem_non_zero_divisors_eq_zero_iff hp, LinearMap.map_eq_zero_iff _ (taylor_injective _)] at hx

/-- The Laurent expansion of rational functions about a value.
Auxiliary definition, usage when over integral domains should prefer `ratfunc.laurent`. -/
def laurentAux : Ratfunc R →+* Ratfunc R :=
  Ratfunc.mapRingHom (RingHom.mk (taylor r) (taylor_one _) (taylor_mul _) (LinearMap.map_zero _) (LinearMap.map_add _))
    (taylor_mem_non_zero_divisors _)

theorem laurent_aux_of_fraction_ring_mk (q : R[X]⁰) :
    laurentAux r (of_fraction_ring (Localization.mk p q)) =
      of_fraction_ring (Localization.mk (taylor r p) ⟨taylor r q, taylor_mem_non_zero_divisors r q q.Prop⟩) :=
  map_apply_of_fraction_ring_mk _ _ _ _

include hdomain

theorem laurent_aux_div :
    laurentAux r (algebraMap _ _ p / algebraMap _ _ q) = algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  map_apply_div _ _ _ _

@[simp]
theorem laurent_aux_algebra_map : laurentAux r (algebraMap _ _ p) = algebraMap _ _ (taylor r p) := by
  rw [← mk_one, ← mk_one, mk_eq_div, laurent_aux_div, mk_eq_div, taylor_one, _root_.map_one]

/-- The Laurent expansion of rational functions about a value. -/
def laurent : Ratfunc R →ₐ[R] Ratfunc R :=
  Ratfunc.mapAlgHom
    (AlgHom.mk (taylor r) (taylor_one _) (taylor_mul _) (LinearMap.map_zero _) (LinearMap.map_add _)
      (by
        simp [← Polynomial.algebra_map_apply]))
    (taylor_mem_non_zero_divisors _)

theorem laurent_div :
    laurent r (algebraMap _ _ p / algebraMap _ _ q) = algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  laurent_aux_div r p q

@[simp]
theorem laurent_algebra_map : laurent r (algebraMap _ _ p) = algebraMap _ _ (taylor r p) :=
  laurent_aux_algebra_map _ _

@[simp]
theorem laurent_X : laurent r x = X + c r := by
  rw [← algebra_map_X, laurent_algebra_map, taylor_X, _root_.map_add, algebra_map_C]

@[simp]
theorem laurent_C (x : R) : laurent r (c x) = c x := by
  rw [← algebra_map_C, laurent_algebra_map, taylor_C]

@[simp]
theorem laurent_at_zero : laurent 0 f = f := by
  induction f using Ratfunc.induction_on
  simp

theorem laurent_laurent : laurent r (laurent s f) = laurent (r + s) f := by
  induction f using Ratfunc.induction_on
  simp_rw [laurent_div, taylor_taylor]

theorem laurent_injective : Function.Injective (laurent r) := fun _ _ h => by
  simpa [← laurent_laurent] using congr_arg (laurent (-r)) h

end Ratfunc

