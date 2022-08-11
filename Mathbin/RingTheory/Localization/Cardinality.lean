/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.RingTheory.IntegralDomain
import Mathbin.RingTheory.Localization.Basic
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of localizations

In this file, we establish the cardinality of localizations. In most cases, a localization has
cardinality equal to the base ring. If there are zero-divisors, however, this is no longer true -
for example, `zmod 6` localized at `{2, 4}` is equal to `zmod 3`, and if you have zero in your
submonoid, then your localization is trivial (see `is_localization.unique_of_zero_mem`).

## Main statements

* `is_localization.card_le`: A localization has cardinality no larger than the base ring.
* `is_localization.card`: If you don't localize at zero-divisors, the localization of a ring has
  cardinality equal to its base ring,

-/


open Cardinal nonZeroDivisors

universe u v

namespace IsLocalization

variable {R : Type u} [CommRingₓ R] (S : Submonoid R) {L : Type u} [CommRingₓ L] [Algebra R L] [IsLocalization S L]

include S

/-- Localizing a finite ring can only reduce the amount of elements. -/
theorem algebra_map_surjective_of_fintype [Fintype R] : Function.Surjective (algebraMap R L) := by
  classical
  have : Fintype L := IsLocalization.fintype' S L
  intro x
  obtain ⟨⟨r, s⟩, h : x * (algebraMap R L) ↑s = (algebraMap R L) r⟩ := IsLocalization.surj S x
  obtain ⟨n, hn, hp⟩ := (is_of_fin_order_iff_pow_eq_one _).1 (exists_pow_eq_one (IsLocalization.map_units L s).Unit)
  rw [Units.ext_iff, Units.coe_pow, IsUnit.unit_spec, ← Nat.succ_pred_eq_of_posₓ hn, pow_succₓ] at hp
  exact
    ⟨r * s ^ (n - 1), by
      erw [map_mul, map_pow, ← h, mul_assoc, hp, mul_oneₓ]⟩

/-- A localization always has cardinality less than or equal to the base ring. -/
theorem card_le : # L ≤ # R := by
  classical
  cases fintypeOrInfinite R
  · exact Cardinal.mk_le_of_surjective (algebra_map_surjective_of_fintype S)
    
  erw [← Cardinal.mul_eq_self <| Cardinal.aleph_0_le_mk R]
  set f : R × R → L := fun aa => IsLocalization.mk' _ aa.1 (if h : aa.2 ∈ S then ⟨aa.2, h⟩ else 1)
  refine' @Cardinal.mk_le_of_surjective _ _ f fun a => _
  obtain ⟨x, y, h⟩ := IsLocalization.mk'_surjective S a
  use (x, y)
  dsimp' [← f]
  rwa [dif_pos <| show ↑y ∈ S from y.2, SetLike.eta]

variable (L)

/-- If you do not localize at any zero-divisors, localization preserves cardinality. -/
theorem card (hS : S ≤ R⁰) : # R = # L :=
  (Cardinal.mk_le_of_injective (IsLocalization.injective L hS)).antisymm (card_le S)

end IsLocalization

