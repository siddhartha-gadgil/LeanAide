/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Integer
import Mathbin.RingTheory.UniqueFactorizationDomain

/-!
# Numerator and denominator in a localization

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRingₓ R] (M : Submonoid R) {S : Type _} [CommRingₓ S]

variable [Algebra R S] {P : Type _} [CommRingₓ P]

namespace IsFractionRing

open IsLocalization

section NumDenom

variable (A : Type _) [CommRingₓ A] [IsDomain A] [UniqueFactorizationMonoid A]

variable {K : Type _} [Field K] [Algebra A K] [IsFractionRing A K]

theorem exists_reduced_fraction (x : K) :
    ∃ (a : A)(b : nonZeroDivisors A), (∀ {d}, d ∣ a → d ∣ b → IsUnit d) ∧ mk' K a b = x := by
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (nonZeroDivisors A) x
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b (mem_non_zero_divisors_iff_ne_zero.mp b_nonzero)
  obtain ⟨c'_nonzero, b'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero
  refine' ⟨a', ⟨b', b'_nonzero⟩, @no_factor, _⟩
  refine' mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors b_nonzero) _
  simp only [← Subtype.coe_mk, ← RingHom.map_mul, ← Algebra.smul_def] at *
  erw [← hab, mul_assoc, mk'_spec' _ a' ⟨b', b'_nonzero⟩]

/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
noncomputable def num (x : K) : A :=
  Classical.some (exists_reduced_fraction A x)

/-- `f.num x` is the denominator of `x : f.codomain` as a reduced fraction. -/
noncomputable def denom (x : K) : nonZeroDivisors A :=
  Classical.some (Classical.some_spec (exists_reduced_fraction A x))

theorem num_denom_reduced (x : K) : ∀ {d}, d ∣ num A x → d ∣ denom A x → IsUnit d :=
  (Classical.some_spec (Classical.some_spec (exists_reduced_fraction A x))).1

@[simp]
theorem mk'_num_denom (x : K) : mk' K (num A x) (denom A x) = x :=
  (Classical.some_spec (Classical.some_spec (exists_reduced_fraction A x))).2

variable {A}

theorem num_mul_denom_eq_num_iff_eq {x y : K} : x * algebraMap A K (denom A y) = algebraMap A K (num A y) ↔ x = y :=
  ⟨fun h => by
    simpa only [← mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp
      (by
        rw [h, mk'_num_denom])⟩

theorem num_mul_denom_eq_num_iff_eq' {x y : K} : y * algebraMap A K (denom A x) = algebraMap A K (num A x) ↔ x = y :=
  ⟨fun h => by
    simpa only [← eq_comm, ← mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp
      (by
        rw [h, mk'_num_denom])⟩

theorem num_mul_denom_eq_num_mul_denom_iff_eq {x y : K} : num A y * denom A x = num A x * denom A y ↔ x = y :=
  ⟨fun h => by
    simpa only [← mk'_num_denom] using mk'_eq_of_eq h, fun h => by
    rw [h]⟩

theorem eq_zero_of_num_eq_zero {x : K} (h : num A x = 0) : x = 0 :=
  num_mul_denom_eq_num_iff_eq'.mp
    (by
      rw [zero_mul, h, RingHom.map_zero])

theorem is_integer_of_is_unit_denom {x : K} (h : IsUnit (denom A x : A)) : IsInteger A x := by
  cases' h with d hd
  have d_ne_zero : algebraMap A K (denom A x) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors (denom A x).2
  use ↑d⁻¹ * Num A x
  refine' trans _ (mk'_num_denom A x)
  rw [RingHom.map_mul, RingHom.map_units_inv, hd]
  apply mul_left_cancel₀ d_ne_zero
  rw [← mul_assoc, mul_inv_cancel d_ne_zero, one_mulₓ, mk'_spec']

theorem is_unit_denom_of_num_eq_zero {x : K} (h : num A x = 0) : IsUnit (denom A x : A) :=
  num_denom_reduced A x (h.symm ▸ dvd_zero _) dvd_rfl

end NumDenom

variable (S)

end IsFractionRing

