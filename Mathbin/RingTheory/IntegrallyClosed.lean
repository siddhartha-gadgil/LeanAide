/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.RingTheory.IntegralClosure
import Mathbin.RingTheory.Localization.Integral

/-!
# Integrally closed rings

An integrally closed domain `R` contains all the elements of `Frac(R)` that are
integral over `R`. A special case of integrally closed domains are the Dedekind domains.

## Main definitions

* `is_integrally_closed R` states `R` contains all integral elements of `Frac(R)`

## Main results

* `is_integrally_closed_iff K`, where `K` is a fraction field of `R`, states `R`
  is integrally closed iff it is the integral closure of `R` in `K`
-/


open nonZeroDivisors

/-- `R` is integrally closed if all integral elements of `Frac(R)` are also elements of `R`.

This definition uses `fraction_ring R` to denote `Frac(R)`. See `is_integrally_closed_iff`
if you want to choose another field of fractions for `R`.
-/
class IsIntegrallyClosed (R : Type _) [CommRingₓ R] [IsDomain R] : Prop where
  algebra_map_eq_of_integral : ∀ {x : FractionRing R}, IsIntegral R x → ∃ y, algebraMap R (FractionRing R) y = x

section Iff

variable {R : Type _} [CommRingₓ R] [IsDomain R]

variable (K : Type _) [Field K] [Algebra R K] [IsFractionRing R K]

/-- `R` is integrally closed iff all integral elements of its fraction field `K`
are also elements of `R`. -/
theorem is_integrally_closed_iff : IsIntegrallyClosed R ↔ ∀ {x : K}, IsIntegral R x → ∃ y, algebraMap R K y = x := by
  let e : K ≃ₐ[R] FractionRing R := IsLocalization.algEquiv R⁰ _ _
  constructor
  · rintro ⟨cl⟩
    refine' fun x hx => _
    obtain ⟨y, hy⟩ := cl ((is_integral_alg_equiv e).mpr hx)
    exact ⟨y, e.algebra_map_eq_apply.mp hy⟩
    
  · rintro cl
    refine' ⟨fun x hx => _⟩
    obtain ⟨y, hy⟩ := cl ((is_integral_alg_equiv e.symm).mpr hx)
    exact ⟨y, e.symm.algebra_map_eq_apply.mp hy⟩
    

/-- `R` is integrally closed iff it is the integral closure of itself in its field of fractions. -/
theorem is_integrally_closed_iff_is_integral_closure : IsIntegrallyClosed R ↔ IsIntegralClosure R R K :=
  (is_integrally_closed_iff K).trans <| by
    let e : K ≃ₐ[R] FractionRing R := IsLocalization.algEquiv R⁰ _ _
    constructor
    · intro cl
      refine' ⟨IsFractionRing.injective _ _, fun x => ⟨cl, _⟩⟩
      rintro ⟨y, y_eq⟩
      rw [← y_eq]
      exact is_integral_algebra_map
      
    · rintro ⟨-, cl⟩ x hx
      exact cl.mp hx
      

end Iff

namespace IsIntegrallyClosed

variable {R : Type _} [CommRingₓ R] [id : IsDomain R] [iic : IsIntegrallyClosed R]

variable {K : Type _} [Field K] [Algebra R K] [ifr : IsFractionRing R K]

include iic ifr

instance : IsIntegralClosure R R K :=
  (is_integrally_closed_iff_is_integral_closure K).mp iic

theorem is_integral_iff {x : K} : IsIntegral R x ↔ ∃ y : R, algebraMap R K y = x :=
  IsIntegralClosure.is_integral_iff

theorem exists_algebra_map_eq_of_is_integral_pow {x : K} {n : ℕ} (hn : 0 < n) (hx : IsIntegral R <| x ^ n) :
    ∃ y : R, algebraMap R K y = x :=
  is_integral_iff.mp <| is_integral_of_pow hn hx

omit iic ifr

theorem exists_algebra_map_eq_of_pow_mem_subalgebra {K : Type _} [Field K] [Algebra R K] {S : Subalgebra R K}
    [IsIntegrallyClosed S] [IsFractionRing S K] {x : K} {n : ℕ} (hn : 0 < n) (hx : x ^ n ∈ S) :
    ∃ y : S, algebraMap S K y = x :=
  exists_algebra_map_eq_of_is_integral_pow hn <| is_integral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩

include id ifr

variable {R} (K)

theorem integral_closure_eq_bot_iff : integralClosure R K = ⊥ ↔ IsIntegrallyClosed R := by
  refine' eq_bot_iff.trans _
  constructor
  · rw [is_integrally_closed_iff K]
    intro h x hx
    exact set.mem_range.mp (algebra.mem_bot.mp (h hx))
    assumption
    
  · intro h x hx
    rw [Algebra.mem_bot, Set.mem_range]
    exact is_integral_iff.mp hx
    

include iic

variable (R K)

@[simp]
theorem integral_closure_eq_bot : integralClosure R K = ⊥ :=
  (integral_closure_eq_bot_iff K).mpr ‹_›

end IsIntegrallyClosed

namespace integralClosure

open IsIntegrallyClosed

variable {R : Type _} [CommRingₓ R] [IsDomain R]

variable (K : Type _) [Field K] [Algebra R K] [IsFractionRing R K]

variable {L : Type _} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

-- Can't be an instance because you need to supply `K`.
theorem is_integrally_closed_of_finite_extension [FiniteDimensional K L] : IsIntegrallyClosed (integralClosure R L) :=
  by
  let this : IsFractionRing (integralClosure R L) L := is_fraction_ring_of_finite_extension K L
  exact (integral_closure_eq_bot_iff L).mp integral_closure_idem

end integralClosure

