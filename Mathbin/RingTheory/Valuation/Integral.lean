/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.RingTheory.IntegrallyClosed
import Mathbin.RingTheory.Valuation.Integers

/-!
# Integral elements over the ring of integers of a valution

The ring of integers is integrally closed inside the original ring.
-/


universe u v w

open BigOperators

namespace Valuation

namespace Integers

section CommRingₓ

variable {R : Type u} {Γ₀ : Type v} [CommRingₓ R] [LinearOrderedCommGroupWithZero Γ₀]

variable {v : Valuation R Γ₀} {O : Type w} [CommRingₓ O] [Algebra O R] (hv : Integers v O)

include hv

open Polynomial

theorem mem_of_integral {x : R} (hx : IsIntegral O x) : x ∈ v.integer :=
  let ⟨p, hpm, hpx⟩ := hx
  le_of_not_ltₓ fun hvx : 1 < v x => by
    rw [hpm.as_sum, eval₂_add, eval₂_pow, eval₂_X, eval₂_finset_sum, add_eq_zero_iff_eq_neg] at hpx
    replace hpx := congr_arg v hpx
    refine' ne_of_gtₓ _ hpx
    rw [v.map_neg, v.map_pow]
    refine' v.map_sum_lt' (zero_lt_one₀.trans_le (one_le_pow_of_one_le' hvx.le _)) fun i hi => _
    rw [eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, v.map_mul, v.map_pow, ← one_mulₓ (v x ^ p.nat_degree)]
    cases' (hv.2 <| p.coeff i).lt_or_eq with hvpi hvpi
    · exact mul_lt_mul₀ hvpi (pow_lt_pow₀ hvx <| Finset.mem_range.1 hi)
      
    · erw [hvpi]
      rw [one_mulₓ, one_mulₓ]
      exact pow_lt_pow₀ hvx (Finset.mem_range.1 hi)
      

protected theorem integral_closure : integralClosure O R = ⊥ :=
  bot_unique fun r hr =>
    let ⟨x, hx⟩ := hv.3 (hv.mem_of_integral hr)
    Algebra.mem_bot.2 ⟨x, hx⟩

end CommRingₓ

section FractionField

variable {K : Type u} {Γ₀ : Type v} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

variable {v : Valuation K Γ₀} {O : Type w} [CommRingₓ O] [IsDomain O]

variable [Algebra O K] [IsFractionRing O K]

variable (hv : Integers v O)

theorem integrally_closed : IsIntegrallyClosed O :=
  (IsIntegrallyClosed.integral_closure_eq_bot_iff K).mp (Valuation.Integers.integral_closure hv)

end FractionField

end Integers

end Valuation

