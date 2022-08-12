/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.RingTheory.HahnSeries
import Mathbin.RingTheory.Localization.FractionRing

/-!
# Laurent Series

## Main Definitions
* Defines `laurent_series` as an abbreviation for `hahn_series ℤ`.
* Provides a coercion `power_series R` into `laurent_series R` given by
  `hahn_series.of_power_series`.
* Defines `laurent_series.power_series_part`
* Defines the localization map `laurent_series.of_power_series_localization` which evaluates to
  `hahn_series.of_power_series`.

-/


open HahnSeries

open BigOperators Classical Polynomial

noncomputable section

universe u

/-- A `laurent_series` is implemented as a `hahn_series` with value group `ℤ`. -/
abbrev LaurentSeries (R : Type _) [Zero R] :=
  HahnSeries ℤ R

variable {R : Type u}

namespace LaurentSeries

section Semiringₓ

variable [Semiringₓ R]

instance : Coe (PowerSeries R) (LaurentSeries R) :=
  ⟨HahnSeries.ofPowerSeries ℤ R⟩

theorem coe_power_series (x : PowerSeries R) : (x : LaurentSeries R) = HahnSeries.ofPowerSeries ℤ R x :=
  rfl

@[simp]
theorem coeff_coe_power_series (x : PowerSeries R) (n : ℕ) :
    HahnSeries.coeff (x : LaurentSeries R) n = PowerSeries.coeff R n x := by
  rw [coe_power_series, of_power_series_apply_coeff]

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `power_series_part` has a nonzero
  constant term.  -/
def powerSeriesPart (x : LaurentSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => x.coeff (x.order + n)

@[simp]
theorem power_series_part_coeff (x : LaurentSeries R) (n : ℕ) :
    PowerSeries.coeff R n x.powerSeriesPart = x.coeff (x.order + n) :=
  PowerSeries.coeff_mk _ _

@[simp]
theorem power_series_part_zero : powerSeriesPart (0 : LaurentSeries R) = 0 := by
  ext
  simp

@[simp]
theorem power_series_part_eq_zero (x : LaurentSeries R) : x.powerSeriesPart = 0 ↔ x = 0 := by
  constructor
  · contrapose!
    intro h
    rw [PowerSeries.ext_iff, not_forall]
    refine' ⟨0, _⟩
    simp [← coeff_order_ne_zero h]
    
  · rintro rfl
    simp
    

@[simp]
theorem single_order_mul_power_series_part (x : LaurentSeries R) :
    (single x.order 1 : LaurentSeries R) * x.powerSeriesPart = x := by
  ext n
  rw [← sub_add_cancel n x.order, single_mul_coeff_add, sub_add_cancel, one_mulₓ]
  by_cases' h : x.order ≤ n
  · rw [Int.eq_nat_abs_of_zero_le (sub_nonneg_of_le h), coeff_coe_power_series, power_series_part_coeff, ←
      Int.eq_nat_abs_of_zero_le (sub_nonneg_of_le h), add_sub_cancel'_right]
    
  · rw [coe_power_series, of_power_series_apply, emb_domain_notin_range]
    · contrapose! h
      exact order_le_of_coeff_ne_zero h.symm
      
    · contrapose! h
      simp only [← Set.mem_range, ← RelEmbedding.coe_fn_mk, ← Function.Embedding.coe_fn_mk] at h
      obtain ⟨m, hm⟩ := h
      rw [← sub_nonneg, ← hm]
      exact Int.zero_le_of_nat _
      
    

theorem of_power_series_power_series_part (x : LaurentSeries R) :
    ofPowerSeries ℤ R x.powerSeriesPart = single (-x.order) 1 * x := by
  refine' Eq.trans _ (congr rfl x.single_order_mul_power_series_part)
  rw [← mul_assoc, single_mul_single, neg_add_selfₓ, mul_oneₓ, ← C_apply, C_one, one_mulₓ, coe_power_series]

end Semiringₓ

instance [CommSemiringₓ R] : Algebra (PowerSeries R) (LaurentSeries R) :=
  (HahnSeries.ofPowerSeries ℤ R).toAlgebra

@[simp]
theorem coe_algebra_map [CommSemiringₓ R] :
    ⇑(algebraMap (PowerSeries R) (LaurentSeries R)) = HahnSeries.ofPowerSeries ℤ R :=
  rfl

/-- The localization map from power series to Laurent series. -/
@[simps]
instance of_power_series_localization [CommRingₓ R] :
    IsLocalization (Submonoid.powers (PowerSeries.x : PowerSeries R)) (LaurentSeries R) where
  map_units := by
    rintro ⟨_, n, rfl⟩
    refine' ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, _, _⟩, _⟩
    · simp only [← single_mul_single, ← mul_oneₓ, ← add_right_negₓ]
      rfl
      
    · simp only [← single_mul_single, ← mul_oneₓ, ← add_left_negₓ]
      rfl
      
    · simp
      
  surj := by
    intro z
    by_cases' h : 0 ≤ z.order
    · refine' ⟨⟨PowerSeries.x ^ Int.natAbs z.order * power_series_part z, 1⟩, _⟩
      simp only [← RingHom.map_one, ← mul_oneₓ, ← RingHom.map_mul, ← coe_algebra_map, ← of_power_series_X_pow, ←
        Submonoid.coe_one]
      rw [Int.nat_abs_of_nonneg h, ← coe_power_series, single_order_mul_power_series_part]
      
    · refine' ⟨⟨power_series_part z, PowerSeries.x ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, _⟩
      simp only [← coe_algebra_map, ← of_power_series_power_series_part]
      rw [mul_comm _ z]
      refine' congr rfl _
      rw [Subtype.coe_mk, of_power_series_X_pow, Int.of_nat_nat_abs_of_nonpos]
      exact le_of_not_geₓ h
      
  eq_iff_exists := by
    intro x y
    rw [coe_algebra_map, of_power_series_injective.eq_iff]
    constructor
    · rintro rfl
      exact ⟨1, rfl⟩
      
    · rintro ⟨⟨_, n, rfl⟩, hc⟩
      rw [← sub_eq_zero, ← sub_mul, PowerSeries.ext_iff] at hc
      rw [← sub_eq_zero, PowerSeries.ext_iff]
      intro m
      have h := hc (m + n)
      rw [LinearMap.map_zero, Subtype.coe_mk, PowerSeries.X_pow_eq, PowerSeries.monomial, PowerSeries.coeff,
        Finsupp.single_add, MvPowerSeries.coeff_add_mul_monomial, mul_oneₓ] at h
      exact h
      

instance {K : Type u} [Field K] : IsFractionRing (PowerSeries K) (LaurentSeries K) :=
  IsLocalization.of_le (Submonoid.powers (PowerSeries.x : PowerSeries K)) _
    (powers_le_non_zero_divisors_of_no_zero_divisors PowerSeries.X_ne_zero) fun f hf =>
    is_unit_of_mem_non_zero_divisors <| map_mem_non_zero_divisors _ HahnSeries.of_power_series_injective hf

end LaurentSeries

namespace PowerSeries

open LaurentSeries

variable {R' : Type _} [Semiringₓ R] [Ringₓ R'] (f g : PowerSeries R) (f' g' : PowerSeries R')

@[simp, norm_cast]
theorem coe_zero : ((0 : PowerSeries R) : LaurentSeries R) = 0 :=
  (ofPowerSeries ℤ R).map_zero

@[simp, norm_cast]
theorem coe_one : ((1 : PowerSeries R) : LaurentSeries R) = 1 :=
  (ofPowerSeries ℤ R).map_one

@[simp, norm_cast]
theorem coe_add : ((f + g : PowerSeries R) : LaurentSeries R) = f + g :=
  (ofPowerSeries ℤ R).map_add _ _

@[simp, norm_cast]
theorem coe_sub : ((f' - g' : PowerSeries R') : LaurentSeries R') = f' - g' :=
  (ofPowerSeries ℤ R').map_sub _ _

@[simp, norm_cast]
theorem coe_neg : ((-f' : PowerSeries R') : LaurentSeries R') = -f' :=
  (ofPowerSeries ℤ R').map_neg _

@[simp, norm_cast]
theorem coe_mul : ((f * g : PowerSeries R) : LaurentSeries R) = f * g :=
  (ofPowerSeries ℤ R).map_mul _ _

theorem coeff_coe (i : ℤ) :
    ((f : PowerSeries R) : LaurentSeries R).coeff i = if i < 0 then 0 else PowerSeries.coeff R i.natAbs f := by
  cases i
  · rw [Int.nat_abs_of_nat_core, Int.of_nat_eq_coe, coeff_coe_power_series, if_neg (Int.coe_nat_nonneg _).not_lt]
    
  · rw [coe_power_series, of_power_series_apply, emb_domain_notin_image_support, if_pos (Int.neg_succ_lt_zeroₓ _)]
    simp only [← not_exists, ← RelEmbedding.coe_fn_mk, ← Set.mem_image, ← not_and, ← Function.Embedding.coe_fn_mk, ←
      Ne.def, ← to_power_series_symm_apply_coeff, ← mem_support, ← Int.coe_nat_eq, ← implies_true_iff, ← not_false_iff]
    

@[simp, norm_cast]
theorem coe_C (r : R) : ((c R r : PowerSeries R) : LaurentSeries R) = HahnSeries.c r :=
  of_power_series_C _

@[simp]
theorem coe_X : ((x : PowerSeries R) : LaurentSeries R) = single 1 1 :=
  of_power_series_X

@[simp, norm_cast]
theorem coe_smul {S : Type _} [Semiringₓ S] [Module R S] (r : R) (x : PowerSeries S) :
    ((r • x : PowerSeries S) : LaurentSeries S) = r • x := by
  ext
  simp [← coeff_coe, ← coeff_smul, ← smul_ite]

@[simp, norm_cast]
theorem coe_bit0 : ((bit0 f : PowerSeries R) : LaurentSeries R) = bit0 f :=
  (ofPowerSeries ℤ R).map_bit0 _

@[simp, norm_cast]
theorem coe_bit1 : ((bit1 f : PowerSeries R) : LaurentSeries R) = bit1 f :=
  (ofPowerSeries ℤ R).map_bit1 _

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : PowerSeries R) : LaurentSeries R) = f ^ n :=
  (ofPowerSeries ℤ R).map_pow _ _

end PowerSeries

