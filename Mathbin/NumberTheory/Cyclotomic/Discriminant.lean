/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathbin.RingTheory.Discriminant

/-!
# Discriminant of cyclotomic fields
We compute the discriminant of a `p ^ n`-th cyclotomic extension.

## Main results
* `is_cyclotomic_extension.discr_odd_prime` : if `p` is an odd prime such that
  `is_cyclotomic_extension {p} K L` and `irreducible (cyclotomic p K)`, then
  `discr K (hζ.power_basis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` for any
  `hζ : is_primitive_root ζ p`.

-/


universe u v

open Algebra Polynomial Nat IsPrimitiveRoot PowerBasis

open Polynomial Cyclotomic

namespace IsPrimitiveRoot

variable {n : ℕ+} {K : Type u} [Field K] [CharZero K] {ζ : K}

variable [IsCyclotomicExtension {n} ℚ K]

/-- The discriminant of the power basis given by a primitive root of unity `ζ` is the same as the
discriminant of the power basis given by `ζ - 1`. -/
theorem discr_zeta_eq_discr_zeta_sub_one (hζ : IsPrimitiveRoot ζ n) :
    discr ℚ (hζ.PowerBasis ℚ).Basis = discr ℚ (hζ.subOnePowerBasis ℚ).Basis := by
  have : NumberField K := NumberField.mk
  have H₁ : (aeval (hζ.power_basis ℚ).Gen) (X - 1 : ℤ[X]) = (hζ.sub_one_power_basis ℚ).Gen := by
    simp
  have H₂ : (aeval (hζ.sub_one_power_basis ℚ).Gen) (X + 1 : ℤ[X]) = (hζ.power_basis ℚ).Gen := by
    simp
  refine'
    discr_eq_discr_of_to_matrix_coeff_is_integral _ (fun i j => to_matrix_is_integral H₁ _ _ _ _) fun i j =>
      to_matrix_is_integral H₂ _ _ _ _
  · exact hζ.is_integral n.pos
    
  · refine' minpoly.gcd_domain_eq_field_fractions' _ (hζ.is_integral n.pos)
    
  · exact is_integral_sub (hζ.is_integral n.pos) is_integral_one
    
  · refine' minpoly.gcd_domain_eq_field_fractions' _ _
    exact is_integral_sub (hζ.is_integral n.pos) is_integral_one
    

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable {p : ℕ+} {k : ℕ} {K : Type u} {L : Type v} {ζ : L} [Field K] [Field L]

variable [Algebra K L]

/-- If `p` is a prime and `is_cyclotomic_extension {p ^ (k + 1)} K L`, then the discriminant of
`hζ.power_basis K` is `(-1) ^ ((p ^ (k + 1).totient) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))`
if `irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`. -/
theorem discr_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact (p : ℕ).Prime]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K))
    (hk : p ^ (k + 1) ≠ 2) :
    discr K (hζ.PowerBasis K).Basis =
      -1 ^ ((p ^ (k + 1) : ℕ).totient / 2) * p ^ ((p : ℕ) ^ k * ((p - 1) * (k + 1) - 1)) :=
  by
  have hne := IsCyclotomicExtension.ne_zero' (p ^ (k + 1)) K L
  have hp2 : p = 2 → 1 ≤ k := by
    intro hp
    refine' one_le_iff_ne_zero.2 fun h => _
    rw [h, hp, zero_addₓ, pow_oneₓ] at hk
    exact hk rfl
  rw [discr_power_basis_eq_norm, finrank _ hirr, hζ.power_basis_gen _, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
    Pnat.pow_coe, totient_prime_pow hp.out (succ_pos k)]
  congr 1
  · by_cases' hptwo : p = 2
    · obtain ⟨k₁, hk₁⟩ := Nat.exists_eq_succ_of_ne_zero (one_le_iff_ne_zero.1 (hp2 hptwo))
      rw [hk₁, succ_sub_one, hptwo, Pnat.coe_bit0, Pnat.one_coe, succ_sub_succ_eq_sub, tsub_zero, mul_oneₓ, pow_succₓ,
        mul_assoc, Nat.mul_div_cancel_leftₓ _ zero_lt_two, Nat.mul_div_cancel_leftₓ _ zero_lt_two]
      by_cases' hk₁zero : k₁ = 0
      · simp [← hk₁zero]
        
      obtain ⟨k₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk₁zero
      rw [pow_succₓ, mul_assoc, pow_mulₓ (-1 : K), pow_mulₓ (-1 : K), neg_one_sq, one_pow, one_pow]
      
    · simp only [← succ_sub_succ_eq_sub, ← tsub_zero]
      replace hptwo : ↑p ≠ 2
      · intro h
        rw [← Pnat.one_coe, ← Pnat.coe_bit0, Pnat.coe_inj] at h
        exact hptwo h
        
      obtain ⟨a, ha⟩ := even_sub_one_of_prime_ne_two hp.out hptwo
      rw [mul_comm ((p : ℕ) ^ k), mul_assoc, ha]
      nth_rw 0[← mul_oneₓ a]
      nth_rw 4[← mul_oneₓ a]
      rw [← Nat.mul_succ, mul_comm a, mul_assoc, mul_assoc 2, Nat.mul_div_cancel_leftₓ _ zero_lt_two,
        Nat.mul_div_cancel_leftₓ _ zero_lt_two, ← mul_assoc, mul_comm (a * (p : ℕ) ^ k), pow_mulₓ, ← ha]
      congr 1
      refine'
        Odd.neg_one_pow
          (Nat.Even.sub_odd (Nat.succ_le_iff.2 (mul_pos (tsub_pos_iff_lt.2 hp.out.one_lt) (pow_pos hp.out.pos _)))
            (Even.mul_right (Nat.even_sub_one_of_prime_ne_two hp.out hptwo) _) odd_one)
      
    
  · have H := congr_arg derivative (cyclotomic_prime_pow_mul_X_pow_sub_one K p k)
    rw [derivative_mul, derivative_sub, derivative_one, sub_zero, derivative_pow, derivative_X, mul_oneₓ,
      derivative_sub, derivative_one, sub_zero, derivative_pow, derivative_X, mul_oneₓ, ← Pnat.pow_coe,
      hζ.minpoly_eq_cyclotomic_of_irreducible hirr] at H
    replace H := congr_arg (fun P => aeval ζ P) H
    simp only [← aeval_add, ← aeval_mul, ← minpoly.aeval, ← zero_mul, ← add_zeroₓ, ← aeval_nat_cast, ← _root_.map_sub, ←
      aeval_one, ← aeval_X_pow] at H
    replace H := congr_arg (Algebra.norm K) H
    have hnorm : (norm K) (ζ ^ (p : ℕ) ^ k - 1) = p ^ (p : ℕ) ^ k := by
      by_cases' hp : p = 2
      · exact hζ.pow_sub_one_norm_prime_pow_of_one_le hirr rfl.le (hp2 hp)
        
      · exact hζ.pow_sub_one_norm_prime_ne_two hirr rfl.le hp
        
    rw [MonoidHom.map_mul, hnorm, MonoidHom.map_mul, ← map_nat_cast (algebraMap K L), Algebra.norm_algebra_map,
      finrank _ hirr, Pnat.pow_coe, totient_prime_pow hp.out (succ_pos k), Nat.sub_one, Nat.pred_succ, ←
      hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_pow, hζ.norm_eq_one hk hirr, one_pow, mul_oneₓ, cast_pow, ←
      coe_coe, ← pow_mulₓ, ← mul_assoc, mul_comm (k + 1), mul_assoc] at H
    · have := mul_pos (succ_pos k) (tsub_pos_iff_lt.2 hp.out.one_lt)
      rw [← succ_pred_eq_of_pos this, mul_succ, pow_addₓ _ _ ((p : ℕ) ^ k)] at H
      replace H := (mul_left_inj' fun h => _).1 H
      · simpa only [Pnat.pow_coe, ← H, ← mul_comm _ (k + 1)]
        
      · replace h := pow_eq_zero h
        rw [coe_coe] at h
        simpa using hne.1
        
      
    all_goals
      infer_instance
    
  all_goals
    infer_instance

/-- If `p` is a prime and `is_cyclotomic_extension {p ^ (k + 1)} K L`, then the discriminant of
`hζ.power_basis K` is `(-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))`
if `irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`. -/
theorem discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact (p : ℕ).Prime]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K))
    (hk : p ^ (k + 1) ≠ 2) :
    discr K (hζ.PowerBasis K).Basis = -1 ^ ((p : ℕ) ^ k * (p - 1) / 2) * p ^ ((p : ℕ) ^ k * ((p - 1) * (k + 1) - 1)) :=
  by
  simpa [← totient_prime_pow hp.out (succ_pos k)] using discr_prime_pow_ne_two hζ hirr hk

/-- If `p` is a prime and `is_cyclotomic_extension {p ^ k} K L`, then the discriminant of
`hζ.power_basis K` is `(-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1))`
if `irreducible (cyclotomic (p ^ k) K))`. Beware that in the cases `p ^ k = 1` and `p ^ k = 2`
the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to have a uniform result.
See also `is_cyclotomic_extension.discr_prime_pow_eq_unit_mul_pow`. -/
theorem discr_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} K L] [hp : Fact (p : ℕ).Prime]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) (hirr : Irreducible (cyclotomic (↑(p ^ k) : ℕ) K)) :
    discr K (hζ.PowerBasis K).Basis = -1 ^ ((p ^ k : ℕ).totient / 2) * p ^ ((p : ℕ) ^ (k - 1) * ((p - 1) * k - 1)) := by
  cases k
  · simp only [← coe_basis, ← pow_zeroₓ, ← power_basis_gen, ← totient_one, ← mul_zero, ← mul_oneₓ, ←
      show 1 / 2 = 0 by
        rfl,
      ← discr, ← trace_matrix]
    have hζone : ζ = 1 := by
      simpa using hζ
    rw [hζ.power_basis_dim _, hζone, ← (algebraMap K L).map_one,
      minpoly.eq_X_sub_C_of_algebra_map_inj _ (algebraMap K L).Injective, nat_degree_X_sub_C]
    simp only [← trace_matrix, ← map_one, ← one_pow, ← Matrix.det_unique, ← trace_form_apply, ← mul_oneₓ]
    rw [← (algebraMap K L).map_one, trace_algebra_map, finrank _ hirr]
    · simp
      
    · infer_instance
      
    · exact hcycl
      
    
  · by_cases' hk : p ^ (k + 1) = 2
    · have hp : p = 2 := by
        rw [← Pnat.coe_inj, Pnat.coe_bit0, Pnat.one_coe, Pnat.pow_coe, ← pow_oneₓ 2] at hk
        replace hk := eq_of_prime_pow_eq (prime_iff.1 hp.out) (prime_iff.1 Nat.prime_two) (succ_pos _) hk
        rwa
          [show 2 = ((2 : ℕ+) : ℕ) by
            simp ,
          Pnat.coe_inj] at hk
      rw [hp, ← Pnat.coe_inj, Pnat.pow_coe, Pnat.coe_bit0, Pnat.one_coe] at hk
      nth_rw 1[← pow_oneₓ 2]  at hk
      replace hk := Nat.pow_right_injective rfl.le hk
      rw [add_left_eq_self] at hk
      simp only [← hp, ← hk, ← pow_oneₓ, ← Pnat.coe_bit0, ← Pnat.one_coe] at hζ
      simp only [← hp, ← hk, ←
        show 1 / 2 = 0 by
          rfl,
        ← coe_basis, ← pow_oneₓ, ← power_basis_gen, ← Pnat.coe_bit0, ← Pnat.one_coe, ← totient_two, ← pow_zeroₓ, ←
        mul_oneₓ, ← mul_zero]
      rw [power_basis_dim, hζ.eq_neg_one_of_two_right,
        show (-1 : L) = algebraMap K L (-1) by
          simp ,
        minpoly.eq_X_sub_C_of_algebra_map_inj _ (algebraMap K L).Injective, nat_degree_X_sub_C]
      simp only [← discr, ← trace_matrix, ← Matrix.det_unique, ← Finₓ.default_eq_zero, ← Finₓ.coe_zero, ← pow_zeroₓ, ←
        trace_form_apply, ← mul_oneₓ]
      rw [← (algebraMap K L).map_one, trace_algebra_map, finrank _ hirr, hp, hk]
      · simp
        
      · infer_instance
        
      · exact hcycl
        
      
    · exact discr_prime_pow_ne_two hζ hirr hk
      
    

/-- If `p` is a prime and `is_cyclotomic_extension {p ^ k} K L`, then there are `u : ℤˣ` and
`n : ℕ` such that the discriminant of `hζ.power_basis K` is `u * p ^ n`. Often this is enough and
less cumbersome to use than `is_cyclotomic_extension.discr_prime_pow`. -/
theorem discr_prime_pow_eq_unit_mul_pow [IsCyclotomicExtension {p ^ k} K L] [hp : Fact (p : ℕ).Prime]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) (hirr : Irreducible (cyclotomic (↑(p ^ k) : ℕ) K)) :
    ∃ (u : ℤˣ)(n : ℕ), discr K (hζ.PowerBasis K).Basis = u * p ^ n := by
  rw [discr_prime_pow hζ hirr]
  by_cases' heven : Even ((p ^ k : ℕ).totient / 2)
  · refine'
      ⟨1, (p : ℕ) ^ (k - 1) * ((p - 1) * k - 1), by
        simp [← heven.neg_one_pow]⟩
    
  · exact
      ⟨-1, (p : ℕ) ^ (k - 1) * ((p - 1) * k - 1), by
        simp [← (odd_iff_not_even.2 heven).neg_one_pow]⟩
    

/-- If `p` is an odd prime and `is_cyclotomic_extension {p} K L`, then
`discr K (hζ.power_basis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` if
`irreducible (cyclotomic p K)`. -/
theorem discr_odd_prime [IsCyclotomicExtension {p} K L] [hp : Fact (p : ℕ).Prime] (hζ : IsPrimitiveRoot ζ p)
    (hirr : Irreducible (cyclotomic p K)) (hodd : p ≠ 2) :
    discr K (hζ.PowerBasis K).Basis = -1 ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} K L := by
    rw [zero_addₓ, pow_oneₓ]
    infer_instance
  have hζ' : IsPrimitiveRoot ζ ↑(p ^ (0 + 1)) := by
    simpa using hζ
  convert
    discr_prime_pow_ne_two hζ'
      (by
        simpa [← hirr] )
      (by
        simp [← hodd])
  · rw [zero_addₓ, pow_oneₓ, totient_prime hp.out]
    
  · rw [pow_zeroₓ, one_mulₓ, zero_addₓ, mul_oneₓ, Nat.sub_sub]
    

end IsCyclotomicExtension

