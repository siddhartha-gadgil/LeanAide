/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.GroupTheory.Perm.Cycle.Type

/-!
# Characteristic and cardinality

We prove some results relating characteristic and cardinality of finite rings

## Tags
characterstic, cardinality, ring
-/


/-- A prime `p` is a unit in a finite commutative ring `R`
iff it does not divide the characteristic. -/
theorem is_unit_iff_not_dvd_char (R : Type _) [CommRingₓ R] [Fintype R] (p : ℕ) [Fact p.Prime] :
    IsUnit (p : R) ↔ ¬p ∣ ringChar R := by
  have hch := CharP.cast_eq_zero R (ringChar R)
  constructor
  · rintro h₁ ⟨q, hq⟩
    rcases IsUnit.exists_left_inv h₁ with ⟨a, ha⟩
    have h₃ : ¬ringChar R ∣ q := by
      rintro ⟨r, hr⟩
      rw [hr, ← mul_assoc, mul_comm p, mul_assoc] at hq
      nth_rw 0[← mul_oneₓ (ringChar R)]  at hq
      exact
        Nat.Prime.not_dvd_one (Fact.out p.prime) ⟨r, mul_left_cancel₀ (CharP.char_ne_zero_of_fintype R (ringChar R)) hq⟩
    have h₄ := mt (CharP.int_cast_eq_zero_iff R (ringChar R) q).mp
    apply_fun (coe : ℕ → R)  at hq
    apply_fun (· * ·) a  at hq
    rw [Nat.cast_mulₓ, hch, mul_zero, ← mul_assoc, ha, one_mulₓ] at hq
    norm_cast  at h₄
    exact h₄ h₃ hq.symm
    
  · intro h
    rcases nat.is_coprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd (Fact.out _)).mpr h) with ⟨a, b, hab⟩
    apply_fun (coe : ℤ → R)  at hab
    push_cast at hab
    rw [hch, mul_zero, add_zeroₓ, mul_comm] at hab
    exact is_unit_of_mul_eq_one (p : R) a hab
    

/-- The prime divisors of the characteristic of a finite commutative ring are exactly
the prime divisors of its cardinality. -/
theorem prime_dvd_char_iff_dvd_card {R : Type _} [CommRingₓ R] [Fintype R] (p : ℕ) [Fact p.Prime] :
    p ∣ ringChar R ↔ p ∣ Fintype.card R := by
  refine'
    ⟨fun h =>
      h.trans <|
        int.coe_nat_dvd.mp <|
          (CharP.int_cast_eq_zero_iff R (ringChar R) (Fintype.card R)).mp <| by
            exact_mod_cast CharP.cast_card_eq_zero R,
      fun h => _⟩
  by_contra h₀
  rcases exists_prime_add_order_of_dvd_card p h with ⟨r, hr⟩
  have hr₁ := add_order_of_nsmul_eq_zero r
  rw [hr, nsmul_eq_mul] at hr₁
  rcases IsUnit.exists_left_inv ((is_unit_iff_not_dvd_char R p).mpr h₀) with ⟨u, hu⟩
  apply_fun (· * ·) u  at hr₁
  rw [mul_zero, ← mul_assoc, hu, one_mulₓ] at hr₁
  exact mt add_monoid.order_of_eq_one_iff.mpr (ne_of_eq_of_ne hr (Nat.Prime.ne_one (Fact.out p.prime))) hr₁

/-- A prime that does not divide the cardinality of a finite commutative ring `R`
is a unit in `R`. -/
theorem not_is_unit_prime_of_dvd_card {R : Type _} [CommRingₓ R] [Fintype R] (p : ℕ) [Fact p.Prime]
    (hp : p ∣ Fintype.card R) : ¬IsUnit (p : R) :=
  mt (is_unit_iff_not_dvd_char R p).mp (not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))

