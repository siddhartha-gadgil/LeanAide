/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Primes congruent to one

We prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that
`p ≡ 1 [MOD k]`.
-/


namespace Nat

open Polynomial Nat Filter

/-- For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. -/
theorem exists_prime_ge_modeq_one {k : ℕ} (n : ℕ) (hpos : 0 < k) : ∃ p : ℕ, Nat.Prime p ∧ n ≤ p ∧ p ≡ 1 [MOD k] := by
  let b := 3 * (k * n.factorial)
  have hgt : 1 < (eval (↑b) (cyclotomic k ℤ)).natAbs := by
    have hkey : ∀ l : ℕ, 2 < 3 * (l.succ * n.factorial) := fun l =>
      lt_mul_of_lt_of_one_le (2 : ℕ).lt_succ_self (le_mul_of_le_of_one_le (Nat.succ_posₓ _) n.factorial_pos)
    rcases k with (_ | _ | k)
    · simpa using hpos
      
    · simp only [← one_mulₓ, ← Int.coe_nat_mul, ← Int.coe_nat_succ, ← Int.coe_nat_zero, ← zero_addₓ, ← cyclotomic_one, ←
        eval_sub, ← eval_X, ← eval_one]
      convert Int.nat_abs_lt_nat_abs_of_nonneg_of_lt Int.one_nonneg _
      rw [lt_sub_iff_add_lt]
      specialize hkey 0
      norm_cast
      rwa [one_mulₓ] at hkey
      
    calc 1 ≤ _ := by
        rw [le_tsub_iff_left (one_le_two.trans (hkey _).le)]
        exact (hkey _).le _ < _ :=
        sub_one_lt_nat_abs_cyclotomic_eval (one_lt_succ_succ k) (one_lt_two.trans (hkey k.succ)).Ne.symm
  let p := min_fac (eval (↑b) (cyclotomic k ℤ)).natAbs
  have hprime : Fact p.prime := ⟨min_fac_prime (ne_of_ltₓ hgt).symm⟩
  have hroot : is_root (cyclotomic k (Zmod p)) (cast_ring_hom (Zmod p) b) := by
    rw [is_root.def, ← map_cyclotomic_int k (Zmod p), eval_map, coe_cast_ring_hom, ← Int.cast_coe_nat, ←
      Int.coe_cast_ring_hom, eval₂_hom, Int.coe_cast_ring_hom, Zmod.int_coe_zmod_eq_zero_iff_dvd _ _]
    apply Int.dvd_nat_abs.1
    exact_mod_cast min_fac_dvd (eval (↑b) (cyclotomic k ℤ)).natAbs
  refine' ⟨p, hprime.1, _, _⟩
  · by_contra habs
    exact
      (prime.dvd_iff_not_coprime hprime.1).1 (dvd_factorial (min_fac_pos _) (le_of_not_geₓ habs))
        (coprime_of_root_cyclotomic hpos hroot).symm.coprime_mul_left_right.coprime_mul_left_right
    
  · have hdiv :=
      order_of_dvd_of_pow_eq_one
        (Zmod.units_pow_card_sub_one_eq_one p (Zmod.unitOfCoprime b (coprime_of_root_cyclotomic hpos hroot)))
    have : ¬p ∣ k :=
      hprime.1.coprime_iff_not_dvd.1
        (coprime_of_root_cyclotomic hpos hroot).symm.coprime_mul_left_right.coprime_mul_right_right
    have := NeZero.of_not_dvd (Zmod p) this
    have : k = orderOf (b : Zmod p) := (is_root_cyclotomic_iff.mp hroot).eq_order_of
    rw [← order_of_units, Zmod.coe_unit_of_coprime, ← this] at hdiv
    exact ((modeq_iff_dvd' hprime.1.Pos).2 hdiv).symm
    

theorem frequently_at_top_modeq_one {k : ℕ} (hpos : 0 < k) : ∃ᶠ p in at_top, Nat.Prime p ∧ p ≡ 1 [MOD k] := by
  refine' frequently_at_top.2 fun n => _
  obtain ⟨p, hp⟩ := exists_prime_ge_modeq_one n hpos
  exact ⟨p, ⟨hp.2.1, hp.1, hp.2.2⟩⟩

theorem infinite_set_of_prime_modeq_one {k : ℕ} (hpos : 0 < k) : Set.Infinite { p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k] } :=
  frequently_at_top_iff_infinite.1 (frequently_at_top_modeq_one hpos)

end Nat

