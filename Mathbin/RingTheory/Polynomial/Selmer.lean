/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.Data.Polynomial.UnitTrinomial
import Mathbin.Tactic.LinearCombination

/-!
# Irreducibility of Selmer Polynomials

This file proves irreducibility of the Selmer polynomials `X ^ n - X - 1`.

## Main results

- `polynomial.selmer_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.

TODO: Show that the Selmer polynomials have full Galois group.
-/


namespace Polynomial

open Polynomial

variable {n : ℕ}

-- ./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr «expr + »(«expr * »(«expr - »(«expr - »(«expr - »(1, z), «expr ^ »(z, 2)), «expr ^ »(z, n)), h1), «expr * »(«expr - »(«expr ^ »(z, n), 2), h2))],
  []]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args
theorem X_pow_sub_X_sub_one_irreducible_aux (z : ℂ) : ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) := by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1
  · trace
      "./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr «expr + »(«expr * »(«expr - »(«expr - »(«expr - »(1, z), «expr ^ »(z, 2)), «expr ^ »(z, n)), h1), «expr * »(«expr - »(«expr ^ »(z, n), 2), h2))],\n  []]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args"
    
  -- thanks polyrith!
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_divₓ n 3, pow_addₓ, pow_mulₓ, h3, one_pow, mul_oneₓ]
    have : n % 3 < 3 := Nat.mod_ltₓ n zero_lt_three
    interval_cases n % 3 <;> simp only [← h, ← pow_zeroₓ, ← pow_oneₓ, ← eq_self_iff_true, ← or_trueₓ, ← true_orₓ]
  have z_ne_zero : z ≠ 0 := fun h =>
    zero_ne_one ((zero_pow zero_lt_three).symm.trans (show (0 : ℂ) ^ 3 = 1 from h ▸ h3))
  rcases key with (key | key | key)
  · exact
      z_ne_zero
        (by
          rwa [key, self_eq_add_left] at h1)
    
  · exact
      one_ne_zero
        (by
          rwa [key, self_eq_add_rightₓ] at h1)
    
  · exact
      z_ne_zero
        (pow_eq_zero
          (by
            rwa [key, add_self_eq_zero] at h2))
    

-- ./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr h1], []]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args
-- ./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr «expr- »(h2)], []]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args
theorem X_pow_sub_X_sub_one_irreducible (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℤ[X]) := by
  by_cases' hn0 : n = 0
  · rw [hn0, pow_zeroₓ, sub_sub, add_commₓ, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
    
  have hn : 1 < n := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [← trinomial, ← C_neg, ← C_1] <;> ring
  rw [hp]
  apply is_unit_trinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩
  rintro z ⟨h1, h2⟩
  apply X_pow_sub_X_sub_one_irreducible_aux z
  rw [trinomial_mirror zero_lt_one hn (-1 : ℤˣ).ne_zero (1 : ℤˣ).ne_zero] at h2
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C] at h1 h2
  simp_rw [Units.coe_neg, Units.coe_one, map_neg, map_one] at h1 h2
  replace h1 : z ^ n = z + 1 := by
    trace
      "./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr h1], []]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args"
  replace h2 := mul_eq_zero_of_left h2 z
  rw [add_mulₓ, add_mulₓ, add_zeroₓ, mul_assoc (-1 : ℂ), ← pow_succ'ₓ, Nat.sub_add_cancelₓ hn.le] at h2
  rw [h1] at h2⊢
  exact
    ⟨rfl, by
      trace
        "./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr «expr- »(h2)], []]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args"⟩

theorem X_pow_sub_X_sub_one_irreducible_rat (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℚ[X]) := by
  by_cases' hn0 : n = 0
  · rw [hn0, pow_zeroₓ, sub_sub, add_commₓ, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
    
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [← trinomial, ← C_neg, ← C_1] <;> ring
  have hn : 1 < n := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have h := (is_primitive.int.irreducible_iff_irreducible_map_cast _).mp (X_pow_sub_X_sub_one_irreducible hn1)
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X] at h
    
  · exact hp.symm ▸ (trinomial_monic zero_lt_one hn).IsPrimitive
    

end Polynomial

