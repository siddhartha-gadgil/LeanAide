/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Data.Nat.Parity
import Mathbin.Order.Filter.AtTopBot

/-!
# Numbers are frequently modeq to fixed numbers

In this file we prove that `m ≡ d [MOD n]` frequently as `m → ∞`.
-/


open Filter

namespace Nat

/-- Infinitely many natural numbers are equal to `d` mod `n`. -/
theorem frequently_modeq {n : ℕ} (h : n ≠ 0) (d : ℕ) : ∃ᶠ m in at_top, m ≡ d [MOD n] :=
  ((tendsto_add_at_top_nat d).comp (tendsto_id.nsmul_at_top h.bot_lt)).Frequently <|
    frequently_of_forall fun m => by
      simp [← Nat.modeq_iff_dvd, sub_sub]

theorem frequently_mod_eq {d n : ℕ} (h : d < n) : ∃ᶠ m in at_top, m % n = d := by
  simpa only [← Nat.Modeq, ← mod_eq_of_lt h] using frequently_modeq h.ne_bot d

theorem frequently_even : ∃ᶠ m : ℕ in at_top, Even m := by
  simpa only [← even_iff] using frequently_mod_eq zero_lt_two

theorem frequently_odd : ∃ᶠ m : ℕ in at_top, Odd m := by
  simpa only [← odd_iff] using frequently_mod_eq one_lt_two

end Nat

