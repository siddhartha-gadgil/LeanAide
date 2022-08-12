/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Data.Nat.Parity
import Mathbin.Data.Zmod.Basic

/-!
# Relating parity to natural numbers mod 2

This module provides lemmas relating `zmod 2` to `even` and `odd`.

## Tags

parity, zmod, even, odd
-/


namespace Zmod

theorem eq_zero_iff_even {n : ℕ} : (n : Zmod 2) = 0 ↔ Even n :=
  (CharP.cast_eq_zero_iff (Zmod 2) 2 n).trans even_iff_two_dvd.symm

theorem eq_one_iff_odd {n : ℕ} : (n : Zmod 2) = 1 ↔ Odd n := by
  rw [← @Nat.cast_oneₓ (Zmod 2), Zmod.eq_iff_modeq_nat, Nat.odd_iff, Nat.Modeq]
  norm_num

theorem ne_zero_iff_odd {n : ℕ} : (n : Zmod 2) ≠ 0 ↔ Odd n := by
  constructor <;>
    · contrapose
      simp [← eq_zero_iff_even]
      

end Zmod

