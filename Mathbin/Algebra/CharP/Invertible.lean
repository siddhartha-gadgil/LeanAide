/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.Invertible
import Mathbin.Algebra.Field.Basic
import Mathbin.Algebra.CharP.Basic

/-!
# Invertibility of elements given a characteristic

This file includes some instances of `invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertible_of_nonzero` is a useful definition.
-/


variable {K : Type _}

section Field

variable [Field K]

/-- A natural number `t` is invertible in a field `K` if the charactistic of `K` does not divide
`t`. -/
def invertibleOfRingCharNotDvd {t : ℕ} (not_dvd : ¬ringChar K ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((ringChar.spec K t).mp h)

theorem not_ring_char_dvd_of_invertible {t : ℕ} [Invertible (t : K)] : ¬ringChar K ∣ t := by
  rw [← ringChar.spec, ← Ne.def]
  exact nonzero_of_invertible (t : K)

/-- A natural number `t` is invertible in a field `K` of charactistic `p` if `p` does not divide
`t`. -/
def invertibleOfCharPNotDvd {p : ℕ} [CharP K p] {t : ℕ} (not_dvd : ¬p ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((CharP.cast_eq_zero_iff K p t).mp h)

instance invertibleOfPos [CharZero K] (n : ℕ) [h : Fact (0 < n)] : Invertible (n : K) :=
  invertibleOfNonzero <| by
    simpa [← pos_iff_ne_zero] using h.out

end Field

section DivisionRing

variable [DivisionRing K] [CharZero K]

instance invertibleSucc (n : ℕ) : Invertible (n.succ : K) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))

/-!
A few `invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/


instance invertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero
    (by
      exact_mod_cast
        (by
          decide : 2 ≠ 0))

instance invertibleThree : Invertible (3 : K) :=
  invertibleOfNonzero
    (by
      exact_mod_cast
        (by
          decide : 3 ≠ 0))

end DivisionRing

