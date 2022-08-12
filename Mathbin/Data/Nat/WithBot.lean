/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Data.Nat.Basic
import Mathbin.Algebra.Order.Group

/-!
# `with_bot ℕ`

Lemmas about the type of natural numbers with a bottom element adjoined.
-/


namespace Nat

theorem WithBot.add_eq_zero_iff : ∀ {n m : WithBot ℕ}, n + m = 0 ↔ n = 0 ∧ m = 0
  | none, m =>
    iff_of_false
      (by
        decide)
      fun h =>
      absurd h.1
        (by
          decide)
  | n, none =>
    iff_of_false
      (by
        cases n <;>
          exact by
            decide)
      fun h =>
      absurd h.2
        (by
          decide)
  | some n, some m =>
    show (n + m : WithBot ℕ) = (0 : ℕ) ↔ (n : WithBot ℕ) = (0 : ℕ) ∧ (m : WithBot ℕ) = (0 : ℕ) by
      rw [← WithBot.coe_add, WithBot.coe_eq_coe, WithBot.coe_eq_coe, WithBot.coe_eq_coe,
        add_eq_zero_iff' (Nat.zero_leₓ _) (Nat.zero_leₓ _)]

theorem WithBot.add_eq_one_iff : ∀ {n m : WithBot ℕ}, n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0
  | none, none => by
    decide
  | none, some m => by
    decide
  | some n, none =>
    iff_of_false
      (by
        decide)
      fun h =>
      h.elim
        (fun h =>
          absurd h.2
            (by
              decide))
        fun h =>
        absurd h.2
          (by
            decide)
  | some n, some 0 => by
    erw [WithBot.coe_eq_coe, WithBot.coe_eq_coe, WithBot.coe_eq_coe, WithBot.coe_eq_coe] <;> simp
  | some n, some (m + 1) => by
    erw [WithBot.coe_eq_coe, WithBot.coe_eq_coe, WithBot.coe_eq_coe, WithBot.coe_eq_coe, WithBot.coe_eq_coe] <;>
      simp [← Nat.add_succ, ← Nat.succ_inj', ← Nat.succ_ne_zero]

@[simp]
theorem WithBot.coe_nonneg {n : ℕ} : 0 ≤ (n : WithBot ℕ) := by
  rw [← WithBot.coe_zero, WithBot.coe_le_coe] <;> exact Nat.zero_leₓ _

@[simp]
theorem WithBot.lt_zero_iff (n : WithBot ℕ) : n < 0 ↔ n = ⊥ :=
  Option.casesOn n
    (by
      decide)
    fun n =>
    iff_of_false
      (by
        simp [← WithBot.some_eq_coe])
      fun h => Option.noConfusion h

theorem WithBot.one_le_iff_zero_lt {x : WithBot ℕ} : 1 ≤ x ↔ 0 < x := by
  refine' ⟨fun h => lt_of_lt_of_leₓ (with_bot.coe_lt_coe.mpr zero_lt_one) h, fun h => _⟩
  induction x using WithBot.recBotCoe
  · exact (not_lt_bot h).elim
    
  · exact with_bot.coe_le_coe.mpr (nat.succ_le_iff.mpr (with_bot.coe_lt_coe.mp h))
    

theorem WithBot.lt_one_iff_le_zero {x : WithBot ℕ} : x < 1 ↔ x ≤ 0 :=
  not_iff_not.mp
    (by
      simpa using with_bot.one_le_iff_zero_lt)

end Nat

