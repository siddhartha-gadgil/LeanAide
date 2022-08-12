/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.Order.SuccPred.Basic

/-!
# Successors and predecessors of `fin n`

In this file, we show that `fin n` is both a `succ_order` and a `pred_order`. Note that they are
also archimedean, but this is derived from the general instance for well-orderings as opposed
to a specific `fin` instance.

-/


namespace Finₓ

instance : ∀ {n : ℕ}, SuccOrder (Finₓ n)
  | 0 => by
    constructor <;> exact elim0
  | n + 1 =>
    SuccOrder.ofCore (fun i => if i < Finₓ.last n then i + 1 else i)
      (by
        intro a ha b
        rw [is_max_iff_eq_top, eq_top_iff, not_leₓ, top_eq_last] at ha
        rw [if_pos ha, lt_iff_coe_lt_coe, le_iff_coe_le_coe, coe_add_one_of_lt ha]
        exact Nat.lt_iff_add_one_le)
      (by
        intro a ha
        rw [is_max_iff_eq_top, top_eq_last] at ha
        rw [if_neg ha.not_lt])

@[simp]
theorem succ_eq {n : ℕ} : SuccOrder.succ = fun a => if a < Finₓ.last n then a + 1 else a :=
  rfl

@[simp]
theorem succ_apply {n : ℕ} (a) : SuccOrder.succ a = if a < Finₓ.last n then a + 1 else a :=
  rfl

instance : ∀ {n : ℕ}, PredOrder (Finₓ n)
  | 0 => by
    constructor <;> exact elim0
  | n + 1 =>
    PredOrder.ofCore (fun x => if x = 0 then 0 else x - 1)
      (by
        intro a ha b
        rw [is_min_iff_eq_bot, eq_bot_iff, not_leₓ, bot_eq_zero] at ha
        rw [if_neg ha.ne', lt_iff_coe_lt_coe, le_iff_coe_le_coe, coe_sub_one, if_neg ha.ne', le_tsub_iff_right,
          Iff.comm]
        exact Nat.lt_iff_add_one_le
        exact ha)
      (by
        intro a ha
        rw [is_min_iff_eq_bot, bot_eq_zero] at ha
        rwa [if_pos ha, eq_comm])

@[simp]
theorem pred_eq {n} : PredOrder.pred = fun a : Finₓ (n + 1) => if a = 0 then 0 else a - 1 :=
  rfl

@[simp]
theorem pred_apply {n : ℕ} (a : Finₓ (n + 1)) : PredOrder.pred a = if a = 0 then 0 else a - 1 :=
  rfl

end Finₓ

