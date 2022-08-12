/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Int.Basic
import Mathbin.Data.Nat.SuccPred

/-!
# Successors and predecessors of integers

In this file, we show that `ℤ` is both an archimedean `succ_order` and an archimedean `pred_order`.
-/


open Function Order

namespace Int

-- so that Lean reads `int.succ` through `succ_order.succ`
@[reducible]
instance : SuccOrder ℤ :=
  { SuccOrder.ofSuccLeIff succ fun a b => Iff.rfl with succ := succ }

-- so that Lean reads `int.pred` through `pred_order.pred`
@[reducible]
instance : PredOrder ℤ where
  pred := pred
  pred_le := fun a => (sub_one_lt_of_leₓ le_rfl).le
  min_of_le_pred := fun a ha => ((sub_one_lt_of_leₓ le_rfl).not_le ha).elim
  le_pred_of_lt := fun a b => le_sub_one_of_ltₓ
  le_of_pred_lt := fun a b => le_of_sub_one_ltₓ

@[simp]
theorem succ_eq_succ : Order.succ = succ :=
  rfl

@[simp]
theorem pred_eq_pred : Order.pred = pred :=
  rfl

theorem succ_iterate (a : ℤ) : ∀ n, (succ^[n]) a = a + n
  | 0 => (add_zeroₓ a).symm
  | n + 1 => by
    rw [Function.iterate_succ', Int.coe_nat_succ, ← add_assocₓ]
    exact congr_arg _ (succ_iterate n)

theorem pred_iterate (a : ℤ) : ∀ n, (pred^[n]) a = a - n
  | 0 => (sub_zero a).symm
  | n + 1 => by
    rw [Function.iterate_succ', Int.coe_nat_succ, ← sub_sub]
    exact congr_arg _ (pred_iterate n)

instance : IsSuccArchimedean ℤ :=
  ⟨fun a b h =>
    ⟨(b - a).toNat, by
      rw [succ_eq_succ, succ_iterate, to_nat_sub_of_le h, ← add_sub_assoc, add_sub_cancel']⟩⟩

instance : IsPredArchimedean ℤ :=
  ⟨fun a b h =>
    ⟨(b - a).toNat, by
      rw [pred_eq_pred, pred_iterate, to_nat_sub_of_le h, sub_sub_cancel]⟩⟩

/-! ### Covering relation -/


protected theorem covby_iff_succ_eq {m n : ℤ} : m ⋖ n ↔ m + 1 = n :=
  succ_eq_iff_covby.symm

end Int

@[simp, norm_cast]
theorem Nat.cast_int_covby_iff {a b : ℕ} : (a : ℤ) ⋖ b ↔ a ⋖ b := by
  rw [Nat.covby_iff_succ_eq, Int.covby_iff_succ_eq]
  exact Int.coe_nat_inj'

alias Nat.cast_int_covby_iff ↔ _ Covby.cast_int

