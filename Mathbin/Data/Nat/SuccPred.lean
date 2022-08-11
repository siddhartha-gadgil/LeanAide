/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.SuccPred.Basic

/-!
# Successors and predecessors of naturals

In this file, we show that `ℕ` is both an archimedean `succ_order` and an archimedean `pred_order`.
-/


open Function Order

namespace Nat

-- so that Lean reads `nat.succ` through `succ_order.succ`
@[reducible]
instance : SuccOrder ℕ :=
  { SuccOrder.ofSuccLeIff succ fun a b => Iff.rfl with succ := succ }

-- so that Lean reads `nat.pred` through `pred_order.pred`
@[reducible]
instance : PredOrder ℕ where
  pred := pred
  pred_le := pred_leₓ
  min_of_le_pred := fun a ha => by
    cases a
    · exact is_min_bot
      
    · exact (not_succ_le_self _ ha).elim
      
  le_pred_of_lt := fun a b h => by
    cases b
    · exact (a.not_lt_zero h).elim
      
    · exact le_of_succ_le_succ h
      
  le_of_pred_lt := fun a b h => by
    cases a
    · exact b.zero_le
      
    · exact h
      

@[simp]
theorem succ_eq_succ : Order.succ = succ :=
  rfl

@[simp]
theorem pred_eq_pred : Order.pred = pred :=
  rfl

theorem succ_iterate (a : ℕ) : ∀ n, (succ^[n]) a = a + n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ', add_succ]
    exact congr_arg _ n.succ_iterate

theorem pred_iterate (a : ℕ) : ∀ n, (pred^[n]) a = a - n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ', sub_succ]
    exact congr_arg _ n.pred_iterate

instance : IsSuccArchimedean ℕ :=
  ⟨fun a b h =>
    ⟨b - a, by
      rw [succ_eq_succ, succ_iterate, add_tsub_cancel_of_le h]⟩⟩

instance : IsPredArchimedean ℕ :=
  ⟨fun a b h =>
    ⟨b - a, by
      rw [pred_eq_pred, pred_iterate, tsub_tsub_cancel_of_le h]⟩⟩

/-! ### Covering relation -/


protected theorem covby_iff_succ_eq {m n : ℕ} : m ⋖ n ↔ m + 1 = n :=
  succ_eq_iff_covby.symm

end Nat

@[simp, norm_cast]
theorem Finₓ.coe_covby_iff {n : ℕ} {a b : Finₓ n} : (a : ℕ) ⋖ b ↔ a ⋖ b :=
  and_congr_right' ⟨fun h c hc => h hc, fun h c ha hb => @h ⟨c, hb.trans b.Prop⟩ ha hb⟩

alias Finₓ.coe_covby_iff ↔ _ Covby.coe_fin

