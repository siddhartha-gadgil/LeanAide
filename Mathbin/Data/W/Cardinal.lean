/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Data.W.Basic
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of W-types

This file proves some theorems about the cardinality of W-types. The main result is
`cardinal_mk_le_max_aleph_0_of_fintype` which says that if for any `a : α`,
`β a` is finite, then the cardinality of `W_type β` is at most the maximum of the
cardinality of `α` and `ℵ₀`.
This can be used to prove theorems about the cardinality of algebraic constructions such as
polynomials. There is a surjection from a `W_type` to `mv_polynomial` for example, and
this surjection can be used to put an upper bound on the cardinality of `mv_polynomial`.

## Tags

W, W type, cardinal, first order
-/


universe u

variable {α : Type u} {β : α → Type u}

noncomputable section

namespace WType

open Cardinal

open Cardinal

theorem cardinal_mk_eq_sum : # (WType β) = Sum fun a : α => # (WType β) ^ # (β a) := by
  simp only [← Cardinal.power_def, Cardinal.mk_sigma]
  exact mk_congr (equiv_sigma β)

/-- `#(W_type β)` is the least cardinal `κ` such that `sum (λ a : α, κ ^ #(β a)) ≤ κ` -/
theorem cardinal_mk_le_of_le {κ : Cardinal.{u}} (hκ : (Sum fun a : α => κ ^ # (β a)) ≤ κ) : # (WType β) ≤ κ := by
  induction' κ using Cardinal.induction_on with γ
  simp only [← Cardinal.power_def, Cardinal.mk_sigma, ← Cardinal.le_def] at hκ
  cases hκ
  exact Cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)

/-- If, for any `a : α`, `β a` is finite, then the cardinality of `W_type β`
  is at most the maximum of the cardinality of `α` and `ℵ₀`  -/
theorem cardinal_mk_le_max_aleph_0_of_finite [∀ a, Finite (β a)] : # (WType β) ≤ max (# α) ℵ₀ :=
  ((is_empty_or_nonempty α).elim
      (by
        intro h
        rw [Cardinal.mk_eq_zero (WType β)]
        exact zero_le _))
    fun hn =>
    let m := max (# α) ℵ₀
    cardinal_mk_le_of_le <|
      calc
        (Cardinal.sum fun a => m ^ # (β a)) ≤ # α * ⨆ a, m ^ # (β a) := Cardinal.sum_le_supr _
        _ ≤ m * ⨆ a, m ^ # (β a) := mul_le_mul' (le_max_leftₓ _ _) le_rfl
        _ = m :=
          mul_eq_left.{u} (le_max_rightₓ _ _)
              (csupr_le' fun i => pow_le (le_max_rightₓ _ _) (lt_aleph_0_of_finite _)) <|
            pos_iff_ne_zero.1 <|
              Order.succ_le_iff.1
                (by
                  rw [succ_zero]
                  obtain ⟨a⟩ : Nonempty α
                  exact hn
                  refine' le_transₓ _ (le_csupr (bdd_above_range.{u, u} _) a)
                  rw [← power_zero]
                  exact power_le_power_left (pos_iff_ne_zero.1 (aleph_0_pos.trans_le (le_max_rightₓ _ _))) (zero_le _))
        

end WType

