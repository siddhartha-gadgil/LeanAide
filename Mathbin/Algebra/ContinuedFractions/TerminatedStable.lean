/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathbin.Algebra.ContinuedFractions.Translations

/-!
# Stabilisation of gcf Computations Under Termination

## Summary

We show that the continuants and convergents of a gcf stabilise once the gcf terminates.
-/


namespace GeneralizedContinuedFraction

variable {K : Type _} {g : GeneralizedContinuedFraction K} {n m : ℕ}

/-- If a gcf terminated at position `n`, it also terminated at `m ≥ n`.-/
theorem terminated_stable (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) : g.TerminatedAt m :=
  g.s.terminated_stable n_le_m terminated_at_n

variable [DivisionRing K]

theorem continuants_aux_stable_step_of_terminated (terminated_at_n : g.TerminatedAt n) :
    g.continuantsAux (n + 2) = g.continuantsAux (n + 1) := by
  rw [terminated_at_iff_s_none] at terminated_at_n
  simp only [← terminated_at_n, ← continuants_aux]

theorem continuants_aux_stable_of_terminated (succ_n_le_m : n + 1 ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.continuantsAux m = g.continuantsAux (n + 1) := by
  induction' succ_n_le_m with m succ_n_le_m IH
  · rfl
    
  · have : g.continuants_aux (m + 1) = g.continuants_aux m := by
      have : n ≤ m - 1 := Nat.le_pred_of_ltₓ succ_n_le_m
      have : g.terminated_at (m - 1) := terminated_stable this terminated_at_n
      have stable_step : g.continuants_aux (m - 1 + 2) = g.continuants_aux (m - 1 + 1) :=
        continuants_aux_stable_step_of_terminated this
      have one_le_m : 1 ≤ m := Nat.one_le_of_lt succ_n_le_m
      have : m - 1 + 2 = m + 2 - 1 := tsub_add_eq_add_tsub one_le_m
      have : m - 1 + 1 = m + 1 - 1 := tsub_add_eq_add_tsub one_le_m
      simpa [*] using stable_step
    exact Eq.trans this IH
    

theorem convergents'_aux_stable_step_of_terminated {s : Seqₓₓ <| Pair K} (terminated_at_n : s.TerminatedAt n) :
    convergents'Aux s (n + 1) = convergents'Aux s n := by
  change s.nth n = none at terminated_at_n
  induction' n with n IH generalizing s
  case nat.zero =>
    simp only [← convergents'_aux, ← terminated_at_n, ← Seqₓₓ.head]
  case nat.succ =>
    cases' s_head_eq : s.head with gp_head
    case option.none =>
      simp only [← convergents'_aux, ← s_head_eq]
    case option.some =>
      have : s.tail.terminated_at n := by
        simp only [← Seqₓₓ.TerminatedAt, ← s.nth_tail, ← terminated_at_n]
      simp only [← convergents'_aux, ← s_head_eq, ← IH this]

theorem convergents'_aux_stable_of_terminated {s : Seqₓₓ <| Pair K} (n_le_m : n ≤ m)
    (terminated_at_n : s.TerminatedAt n) : convergents'Aux s m = convergents'Aux s n := by
  induction' n_le_m with m n_le_m IH generalizing s
  · rfl
    
  · cases' s_head_eq : s.head with gp_head
    case option.none =>
      cases n <;> simp only [← convergents'_aux, ← s_head_eq]
    case option.some =>
      have : convergents'_aux s (n + 1) = convergents'_aux s n :=
        convergents'_aux_stable_step_of_terminated terminated_at_n
      rw [← this]
      have : s.tail.terminated_at n := by
        simpa only [← Seqₓₓ.TerminatedAt, ← Seqₓₓ.nth_tail] using s.le_stable n.le_succ terminated_at_n
      have : convergents'_aux s.tail m = convergents'_aux s.tail n := IH this
      simp only [← convergents'_aux, ← s_head_eq, ← this]
    

theorem continuants_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.continuants m = g.continuants n := by
  simp only [← nth_cont_eq_succ_nth_cont_aux, ←
    continuants_aux_stable_of_terminated (nat.pred_le_iff.elim_left n_le_m) terminated_at_n]

theorem numerators_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.numerators m = g.numerators n := by
  simp only [← num_eq_conts_a, ← continuants_stable_of_terminated n_le_m terminated_at_n]

theorem denominators_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.denominators m = g.denominators n := by
  simp only [← denom_eq_conts_b, ← continuants_stable_of_terminated n_le_m terminated_at_n]

theorem convergents_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.convergents m = g.convergents n := by
  simp only [← convergents, ← denominators_stable_of_terminated n_le_m terminated_at_n, ←
    numerators_stable_of_terminated n_le_m terminated_at_n]

theorem convergents'_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.convergents' m = g.convergents' n := by
  simp only [← convergents', ← convergents'_aux_stable_of_terminated n_le_m terminated_at_n]

end GeneralizedContinuedFraction

