/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.Nat.Form

/-
Subtraction elimination for linear natural number arithmetic.
Works by repeatedly rewriting goals of the preform `P[t-s]` into
`P[x] ∧ (t = s + x ∨ (t ≤ s ∧ x = 0))`, where `x` is fresh.
-/
namespace Omega

namespace Nat

open Omega.Nat

namespace Preterm

/-- Find subtraction inside preterm and return its operands -/
def subTerms : Preterm → Option (preterm × preterm)
  | &i => none
  | i ** n => none
  | t +* s => t.subTerms <|> s.subTerms
  | t -* s => t.subTerms <|> s.subTerms <|> some (t, s)

/-- Find (t - s) inside a preterm and replace it with variable k -/
def subSubst (t s : Preterm) (k : Nat) : Preterm → Preterm
  | t@(&m) => t
  | t@(m ** n) => t
  | x +* y => x.subSubst +* y.subSubst
  | x -* y => if x = t ∧ y = s then 1 ** k else x.subSubst -* y.subSubst

theorem val_sub_subst {k : Nat} {x y : Preterm} {v : Nat → Nat} :
    ∀ {t : Preterm}, t.freshIndex ≤ k → (subSubst x y k t).val (update k (x.val v - y.val v) v) = t.val v
  | &m, h1 => rfl
  | m ** n, h1 => by
    have h2 : n ≠ k := ne_of_ltₓ h1
    simp only [← sub_subst, ← preterm.val]
    rw [update_eq_of_ne _ h2]
  | t +* s, h1 => by
    simp only [← sub_subst, ← val_add]
    apply fun_mono_2 <;> apply val_sub_subst (le_transₓ _ h1)
    apply le_max_leftₓ
    apply le_max_rightₓ
  | t -* s, h1 => by
    simp only [← sub_subst, ← val_sub]
    by_cases' h2 : t = x ∧ s = y
    · rw [if_pos h2]
      simp only [← val_var, ← one_mulₓ]
      rw [update_eq, h2.left, h2.right]
      
    · rw [if_neg h2]
      simp only [← val_sub, ← sub_subst]
      apply fun_mono_2 <;> apply val_sub_subst (le_transₓ _ h1)
      apply le_max_leftₓ
      apply le_max_rightₓ
      

end Preterm

namespace Preform

/-- Find subtraction inside preform and return its operands -/
def subTerms : Preform → Option (preterm × preterm)
  | t =* s => t.subTerms <|> s.subTerms
  | t ≤* s => t.subTerms <|> s.subTerms
  | ¬* p => p.subTerms
  | p ∨* q => p.subTerms <|> q.subTerms
  | p ∧* q => p.subTerms <|> q.subTerms

/-- Find (t - s) inside a preform and replace it with variable k -/
@[simp]
def subSubst (x y : Preterm) (k : Nat) : Preform → Preform
  | t =* s => Preterm.subSubst x y k t =* Preterm.subSubst x y k s
  | t ≤* s => Preterm.subSubst x y k t ≤* Preterm.subSubst x y k s
  | ¬* p => ¬* p.subSubst
  | p ∨* q => p.subSubst ∨* q.subSubst
  | p ∧* q => p.subSubst ∧* q.subSubst

end Preform

/-- Preform which asserts that the value of variable k is
    the truncated difference between preterms t and s -/
def isDiff (t s : Preterm) (k : Nat) : Preform :=
  (t =* s +* 1 ** k) ∨* (t ≤* s) ∧* (1 ** k) =* &0

theorem holds_is_diff {t s : Preterm} {k : Nat} {v : Nat → Nat} : v k = t.val v - s.val v → (isDiff t s k).Holds v := by
  intro h1
  simp only [← preform.holds, ← is_diff, ← if_pos (Eq.refl 1), ← preterm.val_add, ← preterm.val_var, ←
    preterm.val_const]
  cases' le_totalₓ (t.val v) (s.val v) with h2 h2
  · right
    refine' ⟨h2, _⟩
    rw [h1, one_mulₓ, tsub_eq_zero_iff_le]
    exact h2
    
  · left
    rw [h1, one_mulₓ, add_commₓ, tsub_add_cancel_of_le h2]
    

/-- Helper function for sub_elim -/
def subElimCore (t s : Preterm) (k : Nat) (p : Preform) : Preform :=
  Preform.subSubst t s k p ∧* isDiff t s k

/-- Return de Brujin index of fresh variable that does not occur
    in any of the arguments -/
def subFreshIndex (t s : Preterm) (p : Preform) : Nat :=
  max p.freshIndex (max t.freshIndex s.freshIndex)

/-- Return a new preform with all subtractions eliminated -/
def subElim (t s : Preterm) (p : Preform) : Preform :=
  subElimCore t s (subFreshIndex t s p) p

theorem sub_subst_equiv {k : Nat} {x y : Preterm} {v : Nat → Nat} :
    ∀ p : Preform, p.freshIndex ≤ k → ((Preform.subSubst x y k p).Holds (update k (x.val v - y.val v) v) ↔ p.Holds v)
  | t =* s, h1 => by
    simp only [← preform.holds, ← preform.sub_subst]
    apply pred_mono_2 <;> apply preterm.val_sub_subst (le_transₓ _ h1)
    apply le_max_leftₓ
    apply le_max_rightₓ
  | t ≤* s, h1 => by
    simp only [← preform.holds, ← preform.sub_subst]
    apply pred_mono_2 <;> apply preterm.val_sub_subst (le_transₓ _ h1)
    apply le_max_leftₓ
    apply le_max_rightₓ
  | ¬* p, h1 => by
    apply not_iff_not_of_iff
    apply sub_subst_equiv p h1
  | p ∨* q, h1 => by
    simp only [← preform.holds, ← preform.sub_subst]
    apply pred_mono_2 <;> apply propext <;> apply sub_subst_equiv _ (le_transₓ _ h1)
    apply le_max_leftₓ
    apply le_max_rightₓ
  | p ∧* q, h1 => by
    simp only [← preform.holds, ← preform.sub_subst]
    apply pred_mono_2 <;> apply propext <;> apply sub_subst_equiv _ (le_transₓ _ h1)
    apply le_max_leftₓ
    apply le_max_rightₓ

theorem sat_sub_elim {t s : Preterm} {p : Preform} : p.Sat → (subElim t s p).Sat := by
  intro h1
  simp only [← sub_elim, ← sub_elim_core]
  cases' h1 with v h1
  refine' ⟨update (sub_fresh_index t s p) (t.val v - s.val v) v, _⟩
  constructor
  · apply (sub_subst_equiv p _).elim_right h1
    apply le_max_leftₓ
    
  · apply holds_is_diff
    rw [update_eq]
    apply fun_mono_2 <;>
      apply preterm.val_constant <;>
        intro x h2 <;>
          rw [update_eq_of_ne _ (Ne.symm (ne_of_gtₓ _))] <;>
            apply lt_of_lt_of_leₓ h2 <;> apply le_transₓ _ (le_max_rightₓ _ _)
    apply le_max_leftₓ
    apply le_max_rightₓ
    

theorem unsat_of_unsat_sub_elim (t s : Preterm) (p : Preform) : (subElim t s p).Unsat → p.Unsat :=
  mt sat_sub_elim

end Nat

end Omega

