/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.Nat.Preterm

/-
Linear natural number arithmetic preformulas in pre-normalized preform.
-/
namespace Omega

namespace Nat

/-- Intermediate shadow syntax for LNA formulas that includes unreified exprs -/
unsafe inductive exprform
  | Eq : exprterm → exprterm → exprform
  | le : exprterm → exprterm → exprform
  | Not : exprform → exprform
  | Or : exprform → exprform → exprform
  | And : exprform → exprform → exprform

/-- Intermediate shadow syntax for LNA formulas that includes non-canonical terms -/
inductive Preform
  | Eq : Preterm → Preterm → preform
  | le : Preterm → Preterm → preform
  | Not : preform → preform
  | Or : preform → preform → preform
  | And : preform → preform → preform
  deriving has_reflect, Inhabited

-- mathport name: «expr =* »
localized [Omega.Nat] notation x " =* " y => Omega.Nat.Preform.eq x y

-- mathport name: «expr ≤* »
localized [Omega.Nat] notation x " ≤* " y => Omega.Nat.Preform.le x y

-- mathport name: «expr¬* »
localized [Omega.Nat] notation "¬* " p => Omega.Nat.Preform.not p

-- mathport name: «expr ∨* »
localized [Omega.Nat] notation p " ∨* " q => Omega.Nat.Preform.or p q

-- mathport name: «expr ∧* »
localized [Omega.Nat] notation p " ∧* " q => Omega.Nat.Preform.and p q

namespace Preform

/-- Evaluate a preform into prop using the valuation `v`. -/
@[simp]
def Holds (v : Nat → Nat) : Preform → Prop
  | t =* s => t.val v = s.val v
  | t ≤* s => t.val v ≤ s.val v
  | ¬* p => ¬p.Holds
  | p ∨* q => p.Holds ∨ q.Holds
  | p ∧* q => p.Holds ∧ q.Holds

end Preform

/-- `univ_close p n` := `p` closed by prepending `n` universal quantifiers -/
@[simp]
def UnivClose (p : Preform) : (Nat → Nat) → Nat → Prop
  | v, 0 => p.Holds v
  | v, k + 1 => ∀ i : Nat, univ_close (updateZero i v) k

namespace Preform

/-- Argument is free of negations -/
def NegFree : Preform → Prop
  | t =* s => True
  | t ≤* s => True
  | p ∨* q => neg_free p ∧ neg_free q
  | p ∧* q => neg_free p ∧ neg_free q
  | _ => False

/-- Return expr of proof that argument is free of subtractions -/
def SubFree : Preform → Prop
  | t =* s => t.SubFree ∧ s.SubFree
  | t ≤* s => t.SubFree ∧ s.SubFree
  | ¬* p => p.SubFree
  | p ∨* q => p.SubFree ∧ q.SubFree
  | p ∧* q => p.SubFree ∧ q.SubFree

/-- Fresh de Brujin index not used by any variable in argument -/
def freshIndex : Preform → Nat
  | t =* s => max t.freshIndex s.freshIndex
  | t ≤* s => max t.freshIndex s.freshIndex
  | ¬* p => p.freshIndex
  | p ∨* q => max p.freshIndex q.freshIndex
  | p ∧* q => max p.freshIndex q.freshIndex

theorem holds_constant {v w : Nat → Nat} :
    ∀ p : Preform, (∀, ∀ x < p.freshIndex, ∀, v x = w x) → (p.Holds v ↔ p.Holds w)
  | t =* s, h1 => by
    simp only [← holds]
    apply pred_mono_2 <;> apply preterm.val_constant <;> intro x h2 <;> apply h1 _ (lt_of_lt_of_leₓ h2 _)
    apply le_max_leftₓ
    apply le_max_rightₓ
  | t ≤* s, h1 => by
    simp only [← holds]
    apply pred_mono_2 <;> apply preterm.val_constant <;> intro x h2 <;> apply h1 _ (lt_of_lt_of_leₓ h2 _)
    apply le_max_leftₓ
    apply le_max_rightₓ
  | ¬* p, h1 => by
    apply not_iff_not_of_iff
    apply holds_constant p h1
  | p ∨* q, h1 => by
    simp only [← holds]
    apply pred_mono_2' <;> apply holds_constant <;> intro x h2 <;> apply h1 _ (lt_of_lt_of_leₓ h2 _)
    apply le_max_leftₓ
    apply le_max_rightₓ
  | p ∧* q, h1 => by
    simp only [← holds]
    apply pred_mono_2' <;> apply holds_constant <;> intro x h2 <;> apply h1 _ (lt_of_lt_of_leₓ h2 _)
    apply le_max_leftₓ
    apply le_max_rightₓ

/-- All valuations satisfy argument -/
def Valid (p : Preform) : Prop :=
  ∀ v, Holds v p

/-- There exists some valuation that satisfies argument -/
def Sat (p : Preform) : Prop :=
  ∃ v, Holds v p

/-- `implies p q` := under any valuation, `q` holds if `p` holds -/
def Implies (p q : Preform) : Prop :=
  ∀ v, Holds v p → Holds v q

/-- `equiv p q` := under any valuation, `p` holds iff `q` holds -/
def Equiv (p q : Preform) : Prop :=
  ∀ v, Holds v p ↔ Holds v q

theorem sat_of_implies_of_sat {p q : Preform} : Implies p q → Sat p → Sat q := by
  intro h1 h2
  apply exists_imp_exists h1 h2

theorem sat_or {p q : Preform} : Sat (p ∨* q) ↔ Sat p ∨ Sat q := by
  constructor <;> intro h1
  · cases' h1 with v h1
    cases' h1 with h1 h1 <;> [left, right] <;> refine' ⟨v, _⟩ <;> assumption
    
  · cases' h1 with h1 h1 <;> cases' h1 with v h1 <;> refine' ⟨v, _⟩ <;> [left, right] <;> assumption
    

/-- There does not exist any valuation that satisfies argument -/
def Unsat (p : Preform) : Prop :=
  ¬Sat p

def repr : Preform → Stringₓ
  | t =* s => "(" ++ t.repr ++ " = " ++ s.repr ++ ")"
  | t ≤* s => "(" ++ t.repr ++ " ≤ " ++ s.repr ++ ")"
  | ¬* p => "¬" ++ p.repr
  | p ∨* q => "(" ++ p.repr ++ " ∨ " ++ q.repr ++ ")"
  | p ∧* q => "(" ++ p.repr ++ " ∧ " ++ q.repr ++ ")"

instance hasRepr : HasRepr Preform :=
  ⟨repr⟩

unsafe instance has_to_format : has_to_format Preform :=
  ⟨fun x => x.repr⟩

end Preform

theorem univ_close_of_valid {p : Preform} : ∀ {m : Nat} {v : Nat → Nat}, p.valid → UnivClose p v m
  | 0, v, h1 => h1 _
  | m + 1, v, h1 => fun i => univ_close_of_valid h1

theorem valid_of_unsat_not {p : Preform} : (¬* p).Unsat → p.valid := by
  simp only [← preform.sat, ← preform.unsat, ← preform.valid, ← preform.holds]
  rw [not_exists_not]
  intro h
  assumption

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Tactic for setting up proof by induction over preforms. -/
unsafe def preform.induce (t : tactic Unit := tactic.skip) : tactic Unit :=
  sorry

end Nat

end Omega

