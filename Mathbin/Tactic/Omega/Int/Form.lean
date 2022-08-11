/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.Int.Preterm

/-
Linear integer arithmetic formulas in pre-normalized form.
-/
namespace Omega

namespace Int

/-- Intermediate shadow syntax for LNA formulas that includes unreified exprs -/
unsafe inductive exprform
  | Eq : exprterm → exprterm → exprform
  | le : exprterm → exprterm → exprform
  | Not : exprform → exprform
  | Or : exprform → exprform → exprform
  | And : exprform → exprform → exprform

/-- Intermediate shadow syntax for LIA formulas that includes non-canonical terms -/
inductive Preform
  | Eq : Preterm → Preterm → preform
  | le : Preterm → Preterm → preform
  | Not : preform → preform
  | Or : preform → preform → preform
  | And : preform → preform → preform
  deriving has_reflect, Inhabited

-- mathport name: «expr =* »
localized [Omega.Int] notation x " =* " y => Omega.Int.Preform.eq x y

-- mathport name: «expr ≤* »
localized [Omega.Int] notation x " ≤* " y => Omega.Int.Preform.le x y

-- mathport name: «expr¬* »
localized [Omega.Int] notation "¬* " p => Omega.Int.Preform.not p

-- mathport name: «expr ∨* »
localized [Omega.Int] notation p " ∨* " q => Omega.Int.Preform.or p q

-- mathport name: «expr ∧* »
localized [Omega.Int] notation p " ∧* " q => Omega.Int.Preform.and p q

namespace Preform

/-- Evaluate a preform into prop using the valuation v. -/
@[simp]
def Holds (v : Nat → Int) : Preform → Prop
  | t =* s => t.val v = s.val v
  | t ≤* s => t.val v ≤ s.val v
  | ¬* p => ¬p.Holds
  | p ∨* q => p.Holds ∨ q.Holds
  | p ∧* q => p.Holds ∧ q.Holds

end Preform

/-- univ_close p n := p closed by prepending n universal quantifiers -/
@[simp]
def UnivClose (p : Preform) : (Nat → Int) → Nat → Prop
  | v, 0 => p.Holds v
  | v, k + 1 => ∀ i : Int, univ_close (updateZero i v) k

namespace Preform

/-- Fresh de Brujin index not used by any variable in argument -/
def freshIndex : Preform → Nat
  | t =* s => max t.freshIndex s.freshIndex
  | t ≤* s => max t.freshIndex s.freshIndex
  | ¬* p => p.freshIndex
  | p ∨* q => max p.freshIndex q.freshIndex
  | p ∧* q => max p.freshIndex q.freshIndex

/-- All valuations satisfy argument -/
def Valid (p : Preform) : Prop :=
  ∀ v, Holds v p

/-- There exists some valuation that satisfies argument -/
def Sat (p : Preform) : Prop :=
  ∃ v, Holds v p

/-- implies p q := under any valuation, q holds if p holds -/
def Implies (p q : Preform) : Prop :=
  ∀ v, Holds v p → Holds v q

/-- equiv p q := under any valuation, p holds iff q holds -/
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

theorem univ_close_of_valid {p : Preform} : ∀ {m v}, p.valid → UnivClose p v m
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

end Int

end Omega

