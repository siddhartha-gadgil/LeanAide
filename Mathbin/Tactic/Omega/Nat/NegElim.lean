/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.Nat.Form

/-
Negation elimination.
-/
namespace Omega

namespace Nat

open Omega.Nat

/-- push_neg p returns the result of normalizing ¬ p by
    pushing the outermost negation all the way down,
    until it reaches either a negation or an atom -/
@[simp]
def pushNeg : Preform → Preform
  | p ∨* q => push_neg p ∧* push_neg q
  | p ∧* q => push_neg p ∨* push_neg q
  | ¬* p => p
  | p => ¬* p

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
theorem push_neg_equiv : ∀ {p : Preform}, Preform.Equiv (pushNeg p) (¬* p) := by
  run_tac
    preform.induce sorry
  · simp only [← not_not, ← preform.holds, ← push_neg]
    
  · simp only [← preform.holds, ← push_neg, ← not_or_distrib, ← ihp v, ← ihq v]
    
  · simp only [← preform.holds, ← push_neg, ← not_and_distrib, ← ihp v, ← ihq v]
    

/-- NNF transformation -/
def nnf : Preform → Preform
  | ¬* p => pushNeg (nnf p)
  | p ∨* q => nnf p ∨* nnf q
  | p ∧* q => nnf p ∧* nnf q
  | a => a

/-- Asserts that the given preform is in NNF -/
def IsNnf : Preform → Prop
  | t =* s => True
  | t ≤* s => True
  | ¬* t =* s => True
  | ¬* t ≤* s => True
  | p ∨* q => is_nnf p ∧ is_nnf q
  | p ∧* q => is_nnf p ∧ is_nnf q
  | _ => False

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
theorem is_nnf_push_neg : ∀ p : Preform, IsNnf p → IsNnf (pushNeg p) := by
  run_tac
    preform.induce sorry
  · cases p <;>
      try
          cases h1 <;>
        trivial
    
  · cases h1
    constructor <;>
        [· apply ihp
          ,
        · apply ihq
          ] <;>
      assumption
    
  · cases h1
    constructor <;>
        [· apply ihp
          ,
        · apply ihq
          ] <;>
      assumption
    

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
theorem is_nnf_nnf : ∀ p : Preform, IsNnf (nnf p) := by
  run_tac
    preform.induce sorry
  · apply is_nnf_push_neg _ ih
    
  · constructor <;> assumption
    
  · constructor <;> assumption
    

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
theorem nnf_equiv : ∀ {p : Preform}, Preform.Equiv (nnf p) p := by
  run_tac
    preform.induce sorry
  · rw [push_neg_equiv]
    apply not_iff_not_of_iff
    apply ih
    
  · apply pred_mono_2' (ihp v) (ihq v)
    
  · apply pred_mono_2' (ihp v) (ihq v)
    

@[simp]
def negElimCore : Preform → Preform
  | ¬* t =* s => (t.add_one ≤* s) ∨* s.add_one ≤* t
  | ¬* t ≤* s => s.add_one ≤* t
  | p ∨* q => neg_elim_core p ∨* neg_elim_core q
  | p ∧* q => neg_elim_core p ∧* neg_elim_core q
  | p => p

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
theorem neg_free_neg_elim_core : ∀ p, IsNnf p → (negElimCore p).NegFree := by
  run_tac
    preform.induce sorry
  · cases p <;>
      try
          cases h1 <;>
        try
          trivial
    constructor <;> trivial
    
  · cases h1
    constructor <;>
        [· apply ihp
          ,
        · apply ihq
          ] <;>
      assumption
    
  · cases h1
    constructor <;>
        [· apply ihp
          ,
        · apply ihq
          ] <;>
      assumption
    

theorem le_and_le_iff_eq {α : Type} [PartialOrderₓ α] {a b : α} : a ≤ b ∧ b ≤ a ↔ a = b := by
  constructor <;> intro h1
  · cases h1
    apply le_antisymmₓ <;> assumption
    
  · constructor <;> apply le_of_eqₓ <;> rw [h1]
    

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
theorem implies_neg_elim_core : ∀ {p : Preform}, Preform.Implies p (negElimCore p) := by
  run_tac
    preform.induce sorry
  · cases' p with t s t s <;>
      try
        apply h
    · apply Or.symm
      simpa only [← preform.holds, ← le_and_le_iff_eq.symm, ← not_and_distrib, ← not_leₓ] using h
      
    simpa only [← preform.holds, ← not_leₓ, ← Int.add_one_le_iff] using h
    
  · simp only [← neg_elim_core]
    cases h <;>
        [· left
          apply ihp
          ,
        · right
          apply ihq
          ] <;>
      assumption
    
  apply And.imp (ihp _) (ihq _) h

/-- Eliminate all negations in a preform -/
def negElim : Preform → Preform :=
  neg_elim_core ∘ nnf

theorem neg_free_neg_elim {p : Preform} : (negElim p).NegFree :=
  neg_free_neg_elim_core _ (is_nnf_nnf _)

theorem implies_neg_elim {p : Preform} : Preform.Implies p (negElim p) := by
  intro v h1
  apply implies_neg_elim_core
  apply (nnf_equiv v).elim_right h1

end Nat

end Omega

