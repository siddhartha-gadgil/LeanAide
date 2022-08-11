/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Data.List.ProdSigma
import Mathbin.Tactic.Omega.Clause
import Mathbin.Tactic.Omega.Int.Form

/-!
# DNF transformation
-/


namespace Omega

namespace Int

open Omega.Int

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
  · simp only [← not_not, ← push_neg, ← preform.holds]
    
  · simp only [← preform.holds, ← push_neg, ← not_or_distrib, ← ihp v, ← ihq v]
    
  · simp only [← preform.holds, ← push_neg, ← not_and_distrib, ← ihp v, ← ihq v]
    

/-- NNF transformation -/
def nnf : Preform → Preform
  | ¬* p => pushNeg (nnf p)
  | p ∨* q => nnf p ∨* nnf q
  | p ∧* q => nnf p ∧* nnf q
  | a => a

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
    

/-- Argument is free of negations -/
def NegFree : Preform → Prop
  | t =* s => True
  | t ≤* s => True
  | p ∨* q => neg_free p ∧ neg_free q
  | p ∧* q => neg_free p ∧ neg_free q
  | _ => False

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
    

/-- Eliminate all negations from preform -/
@[simp]
def negElim : Preform → Preform
  | ¬* t =* s => (t.add_one ≤* s) ∨* s.add_one ≤* t
  | ¬* t ≤* s => s.add_one ≤* t
  | p ∨* q => neg_elim p ∨* neg_elim q
  | p ∧* q => neg_elim p ∧* neg_elim q
  | p => p

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
theorem neg_free_neg_elim : ∀ p : Preform, IsNnf p → NegFree (negElim p) := by
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
theorem implies_neg_elim : ∀ {p : Preform}, Preform.Implies p (negElim p) := by
  run_tac
    preform.induce sorry
  · cases' p with t s t s <;>
      try
        apply h
    · simp only [← le_and_le_iff_eq.symm, ← not_and_distrib, ← not_leₓ, ← preterm.val, ← preform.holds] at h
      simp only [← Int.add_one_le_iff, ← preterm.add_one, ← preterm.val, ← preform.holds, ← neg_elim]
      rw [or_comm]
      assumption
      
    · simp only [← not_leₓ, ← Int.add_one_le_iff, ← preterm.add_one, ← not_leₓ, ← preterm.val, ← preform.holds, ←
        neg_elim] at *
      assumption
      
    
  · simp only [← neg_elim]
    cases h <;>
        [· left
          apply ihp
          ,
        · right
          apply ihq
          ] <;>
      assumption
    
  · apply And.imp (ihp _) (ihq _) h
    

@[simp]
def dnfCore : Preform → List Clause
  | p ∨* q => dnf_core p ++ dnf_core q
  | p ∧* q => (List.product (dnf_core p) (dnf_core q)).map fun pq => Clause.append pq.fst pq.snd
  | t =* s => [([Term.sub (canonize s) (canonize t)], [])]
  | t ≤* s => [([], [Term.sub (canonize s) (canonize t)])]
  | ¬* _ => []

/-- DNF transformation -/
def dnf (p : Preform) : List Clause :=
  dnf_core <| neg_elim <| nnf p

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
theorem exists_clause_holds {v : Nat → Int} :
    ∀ {p : Preform}, NegFree p → p.Holds v → ∃ c ∈ dnfCore p, Clause.Holds v c := by
  run_tac
    preform.induce sorry
  · apply List.exists_mem_cons_ofₓ
    constructor
    · simp only [← preterm.val, ← preform.holds] at h2
      rw [List.forall_mem_singletonₓ]
      simp only [← h2, ← Omega.Int.val_canonize, ← Omega.Term.val_sub, ← sub_self]
      
    · apply List.forall_mem_nilₓ
      
    
  · apply List.exists_mem_cons_ofₓ
    constructor
    · apply List.forall_mem_nilₓ
      
    · simp only [← preterm.val, ← preform.holds] at h2
      rw [List.forall_mem_singletonₓ]
      simp only [← val_canonize, ← preterm.val, ← term.val_sub]
      rw [le_sub, sub_zero]
      assumption
      
    
  · cases h1
    
  · cases' h2 with h2 h2 <;>
        [· cases' ihp h1.left h2 with c h3
          ,
        · cases' ihq h1.right h2 with c h3
          ] <;>
      cases' h3 with h3 h4 <;> refine' ⟨c, list.mem_append.elim_right _, h4⟩ <;> [left, right] <;> assumption
    
  · rcases ihp h1.left h2.left with ⟨cp, hp1, hp2⟩
    rcases ihq h1.right h2.right with ⟨cq, hq1, hq2⟩
    refine' ⟨clause.append cp cq, ⟨_, clause.holds_append hp2 hq2⟩⟩
    simp only [← dnf_core, ← List.mem_mapₓ]
    refine' ⟨(cp, cq), ⟨_, rfl⟩⟩
    rw [List.mem_product]
    constructor <;> assumption
    

theorem clauses_sat_dnf_core {p : Preform} : NegFree p → p.Sat → Clauses.Sat (dnfCore p) := by
  intro h1 h2
  cases' h2 with v h2
  rcases exists_clause_holds h1 h2 with ⟨c, h3, h4⟩
  refine' ⟨c, h3, v, h4⟩

theorem unsat_of_clauses_unsat {p : Preform} : Clauses.Unsat (dnf p) → p.Unsat := by
  intro h1 h2
  apply h1
  apply clauses_sat_dnf_core
  apply neg_free_neg_elim _ (is_nnf_nnf _)
  apply preform.sat_of_implies_of_sat implies_neg_elim
  have hrw := exists_congr (@nnf_equiv p)
  apply hrw.elim_right h2

end Int

end Omega

