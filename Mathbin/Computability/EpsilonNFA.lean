/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Yaël Dillies
-/
import Mathbin.Computability.NFA

/-!
# Epsilon Nondeterministic Finite Automata
This file contains the definition of an epsilon Nondeterministic Finite Automaton (`ε_NFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitons,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `fintype` instance must be
supplied for true `ε_NFA`'s.
-/


open Set

universe u v

/-- An `ε_NFA` is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `set` of states and can make ε-transitions by
  inputing `none`.
  Since this definition allows for Automata with infinite states, a `fintype` instance must be
  supplied for true `ε_NFA`'s.-/
structure εNFA (α : Type u) (σ : Type v) where
  step : σ → Option α → Set σ
  start : Set σ
  accept : Set σ

variable {α : Type u} {σ σ' : Type v} (M : εNFA α σ) {S : Set σ} {x : List α} {s : σ} {a : α}

namespace εNFA

/-- The `ε_closure` of a set is the set of states which can be reached by taking a finite string of
ε-transitions from an element of the set. -/
inductive εClosure (S : Set σ) : Set σ
  | base : ∀, ∀ s ∈ S, ∀, ε_closure s
  | step : ∀ (s), ∀ t ∈ M.step s none, ∀, ε_closure s → ε_closure t

@[simp]
theorem subset_ε_closure (S : Set σ) : S ⊆ M.εClosure S :=
  ε_closure.base

@[simp]
theorem ε_closure_empty : M.εClosure ∅ = ∅ :=
  eq_empty_of_forall_not_mem fun s hs => by
    induction' hs with t ht _ _ _ _ ih <;> assumption

@[simp]
theorem ε_closure_univ : M.εClosure Univ = univ :=
  eq_univ_of_univ_subset <| subset_ε_closure _ _

/-- `M.step_set S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
def StepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.εClosure <| M.step s a

variable {M}

@[simp]
theorem mem_step_set_iff : s ∈ M.StepSet S a ↔ ∃ t ∈ S, s ∈ M.εClosure (M.step t a) :=
  mem_Union₂

@[simp]
theorem step_set_empty (a : α) : M.StepSet ∅ a = ∅ := by
  simp_rw [step_set, Union_false, Union_empty]

variable (M)

/-- `M.eval_from S x` computes all possible paths through `M` with input `x` starting at an element
of `S`. -/
def EvalFrom (start : Set σ) : List α → Set σ :=
  List.foldlₓ M.StepSet (M.εClosure start)

@[simp]
theorem eval_from_nil (S : Set σ) : M.evalFrom S [] = M.εClosure S :=
  rfl

@[simp]
theorem eval_from_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.StepSet (M.εClosure S) a :=
  rfl

@[simp]
theorem eval_from_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.StepSet (M.evalFrom S x) a := by
  simp only [← eval_from, ← List.foldl_append, ← List.foldl_cons, ← List.foldl_nil]

@[simp]
theorem eval_from_empty (x : List α) : M.evalFrom ∅ x = ∅ := by
  induction' x using List.reverseRecOn with x a ih
  · rw [eval_from_nil, ε_closure_empty]
    
  · rw [eval_from_append_singleton, ih, step_set_empty]
    

/-- `M.eval x` computes all possible paths through `M` with input `x` starting at an element of
`M.start`. -/
def Eval :=
  M.evalFrom M.start

@[simp]
theorem eval_nil : M.eval [] = M.εClosure M.start :=
  rfl

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.StepSet (M.εClosure M.start) a :=
  rfl

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.StepSet (M.eval x) a :=
  eval_from_append_singleton _ _ _ _

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def Accepts : Language α :=
  { x | ∃ S ∈ M.accept, S ∈ M.eval x }

/-! ### Conversions between `ε_NFA` and `NFA` -/


/-- `M.to_NFA` is an `NFA` constructed from an `ε_NFA` `M`. -/
def toNFA : NFA α σ where
  step := fun S a => M.εClosure (M.step S a)
  start := M.εClosure M.start
  accept := M.accept

@[simp]
theorem to_NFA_eval_from_match (start : Set σ) : M.toNFA.evalFrom (M.εClosure start) = M.evalFrom start :=
  rfl

@[simp]
theorem to_NFA_correct : M.toNFA.Accepts = M.Accepts := by
  ext x
  rw [accepts, NFA.Accepts, eval, NFA.Eval, ← to_NFA_eval_from_match]
  rfl

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.Accepts) (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * Language.Star {b} * {c} ≤ M.Accepts :=
  by
  rw [← to_NFA_correct] at hx⊢
  exact M.to_NFA.pumping_lemma hx hlen

end εNFA

namespace NFA

/-- `M.to_ε_NFA` is an `ε_NFA` constructed from an `NFA` `M` by using the same start and accept
  states and transition functions. -/
def toεNFA (M : NFA α σ) : εNFA α σ where
  step := fun s a => a.casesOn' ∅ fun a => M.step s a
  start := M.start
  accept := M.accept

@[simp]
theorem to_ε_NFA_ε_closure (M : NFA α σ) (S : Set σ) : M.toεNFA.εClosure S = S := by
  ext a
  refine' ⟨_, εNFA.εClosure.base _⟩
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩)
  · exact h
    
  · cases h
    

@[simp]
theorem to_ε_NFA_eval_from_match (M : NFA α σ) (start : Set σ) : M.toεNFA.evalFrom start = M.evalFrom start := by
  rw [eval_from, εNFA.EvalFrom, to_ε_NFA_ε_closure]
  congr
  ext S s
  simp only [← step_set, ← εNFA.StepSet, ← exists_prop, ← Set.mem_Union, ← Set.bind_def]
  apply exists_congr
  simp only [← And.congr_right_iff]
  intro t ht
  rw [M.to_ε_NFA_ε_closure]
  rfl

@[simp]
theorem to_ε_NFA_correct (M : NFA α σ) : M.toεNFA.Accepts = M.Accepts := by
  rw [accepts, εNFA.Accepts, eval, εNFA.Eval, to_ε_NFA_eval_from_match]
  rfl

end NFA

/-! ### Regex-like operations -/


namespace εNFA

instance : Zero (εNFA α σ) :=
  ⟨⟨fun _ _ => ∅, ∅, ∅⟩⟩

instance : One (εNFA α σ) :=
  ⟨⟨fun _ _ => ∅, Univ, Univ⟩⟩

instance : Inhabited (εNFA α σ) :=
  ⟨0⟩

variable (P : εNFA α σ) (Q : εNFA α σ')

@[simp]
theorem step_zero (s a) : (0 : εNFA α σ).step s a = ∅ :=
  rfl

@[simp]
theorem step_one (s a) : (1 : εNFA α σ).step s a = ∅ :=
  rfl

@[simp]
theorem start_zero : (0 : εNFA α σ).start = ∅ :=
  rfl

@[simp]
theorem start_one : (1 : εNFA α σ).start = univ :=
  rfl

@[simp]
theorem accept_zero : (0 : εNFA α σ).accept = ∅ :=
  rfl

@[simp]
theorem accept_one : (1 : εNFA α σ).accept = univ :=
  rfl

end εNFA

