/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Computability.Language
import Mathbin.Tactic.NormNum

/-!
# Deterministic Finite Automata
This file contains the definition of a Deterministic Finite Automaton (DFA), a state machine which
determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular set
in linear time.
Note that this definition allows for Automaton with infinite states, a `fintype` instance must be
supplied for true DFA's.
-/


universe u v

/-- A DFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`). -/
structure DFA (α : Type u) (σ : Type v) where
  step : σ → α → σ
  start : σ
  accept : Set σ

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

instance [Inhabited σ] : Inhabited (DFA α σ) :=
  ⟨DFA.mk (fun _ _ => default) default ∅⟩

/-- `M.eval_from s x` evaluates `M` with input `x` starting from the state `s`. -/
def evalFrom (start : σ) : List α → σ :=
  List.foldlₓ M.step start

@[simp]
theorem eval_from_nil (s : σ) : M.evalFrom s [] = s :=
  rfl

@[simp]
theorem eval_from_singleton (s : σ) (a : α) : M.evalFrom s [a] = M.step s a :=
  rfl

@[simp]
theorem eval_from_append_singleton (s : σ) (x : List α) (a : α) : M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a :=
  by
  simp only [← eval_from, ← List.foldl_append, ← List.foldl_cons, ← List.foldl_nil]

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval : List α → σ :=
  M.evalFrom M.start

@[simp]
theorem eval_nil : M.eval [] = M.start :=
  rfl

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.step M.start a :=
  rfl

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.step (M.eval x) a :=
  eval_from_append_singleton _ _ _ _

theorem eval_from_of_append (start : σ) (x y : List α) :
    M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y :=
  x.foldl_append _ _ y

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def Accepts : Language α := fun x => M.eval x ∈ M.accept

theorem mem_accepts (x : List α) : x ∈ M.Accepts ↔ M.evalFrom M.start x ∈ M.accept := by
  rfl

theorem eval_from_split [Fintype σ] {x : List α} {s t : σ} (hlen : Fintype.card σ ≤ x.length)
    (hx : M.evalFrom s x = t) :
    ∃ q a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧ M.evalFrom s a = q ∧ M.evalFrom q b = q ∧ M.evalFrom q c = t :=
  by
  obtain ⟨n, m, hneq, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun n : Finₓ (Fintype.card σ + 1) => M.eval_from s (x.take n))
      (by
        norm_num)
  wlog hle : (n : ℕ) ≤ m using n m
  have hlt : (n : ℕ) < m := (Ne.le_iff_lt hneq).mp hle
  have hm : (m : ℕ) ≤ Fintype.card σ := Finₓ.is_le m
  dsimp'  at heq
  refine'
    ⟨M.eval_from s ((x.take m).take n), (x.take m).take n, (x.take m).drop n, x.drop m, _, _, _, by
      rfl, _⟩
  · rw [List.take_append_dropₓ, List.take_append_dropₓ]
    
  · simp only [← List.length_dropₓ, ← List.length_takeₓ]
    rw [min_eq_leftₓ (hm.trans hlen), min_eq_leftₓ hle, add_tsub_cancel_of_le hle]
    exact hm
    
  · intro h
    have hlen' := congr_arg List.length h
    simp only [← List.length_dropₓ, ← List.length, ← List.length_takeₓ] at hlen'
    rw [min_eq_leftₓ, tsub_eq_zero_iff_le] at hlen'
    · apply hneq
      apply le_antisymmₓ
      assumption'
      
    exact hm.trans hlen
    
  have hq : M.eval_from (M.eval_from s ((x.take m).take n)) ((x.take m).drop n) = M.eval_from s ((x.take m).take n) :=
    by
    rw [List.take_take, min_eq_leftₓ hle, ← eval_from_of_append, HEq, ← min_eq_leftₓ hle, ← List.take_take,
      min_eq_leftₓ hle, List.take_append_dropₓ]
  use hq
  rwa [← hq, ← eval_from_of_append, ← eval_from_of_append, ← List.append_assoc, List.take_append_dropₓ,
    List.take_append_dropₓ]

theorem eval_from_of_pow {x y : List α} {s : σ} (hx : M.evalFrom s x = s) (hy : y ∈ @Language.Star α {x}) :
    M.evalFrom s y = s := by
  rw [Language.mem_star] at hy
  rcases hy with ⟨S, rfl, hS⟩
  induction' S with a S ih
  · rfl
    
  · have ha := hS a (List.mem_cons_selfₓ _ _)
    rw [Set.mem_singleton_iff] at ha
    rw [List.join, eval_from_of_append, ha, hx]
    apply ih
    intro z hz
    exact hS z (List.mem_cons_of_memₓ a hz)
    

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.Accepts) (hlen : Fintype.card σ ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧ {a} * Language.Star {b} * {c} ≤ M.Accepts :=
  by
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := M.eval_from_split hlen rfl
  use a, b, c, hx, hlen, hnil
  intro y hy
  rw [Language.mem_mul] at hy
  rcases hy with ⟨ab, c', hab, hc', rfl⟩
  rw [Language.mem_mul] at hab
  rcases hab with ⟨a', b', ha', hb', rfl⟩
  rw [Set.mem_singleton_iff] at ha' hc'
  substs ha' hc'
  have h := M.eval_from_of_pow hb hb'
  rwa [mem_accepts, eval_from_of_append, eval_from_of_append, h, hc]

end DFA

