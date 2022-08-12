/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Scott Morrison, Eric Rodriguez
-/
import Mathbin.Data.List.Basic
import Mathbin.Data.Nat.Prime
import Mathbin.SetTheory.Cardinal.Finite

/-!
# Counting on ℕ

This file defines the `count` function, which gives, for any predicate on the natural numbers,
"how many numbers under `k` satisfy this predicate?".
We then prove several expected lemmas about `count`, relating it to the cardinality of other
objects, and helping to evaluate it for specific `k`.

-/


open Finset

namespace Nat

variable (p : ℕ → Prop)

section Count

variable [DecidablePred p]

/-- Count the number of naturals `k < n` satisfying `p k`. -/
def count (n : ℕ) : ℕ :=
  (List.range n).countp p

@[simp]
theorem count_zero : count p 0 = 0 := by
  rw [count, List.range_zero, List.countp]

/-- A fintype instance for the set relevant to `nat.count`. Locally an instance in locale `count` -/
def CountSet.fintype (n : ℕ) : Fintype { i // i < n ∧ p i } := by
  apply Fintype.ofFinset ((Finset.range n).filter p)
  intro x
  rw [mem_filter, mem_range]
  rfl

localized [Count] attribute [instance] Nat.CountSet.fintype

theorem count_eq_card_filter_range (n : ℕ) : count p n = ((range n).filter p).card := by
  rw [count, List.countp_eq_length_filter]
  rfl

/-- `count p n` can be expressed as the cardinality of `{k // k < n ∧ p k}`. -/
theorem count_eq_card_fintype (n : ℕ) : count p n = Fintype.card { k : ℕ // k < n ∧ p k } := by
  rw [count_eq_card_filter_range, ← Fintype.card_of_finset, ← count_set.fintype]
  rfl

theorem count_succ (n : ℕ) : count p (n + 1) = count p n + if p n then 1 else 0 := by
  split_ifs <;> simp [← count, ← List.range_succ, ← h]

@[mono]
theorem count_monotone : Monotone (count p) :=
  monotone_nat_of_le_succ fun n => by
    by_cases' h : p n <;> simp [← count_succ, ← h]

theorem count_add (a b : ℕ) : count p (a + b) = count p a + count (fun k => p (a + k)) b := by
  have : Disjoint ((range a).filter p) (((range b).map <| addLeftEmbedding a).filter p) := by
    intro x hx
    simp_rw [inf_eq_inter, mem_inter, mem_filter, mem_map, mem_range] at hx
    obtain ⟨⟨hx, _⟩, ⟨c, _, rfl⟩, _⟩ := hx
    exact (self_le_add_right _ _).not_lt hx
  simp_rw [count_eq_card_filter_range, range_add, filter_union, card_disjoint_union this, map_filter, addLeftEmbedding,
    card_map]
  rfl

theorem count_add' (a b : ℕ) : count p (a + b) = count (fun k => p (k + b)) a + count p b := by
  rw [add_commₓ, count_add, add_commₓ]
  simp_rw [add_commₓ b]

theorem count_one : count p 1 = if p 0 then 1 else 0 := by
  simp [← count_succ]

theorem count_succ' (n : ℕ) : count p (n + 1) = count (fun k => p (k + 1)) n + if p 0 then 1 else 0 := by
  rw [count_add', count_one]

variable {p}

@[simp]
theorem count_lt_count_succ_iff {n : ℕ} : count p n < count p (n + 1) ↔ p n := by
  by_cases' h : p n <;> simp [← count_succ, ← h]

theorem count_succ_eq_succ_count_iff {n : ℕ} : count p (n + 1) = count p n + 1 ↔ p n := by
  by_cases' h : p n <;> simp [← h, ← count_succ]

theorem count_succ_eq_count_iff {n : ℕ} : count p (n + 1) = count p n ↔ ¬p n := by
  by_cases' h : p n <;> simp [← h, ← count_succ]

alias count_succ_eq_succ_count_iff ↔ _ count_succ_eq_succ_count

alias count_succ_eq_count_iff ↔ _ count_succ_eq_count

theorem count_le_cardinal (n : ℕ) : (count p n : Cardinal) ≤ Cardinal.mk { k | p k } := by
  rw [count_eq_card_fintype, ← Cardinal.mk_fintype]
  exact Cardinal.mk_subtype_mono fun x hx => hx.2

theorem lt_of_count_lt_count {a b : ℕ} (h : count p a < count p b) : a < b :=
  (count_monotone p).reflect_lt h

theorem count_strict_mono {m n : ℕ} (hm : p m) (hmn : m < n) : count p m < count p n :=
  (count_lt_count_succ_iff.2 hm).trans_le <| count_monotone _ (Nat.succ_le_iff.2 hmn)

theorem count_injective {m n : ℕ} (hm : p m) (hn : p n) (heq : count p m = count p n) : m = n := by
  by_contra
  wlog hmn : m < n
  · exact Ne.lt_or_lt h
    
  · simpa [← HEq] using count_strict_mono hm hmn
    

theorem count_le_card (hp : (SetOf p).Finite) (n : ℕ) : count p n ≤ hp.toFinset.card := by
  rw [count_eq_card_filter_range]
  exact Finset.card_mono fun x hx => hp.mem_to_finset.2 (mem_filter.1 hx).2

theorem count_lt_card {n : ℕ} (hp : (SetOf p).Finite) (hpn : p n) : count p n < hp.toFinset.card :=
  (count_lt_count_succ_iff.2 hpn).trans_le (count_le_card hp _)

variable {q : ℕ → Prop}

variable [DecidablePred q]

theorem count_mono_left {n : ℕ} (hpq : ∀ k, p k → q k) : count p n ≤ count q n := by
  simp only [← count_eq_card_filter_range]
  exact card_le_of_subset ((range n).monotone_filter_right hpq)

end Count

end Nat

