/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathbin.Data.List.BigOperators

/-!
# Counting in lists

This file proves basic properties of `list.countp` and `list.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in [`data.list.defs`](./defs).
-/


open Nat

variable {α β : Type _} {l l₁ l₂ : List α}

namespace List

section Countp

variable (p : α → Prop) [DecidablePred p]

@[simp]
theorem countp_nil : countp p [] = 0 :=
  rfl

@[simp]
theorem countp_cons_of_pos {a : α} (l) (pa : p a) : countp p (a :: l) = countp p l + 1 :=
  if_pos pa

@[simp]
theorem countp_cons_of_neg {a : α} (l) (pa : ¬p a) : countp p (a :: l) = countp p l :=
  if_neg pa

theorem countp_cons (a : α) (l) : countp p (a :: l) = countp p l + ite (p a) 1 0 := by
  by_cases' h : p a <;> simp [← h]

theorem length_eq_countp_add_countp (l) : length l = countp p l + countp (fun a => ¬p a) l := by
  induction' l with x h ih <;> [rfl, by_cases' p x] <;>
      [simp only [← countp_cons_of_pos _ _ h, ← countp_cons_of_neg (fun a => ¬p a) _ (Decidable.not_not.2 h), ← ih, ←
        length],
      simp only [← countp_cons_of_pos (fun a => ¬p a) _ h, ← countp_cons_of_neg _ _ h, ← ih, ← length]] <;>
    ac_rfl

theorem countp_eq_length_filter (l) : countp p l = length (filterₓ p l) := by
  induction' l with x l ih <;> [rfl, by_cases' p x] <;>
      [simp only [← filter_cons_of_pos _ h, ← countp, ← ih, ← if_pos h],
      simp only [← countp_cons_of_neg _ _ h, ← ih, ← filter_cons_of_neg _ h]] <;>
    rfl

theorem countp_le_length : countp p l ≤ l.length := by
  simpa only [← countp_eq_length_filter] using length_le_of_sublist (filter_sublist _)

@[simp]
theorem countp_append (l₁ l₂) : countp p (l₁ ++ l₂) = countp p l₁ + countp p l₂ := by
  simp only [← countp_eq_length_filter, ← filter_append, ← length_append]

theorem countp_pos {l} : 0 < countp p l ↔ ∃ a ∈ l, p a := by
  simp only [← countp_eq_length_filter, ← length_pos_iff_exists_mem, ← mem_filter, ← exists_prop]

theorem countp_eq_zero {l} : countp p l = 0 ↔ ∀, ∀ a ∈ l, ∀, ¬p a := by
  rw [← not_iff_not, ← Ne.def, ← pos_iff_ne_zero, countp_pos]
  simp

theorem countp_eq_length {l} : countp p l = l.length ↔ ∀, ∀ a ∈ l, ∀, p a := by
  rw [countp_eq_length_filter, filter_length_eq_length]

theorem length_filter_lt_length_iff_exists (l) : length (filterₓ p l) < length l ↔ ∃ x ∈ l, ¬p x := by
  rw [length_eq_countp_add_countp p l, ← countp_pos, countp_eq_length_filter, lt_add_iff_pos_right]

theorem Sublist.countp_le (s : l₁ <+ l₂) : countp p l₁ ≤ countp p l₂ := by
  simpa only [← countp_eq_length_filter] using length_le_of_sublist (s.filter p)

@[simp]
theorem countp_filter {q} [DecidablePred q] (l : List α) : countp p (filterₓ q l) = countp (fun a => p a ∧ q a) l := by
  simp only [← countp_eq_length_filter, ← filter_filter]

@[simp]
theorem countp_true : (l.countp fun _ => True) = l.length := by
  simp [← countp_eq_length_filter]

@[simp]
theorem countp_false : (l.countp fun _ => False) = 0 := by
  simp [← countp_eq_length_filter]

end Countp

/-! ### count -/


section Count

variable [DecidableEq α]

@[simp]
theorem count_nil (a : α) : count a [] = 0 :=
  rfl

theorem count_cons (a b : α) (l : List α) : count a (b :: l) = if a = b then succ (count a l) else count a l :=
  rfl

theorem count_cons' (a b : α) (l : List α) : count a (b :: l) = count a l + if a = b then 1 else 0 := by
  rw [count_cons]
  split_ifs <;> rfl

@[simp]
theorem count_cons_self (a : α) (l : List α) : count a (a :: l) = succ (count a l) :=
  if_pos rfl

@[simp]
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (l : List α) : count a (b :: l) = count a l :=
  if_neg h

theorem count_tail :
    ∀ (l : List α) (a : α) (h : 0 < l.length), l.tail.count a = l.count a - ite (a = List.nthLe l 0 h) 1 0
  | _ :: _, a, h => by
    rw [count_cons]
    split_ifs <;> simp

theorem count_le_length (a : α) (l : List α) : count a l ≤ l.length :=
  countp_le_length _

theorem Sublist.count_le (h : l₁ <+ l₂) (a : α) : count a l₁ ≤ count a l₂ :=
  h.countp_le _

theorem count_le_count_cons (a b : α) (l : List α) : count a l ≤ count a (b :: l) :=
  (sublist_cons _ _).count_le _

theorem count_singleton (a : α) : count a [a] = 1 :=
  if_pos rfl

theorem count_singleton' (a b : α) : count a [b] = ite (a = b) 1 0 :=
  rfl

@[simp]
theorem count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
  countp_append _

theorem count_concat (a : α) (l : List α) : count a (concat l a) = succ (count a l) := by
  simp [-add_commₓ]

@[simp]
theorem count_pos {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  simp only [← count, ← countp_pos, ← exists_prop, ← exists_eq_right']

@[simp]
theorem one_le_count_iff_mem {a : α} {l : List α} : 1 ≤ count a l ↔ a ∈ l :=
  count_pos

@[simp]
theorem count_eq_zero_of_not_mem {a : α} {l : List α} (h : a ∉ l) : count a l = 0 :=
  Decidable.by_contradiction fun h' => h <| count_pos.1 (Nat.pos_of_ne_zeroₓ h')

theorem not_mem_of_count_eq_zero {a : α} {l : List α} (h : count a l = 0) : a ∉ l := fun h' => (count_pos.2 h').ne' h

theorem count_eq_zero {a : α} {l} : count a l = 0 ↔ a ∉ l :=
  ⟨not_mem_of_count_eq_zero, count_eq_zero_of_not_mem⟩

theorem count_eq_length {a : α} {l} : count a l = l.length ↔ ∀, ∀ b ∈ l, ∀, a = b := by
  rw [count, countp_eq_length]

@[simp]
theorem count_repeat (a : α) (n : ℕ) : count a (repeat a n) = n := by
  rw [count, countp_eq_length_filter, filter_eq_self.2, length_repeat] <;> exact fun b m => (eq_of_mem_repeat m).symm

theorem le_count_iff_repeat_sublist {a : α} {l : List α} {n : ℕ} : n ≤ count a l ↔ repeat a n <+ l :=
  ⟨fun h =>
    ((repeat_sublist_repeat a).2 h).trans <| by
      have : filterₓ (Eq a) l = repeat a (count a l) :=
        eq_repeat.2
          ⟨by
            simp only [← count, ← countp_eq_length_filter], fun b m => (of_mem_filter m).symm⟩
      rw [← this] <;> apply filter_sublist,
    fun h => by
    simpa only [← count_repeat] using h.count_le a⟩

theorem repeat_count_eq_of_count_eq_length {a : α} {l : List α} (h : count a l = length l) : repeat a (count a l) = l :=
  eq_of_sublist_of_length_eq (le_count_iff_repeat_sublist.mp (le_reflₓ (count a l)))
    (Eq.trans (length_repeat a (count a l)) h)

@[simp]
theorem count_filter {p} [DecidablePred p] {a} {l : List α} (h : p a) : count a (filterₓ p l) = count a l := by
  simp only [← count, ← countp_filter, ←
    show (fun b => a = b ∧ p b) = Eq a by
      ext b
      constructor <;> cc]

theorem count_bind {α β} [DecidableEq β] (l : List α) (f : α → List β) (x : β) :
    count x (l.bind f) = sum (map (count x ∘ f) l) := by
  induction' l with hd tl IH
  · simp
    
  · simpa
    

@[simp]
theorem count_map_of_injective {α β} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β)
    (hf : Function.Injective f) (x : α) : count (f x) (map f l) = count x l := by
  induction' l with y l IH generalizing x
  · simp
    
  · simp [← map_cons, ← count_cons', ← IH, ← hf.eq_iff]
    

theorem count_le_count_map [DecidableEq β] (l : List α) (f : α → β) (x : α) : count x l ≤ count (f x) (map f l) := by
  induction' l with a as IH
  · simp
    
  rcases eq_or_ne x a with (rfl | hxa)
  · simp [← succ_le_succ IH]
    
  · simp [← hxa, ← le_add_right IH, ← count_cons']
    

@[simp]
theorem count_erase_self (a : α) : ∀ s : List α, count a (List.eraseₓ s a) = pred (count a s)
  | [] => by
    simp
  | h :: t => by
    rw [erase_cons]
    by_cases' p : h = a
    · rw [if_pos p, count_cons', if_pos p.symm]
      simp
      
    · rw [if_neg p, count_cons', count_cons', if_neg fun x : a = h => p x.symm, count_erase_self]
      simp
      

@[simp]
theorem count_erase_of_ne {a b : α} (ab : a ≠ b) : ∀ s : List α, count a (List.eraseₓ s b) = count a s
  | [] => by
    simp
  | x :: xs => by
    rw [erase_cons]
    split_ifs with h
    · rw [count_cons', h, if_neg ab]
      simp
      
    · rw [count_cons', count_cons', count_erase_of_ne]
      

end Count

end List

