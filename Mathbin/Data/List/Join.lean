/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Mario Carneiro
-/
import Mathbin.Data.List.BigOperators

/-!
# Join of a list of lists

This file proves basic properties of `list.join`, which concatenates a list of lists. It is defined
in [`data.list.defs`](./defs).
-/


variable {α β : Type _}

namespace List

attribute [simp] join

@[simp]
theorem join_nil : [([] : List α)].join = [] :=
  rfl

@[simp]
theorem join_eq_nil : ∀ {L : List (List α)}, join L = [] ↔ ∀, ∀ l ∈ L, ∀, l = []
  | [] => iff_of_true rfl (forall_mem_nilₓ _)
  | l :: L => by
    simp only [← join, ← append_eq_nil, ← join_eq_nil, ← forall_mem_cons]

@[simp]
theorem join_append (L₁ L₂ : List (List α)) : join (L₁ ++ L₂) = join L₁ ++ join L₂ := by
  induction L₁ <;> [rfl, simp only [*, ← join, ← cons_append, ← append_assoc]]

theorem join_concat (L : List (List α)) (l : List α) : join (L.concat l) = join L ++ l := by
  simp

@[simp]
theorem join_filter_empty_eq_ff [DecidablePred fun l : List α => l.Empty = ff] :
    ∀ {L : List (List α)}, join (L.filter fun l => l.Empty = ff) = L.join
  | [] => rfl
  | [] :: L => by
    simp [← @join_filter_empty_eq_ff L]
  | (a :: l) :: L => by
    simp [← @join_filter_empty_eq_ff L]

@[simp]
theorem join_filter_ne_nil [DecidablePred fun l : List α => l ≠ []] {L : List (List α)} :
    join (L.filter fun l => l ≠ []) = L.join := by
  simp [← join_filter_empty_eq_ff, empty_iff_eq_nil]

theorem join_join (l : List (List (List α))) : l.join.join = (l.map join).join := by
  induction l
  simp
  simp [← l_ih]

@[simp]
theorem length_join (L : List (List α)) : length (join L) = sum (map length L) := by
  induction L <;> [rfl, simp only [*, ← join, ← map, ← sum_cons, ← length_append]]

@[simp]
theorem length_bind (l : List α) (f : α → List β) : length (List.bind l f) = sum (map (length ∘ f) l) := by
  rw [List.bind, length_join, map_map]

@[simp]
theorem bind_eq_nil {l : List α} {f : α → List β} : List.bind l f = [] ↔ ∀, ∀ x ∈ l, ∀, f x = [] :=
  join_eq_nil.trans <| by
    simp only [← mem_map, ← forall_exists_index, ← and_imp, ← forall_apply_eq_imp_iff₂]

/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists. -/
theorem take_sum_join (L : List (List α)) (i : ℕ) : L.join.take ((L.map length).take i).Sum = (L.take i).join := by
  induction L generalizing i
  · simp
    
  cases i
  · simp
    
  simp [← take_append, ← L_ih]

/-- In a join, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists. -/
theorem drop_sum_join (L : List (List α)) (i : ℕ) : L.join.drop ((L.map length).take i).Sum = (L.drop i).join := by
  induction L generalizing i
  · simp
    
  cases i
  · simp
    
  simp [← drop_append, ← L_ih]

/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
theorem drop_take_succ_eq_cons_nth_le (L : List α) {i : ℕ} (hi : i < L.length) :
    (L.take (i + 1)).drop i = [nthLe L i hi] := by
  induction L generalizing i
  · simp only [← length] at hi
    exact (Nat.not_succ_le_zeroₓ i hi).elim
    
  cases i
  · simp
    
  have : i < L_tl.length := by
    simp at hi
    exact Nat.lt_of_succ_lt_succₓ hi
  simp [← L_ih this]
  rfl

/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lenghts of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
theorem drop_take_succ_join_eq_nth_le (L : List (List α)) {i : ℕ} (hi : i < L.length) :
    (L.join.take ((L.map length).take (i + 1)).Sum).drop ((L.map length).take i).Sum = nthLe L i hi := by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [← map_take, ← take_take]
  simp [← take_sum_join, ← this, ← drop_sum_join, ← drop_take_succ_eq_cons_nth_le _ hi]

/-- Auxiliary lemma to control elements in a join. -/
theorem sum_take_map_length_lt1 (L : List (List α)) {i j : ℕ} (hi : i < L.length) (hj : j < (nthLe L i hi).length) :
    ((L.map length).take i).Sum + j < ((L.map length).take (i + 1)).Sum := by
  simp [← hi, ← sum_take_succ, ← hj]

/-- Auxiliary lemma to control elements in a join. -/
theorem sum_take_map_length_lt2 (L : List (List α)) {i j : ℕ} (hi : i < L.length) (hj : j < (nthLe L i hi).length) :
    ((L.map length).take i).Sum + j < L.join.length := by
  convert lt_of_lt_of_leₓ (sum_take_map_length_lt1 L hi hj) (monotone_sum_take _ hi)
  have : L.length = (L.map length).length := by
    simp
  simp [← this, -length_map]

/-- The `n`-th element in a join of sublists is the `j`-th element of the `i`th sublist,
where `n` can be obtained in terms of `i` and `j` by adding the lengths of all the sublists
of index `< i`, and adding `j`. -/
theorem nth_le_join (L : List (List α)) {i j : ℕ} (hi : i < L.length) (hj : j < (nthLe L i hi).length) :
    nthLe L.join (((L.map length).take i).Sum + j) (sum_take_map_length_lt2 L hi hj) = nthLe (nthLe L i hi) j hj := by
  rw [nth_le_take L.join (sum_take_map_length_lt2 L hi hj) (sum_take_map_length_lt1 L hi hj), nth_le_drop,
    nth_le_of_eq (drop_take_succ_join_eq_nth_le L hi)]

/-- Two lists of sublists are equal iff their joins coincide, as well as the lengths of the
sublists. -/
theorem eq_iff_join_eq (L L' : List (List α)) : L = L' ↔ L.join = L'.join ∧ map length L = map length L' := by
  refine'
    ⟨fun H => by
      simp [← H], _⟩
  rintro ⟨join_eq, length_eq⟩
  apply ext_le
  · have : length (map length L) = length (map length L') := by
      rw [length_eq]
    simpa using this
    
  · intro n h₁ h₂
    rw [← drop_take_succ_join_eq_nth_le, ← drop_take_succ_join_eq_nth_le, join_eq, length_eq]
    

end List

