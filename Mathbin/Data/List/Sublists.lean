/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.List.Basic
import Mathbin.Data.Nat.Choose.Basic

/-! # sublists

`list.sublists` gives a list of all (not necessarily contiguous) sublists of a list.

This file contains basic results on this function.
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Nat

namespace List

/-! ### sublists -/


@[simp]
theorem sublists'_nil : sublists' (@nil α) = [[]] :=
  rfl

@[simp]
theorem sublists'_singleton (a : α) : sublists' [a] = [[], [a]] :=
  rfl

theorem map_sublists'_aux (g : List β → List γ) (l : List α) (f r) :
    map g (sublists'Aux l f r) = sublists'Aux l (g ∘ f) (map g r) := by
  induction l generalizing f r <;> [rfl, simp only [*, ← sublists'_aux]]

theorem sublists'_aux_append (r' : List (List β)) (l : List α) (f r) :
    sublists'Aux l f (r ++ r') = sublists'Aux l f r ++ r' := by
  induction l generalizing f r <;> [rfl, simp only [*, ← sublists'_aux]]

theorem sublists'_aux_eq_sublists' (l f r) : @sublists'Aux α β l f r = map f (sublists' l) ++ r := by
  rw [sublists', map_sublists'_aux, ← sublists'_aux_append] <;> rfl

@[simp]
theorem sublists'_cons (a : α) (l : List α) : sublists' (a :: l) = sublists' l ++ map (cons a) (sublists' l) := by
  rw [sublists', sublists'_aux] <;> simp only [← sublists'_aux_eq_sublists', ← map_id, ← append_nil] <;> rfl

@[simp]
theorem mem_sublists' {s t : List α} : s ∈ sublists' t ↔ s <+ t := by
  induction' t with a t IH generalizing s
  · simp only [← sublists'_nil, ← mem_singleton]
    exact
      ⟨fun h => by
        rw [h], eq_nil_of_sublist_nil⟩
    
  simp only [← sublists'_cons, ← mem_append, ← IH, ← mem_map]
  constructor <;> intro h
  rcases h with (h | ⟨s, h, rfl⟩)
  · exact sublist_cons_of_sublist _ h
    
  · exact h.cons_cons _
    
  · cases' h with _ _ _ h s _ _ h
    · exact Or.inl h
      
    · exact Or.inr ⟨s, h, rfl⟩
      
    

@[simp]
theorem length_sublists' : ∀ l : List α, length (sublists' l) = 2 ^ length l
  | [] => rfl
  | a :: l => by
    simp only [← sublists'_cons, ← length_append, ← length_sublists' l, ← length_map, ← length, ← pow_succ'ₓ, ←
      mul_succ, ← mul_zero, ← zero_addₓ]

@[simp]
theorem sublists_nil : sublists (@nil α) = [[]] :=
  rfl

@[simp]
theorem sublists_singleton (a : α) : sublists [a] = [[], [a]] :=
  rfl

theorem sublists_aux₁_eq_sublists_aux :
    ∀ (l) (f : List α → List β), sublistsAux₁ l f = sublistsAux l fun ys r => f ys ++ r
  | [], f => rfl
  | a :: l, f => by
    rw [sublists_aux₁, sublists_aux] <;> simp only [*, ← append_assoc]

theorem sublists_aux_cons_eq_sublists_aux₁ (l : List α) : sublistsAux l cons = sublistsAux₁ l fun x => [x] := by
  rw [sublists_aux₁_eq_sublists_aux] <;> rfl

theorem SublistsAuxEqFoldr.aux {a : α} {l : List α}
    (IH₁ : ∀ f : List α → List β → List β, sublistsAux l f = foldr f [] (sublistsAux l cons))
    (IH₂ : ∀ f : List α → List (List α) → List (List α), sublistsAux l f = foldr f [] (sublistsAux l cons))
    (f : List α → List β → List β) : sublistsAux (a :: l) f = foldr f [] (sublistsAux (a :: l) cons) := by
  simp only [← sublists_aux, ← foldr_cons]
  rw [IH₂, IH₁]
  congr 1
  induction' sublists_aux l cons with _ _ ih
  · rfl
    
  simp only [← ih, ← foldr_cons]

theorem sublists_aux_eq_foldr (l : List α) :
    ∀ f : List α → List β → List β, sublistsAux l f = foldr f [] (sublistsAux l cons) := by
  suffices _ ∧ ∀ f : List α → List (List α) → List (List α), sublistsAux l f = foldr f [] (sublistsAux l cons) from
    this.1
  induction' l with a l IH
  · constructor <;> intro <;> rfl
    
  exact ⟨sublists_aux_eq_foldr.aux IH.1 IH.2, sublists_aux_eq_foldr.aux IH.2 IH.2⟩

theorem sublists_aux_cons_cons (l : List α) (a : α) :
    sublistsAux (a :: l) cons = [a] :: foldr (fun ys r => ys :: (a :: ys) :: r) [] (sublistsAux l cons) := by
  rw [← sublists_aux_eq_foldr] <;> rfl

theorem sublists_aux₁_append :
    ∀ (l₁ l₂ : List α) (f : List α → List β),
      sublistsAux₁ (l₁ ++ l₂) f = sublistsAux₁ l₁ f ++ sublistsAux₁ l₂ fun x => f x ++ sublistsAux₁ l₁ (f ∘ (· ++ x))
  | [], l₂, f => by
    simp only [← sublists_aux₁, ← nil_append, ← append_nil]
  | a :: l₁, l₂, f => by
    simp only [← sublists_aux₁, ← cons_append, ← sublists_aux₁_append l₁, ← append_assoc] <;> rfl

theorem sublists_aux₁_concat (l : List α) (a : α) (f : List α → List β) :
    sublistsAux₁ (l ++ [a]) f = sublistsAux₁ l f ++ f [a] ++ sublistsAux₁ l fun x => f (x ++ [a]) := by
  simp only [← sublists_aux₁_append, ← sublists_aux₁, ← append_assoc, ← append_nil]

theorem sublists_aux₁_bind :
    ∀ (l : List α) (f : List α → List β) (g : β → List γ),
      (sublistsAux₁ l f).bind g = sublistsAux₁ l fun x => (f x).bind g
  | [], f, g => rfl
  | a :: l, f, g => by
    simp only [← sublists_aux₁, ← bind_append, ← sublists_aux₁_bind l]

theorem sublists_aux_cons_append (l₁ l₂ : List α) :
    sublistsAux (l₁ ++ l₂) cons =
      sublistsAux l₁ cons ++ do
        let x ← sublistsAux l₂ cons
        (· ++ x) <$> sublists l₁ :=
  by
  simp only [← sublists, ← sublists_aux_cons_eq_sublists_aux₁, ← sublists_aux₁_append, ← bind_eq_bind, ←
    sublists_aux₁_bind]
  congr
  funext x
  apply congr_arg _
  rw [← bind_ret_eq_map, sublists_aux₁_bind]
  exact (append_nil _).symm

theorem sublists_append (l₁ l₂ : List α) :
    sublists (l₁ ++ l₂) = do
      let x ← sublists l₂
      (· ++ x) <$> sublists l₁ :=
  by
  simp only [← map, ← sublists, ← sublists_aux_cons_append, ← map_eq_map, ← bind_eq_bind, ← cons_bind, ← map_id', ←
      append_nil, ← cons_append, ← map_id' fun _ => rfl] <;>
    constructor <;> rfl

@[simp]
theorem sublists_concat (l : List α) (a : α) :
    sublists (l ++ [a]) = sublists l ++ map (fun x => x ++ [a]) (sublists l) := by
  rw [sublists_append, sublists_singleton, bind_eq_bind, cons_bind, cons_bind, nil_bind, map_eq_map, map_eq_map,
    map_id' append_nil, append_nil]

theorem sublists_reverse (l : List α) : sublists (reverse l) = map reverse (sublists' l) := by
  induction' l with hd tl ih <;> [rfl,
    simp only [← reverse_cons, ← sublists_append, ← sublists'_cons, ← map_append, ← ih, ← sublists_singleton, ←
      map_eq_map, ← bind_eq_bind, ← map_map, ← cons_bind, ← append_nil, ← nil_bind, ← (· ∘ ·)]]

theorem sublists_eq_sublists' (l : List α) : sublists l = map reverse (sublists' (reverse l)) := by
  rw [← sublists_reverse, reverse_reverse]

theorem sublists'_reverse (l : List α) : sublists' (reverse l) = map reverse (sublists l) := by
  simp only [← sublists_eq_sublists', ← map_map, ← map_id' reverse_reverse]

theorem sublists'_eq_sublists (l : List α) : sublists' l = map reverse (sublists (reverse l)) := by
  rw [← sublists'_reverse, reverse_reverse]

theorem sublists_aux_ne_nil : ∀ l : List α, [] ∉ sublistsAux l cons
  | [] => id
  | a :: l => by
    rw [sublists_aux_cons_cons]
    refine' not_mem_cons_of_ne_of_not_mem (cons_ne_nil _ _).symm _
    have := sublists_aux_ne_nil l
    revert this
    induction sublists_aux l cons <;> intro
    · rwa [foldr]
      
    simp only [← foldr, ← mem_cons_iff, ← false_orₓ, ← not_or_distrib]
    exact ⟨ne_of_not_mem_cons this, ih (not_mem_of_not_mem_cons this)⟩

@[simp]
theorem mem_sublists {s t : List α} : s ∈ sublists t ↔ s <+ t := by
  rw [← reverse_sublist_iff, ← mem_sublists', sublists'_reverse, mem_map_of_injective reverse_injective]

@[simp]
theorem length_sublists (l : List α) : length (sublists l) = 2 ^ length l := by
  simp only [← sublists_eq_sublists', ← length_map, ← length_sublists', ← length_reverse]

theorem map_ret_sublist_sublists (l : List α) : map List.ret l <+ sublists l :=
  (reverseRecOn l (nil_sublist _)) fun l a IH => by
    simp only [← map, ← map_append, ← sublists_concat] <;>
      exact
        ((append_sublist_append_left _).2 <|
              singleton_sublist.2 <|
                mem_map.2
                  ⟨[], mem_sublists.2 (nil_sublist _), by
                    rfl⟩).trans
          ((append_sublist_append_right _).2 IH)

/-! ### sublists_len -/


/-- Auxiliary function to construct the list of all sublists of a given length. Given an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns the list made of
of `f` applied to all sublists of `l` of length `n`, concatenated with `L`. -/
def sublistsLenAux {α β : Type _} : ℕ → List α → (List α → β) → List β → List β
  | 0, l, f, r => f [] :: r
  | n + 1, [], f, r => r
  | n + 1, a :: l, f, r => sublists_len_aux (n + 1) l f (sublists_len_aux n l (f ∘ List.cons a) r)

/-- The list of all sublists of a list `l` that are of length `n`. For instance, for
`l = [0, 1, 2, 3]` and `n = 2`, one gets
`[[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]`. -/
def sublistsLen {α : Type _} (n : ℕ) (l : List α) : List (List α) :=
  sublistsLenAux n l id []

theorem sublists_len_aux_append {α β γ : Type _} :
    ∀ (n : ℕ) (l : List α) (f : List α → β) (g : β → γ) (r : List β) (s : List γ),
      sublistsLenAux n l (g ∘ f) (r.map g ++ s) = (sublistsLenAux n l f r).map g ++ s
  | 0, l, f, g, r, s => rfl
  | n + 1, [], f, g, r, s => rfl
  | n + 1, a :: l, f, g, r, s => by
    unfold sublists_len_aux
    rw
      [show (g ∘ f) ∘ List.cons a = g ∘ f ∘ List.cons a by
        rfl,
      sublists_len_aux_append, sublists_len_aux_append]

theorem sublists_len_aux_eq {α β : Type _} (l : List α) (n) (f : List α → β) (r) :
    sublistsLenAux n l f r = (sublistsLen n l).map f ++ r := by
  rw [sublists_len, ← sublists_len_aux_append] <;> rfl

theorem sublists_len_aux_zero {α : Type _} (l : List α) (f : List α → β) (r) : sublistsLenAux 0 l f r = f [] :: r := by
  cases l <;> rfl

@[simp]
theorem sublists_len_zero {α : Type _} (l : List α) : sublistsLen 0 l = [[]] :=
  sublists_len_aux_zero _ _ _

@[simp]
theorem sublists_len_succ_nil {α : Type _} (n) : sublistsLen (n + 1) (@nil α) = [] :=
  rfl

@[simp]
theorem sublists_len_succ_cons {α : Type _} (n) (a : α) (l) :
    sublistsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons a) := by
  rw [sublists_len, sublists_len_aux, sublists_len_aux_eq, sublists_len_aux_eq, map_id, append_nil] <;> rfl

@[simp]
theorem length_sublists_len {α : Type _} : ∀ (n) (l : List α), length (sublistsLen n l) = Nat.choose (length l) n
  | 0, l => by
    simp
  | n + 1, [] => by
    simp
  | n + 1, a :: l => by
    simp [-add_commₓ, ← Nat.choose, *] <;> apply add_commₓ

theorem sublists_len_sublist_sublists' {α : Type _} : ∀ (n) (l : List α), sublistsLen n l <+ sublists' l
  | 0, l => singleton_sublist.2 (mem_sublists'.2 (nil_sublist _))
  | n + 1, [] => nil_sublist _
  | n + 1, a :: l => by
    rw [sublists_len_succ_cons, sublists'_cons]
    exact (sublists_len_sublist_sublists' _ _).append ((sublists_len_sublist_sublists' _ _).map _)

theorem sublists_len_sublist_of_sublist {α : Type _} (n) {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    sublistsLen n l₁ <+ sublistsLen n l₂ := by
  induction' n with n IHn generalizing l₁ l₂
  · simp
    
  induction' h with l₁ l₂ a s IH l₁ l₂ a s IH
  · rfl
    
  · refine' IH.trans _
    rw [sublists_len_succ_cons]
    apply sublist_append_left
    
  · simp [← sublists_len_succ_cons]
    exact IH.append ((IHn s).map _)
    

theorem length_of_sublists_len {α : Type _} : ∀ {n} {l l' : List α}, l' ∈ sublistsLen n l → length l' = n
  | 0, l, l', Or.inl rfl => rfl
  | n + 1, a :: l, l', h => by
    rw [sublists_len_succ_cons, mem_append, mem_map] at h
    rcases h with (h | ⟨l', h, rfl⟩)
    · exact length_of_sublists_len h
      
    · exact congr_arg (· + 1) (length_of_sublists_len h)
      

theorem mem_sublists_len_self {α : Type _} {l l' : List α} (h : l' <+ l) : l' ∈ sublistsLen (length l') l := by
  induction' h with l₁ l₂ a s IH l₁ l₂ a s IH
  · exact Or.inl rfl
    
  · cases' l₁ with b l₁
    · exact Or.inl rfl
      
    · rw [length, sublists_len_succ_cons]
      exact mem_append_left _ IH
      
    
  · rw [length, sublists_len_succ_cons]
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩)
    

@[simp]
theorem mem_sublists_len {α : Type _} {n} {l l' : List α} : l' ∈ sublistsLen n l ↔ l' <+ l ∧ length l' = n :=
  ⟨fun h => ⟨mem_sublists'.1 ((sublists_len_sublist_sublists' _ _).Subset h), length_of_sublists_len h⟩, fun ⟨h₁, h₂⟩ =>
    h₂ ▸ mem_sublists_len_self h₁⟩

end List

