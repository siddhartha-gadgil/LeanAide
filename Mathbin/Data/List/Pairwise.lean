/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.List.Count
import Mathbin.Data.List.Lex
import Mathbin.Data.List.Sublists
import Mathbin.Data.Set.Pairwise

/-!
# Pairwise relations on a list

This file provides basic results about `list.pairwise` and `list.pw_filter` (definitions are in
`data.list.defs`).
`pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`pairwise (≠) l` means that all elements of `l` are distinct, and `pairwise (<) l` means that `l`
is strictly increasing.
`pw_filter r l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`pairwise r l'`.

## Tags

sorted, nodup
-/


open Nat Function

namespace List

variable {α β : Type _} {R S T : α → α → Prop} {a : α} {l : List α}

mk_iff_of_inductive_prop List.Pairwiseₓ List.pairwise_iff

/-! ### Pairwise -/


theorem rel_of_pairwise_cons (p : (a :: l).Pairwise R) : ∀ {a'}, a' ∈ l → R a a' :=
  (pairwise_cons.1 p).1

theorem Pairwiseₓ.of_cons (p : (a :: l).Pairwise R) : Pairwiseₓ R l :=
  (pairwise_cons.1 p).2

theorem Pairwiseₓ.tail : ∀ {l : List α} (p : Pairwiseₓ R l), Pairwiseₓ R l.tail
  | [], h => h
  | a :: l, h => h.of_cons

theorem Pairwiseₓ.drop : ∀ {l : List α} {n : ℕ}, List.Pairwiseₓ R l → List.Pairwiseₓ R (l.drop n)
  | _, 0, h => h
  | [], n + 1, h => List.Pairwiseₓ.nil
  | a :: l, n + 1, h => pairwise.drop (pairwise_cons.mp h).right

theorem Pairwiseₓ.imp_of_mem {S : α → α → Prop} {l : List α} (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b)
    (p : Pairwiseₓ R l) : Pairwiseₓ S l := by
  induction' p with a l r p IH generalizing H <;> constructor
  · exact Ball.imp_right (fun x h => H (mem_cons_self _ _) (mem_cons_of_mem _ h)) r
    
  · exact IH fun a b m m' => H (mem_cons_of_mem _ m) (mem_cons_of_mem _ m')
    

theorem Pairwiseₓ.imp (H : ∀ a b, R a b → S a b) : Pairwiseₓ R l → Pairwiseₓ S l :=
  Pairwiseₓ.imp_of_mem fun a b _ _ => H a b

theorem pairwise_and_iff : (l.Pairwise fun a b => R a b ∧ S a b) ↔ l.Pairwise R ∧ l.Pairwise S :=
  ⟨fun h => ⟨h.imp fun a b h => h.1, h.imp fun a b h => h.2⟩, fun ⟨hR, hS⟩ => by
    clear_
    induction' hR with a l R1 R2 IH <;> simp only [← pairwise.nil, ← pairwise_cons] at *
    exact ⟨fun b bl => ⟨R1 b bl, hS.1 b bl⟩, IH hS.2⟩⟩

theorem Pairwiseₓ.and (hR : l.Pairwise R) (hS : l.Pairwise S) : l.Pairwise fun a b => R a b ∧ S a b :=
  pairwise_and_iff.2 ⟨hR, hS⟩

theorem Pairwiseₓ.imp₂ (H : ∀ a b, R a b → S a b → T a b) (hR : l.Pairwise R) (hS : l.Pairwise S) : l.Pairwise T :=
  (hR.And hS).imp fun a b => And.ndrec (H a b)

theorem Pairwiseₓ.iff_of_mem {S : α → α → Prop} {l : List α} (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) :
    Pairwiseₓ R l ↔ Pairwiseₓ S l :=
  ⟨Pairwiseₓ.imp_of_mem fun a b m m' => (H m m').1, Pairwiseₓ.imp_of_mem fun a b m m' => (H m m').2⟩

theorem Pairwiseₓ.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} : Pairwiseₓ R l ↔ Pairwiseₓ S l :=
  Pairwiseₓ.iff_of_mem fun a b _ _ => H a b

theorem pairwise_of_forall {l : List α} (H : ∀ x y, R x y) : Pairwiseₓ R l := by
  induction l <;> [exact pairwise.nil, simp only [*, ← pairwise_cons, ← forall_2_true_iff, ← and_trueₓ]]

theorem Pairwiseₓ.and_mem {l : List α} : Pairwiseₓ R l ↔ Pairwiseₓ (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l :=
  Pairwiseₓ.iff_of_mem
    (by
      simp (config := { contextual := true })only [← true_andₓ, ← iff_selfₓ, ← forall_2_true_iff])

theorem Pairwiseₓ.imp_mem {l : List α} : Pairwiseₓ R l ↔ Pairwiseₓ (fun x y => x ∈ l → y ∈ l → R x y) l :=
  Pairwiseₓ.iff_of_mem
    (by
      simp (config := { contextual := true })only [← forall_prop_of_true, ← iff_selfₓ, ← forall_2_true_iff])

protected theorem Pairwiseₓ.sublist : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → Pairwiseₓ R l₂ → Pairwiseₓ R l₁
  | _, _, sublist.slnil, h => h
  | _, _, sublist.cons l₁ l₂ a s, pairwise.cons i h => h.Sublist s
  | _, _, sublist.cons2 l₁ l₂ a s, pairwise.cons i h => (h.Sublist s).cons (Ball.imp_left s.Subset i)

theorem Pairwiseₓ.forall_of_forall_of_flip (h₁ : ∀, ∀ x ∈ l, ∀, R x x) (h₂ : l.Pairwise R) (h₃ : l.Pairwise (flip R)) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y := by
  induction' l with a l ih
  · exact forall_mem_nil _
    
  rw [pairwise_cons] at h₂ h₃
  rintro x (rfl | hx) y (rfl | hy)
  · exact h₁ _ (l.mem_cons_self _)
    
  · exact h₂.1 _ hy
    
  · exact h₃.1 _ hx
    
  · exact ih (fun x hx => h₁ _ <| mem_cons_of_mem _ hx) h₂.2 h₃.2 hx hy
    

theorem Pairwiseₓ.forall_of_forall (H : Symmetric R) (H₁ : ∀, ∀ x ∈ l, ∀, R x x) (H₂ : l.Pairwise R) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
  H₂.forall_of_forall_of_flip H₁ <| by
    rwa [H.flip_eq]

theorem Pairwiseₓ.forall (hR : Symmetric R) (hl : l.Pairwise R) : ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b :=
  Pairwiseₓ.forall_of_forall (fun a b h hne => hR (h hne.symm)) (fun _ _ h => (h rfl).elim) (hl.imp fun _ _ h _ => h)

theorem Pairwiseₓ.set_pairwise (hl : Pairwiseₓ R l) (hr : Symmetric R) : { x | x ∈ l }.Pairwise R :=
  hl.forall hr

theorem pairwise_singleton (R) (a : α) : Pairwiseₓ R [a] := by
  simp only [← pairwise_cons, ← mem_singleton, ← forall_prop_of_false (not_mem_nil _), ← forall_true_iff, ←
    pairwise.nil, ← and_trueₓ]

theorem pairwise_pair {a b : α} : Pairwiseₓ R [a, b] ↔ R a b := by
  simp only [← pairwise_cons, ← mem_singleton, ← forall_eq, ← forall_prop_of_false (not_mem_nil _), ← forall_true_iff, ←
    pairwise.nil, ← and_trueₓ]

theorem pairwise_append {l₁ l₂ : List α} :
    Pairwiseₓ R (l₁ ++ l₂) ↔ Pairwiseₓ R l₁ ∧ Pairwiseₓ R l₂ ∧ ∀, ∀ x ∈ l₁, ∀, ∀, ∀ y ∈ l₂, ∀, R x y := by
  induction' l₁ with x l₁ IH <;>
    [simp only [← List.Pairwiseₓ.nil, ← forall_prop_of_false (not_mem_nil _), ← forall_true_iff, ← and_trueₓ, ←
      true_andₓ, ← nil_append],
    simp only [← cons_append, ← pairwise_cons, ← forall_mem_append, ← IH, ← forall_mem_cons, ← forall_and_distrib, ←
      and_assoc, ← And.left_comm]]

theorem pairwise_append_comm (s : Symmetric R) {l₁ l₂ : List α} : Pairwiseₓ R (l₁ ++ l₂) ↔ Pairwiseₓ R (l₂ ++ l₁) := by
  have : ∀ l₁ l₂ : List α, (∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y) → ∀ x : α, x ∈ l₂ → ∀ y : α, y ∈ l₁ → R x y :=
    fun l₁ l₂ a x xm y ym => s (a y ym x xm)
  simp only [← pairwise_append, ← And.left_comm] <;> rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]

theorem pairwise_middle (s : Symmetric R) {a : α} {l₁ l₂ : List α} :
    Pairwiseₓ R (l₁ ++ a :: l₂) ↔ Pairwiseₓ R (a :: (l₁ ++ l₂)) :=
  show Pairwiseₓ R (l₁ ++ ([a] ++ l₂)) ↔ Pairwiseₓ R ([a] ++ l₁ ++ l₂) by
    rw [← append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁), pairwise_append_comm s] <;>
      simp only [← mem_append, ← or_comm]

theorem pairwise_map (f : β → α) : ∀ {l : List β}, Pairwiseₓ R (map f l) ↔ Pairwiseₓ (fun a b : β => R (f a) (f b)) l
  | [] => by
    simp only [← map, ← pairwise.nil]
  | b :: l => by
    have : (∀ a b', b' ∈ l → f b' = a → R (f b) a) ↔ ∀ b' : β, b' ∈ l → R (f b) (f b') :=
      forall_swap.trans <|
        forall_congrₓ fun a =>
          forall_swap.trans <| by
            simp only [← forall_eq']
    simp only [← map, ← pairwise_cons, ← mem_map, ← exists_imp_distrib, ← and_imp, ← this, ← pairwise_map]

theorem Pairwiseₓ.of_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    (p : Pairwiseₓ S (map f l)) : Pairwiseₓ R l :=
  ((pairwise_map f).1 p).imp H

theorem Pairwiseₓ.map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b)) (p : Pairwiseₓ R l) :
    Pairwiseₓ S (map f l) :=
  (pairwise_map f).2 <| p.imp H

theorem pairwise_filter_map (f : β → Option α) {l : List β} :
    Pairwiseₓ R (filterMap f l) ↔ Pairwiseₓ (fun a a' : β => ∀, ∀ b ∈ f a, ∀, ∀ b' ∈ f a', ∀, R b b') l := by
  let S (a a' : β) := ∀, ∀ b ∈ f a, ∀, ∀ b' ∈ f a', ∀, R b b'
  simp only [← Option.mem_def]
  induction' l with a l IH
  · simp only [← filter_map, ← pairwise.nil]
    
  cases' e : f a with b
  · rw [filter_map_cons_none _ _ e, IH, pairwise_cons]
    simp only [← e, ← forall_prop_of_false not_false, ← forall_3_true_iff, ← true_andₓ]
    
  rw [filter_map_cons_some _ _ _ e]
  simp only [← pairwise_cons, ← mem_filter_map, ← exists_imp_distrib, ← and_imp, ← IH, ← e, ← forall_eq']
  show
    (∀ (a' : α) (x : β), x ∈ l → f x = some a' → R b a') ∧ Pairwise S l ↔
      (∀ a' : β, a' ∈ l → ∀ b' : α, f a' = some b' → R b b') ∧ Pairwise S l
  exact and_congr ⟨fun h b mb a ma => h a b mb ma, fun h a b mb ma => h b mb a ma⟩ Iff.rfl

theorem Pairwiseₓ.filter_map {S : β → β → Prop} (f : α → Option β)
    (H : ∀ a a' : α, R a a' → ∀, ∀ b ∈ f a, ∀, ∀ b' ∈ f a', ∀, S b b') {l : List α} (p : Pairwiseₓ R l) :
    Pairwiseₓ S (filterMap f l) :=
  (pairwise_filter_map _).2 <| p.imp H

theorem pairwise_filter (p : α → Prop) [DecidablePred p] {l : List α} :
    Pairwiseₓ R (filterₓ p l) ↔ Pairwiseₓ (fun x y => p x → p y → R x y) l := by
  rw [← filter_map_eq_filter, pairwise_filter_map]
  apply pairwise.iff
  intros
  simp only [← Option.mem_def, ← Option.guard_eq_some, ← and_imp, ← forall_eq']

theorem Pairwiseₓ.filter (p : α → Prop) [DecidablePred p] : Pairwiseₓ R l → Pairwiseₓ R (filterₓ p l) :=
  Pairwiseₓ.sublist (filter_sublist _)

theorem pairwise_pmap {p : β → Prop} {f : ∀ b, p b → α} {l : List β} (h : ∀, ∀ x ∈ l, ∀, p x) :
    Pairwiseₓ R (l.pmap f h) ↔ Pairwiseₓ (fun b₁ b₂ => ∀ (h₁ : p b₁) (h₂ : p b₂), R (f b₁ h₁) (f b₂ h₂)) l := by
  induction' l with a l ihl
  · simp
    
  obtain ⟨ha, hl⟩ : p a ∧ ∀ b, b ∈ l → p b := by
    simpa using h
  simp only [← ihl hl, ← pairwise_cons, ← bex_imp_distrib, ← pmap, ← And.congr_left_iff, ← mem_pmap]
  refine' fun _ => ⟨fun H b hb hpa hpb => H _ _ hb rfl, _⟩
  rintro H _ b hb rfl
  exact H b hb _ _

theorem Pairwiseₓ.pmap {l : List α} (hl : Pairwiseₓ R l) {p : α → Prop} {f : ∀ a, p a → β} (h : ∀, ∀ x ∈ l, ∀, p x)
    {S : β → β → Prop} (hS : ∀ ⦃x⦄ (hx : p x) ⦃y⦄ (hy : p y), R x y → S (f x hx) (f y hy)) : Pairwiseₓ S (l.pmap f h) :=
  by
  refine' (pairwise_pmap h).2 (pairwise.imp_of_mem _ hl)
  intros
  apply hS
  assumption

theorem pairwise_join {L : List (List α)} :
    Pairwiseₓ R (join L) ↔
      (∀, ∀ l ∈ L, ∀, Pairwiseₓ R l) ∧ Pairwiseₓ (fun l₁ l₂ => ∀, ∀ x ∈ l₁, ∀, ∀ y ∈ l₂, ∀, R x y) L :=
  by
  induction' L with l L IH
  · simp only [← join, ← pairwise.nil, ← forall_prop_of_false (not_mem_nil _), ← forall_const, ← and_selfₓ]
    
  have :
    (∀ x : α, x ∈ l → ∀ (y : α) (x_1 : List α), x_1 ∈ L → y ∈ x_1 → R x y) ↔
      ∀ a' : List α, a' ∈ L → ∀ x : α, x ∈ l → ∀ y : α, y ∈ a' → R x y :=
    ⟨fun h a b c d e => h c d e a b, fun h c d e a b => h a b c d e⟩
  simp only [← join, ← pairwise_append, ← IH, ← mem_join, ← exists_imp_distrib, ← and_imp, ← this, ← forall_mem_cons, ←
    pairwise_cons]
  simp only [← and_assoc, ← and_comm, ← And.left_comm]

theorem pairwise_bind {R : β → β → Prop} {l : List α} {f : α → List β} :
    List.Pairwiseₓ R (l.bind f) ↔
      (∀, ∀ a ∈ l, ∀, Pairwiseₓ R (f a)) ∧ Pairwiseₓ (fun a₁ a₂ => ∀, ∀ x ∈ f a₁, ∀, ∀ y ∈ f a₂, ∀, R x y) l :=
  by
  simp [← List.bind, ← List.pairwise_join, ← List.mem_mapₓ, ← List.pairwise_map]

@[simp]
theorem pairwise_reverse : ∀ {R} {l : List α}, Pairwiseₓ R (reverse l) ↔ Pairwiseₓ (fun x y => R y x) l :=
  suffices ∀ {R l}, @Pairwiseₓ α R l → Pairwiseₓ (fun x y => R y x) (reverse l) from fun R l =>
    ⟨fun p => reverse_reverse l ▸ this p, this⟩
  fun R l p => by
  induction' p with a l h p IH <;> [apply pairwise.nil,
    simpa only [← reverse_cons, ← pairwise_append, ← IH, ← pairwise_cons, ← forall_prop_of_false (not_mem_nil _), ←
      forall_true_iff, ← pairwise.nil, ← mem_reverse, ← mem_singleton, ← forall_eq, ← true_andₓ] using h]

theorem pairwise_of_reflexive_on_dupl_of_forall_ne [DecidableEq α] {l : List α} {r : α → α → Prop}
    (hr : ∀ a, 1 < count a l → r a a) (h : ∀, ∀ a ∈ l, ∀, ∀ b ∈ l, ∀, a ≠ b → r a b) : l.Pairwise r := by
  induction' l with hd tl IH
  · simp
    
  · rw [List.pairwise_cons]
    constructor
    · intro x hx
      by_cases' H : hd = x
      · rw [H]
        refine' hr _ _
        simpa [← count_cons, ← H, ← Nat.succ_lt_succ_iff, ← count_pos] using hx
        
      · exact h hd (mem_cons_self _ _) x (mem_cons_of_mem _ hx) H
        
      
    · refine' IH _ _
      · intro x hx
        refine' hr _ _
        rw [count_cons]
        split_ifs
        · exact hx.trans (Nat.lt_succ_selfₓ _)
          
        · exact hx
          
        
      · intro x hx y hy
        exact h x (mem_cons_of_mem _ hx) y (mem_cons_of_mem _ hy)
        
      
    

theorem pairwise_of_forall_mem_list {l : List α} {r : α → α → Prop} (h : ∀, ∀ a ∈ l, ∀, ∀ b ∈ l, ∀, r a b) :
    l.Pairwise r := by
  classical
  refine' pairwise_of_reflexive_on_dupl_of_forall_ne (fun a ha' => _) fun a ha b hb _ => h a ha b hb
  have ha := List.one_le_count_iff_mem.1 ha'.le
  exact h a ha a ha

theorem pairwise_of_reflexive_of_forall_ne {l : List α} {r : α → α → Prop} (hr : Reflexive r)
    (h : ∀, ∀ a ∈ l, ∀, ∀ b ∈ l, ∀, a ≠ b → r a b) : l.Pairwise r := by
  classical
  exact pairwise_of_reflexive_on_dupl_of_forall_ne (fun _ _ => hr _) h

theorem pairwise_iff_nth_le {R} :
    ∀ {l : List α},
      Pairwiseₓ R l ↔ ∀ (i j) (h₁ : j < length l) (h₂ : i < j), R (nthLe l i (lt_transₓ h₂ h₁)) (nthLe l j h₁)
  | [] => by
    simp only [← pairwise.nil, ← true_iffₓ] <;> exact fun i j h => (Nat.not_lt_zeroₓ j).elim h
  | a :: l => by
    rw [pairwise_cons, pairwise_iff_nth_le]
    refine' ⟨fun H i j h₁ h₂ => _, fun H => ⟨fun a' m => _, fun i j h₁ h₂ => H _ _ (succ_lt_succ h₁) (succ_lt_succ h₂)⟩⟩
    · cases' j with j
      · exact (Nat.not_lt_zeroₓ _).elim h₂
        
      cases' i with i
      · exact H.1 _ (nth_le_mem l _ _)
        
      · exact H.2 _ _ (lt_of_succ_lt_succ h₁) (lt_of_succ_lt_succ h₂)
        
      
    · rcases nth_le_of_mem m with ⟨n, h, rfl⟩
      exact H _ _ (succ_lt_succ h) (succ_pos _)
      

theorem Pairwiseₓ.sublists' {R} : ∀ {l : List α}, Pairwiseₓ R l → Pairwiseₓ (Lex (swap R)) (sublists' l)
  | _, pairwise.nil => pairwise_singleton _ _
  | _, @pairwise.cons _ _ a l H₁ H₂ => by
    simp only [← sublists'_cons, ← pairwise_append, ← pairwise_map, ← mem_sublists', ← mem_map, ← exists_imp_distrib, ←
      and_imp]
    refine' ⟨H₂.sublists', H₂.sublists'.imp fun l₁ l₂ => lex.cons, _⟩
    rintro l₁ sl₁ x l₂ sl₂ rfl
    cases' l₁ with b l₁
    · constructor
      
    exact lex.rel (H₁ _ <| sl₁.subset <| mem_cons_self _ _)

theorem pairwise_sublists {R} {l : List α} (H : Pairwiseₓ R l) :
    Pairwiseₓ (fun l₁ l₂ => Lex R (reverse l₁) (reverse l₂)) (sublists l) := by
  have := (pairwise_reverse.2 H).sublists'
  rwa [sublists'_reverse, pairwise_map] at this

theorem pairwise_repeat {α : Type _} {r : α → α → Prop} {x : α} (hx : r x x) : ∀ n : ℕ, Pairwiseₓ r (repeat x n)
  | 0 => by
    simp
  | n + 1 => by
    simp [← hx, ← mem_repeat, ← pairwise_repeat n]

/-! ### Pairwise filtering -/


variable [DecidableRel R]

@[simp]
theorem pw_filter_nil : pwFilterₓ R [] = [] :=
  rfl

@[simp]
theorem pw_filter_cons_of_pos {a : α} {l : List α} (h : ∀, ∀ b ∈ pwFilterₓ R l, ∀, R a b) :
    pwFilterₓ R (a :: l) = a :: pwFilterₓ R l :=
  if_pos h

@[simp]
theorem pw_filter_cons_of_neg {a : α} {l : List α} (h : ¬∀, ∀ b ∈ pwFilterₓ R l, ∀, R a b) :
    pwFilterₓ R (a :: l) = pwFilterₓ R l :=
  if_neg h

theorem pw_filter_map (f : β → α) : ∀ l : List β, pwFilterₓ R (map f l) = map f (pwFilterₓ (fun x y => R (f x) (f y)) l)
  | [] => rfl
  | x :: xs =>
    if h : ∀, ∀ b ∈ pwFilterₓ R (map f xs), ∀, R (f x) b then by
      have h' : ∀ b : β, b ∈ pwFilterₓ (fun x y : β => R (f x) (f y)) xs → R (f x) (f b) := fun b hb =>
        h _
          (by
            rw [pw_filter_map] <;> apply mem_map_of_mem _ hb)
      rw [map, pw_filter_cons_of_pos h, pw_filter_cons_of_pos h', pw_filter_map, map]
    else by
      have h' : ¬∀ b : β, b ∈ pwFilterₓ (fun x y : β => R (f x) (f y)) xs → R (f x) (f b) := fun hh =>
        h fun a ha => by
          rw [pw_filter_map, mem_map] at ha
          rcases ha with ⟨b, hb₀, hb₁⟩
          subst a
          exact hh _ hb₀
      rw [map, pw_filter_cons_of_neg h, pw_filter_cons_of_neg h', pw_filter_map]

theorem pw_filter_sublist : ∀ l : List α, pwFilterₓ R l <+ l
  | [] => nil_sublist _
  | x :: l => by
    by_cases' ∀, ∀ y ∈ pw_filter R l, ∀, R x y
    · rw [pw_filter_cons_of_pos h]
      exact (pw_filter_sublist l).cons_cons _
      
    · rw [pw_filter_cons_of_neg h]
      exact sublist_cons_of_sublist _ (pw_filter_sublist l)
      

theorem pw_filter_subset (l : List α) : pwFilterₓ R l ⊆ l :=
  (pw_filter_sublist _).Subset

theorem pairwise_pw_filter : ∀ l : List α, Pairwiseₓ R (pwFilterₓ R l)
  | [] => Pairwiseₓ.nil
  | x :: l => by
    by_cases' ∀, ∀ y ∈ pw_filter R l, ∀, R x y
    · rw [pw_filter_cons_of_pos h]
      exact pairwise_cons.2 ⟨h, pairwise_pw_filter l⟩
      
    · rw [pw_filter_cons_of_neg h]
      exact pairwise_pw_filter l
      

theorem pw_filter_eq_self {l : List α} : pwFilterₓ R l = l ↔ Pairwiseₓ R l :=
  ⟨fun e => e ▸ pairwise_pw_filter l, fun p => by
    induction' l with x l IH
    · rfl
      
    cases' pairwise_cons.1 p with al p
    rw [pw_filter_cons_of_pos (Ball.imp_left (pw_filter_subset l) al), IH p]⟩

alias pw_filter_eq_self ↔ _ pairwise.pw_filter

attribute [protected] pairwise.pw_filter

@[simp]
theorem pw_filter_idempotent : pwFilterₓ R (pwFilterₓ R l) = pwFilterₓ R l :=
  (pairwise_pw_filter l).pwFilter

theorem forall_mem_pw_filter (neg_trans : ∀ {x y z}, R x z → R x y ∨ R y z) (a : α) (l : List α) :
    (∀, ∀ b ∈ pwFilterₓ R l, ∀, R a b) ↔ ∀, ∀ b ∈ l, ∀, R a b :=
  ⟨by
    induction' l with x l IH
    · exact fun _ _ => False.elim
      
    simp only [← forall_mem_cons]
    by_cases' ∀, ∀ y ∈ pw_filter R l, ∀, R x y <;> dsimp'  at h
    · simp only [← pw_filter_cons_of_pos h, ← forall_mem_cons, ← and_imp]
      exact fun r H => ⟨r, IH H⟩
      
    · rw [pw_filter_cons_of_neg h]
      refine' fun H => ⟨_, IH H⟩
      cases' e : find (fun y => ¬R x y) (pw_filter R l) with k
      · refine' h.elim (Ball.imp_right _ (find_eq_none.1 e))
        exact fun y _ => not_not.1
        
      · have := find_some e
        exact (neg_trans (H k (find_mem e))).resolve_right this
        
      ,
    Ball.imp_left (pw_filter_subset l)⟩

end List

