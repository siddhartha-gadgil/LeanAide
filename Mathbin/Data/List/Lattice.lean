/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
Scott Morrison
-/
import Mathbin.Data.List.Count
import Mathbin.Data.List.Infix

/-!
# Lattice structure of lists

This files prove basic properties about `list.disjoint`, `list.union`, `list.inter` and
`list.bag_inter`, which are defined in core Lean and `data.list.defs`.

`l₁ ∪ l₂` is the list where all elements of `l₁` have been inserted in `l₂` in order. For example,
`[0, 0, 1, 2, 2, 3] ∪ [4, 3, 3, 0] = [1, 2, 4, 3, 3, 0]`

`l₁ ∩ l₂` is the list of elements of `l₁` in order which are in `l₂`. For example,
`[0, 0, 1, 2, 2, 3] ∪ [4, 3, 3, 0] = [0, 0, 3]`

`bag_inter l₁ l₂` is the list of elements that are in both `l₁` and `l₂`, counted with multiplicity
and in the order they appear in `l₁`. As opposed to `list.inter`, `list.bag_inter` copes well with
multiplicity. For example,
`bag_inter [0, 1, 2, 3, 2, 1, 0] [1, 0, 1, 4, 3] = [0, 1, 3, 1]`
-/


open Nat

namespace List

variable {α : Type _} {l l₁ l₂ : List α} {p : α → Prop} {a : α}

/-! ### `disjoint` -/


section Disjoint

theorem Disjoint.symm (d : Disjoint l₁ l₂) : Disjoint l₂ l₁ := fun a i₂ i₁ => d i₁ i₂

theorem disjoint_commₓ : Disjoint l₁ l₂ ↔ Disjoint l₂ l₁ :=
  ⟨Disjoint.symm, Disjoint.symm⟩

theorem disjoint_leftₓ : Disjoint l₁ l₂ ↔ ∀ ⦃a⦄, a ∈ l₁ → a ∉ l₂ :=
  Iff.rfl

theorem disjoint_rightₓ : Disjoint l₁ l₂ ↔ ∀ ⦃a⦄, a ∈ l₂ → a ∉ l₁ :=
  disjoint_comm

theorem disjoint_iff_neₓ : Disjoint l₁ l₂ ↔ ∀, ∀ a ∈ l₁, ∀, ∀, ∀ b ∈ l₂, ∀, a ≠ b := by
  simp only [← disjoint_left, ← imp_not_comm, ← forall_eq']

theorem disjoint_of_subset_leftₓ (ss : l₁ ⊆ l) (d : Disjoint l l₂) : Disjoint l₁ l₂ := fun x m => d (ss m)

theorem disjoint_of_subset_rightₓ (ss : l₂ ⊆ l) (d : Disjoint l₁ l) : Disjoint l₁ l₂ := fun x m m₁ => d m (ss m₁)

theorem disjoint_of_disjoint_cons_leftₓ {l₁ l₂} : Disjoint (a :: l₁) l₂ → Disjoint l₁ l₂ :=
  disjoint_of_subset_leftₓ (List.subset_consₓ _ _)

theorem disjoint_of_disjoint_cons_rightₓ {l₁ l₂} : Disjoint l₁ (a :: l₂) → Disjoint l₁ l₂ :=
  disjoint_of_subset_rightₓ (List.subset_consₓ _ _)

@[simp]
theorem disjoint_nil_leftₓ (l : List α) : Disjoint [] l := fun a => (not_mem_nilₓ a).elim

@[simp]
theorem disjoint_nil_rightₓ (l : List α) : Disjoint l [] := by
  rw [disjoint_comm]
  exact disjoint_nil_left _

@[simp]
theorem singleton_disjointₓ : Disjoint [a] l ↔ a ∉ l := by
  simp only [← Disjoint, ← mem_singleton, ← forall_eq]
  rfl

@[simp]
theorem disjoint_singletonₓ : Disjoint l [a] ↔ a ∉ l := by
  rw [disjoint_comm, singleton_disjoint]

@[simp]
theorem disjoint_append_leftₓ : Disjoint (l₁ ++ l₂) l ↔ Disjoint l₁ l ∧ Disjoint l₂ l := by
  simp only [← Disjoint, ← mem_append, ← or_imp_distrib, ← forall_and_distrib]

@[simp]
theorem disjoint_append_right : Disjoint l (l₁ ++ l₂) ↔ Disjoint l l₁ ∧ Disjoint l l₂ :=
  disjoint_commₓ.trans <| by
    simp only [← disjoint_comm, ← disjoint_append_left]

@[simp]
theorem disjoint_cons_leftₓ : Disjoint (a :: l₁) l₂ ↔ a ∉ l₂ ∧ Disjoint l₁ l₂ :=
  (@disjoint_append_leftₓ _ l₂ [a] l₁).trans <| by
    simp only [← singleton_disjoint]

@[simp]
theorem disjoint_cons_right : Disjoint l₁ (a :: l₂) ↔ a ∉ l₁ ∧ Disjoint l₁ l₂ :=
  disjoint_commₓ.trans <| by
    simp only [← disjoint_comm, ← disjoint_cons_left]

theorem disjoint_of_disjoint_append_left_leftₓ (d : Disjoint (l₁ ++ l₂) l) : Disjoint l₁ l :=
  (disjoint_append_leftₓ.1 d).1

theorem disjoint_of_disjoint_append_left_rightₓ (d : Disjoint (l₁ ++ l₂) l) : Disjoint l₂ l :=
  (disjoint_append_leftₓ.1 d).2

theorem disjoint_of_disjoint_append_right_left (d : Disjoint l (l₁ ++ l₂)) : Disjoint l l₁ :=
  (disjoint_append_right.1 d).1

theorem disjoint_of_disjoint_append_right_right (d : Disjoint l (l₁ ++ l₂)) : Disjoint l l₂ :=
  (disjoint_append_right.1 d).2

theorem disjoint_take_drop {m n : ℕ} (hl : l.Nodup) (h : m ≤ n) : Disjoint (l.take m) (l.drop n) := by
  induction l generalizing m n
  case list.nil m n =>
    simp
  case list.cons x xs xs_ih m n =>
    cases m <;>
      cases n <;>
        simp only [← disjoint_cons_left, ← mem_cons_iff, ← disjoint_cons_right, ← drop, ← true_orₓ, ← eq_self_iff_true,
          ← not_true, ← false_andₓ, ← disjoint_nil_left, ← take]
    · cases h
      
    cases' hl with _ _ h₀ h₁
    constructor
    · intro h
      exact h₀ _ (mem_of_mem_drop h) rfl
      
    solve_by_elim [← le_of_succ_le_succ]

end Disjoint

variable [DecidableEq α]

/-! ### `union` -/


section Union

@[simp]
theorem nil_union (l : List α) : [] ∪ l = l :=
  rfl

@[simp]
theorem cons_unionₓ (l₁ l₂ : List α) (a : α) : a :: l₁ ∪ l₂ = insert a (l₁ ∪ l₂) :=
  rfl

@[simp]
theorem mem_union : a ∈ l₁ ∪ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ := by
  induction l₁ <;>
    simp only [← nil_union, ← not_mem_nil, ← false_orₓ, ← cons_union, ← mem_insert_iff, ← mem_cons_iff, ← or_assoc, *]

theorem mem_union_left (h : a ∈ l₁) (l₂ : List α) : a ∈ l₁ ∪ l₂ :=
  mem_union.2 (Or.inl h)

theorem mem_union_right (l₁ : List α) (h : a ∈ l₂) : a ∈ l₁ ∪ l₂ :=
  mem_union.2 (Or.inr h)

theorem sublist_suffix_of_union : ∀ l₁ l₂ : List α, ∃ t, t <+ l₁ ∧ t ++ l₂ = l₁ ∪ l₂
  | [], l₂ =>
    ⟨[], by
      rfl, rfl⟩
  | a :: l₁, l₂ =>
    let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂
    if h : a ∈ l₁ ∪ l₂ then
      ⟨t, sublist_cons_of_sublist _ s, by
        simp only [← e, ← cons_union, ← insert_of_mem h]⟩
    else
      ⟨a :: t, s.cons_cons _, by
        simp only [← cons_append, ← cons_union, ← e, ← insert_of_not_mem h] <;> constructor <;> rfl⟩

theorem suffix_union_right (l₁ l₂ : List α) : l₂ <:+ l₁ ∪ l₂ :=
  (sublist_suffix_of_union l₁ l₂).imp fun a => And.right

theorem union_sublist_append (l₁ l₂ : List α) : l₁ ∪ l₂ <+ l₁ ++ l₂ :=
  let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂
  e ▸ (append_sublist_append_right _).2 s

theorem forall_mem_union : (∀, ∀ x ∈ l₁ ∪ l₂, ∀, p x) ↔ (∀, ∀ x ∈ l₁, ∀, p x) ∧ ∀, ∀ x ∈ l₂, ∀, p x := by
  simp only [← mem_union, ← or_imp_distrib, ← forall_and_distrib]

theorem forall_mem_of_forall_mem_union_left (h : ∀, ∀ x ∈ l₁ ∪ l₂, ∀, p x) : ∀, ∀ x ∈ l₁, ∀, p x :=
  (forall_mem_union.1 h).1

theorem forall_mem_of_forall_mem_union_right (h : ∀, ∀ x ∈ l₁ ∪ l₂, ∀, p x) : ∀, ∀ x ∈ l₂, ∀, p x :=
  (forall_mem_union.1 h).2

end Union

/-! ### `inter` -/


section Inter

@[simp]
theorem inter_nil (l : List α) : [] ∩ l = [] :=
  rfl

@[simp]
theorem inter_cons_of_mem (l₁ : List α) (h : a ∈ l₂) : (a :: l₁) ∩ l₂ = a :: l₁ ∩ l₂ :=
  if_pos h

@[simp]
theorem inter_cons_of_not_mem (l₁ : List α) (h : a ∉ l₂) : (a :: l₁) ∩ l₂ = l₁ ∩ l₂ :=
  if_neg h

theorem mem_of_mem_inter_left : a ∈ l₁ ∩ l₂ → a ∈ l₁ :=
  mem_of_mem_filter

theorem mem_of_mem_inter_right : a ∈ l₁ ∩ l₂ → a ∈ l₂ :=
  of_mem_filter

theorem mem_inter_of_mem_of_mem : a ∈ l₁ → a ∈ l₂ → a ∈ l₁ ∩ l₂ :=
  mem_filter_of_mem

@[simp]
theorem mem_inter : a ∈ l₁ ∩ l₂ ↔ a ∈ l₁ ∧ a ∈ l₂ :=
  mem_filter

theorem inter_subset_left (l₁ l₂ : List α) : l₁ ∩ l₂ ⊆ l₁ :=
  filter_subset _

theorem inter_subset_right (l₁ l₂ : List α) : l₁ ∩ l₂ ⊆ l₂ := fun a => mem_of_mem_inter_right

theorem subset_inter {l l₁ l₂ : List α} (h₁ : l ⊆ l₁) (h₂ : l ⊆ l₂) : l ⊆ l₁ ∩ l₂ := fun a h => mem_inter.2 ⟨h₁ h, h₂ h⟩

theorem inter_eq_nil_iff_disjoint : l₁ ∩ l₂ = [] ↔ Disjoint l₁ l₂ := by
  simp only [← eq_nil_iff_forall_not_mem, ← mem_inter, ← not_and]
  rfl

theorem forall_mem_inter_of_forall_left (h : ∀, ∀ x ∈ l₁, ∀, p x) (l₂ : List α) : ∀ x, x ∈ l₁ ∩ l₂ → p x :=
  Ball.imp_left (fun x => mem_of_mem_inter_left) h

theorem forall_mem_inter_of_forall_right (l₁ : List α) (h : ∀, ∀ x ∈ l₂, ∀, p x) : ∀ x, x ∈ l₁ ∩ l₂ → p x :=
  Ball.imp_left (fun x => mem_of_mem_inter_right) h

@[simp]
theorem inter_reverse {xs ys : List α} : xs.inter ys.reverse = xs.inter ys := by
  simp only [← List.interₓ, ← mem_reverse]

end Inter

/-! ### `bag_inter` -/


section BagInter

@[simp]
theorem nil_bag_inter (l : List α) : [].bagInter l = [] := by
  cases l <;> rfl

@[simp]
theorem bag_inter_nil (l : List α) : l.bagInter [] = [] := by
  cases l <;> rfl

@[simp]
theorem cons_bag_inter_of_pos (l₁ : List α) (h : a ∈ l₂) : (a :: l₁).bagInter l₂ = a :: l₁.bagInter (l₂.erase a) := by
  cases l₂ <;> exact if_pos h

@[simp]
theorem cons_bag_inter_of_neg (l₁ : List α) (h : a ∉ l₂) : (a :: l₁).bagInter l₂ = l₁.bagInter l₂ := by
  cases l₂
  · simp only [← bag_inter_nil]
    
  simp only [← erase_of_not_mem h, ← List.bagInterₓ, ← if_neg h]

@[simp]
theorem mem_bag_inter {a : α} : ∀ {l₁ l₂ : List α}, a ∈ l₁.bagInter l₂ ↔ a ∈ l₁ ∧ a ∈ l₂
  | [], l₂ => by
    simp only [← nil_bag_inter, ← not_mem_nil, ← false_andₓ]
  | b :: l₁, l₂ => by
    by_cases' b ∈ l₂
    · rw [cons_bag_inter_of_pos _ h, mem_cons_iff, mem_cons_iff, mem_bag_inter]
      by_cases' ba : a = b
      · simp only [← ba, ← h, ← eq_self_iff_true, ← true_orₓ, ← true_andₓ]
        
      · simp only [← mem_erase_of_ne ba, ← ba, ← false_orₓ]
        
      
    · rw [cons_bag_inter_of_neg _ h, mem_bag_inter, mem_cons_iff, or_and_distrib_right]
      symm
      apply or_iff_right_of_imp
      rintro ⟨rfl, h'⟩
      exact h.elim h'
      

@[simp]
theorem count_bag_inter {a : α} : ∀ {l₁ l₂ : List α}, count a (l₁.bagInter l₂) = min (count a l₁) (count a l₂)
  | [], l₂ => by
    simp
  | l₁, [] => by
    simp
  | h₁ :: l₁, h₂ :: l₂ => by
    simp only [← List.bagInterₓ, ← List.mem_cons_iff]
    by_cases' p₁ : h₂ = h₁ <;> by_cases' p₂ : h₁ = a
    · simp only [← p₁, ← p₂, ← count_bag_inter, ← min_succ_succ, ← erase_cons_head, ← if_true, ← mem_cons_iff, ←
        count_cons_self, ← true_orₓ, ← eq_self_iff_true]
      
    · simp only [← p₁, ← Ne.symm p₂, ← count_bag_inter, ← count_cons, ← erase_cons_head, ← if_true, ← mem_cons_iff, ←
        true_orₓ, ← eq_self_iff_true, ← if_false]
      
    · rw [p₂] at p₁
      by_cases' p₃ : a ∈ l₂
      · simp only [← p₁, ← Ne.symm p₁, ← p₂, ← p₃, ← erase_cons, ← count_bag_inter, ← Eq.symm (min_succ_succ _ _), ←
          succ_pred_eq_of_pos (count_pos.2 p₃), ← if_true, ← mem_cons_iff, ← false_orₓ, ← count_cons_self, ←
          eq_self_iff_true, ← if_false, ← Ne.def, ← not_false_iff, ← count_erase_self, ← List.count_cons_of_ne]
        
      · simp [← Ne.symm p₁, ← p₂, ← p₃]
        
      
    · by_cases' p₄ : h₁ ∈ l₂ <;>
        simp only [← Ne.symm p₁, ← Ne.symm p₂, ← p₄, ← count_bag_inter, ← if_true, ← if_false, ← mem_cons_iff, ←
          false_orₓ, ← eq_self_iff_true, ← Ne.def, ← not_false_iff, ← count_erase_of_ne, ← count_cons_of_ne]
      

theorem bag_inter_sublist_left : ∀ l₁ l₂ : List α, l₁.bagInter l₂ <+ l₁
  | [], l₂ => by
    simp [← nil_sublist]
  | b :: l₁, l₂ => by
    by_cases' b ∈ l₂ <;> simp [← h]
    · exact (bag_inter_sublist_left _ _).cons_cons _
      
    · apply sublist_cons_of_sublist
      apply bag_inter_sublist_left
      

theorem bag_inter_nil_iff_inter_nil : ∀ l₁ l₂ : List α, l₁.bagInter l₂ = [] ↔ l₁ ∩ l₂ = []
  | [], l₂ => by
    simp
  | b :: l₁, l₂ => by
    by_cases' h : b ∈ l₂ <;> simp [← h]
    exact bag_inter_nil_iff_inter_nil l₁ l₂

end BagInter

end List

