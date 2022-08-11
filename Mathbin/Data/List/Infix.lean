/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.List.Basic

/-!
# Prefixes, subfixes, infixes

This file proves properties about
* `list.prefix`: `l₁` is a prefix of `l₂` if `l₂` starts with `l₁`.
* `list.subfix`: `l₁` is a subfix of `l₂` if `l₂` ends with `l₁`.
* `list.infix`: `l₁` is an infix of `l₂` if `l₁` is a prefix of some subfix of `l₂`.
* `list.inits`: The list of prefixes of a list.
* `list.tails`: The list of prefixes of a list.
* `insert` on lists

All those (except `insert`) are defined in `data.list.defs`.

## Notation

`l₁ <+: l₂`: `l₁` is a prefix of `l₂`.
`l₁ <:+ l₂`: `l₁` is a subfix of `l₂`.
`l₁ <:+: l₂`: `l₁` is an infix of `l₂`.
-/


open Nat

variable {α β : Type _}

namespace List

variable {l l₁ l₂ l₃ : List α} {a b : α} {m n : ℕ}

/-! ### prefix, suffix, infix -/


section Fix

@[simp]
theorem prefix_append (l₁ l₂ : List α) : l₁ <+: l₁ ++ l₂ :=
  ⟨l₂, rfl⟩

@[simp]
theorem suffix_append (l₁ l₂ : List α) : l₂ <:+ l₁ ++ l₂ :=
  ⟨l₁, rfl⟩

theorem infix_append (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ l₂ ++ l₃ :=
  ⟨l₁, l₃, rfl⟩

@[simp]
theorem infix_append' (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← List.append_assoc] <;> apply infix_append

theorem IsPrefix.is_infix : l₁ <+: l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨[], t, h⟩

theorem IsSuffix.is_infix : l₁ <:+ l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ =>
  ⟨t, [], by
    rw [h, append_nil]⟩

theorem nil_prefix (l : List α) : [] <+: l :=
  ⟨l, rfl⟩

theorem nil_suffix (l : List α) : [] <:+ l :=
  ⟨l, append_nil _⟩

theorem nil_infix (l : List α) : [] <:+: l :=
  (nil_prefix _).IsInfix

@[refl]
theorem prefix_refl (l : List α) : l <+: l :=
  ⟨[], append_nil _⟩

@[refl]
theorem suffix_refl (l : List α) : l <:+ l :=
  ⟨[], rfl⟩

@[refl]
theorem infix_refl (l : List α) : l <:+: l :=
  (prefix_refl l).IsInfix

theorem prefix_rfl : l <+: l :=
  prefix_refl _

theorem suffix_rfl : l <:+ l :=
  suffix_refl _

theorem infix_rfl : l <:+: l :=
  infix_refl _

@[simp]
theorem suffix_cons (a : α) : ∀ l, l <:+ a :: l :=
  suffix_append [a]

theorem prefix_concat (a : α) (l) : l <+: concat l a := by
  simp

theorem infix_cons : l₁ <:+: l₂ → l₁ <:+: a :: l₂ := fun ⟨L₁, L₂, h⟩ => ⟨a :: L₁, L₂, h ▸ rfl⟩

theorem infix_concat : l₁ <:+: l₂ → l₁ <:+: concat l₂ a := fun ⟨L₁, L₂, h⟩ =>
  ⟨L₁, concat L₂ a, by
    simp_rw [← h, concat_eq_append, append_assoc]⟩

@[trans]
theorem IsPrefix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
  | l, _, _, ⟨r₁, rfl⟩, ⟨r₂, rfl⟩ => ⟨r₁ ++ r₂, (append_assoc _ _ _).symm⟩

@[trans]
theorem IsSuffix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
  | l, _, _, ⟨l₁, rfl⟩, ⟨l₂, rfl⟩ => ⟨l₂ ++ l₁, append_assoc _ _ _⟩

@[trans]
theorem IsInfix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
  | l, _, _, ⟨l₁, r₁, rfl⟩, ⟨l₂, r₂, rfl⟩ =>
    ⟨l₂ ++ l₁, r₁ ++ r₂, by
      simp only [← append_assoc]⟩

protected theorem IsInfix.sublist : l₁ <:+: l₂ → l₁ <+ l₂ := fun ⟨s, t, h⟩ => by
  rw [← h]
  exact (sublist_append_right _ _).trans (sublist_append_left _ _)

protected theorem IsInfix.subset (hl : l₁ <:+: l₂) : l₁ ⊆ l₂ :=
  hl.Sublist.Subset

protected theorem IsPrefix.sublist (h : l₁ <+: l₂) : l₁ <+ l₂ :=
  h.IsInfix.Sublist

protected theorem IsPrefix.subset (hl : l₁ <+: l₂) : l₁ ⊆ l₂ :=
  hl.Sublist.Subset

protected theorem IsSuffix.sublist (h : l₁ <:+ l₂) : l₁ <+ l₂ :=
  h.IsInfix.Sublist

protected theorem IsSuffix.subset (hl : l₁ <:+ l₂) : l₁ ⊆ l₂ :=
  hl.Sublist.Subset

@[simp]
theorem reverse_suffix : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ :=
  ⟨fun ⟨r, e⟩ =>
    ⟨reverse r, by
      rw [← reverse_reverse l₁, ← reverse_append, e, reverse_reverse]⟩,
    fun ⟨r, e⟩ =>
    ⟨reverse r, by
      rw [← reverse_append, e]⟩⟩

@[simp]
theorem reverse_prefix : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ := by
  rw [← reverse_suffix] <;> simp only [← reverse_reverse]

@[simp]
theorem reverse_infix : reverse l₁ <:+: reverse l₂ ↔ l₁ <:+: l₂ :=
  ⟨fun ⟨s, t, e⟩ =>
    ⟨reverse t, reverse s, by
      rw [← reverse_reverse l₁, append_assoc, ← reverse_append, ← reverse_append, e, reverse_reverse]⟩,
    fun ⟨s, t, e⟩ =>
    ⟨reverse t, reverse s, by
      rw [append_assoc, ← reverse_append, ← reverse_append, e]⟩⟩

alias reverse_prefix ↔ _ is_suffix.reverse

alias reverse_suffix ↔ _ is_prefix.reverse

alias reverse_infix ↔ _ is_infix.reverse

theorem IsInfix.length_le (h : l₁ <:+: l₂) : l₁.length ≤ l₂.length :=
  length_le_of_sublistₓ h.Sublist

theorem IsPrefix.length_le (h : l₁ <+: l₂) : l₁.length ≤ l₂.length :=
  length_le_of_sublistₓ h.Sublist

theorem IsSuffix.length_le (h : l₁ <:+ l₂) : l₁.length ≤ l₂.length :=
  length_le_of_sublistₓ h.Sublist

theorem eq_nil_of_infix_nil (h : l <:+: []) : l = [] :=
  eq_nil_of_sublist_nil h.Sublist

@[simp]
theorem infix_nil_iff : l <:+: [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_sublist_nil h.Sublist, fun h => h ▸ infix_rfl⟩

alias infix_nil_iff ↔ eq_nil_of_infix_nil _

@[simp]
theorem prefix_nil_iff : l <+: [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_infix_nil h.IsInfix, fun h => h ▸ prefix_rfl⟩

@[simp]
theorem suffix_nil_iff : l <:+ [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_infix_nil h.IsInfix, fun h => h ▸ suffix_rfl⟩

alias prefix_nil_iff ↔ eq_nil_of_prefix_nil _

alias suffix_nil_iff ↔ eq_nil_of_suffix_nil _

theorem infix_iff_prefix_suffix (l₁ l₂ : List α) : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
  ⟨fun ⟨s, t, e⟩ =>
    ⟨l₁ ++ t, ⟨_, rfl⟩, by
      rw [← e, append_assoc] <;> exact ⟨_, rfl⟩⟩,
    fun ⟨_, ⟨t, rfl⟩, s, e⟩ =>
    ⟨s, t, by
      rw [append_assoc] <;> exact e⟩⟩

theorem eq_of_infix_of_length_eq (h : l₁ <:+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  eq_of_sublist_of_length_eq h.Sublist

theorem eq_of_prefix_of_length_eq (h : l₁ <+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  eq_of_sublist_of_length_eq h.Sublist

theorem eq_of_suffix_of_length_eq (h : l₁ <:+ l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  eq_of_sublist_of_length_eq h.Sublist

theorem prefix_of_prefix_length_le : ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₃ → l₂ <+: l₃ → length l₁ ≤ length l₂ → l₁ <+: l₂
  | [], l₂, l₃, h₁, h₂, _ => nil_prefix _
  | a :: l₁, b :: l₂, _, ⟨r₁, rfl⟩, ⟨r₂, e⟩, ll => by
    injection e with _ e'
    subst b
    rcases prefix_of_prefix_length_le ⟨_, rfl⟩ ⟨_, e'⟩ (le_of_succ_le_succ ll) with ⟨r₃, rfl⟩
    exact ⟨r₃, rfl⟩

theorem prefix_or_prefix_of_prefix (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁ :=
  (le_totalₓ (length l₁) (length l₂)).imp (prefix_of_prefix_length_le h₁ h₂) (prefix_of_prefix_length_le h₂ h₁)

theorem suffix_of_suffix_length_le (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) (ll : length l₁ ≤ length l₂) : l₁ <:+ l₂ :=
  reverse_prefix.1 <|
    prefix_of_prefix_length_le (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)
      (by
        simp [← ll])

theorem suffix_or_suffix_of_suffix (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) : l₁ <:+ l₂ ∨ l₂ <:+ l₁ :=
  (prefix_or_prefix_of_prefix (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)).imp reverse_prefix.1 reverse_prefix.1

theorem suffix_cons_iff : l₁ <:+ a :: l₂ ↔ l₁ = a :: l₂ ∨ l₁ <:+ l₂ := by
  constructor
  · rintro ⟨⟨hd, tl⟩, hl₃⟩
    · exact Or.inl hl₃
      
    · simp only [← cons_append] at hl₃
      exact Or.inr ⟨_, hl₃.2⟩
      
    
  · rintro (rfl | hl₁)
    · exact (a :: l₂).suffix_refl
      
    · exact hl₁.trans (l₂.suffix_cons _)
      
    

theorem infix_cons_iff : l₁ <:+: a :: l₂ ↔ l₁ <+: a :: l₂ ∨ l₁ <:+: l₂ := by
  constructor
  · rintro ⟨⟨hd, tl⟩, t, hl₃⟩
    · exact Or.inl ⟨t, hl₃⟩
      
    · simp only [← cons_append] at hl₃
      exact Or.inr ⟨_, t, hl₃.2⟩
      
    
  · rintro (h | hl₁)
    · exact h.is_infix
      
    · exact infix_cons hl₁
      
    

theorem infix_of_mem_join : ∀ {L : List (List α)}, l ∈ L → l <:+: join L
  | _ :: L, Or.inl rfl => infix_append [] _ _
  | l' :: L, Or.inr h => IsInfix.trans (infix_of_mem_join h) <| (suffix_append _ _).IsInfix

theorem prefix_append_right_inj (l) : l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂ :=
  exists_congr fun r => by
    rw [append_assoc, append_right_inj]

theorem prefix_cons_inj (a) : a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ :=
  prefix_append_right_inj [a]

theorem take_prefix (n) (l : List α) : takeₓ n l <+: l :=
  ⟨_, take_append_dropₓ _ _⟩

theorem drop_suffix (n) (l : List α) : dropₓ n l <:+ l :=
  ⟨_, take_append_dropₓ _ _⟩

theorem take_sublist (n) (l : List α) : takeₓ n l <+ l :=
  (take_prefix n l).Sublist

theorem drop_sublist (n) (l : List α) : dropₓ n l <+ l :=
  (drop_suffix n l).Sublist

theorem take_subset (n) (l : List α) : takeₓ n l ⊆ l :=
  (take_sublist n l).Subset

theorem drop_subset (n) (l : List α) : dropₓ n l ⊆ l :=
  (drop_sublist n l).Subset

theorem mem_of_mem_take (h : a ∈ l.take n) : a ∈ l :=
  take_subset n l h

theorem mem_of_mem_drop (h : a ∈ l.drop n) : a ∈ l :=
  drop_subset n l h

theorem init_prefix : ∀ l : List α, l.init <+: l
  | [] =>
    ⟨nil, by
      rw [init, List.append_nil]⟩
  | a :: l => ⟨_, init_append_last (cons_ne_nil a l)⟩

theorem tail_suffix (l : List α) : tail l <:+ l := by
  rw [← drop_one] <;> apply drop_suffix

theorem init_sublist (l : List α) : l.init <+ l :=
  (init_prefix l).Sublist

theorem tail_sublist (l : List α) : l.tail <+ l :=
  (tail_suffix l).Sublist

theorem init_subset (l : List α) : l.init ⊆ l :=
  (init_sublist l).Subset

theorem tail_subset (l : List α) : tail l ⊆ l :=
  (tail_sublist l).Subset

theorem mem_of_mem_init (h : a ∈ l.init) : a ∈ l :=
  init_subset l h

theorem mem_of_mem_tail (h : a ∈ l.tail) : a ∈ l :=
  tail_subset l h

theorem prefix_iff_eq_append : l₁ <+: l₂ ↔ l₁ ++ dropₓ (length l₁) l₂ = l₂ :=
  ⟨by
    rintro ⟨r, rfl⟩ <;> rw [drop_left], fun e => ⟨_, e⟩⟩

theorem suffix_iff_eq_append : l₁ <:+ l₂ ↔ takeₓ (length l₂ - length l₁) l₂ ++ l₁ = l₂ :=
  ⟨by
    rintro ⟨r, rfl⟩ <;> simp only [← length_append, ← add_tsub_cancel_right, ← take_left], fun e => ⟨_, e⟩⟩

theorem prefix_iff_eq_take : l₁ <+: l₂ ↔ l₁ = takeₓ (length l₁) l₂ :=
  ⟨fun h => append_right_cancel <| (prefix_iff_eq_append.1 h).trans (take_append_dropₓ _ _).symm, fun e =>
    e.symm ▸ take_prefix _ _⟩

theorem suffix_iff_eq_drop : l₁ <:+ l₂ ↔ l₁ = dropₓ (length l₂ - length l₁) l₂ :=
  ⟨fun h => append_left_cancel <| (suffix_iff_eq_append.1 h).trans (take_append_dropₓ _ _).symm, fun e =>
    e.symm ▸ drop_suffix _ _⟩

instance decidablePrefix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <+: l₂)
  | [], l₂ => isTrue ⟨l₂, rfl⟩
  | a :: l₁, [] => is_false fun ⟨t, te⟩ => List.noConfusion te
  | a :: l₁, b :: l₂ =>
    if h : a = b then
      decidableOfDecidableOfIff (decidable_prefix l₁ l₂)
        (by
          rw [← h, prefix_cons_inj])
    else
      is_false fun ⟨t, te⟩ =>
        h <| by
          injection te

-- Alternatively, use mem_tails
instance decidableSuffix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+ l₂)
  | [], l₂ => isTrue ⟨l₂, append_nil _⟩
  | a :: l₁, [] =>
    is_false <|
      mt (length_le_of_sublist ∘ is_suffix.sublist)
        (by
          decide)
  | l₁, b :: l₂ => decidableOfDecidableOfIff (@Or.decidable _ _ _ (l₁.decidableSuffix l₂)) suffix_cons_iff.symm

instance decidableInfix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+: l₂)
  | [], l₂ => isTrue ⟨[], l₂, rfl⟩
  | a :: l₁, [] =>
    is_false fun ⟨s, t, te⟩ => by
      simp at te <;> exact te
  | l₁, b :: l₂ =>
    decidableOfDecidableOfIff (@Or.decidable _ _ (l₁.decidablePrefix (b :: l₂)) (l₁.decidableInfix l₂))
      infix_cons_iff.symm

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:494:6: unsupported: specialize @hyp
theorem prefix_take_le_iff {L : List (List (Option α))} (hm : m < L.length) : L.take m <+: L.take n ↔ m ≤ n := by
  simp only [← prefix_iff_eq_take, ← length_take]
  induction' m with m IH generalizing L n
  · simp only [← min_eq_leftₓ, ← eq_self_iff_true, ← Nat.zero_leₓ, ← take]
    
  cases' L with l ls
  · exact (not_lt_bot hm).elim
    
  cases n
  · refine' iff_of_false _ (zero_lt_succ _).not_le
    rw [take_zero, take_nil]
    simp only [← take]
    exact not_false
    
  · simp only [← length] at hm
    specialize IH ls n (Nat.lt_of_succ_lt_succₓ hm)
    simp only [← le_of_ltₓ (Nat.lt_of_succ_lt_succₓ hm), ← min_eq_leftₓ] at IH
    simp only [← le_of_ltₓ hm, ← IH, ← true_andₓ, ← min_eq_leftₓ, ← eq_self_iff_true, ← length, ← take]
    exact ⟨Nat.succ_le_succₓ, Nat.le_of_succ_le_succₓ⟩
    

theorem cons_prefix_iff : a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂ := by
  constructor
  · rintro ⟨L, hL⟩
    simp only [← cons_append] at hL
    exact ⟨hL.left, ⟨L, hL.right⟩⟩
    
  · rintro ⟨rfl, h⟩
    rwa [prefix_cons_inj]
    

theorem IsPrefix.map (h : l₁ <+: l₂) (f : α → β) : l₁.map f <+: l₂.map f := by
  induction' l₁ with hd tl hl generalizing l₂
  · simp only [← nil_prefix, ← map_nil]
    
  · cases' l₂ with hd₂ tl₂
    · simpa only using eq_nil_of_prefix_nil h
      
    · rw [cons_prefix_iff] at h
      simp only [← h, ← prefix_cons_inj, ← hl, ← map]
      
    

theorem IsPrefix.filter_map (h : l₁ <+: l₂) (f : α → Option β) : l₁.filterMap f <+: l₂.filterMap f := by
  induction' l₁ with hd₁ tl₁ hl generalizing l₂
  · simp only [← nil_prefix, ← filter_map_nil]
    
  · cases' l₂ with hd₂ tl₂
    · simpa only using eq_nil_of_prefix_nil h
      
    · rw [cons_prefix_iff] at h
      rw [← @singleton_append _ hd₁ _, ← @singleton_append _ hd₂ _, filter_map_append, filter_map_append, h.left,
        prefix_append_right_inj]
      exact hl h.right
      
    

theorem IsPrefix.reduce_option {l₁ l₂ : List (Option α)} (h : l₁ <+: l₂) : l₁.reduceOption <+: l₂.reduceOption :=
  h.filterMap id

theorem IsPrefix.filter (p : α → Prop) [DecidablePred p] ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]
  exact prefix_append _ _

theorem IsSuffix.filter (p : α → Prop) [DecidablePred p] ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) :
    l₁.filter p <:+ l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]
  exact suffix_append _ _

theorem IsInfix.filter (p : α → Prop) [DecidablePred p] ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filter p <:+: l₂.filter p := by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filter_append, filter_append]
  exact infix_append _ _ _

instance : IsPartialOrder (List α) (· <+: ·) where
  refl := prefix_refl
  trans := fun _ _ _ => IsPrefix.trans
  antisymm := fun _ _ h₁ h₂ => eq_of_prefix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+ ·) where
  refl := suffix_refl
  trans := fun _ _ _ => IsSuffix.trans
  antisymm := fun _ _ h₁ h₂ => eq_of_suffix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+: ·) where
  refl := infix_refl
  trans := fun _ _ _ => IsInfix.trans
  antisymm := fun _ _ h₁ h₂ => eq_of_infix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

end Fix

section InitsTails

@[simp]
theorem mem_inits : ∀ s t : List α, s ∈ inits t ↔ s <+: t
  | s, [] =>
    suffices s = nil ↔ s <+: nil by
      simpa only [← inits, ← mem_singleton]
    ⟨fun h => h.symm ▸ prefix_refl [], eq_nil_of_prefix_nil⟩
  | s, a :: t =>
    suffices (s = nil ∨ ∃ l ∈ inits t, a :: l = s) ↔ s <+: a :: t by
      simpa
    ⟨fun o =>
      match s, o with
      | _, Or.inl rfl => ⟨_, rfl⟩
      | s, Or.inr ⟨r, hr, hs⟩ => by
        let ⟨s, ht⟩ := (mem_inits _ _).1 hr
        rw [← hs, ← ht] <;> exact ⟨s, rfl⟩,
      fun mi =>
      match s, mi with
      | [], ⟨_, rfl⟩ => Or.inl rfl
      | b :: s, ⟨r, hr⟩ =>
        (List.noConfusion hr) fun ba (st : s ++ r = t) =>
          Or.inr <| by
            rw [ba] <;> exact ⟨_, (mem_inits _ _).2 ⟨_, st⟩, rfl⟩⟩

@[simp]
theorem mem_tails : ∀ s t : List α, s ∈ tails t ↔ s <:+ t
  | s, [] => by
    simp only [← tails, ← mem_singleton] <;>
      exact
        ⟨fun h => by
          rw [h] <;> exact suffix_refl [], eq_nil_of_suffix_nil⟩
  | s, a :: t => by
    simp only [← tails, ← mem_cons_iff, ← mem_tails s t] <;>
      exact
        show s = a :: t ∨ s <:+ t ↔ s <:+ a :: t from
          ⟨fun o =>
            match s, t, o with
            | _, t, Or.inl rfl => suffix_rfl
            | s, _, Or.inr ⟨l, rfl⟩ => ⟨a :: l, rfl⟩,
            fun e =>
            match s, t, e with
            | _, t, ⟨[], rfl⟩ => Or.inl rfl
            | s, t, ⟨b :: l, he⟩ => List.noConfusion he fun ab lt => Or.inr ⟨l, lt⟩⟩

theorem inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t => a :: t := by
  simp

theorem tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails := by
  simp

@[simp]
theorem inits_append : ∀ s t : List α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
  | [], [] => by
    simp
  | [], a :: t => by
    simp
  | a :: s, t => by
    simp [← inits_append s t]

@[simp]
theorem tails_append : ∀ s t : List α, tails (s ++ t) = (s.tails.map fun l => l ++ t) ++ t.tails.tail
  | [], [] => by
    simp
  | [], a :: t => by
    simp
  | a :: s, t => by
    simp [← tails_append s t]

-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`
theorem inits_eq_tails : ∀ l : List α, l.inits = (reverse <| map reverse <| tails <| reverse l)
  | [] => by
    simp
  | a :: l => by
    simp [← inits_eq_tails l, ← map_eq_map_iff]

theorem tails_eq_inits : ∀ l : List α, l.tails = (reverse <| map reverse <| inits <| reverse l)
  | [] => by
    simp
  | a :: l => by
    simp [← tails_eq_inits l, ← append_left_inj]

theorem inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.tails) := by
  rw [tails_eq_inits l]
  simp [← reverse_involutive.comp_self]

theorem tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.inits) := by
  rw [inits_eq_tails l]
  simp [← reverse_involutive.comp_self]

theorem map_reverse_inits (l : List α) : map reverse l.inits = (reverse <| tails <| reverse l) := by
  rw [inits_eq_tails l]
  simp [← reverse_involutive.comp_self]

theorem map_reverse_tails (l : List α) : map reverse l.tails = (reverse <| inits <| reverse l) := by
  rw [tails_eq_inits l]
  simp [← reverse_involutive.comp_self]

@[simp]
theorem length_tails (l : List α) : length (tails l) = length l + 1 := by
  induction' l with x l IH
  · simp
    
  · simpa using IH
    

@[simp]
theorem length_inits (l : List α) : length (inits l) = length l + 1 := by
  simp [← inits_eq_tails]

@[simp]
theorem nth_le_tails (l : List α) (n : ℕ) (hn : n < length (tails l)) : nthLe (tails l) n hn = l.drop n := by
  induction' l with x l IH generalizing n
  · simp
    
  · cases n
    · simp
      
    · simpa using IH n _
      
    

@[simp]
theorem nth_le_inits (l : List α) (n : ℕ) (hn : n < length (inits l)) : nthLe (inits l) n hn = l.take n := by
  induction' l with x l IH generalizing n
  · simp
    
  · cases n
    · simp
      
    · simpa using IH n _
      
    

end InitsTails

/-! ### insert -/


section Insert

variable [DecidableEq α]

@[simp]
theorem insert_nil (a : α) : insert a nil = [a] :=
  rfl

theorem insertₓ.def (a : α) (l : List α) : insert a l = if a ∈ l then l else a :: l :=
  rfl

@[simp]
theorem insert_of_memₓ (h : a ∈ l) : insert a l = l := by
  simp only [← insert.def, ← if_pos h]

@[simp]
theorem insert_of_not_memₓ (h : a ∉ l) : insert a l = a :: l := by
  simp only [← insert.def, ← if_neg h] <;> constructor <;> rfl

@[simp]
theorem mem_insert_iffₓ : a ∈ insert b l ↔ a = b ∨ a ∈ l := by
  by_cases' h' : b ∈ l
  · simp only [← insert_of_mem h']
    apply (or_iff_right_of_imp _).symm
    exact fun e => e.symm ▸ h'
    
  · simp only [← insert_of_not_mem h', ← mem_cons_iff]
    

@[simp]
theorem suffix_insert (a : α) (l : List α) : l <:+ insert a l := by
  by_cases' a ∈ l <;> [simp only [← insert_of_mem h], simp only [← insert_of_not_mem h, ← suffix_cons]]

theorem infix_insert (a : α) (l : List α) : l <:+: insert a l :=
  (suffix_insert a l).IsInfix

theorem sublist_insert (a : α) (l : List α) : l <+ l.insert a :=
  (suffix_insert a l).Sublist

theorem subset_insert (a : α) (l : List α) : l ⊆ l.insert a :=
  (sublist_insert a l).Subset

@[simp]
theorem mem_insert_selfₓ (a : α) (l : List α) : a ∈ l.insert a :=
  mem_insert_iffₓ.2 <| Or.inl rfl

theorem mem_insert_of_memₓ (h : a ∈ l) : a ∈ insert b l :=
  mem_insert_iffₓ.2 (Or.inr h)

theorem eq_or_mem_of_mem_insertₓ (h : a ∈ insert b l) : a = b ∨ a ∈ l :=
  mem_insert_iffₓ.1 h

@[simp]
theorem length_insert_of_memₓ (h : a ∈ l) : (insert a l).length = l.length :=
  congr_arg _ <| insert_of_memₓ h

@[simp]
theorem length_insert_of_not_memₓ (h : a ∉ l) : (insert a l).length = l.length + 1 :=
  congr_arg _ <| insert_of_not_memₓ h

end Insert

theorem mem_of_mem_suffix (hx : a ∈ l₁) (hl : l₁ <:+ l₂) : a ∈ l₂ :=
  hl.Subset hx

end List

