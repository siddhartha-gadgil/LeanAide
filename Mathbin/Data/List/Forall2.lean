/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Data.List.Infix

/-!
# Double universal quantification on a list

This file provides an API for `list.forall₂` (definition in `data.list.defs`).
`forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length, and whenever `a` is the nth element
of `l₁`, and `b` is the nth element of `l₂`, then `R a b` is satisfied.
-/


open Nat Function

namespace List

variable {α β γ δ : Type _} {r : α → β → Prop} {p : γ → δ → Prop}

open Relator

mk_iff_of_inductive_prop List.Forall₂ List.forall₂_iff

@[simp]
theorem forall₂_cons {R : α → β → Prop} {a b l₁ l₂} : Forall₂ R (a :: l₁) (b :: l₂) ↔ R a b ∧ Forall₂ R l₁ l₂ :=
  ⟨fun h => by
    cases' h with h₁ h₂ <;> constructor <;> assumption, fun ⟨h₁, h₂⟩ => Forall₂.cons h₁ h₂⟩

theorem Forall₂.imp {R S : α → β → Prop} (H : ∀ a b, R a b → S a b) {l₁ l₂} (h : Forall₂ R l₁ l₂) : Forall₂ S l₁ l₂ :=
  by
  induction h <;> constructor <;> solve_by_elim

theorem Forall₂.mp {r q s : α → β → Prop} (h : ∀ a b, r a b → q a b → s a b) :
    ∀ {l₁ l₂}, Forall₂ r l₁ l₂ → Forall₂ q l₁ l₂ → Forall₂ s l₁ l₂
  | [], [], forall₂.nil, forall₂.nil => Forall₂.nil
  | a :: l₁, b :: l₂, forall₂.cons hr hrs, forall₂.cons hq hqs => Forall₂.cons (h a b hr hq) (forall₂.mp hrs hqs)

theorem Forall₂.flip : ∀ {a b}, Forall₂ (flip r) b a → Forall₂ r a b
  | _, _, forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => Forall₂.cons h₁ h₂.flip

@[simp]
theorem forall₂_same {r : α → α → Prop} : ∀ {l : List α}, Forall₂ r l l ↔ ∀, ∀ x ∈ l, ∀, r x x
  | [] => by
    simp
  | a :: l => by
    simp [← @forall₂_same l]

theorem forall₂_refl {r} [IsRefl α r] (l : List α) : Forall₂ r l l :=
  forall₂_same.2 fun a h => refl _

@[simp]
theorem forall₂_eq_eq_eq : Forall₂ ((· = ·) : α → α → Prop) = (· = ·) := by
  funext a b
  apply propext
  constructor
  · intro h
    induction h
    · rfl
      
    simp only [*] <;> constructor <;> rfl
    
  · rintro rfl
    exact forall₂_refl _
    

@[simp]
theorem forall₂_nil_left_iff {l} : Forall₂ r nil l ↔ l = nil :=
  ⟨fun H => by
    cases H <;> rfl, by
    rintro rfl <;> exact forall₂.nil⟩

@[simp]
theorem forall₂_nil_right_iff {l} : Forall₂ r l nil ↔ l = nil :=
  ⟨fun H => by
    cases H <;> rfl, by
    rintro rfl <;> exact forall₂.nil⟩

theorem forall₂_cons_left_iff {a l u} : Forall₂ r (a :: l) u ↔ ∃ b u', r a b ∧ Forall₂ r l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨b, u', h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

theorem forall₂_cons_right_iff {b l u} : Forall₂ r u (b :: l) ↔ ∃ a u', r a b ∧ Forall₂ r u' l ∧ u = a :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨b, u', h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

theorem forall₂_and_left {r : α → β → Prop} {p : α → Prop} :
    ∀ l u, Forall₂ (fun a b => p a ∧ r a b) l u ↔ (∀, ∀ a ∈ l, ∀, p a) ∧ Forall₂ r l u
  | [], u => by
    simp only [← forall₂_nil_left_iff, ← forall_prop_of_false (not_mem_nil _), ← imp_true_iff, ← true_andₓ]
  | a :: l, u => by
    simp only [← forall₂_and_left l, ← forall₂_cons_left_iff, ← forall_mem_cons, ← and_assoc, ← and_comm, ←
      And.left_comm, ← exists_and_distrib_left.symm]

@[simp]
theorem forall₂_map_left_iff {f : γ → α} : ∀ {l u}, Forall₂ r (map f l) u ↔ Forall₂ (fun c b => r (f c) b) l u
  | [], _ => by
    simp only [← map, ← forall₂_nil_left_iff]
  | a :: l, _ => by
    simp only [← map, ← forall₂_cons_left_iff, ← forall₂_map_left_iff]

@[simp]
theorem forall₂_map_right_iff {f : γ → β} : ∀ {l u}, Forall₂ r l (map f u) ↔ Forall₂ (fun a c => r a (f c)) l u
  | _, [] => by
    simp only [← map, ← forall₂_nil_right_iff]
  | _, b :: u => by
    simp only [← map, ← forall₂_cons_right_iff, ← forall₂_map_right_iff]

theorem left_unique_forall₂' (hr : LeftUnique r) : ∀ {a b c}, Forall₂ r a c → Forall₂ r b c → a = b
  | a₀, nil, a₁, forall₂.nil, forall₂.nil => rfl
  | a₀ :: l₀, b :: l, a₁ :: l₁, forall₂.cons ha₀ h₀, forall₂.cons ha₁ h₁ =>
    hr ha₀ ha₁ ▸ left_unique_forall₂' h₀ h₁ ▸ rfl

theorem _root_.relator.left_unique.forall₂ (hr : LeftUnique r) : LeftUnique (Forall₂ r) :=
  @left_unique_forall₂' _ _ _ hr

theorem right_unique_forall₂' (hr : RightUnique r) : ∀ {a b c}, Forall₂ r a b → Forall₂ r a c → b = c
  | nil, a₀, a₁, forall₂.nil, forall₂.nil => rfl
  | b :: l, a₀ :: l₀, a₁ :: l₁, forall₂.cons ha₀ h₀, forall₂.cons ha₁ h₁ =>
    hr ha₀ ha₁ ▸ right_unique_forall₂' h₀ h₁ ▸ rfl

theorem _root_.relator.right_unique.forall₂ (hr : RightUnique r) : RightUnique (Forall₂ r) :=
  @right_unique_forall₂' _ _ _ hr

theorem _root_.relator.bi_unique.forall₂ (hr : BiUnique r) : BiUnique (Forall₂ r) :=
  ⟨hr.left.Forall₂, hr.right.Forall₂⟩

theorem forall₂_length_eq {R : α → β → Prop} : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → length l₁ = length l₂
  | _, _, forall₂.nil => rfl
  | _, _, forall₂.cons h₁ h₂ => congr_arg succ (forall₂_length_eq h₂)

theorem forall₂_zip {R : α → β → Prop} : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → ∀ {a b}, (a, b) ∈ zipₓ l₁ l₂ → R a b
  | _, _, forall₂.cons h₁ h₂, x, y, Or.inl rfl => h₁
  | _, _, forall₂.cons h₁ h₂, x, y, Or.inr h₃ => forall₂_zip h₂ h₃

theorem forall₂_iff_zip {R : α → β → Prop} {l₁ l₂} :
    Forall₂ R l₁ l₂ ↔ length l₁ = length l₂ ∧ ∀ {a b}, (a, b) ∈ zipₓ l₁ l₂ → R a b :=
  ⟨fun h => ⟨forall₂_length_eq h, @forall₂_zip _ _ _ _ _ h⟩, fun h => by
    cases' h with h₁ h₂
    induction' l₁ with a l₁ IH generalizing l₂
    · cases length_eq_zero.1 h₁.symm
      constructor
      
    · cases' l₂ with b l₂ <;> injection h₁ with h₁
      exact forall₂.cons (h₂ <| Or.inl rfl) ((IH h₁) fun a b h => h₂ <| Or.inr h)
      ⟩

theorem forall₂_take {R : α → β → Prop} : ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (takeₓ n l₁) (takeₓ n l₂)
  | 0, _, _, _ => by
    simp only [← forall₂.nil, ← take]
  | n + 1, _, _, forall₂.nil => by
    simp only [← forall₂.nil, ← take]
  | n + 1, _, _, forall₂.cons h₁ h₂ => by
    simp [← And.intro h₁ h₂, ← forall₂_take n]

theorem forall₂_drop {R : α → β → Prop} : ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (dropₓ n l₁) (dropₓ n l₂)
  | 0, _, _, h => by
    simp only [← drop, ← h]
  | n + 1, _, _, forall₂.nil => by
    simp only [← forall₂.nil, ← drop]
  | n + 1, _, _, forall₂.cons h₁ h₂ => by
    simp [← And.intro h₁ h₂, ← forall₂_drop n]

theorem forall₂_take_append {R : α → β → Prop} (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.takeₓ (length l₁) l) l₁ := by
  have h' : Forall₂ R (takeₓ (length l₁) l) (takeₓ (length l₁) (l₁ ++ l₂)) := forall₂_take (length l₁) h
  rwa [take_left] at h'

theorem forall₂_drop_append {R : α → β → Prop} (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.dropₓ (length l₁) l) l₂ := by
  have h' : Forall₂ R (dropₓ (length l₁) l) (dropₓ (length l₁) (l₁ ++ l₂)) := forall₂_drop (length l₁) h
  rwa [drop_left] at h'

theorem rel_mem (hr : BiUnique r) : (r⇒Forall₂ r⇒Iff) (· ∈ ·) (· ∈ ·)
  | a, b, h, [], [], forall₂.nil => by
    simp only [← not_mem_nil]
  | a, b, h, a' :: as, b' :: bs, forall₂.cons h₁ h₂ => rel_or (rel_eq hr h h₁) (rel_mem h h₂)

theorem rel_map : ((r⇒p)⇒Forall₂ r⇒Forall₂ p) map map
  | f, g, h, [], [], forall₂.nil => Forall₂.nil
  | f, g, h, a :: as, b :: bs, forall₂.cons h₁ h₂ => Forall₂.cons (h h₁) (rel_map (@h) h₂)

theorem rel_append : (Forall₂ r⇒Forall₂ r⇒Forall₂ r) append append
  | [], [], h, l₁, l₂, hl => hl
  | a :: as, b :: bs, forall₂.cons h₁ h₂, l₁, l₂, hl => Forall₂.cons h₁ (rel_append h₂ hl)

theorem rel_reverse : (Forall₂ r⇒Forall₂ r) reverse reverse
  | [], [], forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => by
    simp only [← reverse_cons]
    exact rel_append (rel_reverse h₂) (forall₂.cons h₁ forall₂.nil)

@[simp]
theorem forall₂_reverse_iff {l₁ l₂} : Forall₂ r (reverse l₁) (reverse l₂) ↔ Forall₂ r l₁ l₂ :=
  Iff.intro
    (fun h => by
      rw [← reverse_reverse l₁, ← reverse_reverse l₂]
      exact rel_reverse h)
    fun h => rel_reverse h

theorem rel_join : (Forall₂ (Forall₂ r)⇒Forall₂ r) join join
  | [], [], forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => rel_append h₁ (rel_join h₂)

theorem rel_bind : (Forall₂ r⇒(r⇒Forall₂ p)⇒Forall₂ p) List.bind List.bind := fun a b h₁ f g h₂ =>
  rel_join (rel_map (@h₂) h₁)

theorem rel_foldl : ((p⇒r⇒p)⇒p⇒Forall₂ r⇒p) foldlₓ foldlₓ
  | f, g, hfg, _, _, h, _, _, forall₂.nil => h
  | f, g, hfg, x, y, hxy, _, _, forall₂.cons hab hs => rel_foldl (@hfg) (hfg hxy hab) hs

theorem rel_foldr : ((r⇒p⇒p)⇒p⇒Forall₂ r⇒p) foldr foldr
  | f, g, hfg, _, _, h, _, _, forall₂.nil => h
  | f, g, hfg, x, y, hxy, _, _, forall₂.cons hab hs => hfg hab (rel_foldr (@hfg) hxy hs)

theorem rel_filter {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q] (hpq : (r⇒(· ↔ ·)) p q) :
    (Forall₂ r⇒Forall₂ r) (filterₓ p) (filterₓ q)
  | _, _, forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => by
    by_cases' p a
    · have : q b := by
        rwa [← hpq h₁]
      simp only [← filter_cons_of_pos _ h, ← filter_cons_of_pos _ this, ← forall₂_cons, ← h₁, ← rel_filter h₂, ←
        and_trueₓ]
      
    · have : ¬q b := by
        rwa [← hpq h₁]
      simp only [← filter_cons_of_neg _ h, ← filter_cons_of_neg _ this, ← rel_filter h₂]
      

theorem rel_filter_map : ((r⇒Option.Rel p)⇒Forall₂ r⇒Forall₂ p) filterMap filterMap
  | f, g, hfg, _, _, forall₂.nil => Forall₂.nil
  | f, g, hfg, a :: as, b :: bs, forall₂.cons h₁ h₂ => by
    rw [filter_map_cons, filter_map_cons] <;>
      exact
        match f a, g b, hfg h₁ with
        | _, _, Option.Rel.none => rel_filter_map (@hfg) h₂
        | _, _, Option.Rel.some h => forall₂.cons h (rel_filter_map (@hfg) h₂)

@[to_additive]
theorem rel_prod [Monoidₓ α] [Monoidₓ β] (h : r 1 1) (hf : (r⇒r⇒r) (· * ·) (· * ·)) : (Forall₂ r⇒r) prod prod :=
  rel_foldl hf h

/-- Given a relation `r`, `sublist_forall₂ r l₁ l₂` indicates that there is a sublist of `l₂` such
  that `forall₂ r l₁ l₂`. -/
inductive SublistForall₂ (r : α → β → Prop) : List α → List β → Prop
  | nil {l} : sublist_forall₂ [] l
  | cons {a₁ a₂ l₁ l₂} : r a₁ a₂ → sublist_forall₂ l₁ l₂ → sublist_forall₂ (a₁ :: l₁) (a₂ :: l₂)
  | cons_right {a l₁ l₂} : sublist_forall₂ l₁ l₂ → sublist_forall₂ l₁ (a :: l₂)

theorem sublist_forall₂_iff {l₁ : List α} {l₂ : List β} : SublistForall₂ r l₁ l₂ ↔ ∃ l, Forall₂ r l₁ l ∧ l <+ l₂ := by
  constructor <;> intro h
  · induction' h with _ a b l1 l2 rab rll ih b l1 l2 hl ih
    · exact ⟨nil, forall₂.nil, nil_sublist _⟩
      
    · obtain ⟨l, hl1, hl2⟩ := ih
      refine' ⟨b :: l, forall₂.cons rab hl1, hl2.cons_cons b⟩
      
    · obtain ⟨l, hl1, hl2⟩ := ih
      exact ⟨l, hl1, hl2.trans (sublist.cons _ _ _ (sublist.refl _))⟩
      
    
  · obtain ⟨l, hl1, hl2⟩ := h
    revert l₁
    induction' hl2 with _ _ _ _ ih _ _ _ _ ih <;> intro l₁ hl1
    · rw [forall₂_nil_right_iff.1 hl1]
      exact sublist_forall₂.nil
      
    · exact sublist_forall₂.cons_right (ih hl1)
      
    · cases' hl1 with _ _ _ _ hr hl _
      exact sublist_forall₂.cons hr (ih hl)
      
    

variable {ra : α → α → Prop}

instance SublistForall₂.is_refl [IsRefl α ra] : IsRefl (List α) (SublistForall₂ ra) :=
  ⟨fun l => sublist_forall₂_iff.2 ⟨l, forall₂_refl l, Sublist.refl l⟩⟩

instance SublistForall₂.is_trans [IsTrans α ra] : IsTrans (List α) (SublistForall₂ ra) :=
  ⟨fun a b c => by
    revert a b
    induction' c with _ _ ih
    · rintro _ _ h1 (_ | _ | _)
      exact h1
      
    · rintro a b h1 h2
      cases' h2 with _ _ _ _ _ hbc tbc _ _ y1 btc
      · cases h1
        exact sublist_forall₂.nil
        
      · cases' h1 with _ _ _ _ _ hab tab _ _ _ atb
        · exact sublist_forall₂.nil
          
        · exact sublist_forall₂.cons (trans hab hbc) (ih _ _ tab tbc)
          
        · exact sublist_forall₂.cons_right (ih _ _ atb tbc)
          
        
      · exact sublist_forall₂.cons_right (ih _ _ h1 btc)
        
      ⟩

theorem Sublist.sublist_forall₂ {l₁ l₂ : List α} (h : l₁ <+ l₂) (r : α → α → Prop) [IsRefl α r] :
    SublistForall₂ r l₁ l₂ :=
  sublist_forall₂_iff.2 ⟨l₁, forall₂_refl l₁, h⟩

theorem tail_sublist_forall₂_self [IsRefl α ra] (l : List α) : SublistForall₂ ra l.tail l :=
  l.tail_sublist.SublistForall₂ ra

end List

