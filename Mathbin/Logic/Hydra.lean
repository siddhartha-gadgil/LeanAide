/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathbin.Data.Multiset.Basic
import Mathbin.Order.WellFounded

/-!
# Termination of a hydra game

This file deals with the following version of the hydra game: each head of the hydra is
labelled by an element in a type `α`, and when you cut off one head with label `a`, it
grows back an arbitrary but finite number of heads, all labelled by elements smaller than
`a` with respect to a well-founded relation `r` on `α`. We show that no matter how (in
what order) you choose cut off the heads, the game always terminates, i.e. all heads will
eventually be cut off (but of course it can last arbitrarily long, i.e. takes an
arbitrary finite number of steps).

This result is stated as the well-foundedness of the `cut_expand` relation defined in
this file: we model the heads of the hydra as a multiset of elements of `α`, and the
valid "moves" of the game are modelled by the relation `cut_expand r` on `multiset α`:
`cut_expand r s' s` is true iff `s'` is obtained by removing one head `a ∈ s` and
adding back an arbitrary multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

To prove this theorem, we follow the proof by Peter LeFanu Lumsdaine at
https://mathoverflow.net/a/229084/3332, and along the way we introduce the notion of `fibration`
of relations, and a new operation `game_add` that combines to relations to form a relation on the
product type, which is used to define addition of games in combinatorial game theory.

TODO: formalize the relations corresponding to more powerful (e.g. Kirby–Paris and Buchholz)
hydras, and prove their well-foundedness.
-/


namespace Relation

variable {α β : Type _}

section TwoRels

variable (rα : α → α → Prop) (rβ : β → β → Prop) (f : α → β)

/-- A function `f : α → β` is a fibration between the relation `rα` and `rβ` if for all
  `a : α` and `b : β`, whenever `b : β` and `f a` are related by `rβ`, `b` is the image
  of some `a' : α` under `f`, and `a'` and `a` are related by `rα`. -/
def Fibration :=
  ∀ ⦃a b⦄, rβ b (f a) → ∃ a', rα a' a ∧ f a' = b

variable {rα rβ}

/-- If `f : α → β` is a fibration between relations `rα` and `rβ`, and `a : α` is
  accessible under `rα`, then `f a` is accessible under `rβ`. -/
theorem _root_.acc.of_fibration (fib : Fibration rα rβ f) {a} (ha : Acc rα a) : Acc rβ (f a) := by
  induction' ha with a ha ih
  refine' Acc.intro (f a) fun b hr => _
  obtain ⟨a', hr', rfl⟩ := fib hr
  exact ih a' hr'

theorem _root_.acc.of_downward_closed (dc : ∀ {a b}, rβ b (f a) → b ∈ Set.Range f) (a : α)
    (ha : Acc (InvImage rβ f) a) : Acc rβ (f a) :=
  ha.of_fibration f fun a b h =>
    let ⟨a', he⟩ := dc h
    ⟨a', he.substr h, he⟩

variable (rα rβ)

/-- The "addition of games" relation in combinatorial game theory, on the product type: if
  `rα a' a` means that `a ⟶ a'` is a valid move in game `α`, and `rβ b' b` means that `b ⟶ b'`
  is a valid move in game `β`, then `game_add rα rβ` specifies the valid moves in the juxtaposition
  of `α` and `β`: the player is free to choose one of the games and make a move in it,
  while leaving the other game unchanged. -/
inductive GameAdd : α × β → α × β → Prop
  | fst {a' a b} : rα a' a → game_add (a', b) (a, b)
  | snd {a b' b} : rβ b' b → game_add (a, b') (a, b)

/-- `game_add` is a `subrelation` of `prod.lex`. -/
theorem game_add_le_lex : GameAdd rα rβ ≤ Prod.Lex rα rβ := fun _ _ h =>
  h.rec (fun _ _ b => Prod.Lex.left b b) fun a _ _ => Prod.Lex.right a

/-- `prod.rprod` is a subrelation of the transitive closure of `game_add`. -/
theorem rprod_le_trans_gen_game_add : Prod.Rprod rα rβ ≤ TransGen (GameAdd rα rβ) := fun _ _ h =>
  h.rec
    (by
      intro _ _ _ _ hα hβ
      exact trans_gen.tail (trans_gen.single <| game_add.fst hα) (game_add.snd hβ))

variable {rα rβ}

/-- If `a` is accessible under `rα` and `b` is accessible under `rβ`, then `(a, b)` is
  accessible under `relation.game_add rα rβ`. Notice that `prod.lex_accessible` requires the
  stronger condition `∀ b, acc rβ b`. -/
theorem _root_.acc.game_add {a b} (ha : Acc rα a) (hb : Acc rβ b) : Acc (GameAdd rα rβ) (a, b) := by
  induction' ha with a ha iha generalizing b
  induction' hb with b hb ihb
  refine' Acc.intro _ fun h => _
  rintro (⟨_, _, _, ra⟩ | ⟨_, _, _, rb⟩)
  exacts[iha _ ra (Acc.intro b hb), ihb _ rb]

/-- The sum of two well-founded games is well-founded. -/
theorem _root_.well_founded.game_add (hα : WellFounded rα) (hβ : WellFounded rβ) : WellFounded (GameAdd rα rβ) :=
  ⟨fun ⟨a, b⟩ => (hα.apply a).GameAdd (hβ.apply b)⟩

end TwoRels

section Hydra

open GameAdd Multiset

/-- The relation that specifies valid moves in our hydra game. `cut_expand r s' s`
  means that `s'` is obtained by removing one head `a ∈ s` and adding back an arbitrary
  multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

  This is most directly translated into `s' = s.erase a + t`, but `multiset.erase` requires
  `decidable_eq α`, so we use the equivalent condition `s' + {a} = s + t` instead, which
  is also easier to verify for explicit multisets `s'`, `s` and `t`.

  We also don't include the condition `a ∈ s` because `s' + {a} = s + t` already
  guarantees `a ∈ s + t`, and if `r` is irreflexive then `a ∉ t`, which is the
  case when `r` is well-founded, the case we are primarily interested in.

  The lemma `relation.cut_expand_iff` below converts between this convenient definition
  and the direct translation when `r` is irreflexive. -/
def CutExpand (r : α → α → Prop) (s' s : Multiset α) : Prop :=
  ∃ (t : Multiset α)(a : α), (∀, ∀ a' ∈ t, ∀, r a' a) ∧ s' + {a} = s + t

variable {r : α → α → Prop}

theorem cut_expand_singleton {s x} (h : ∀, ∀ x' ∈ s, ∀, r x' x) : CutExpand r s {x} :=
  ⟨s, x, h, add_commₓ s _⟩

theorem cut_expand_singleton_singleton {x' x} (h : r x' x) : CutExpand r {x'} {x} :=
  cut_expand_singleton fun a h => by
    rwa [mem_singleton.1 h]

theorem cut_expand_add_left {t u} (s) : CutExpand r (s + t) (s + u) ↔ CutExpand r t u :=
  exists₂_congrₓ fun _ _ =>
    and_congr Iff.rfl <| by
      rw [add_assocₓ, add_assocₓ, add_left_cancel_iffₓ]

theorem cut_expand_iff [DecidableEq α] [IsIrrefl α r] {s' s : Multiset α} :
    CutExpand r s' s ↔ ∃ (t : Multiset α)(a : _), (∀, ∀ a' ∈ t, ∀, r a' a) ∧ a ∈ s ∧ s' = s.erase a + t := by
  simp_rw [cut_expand, add_singleton_eq_iff]
  refine' exists₂_congrₓ fun t a => ⟨_, _⟩
  · rintro ⟨ht, ha, rfl⟩
    obtain h | h := mem_add.1 ha
    exacts[⟨ht, h, t.erase_add_left_pos h⟩, (@irrefl α r _ a (ht a h)).elim]
    
  · rintro ⟨ht, h, rfl⟩
    exact ⟨ht, mem_add.2 (Or.inl h), (t.erase_add_left_pos h).symm⟩
    

theorem not_cut_expand_zero [IsIrrefl α r] (s) : ¬CutExpand r s 0 := by
  classical
  rw [cut_expand_iff]
  rintro ⟨_, _, _, ⟨⟩, _⟩

/-- For any relation `r` on `α`, multiset addition `multiset α × multiset α → multiset α` is a
  fibration between the game sum of `cut_expand r` with itself and `cut_expand r` itself. -/
theorem cut_expand_fibration (r : α → α → Prop) :
    Fibration (GameAdd (CutExpand r) (CutExpand r)) (CutExpand r) fun s => s.1 + s.2 := by
  rintro ⟨s₁, s₂⟩ s ⟨t, a, hr, he⟩
  dsimp'  at he⊢
  classical
  obtain ⟨ha, rfl⟩ := add_singleton_eq_iff.1 he
  rw [add_assocₓ, mem_add] at ha
  obtain h | h := ha
  · refine' ⟨(s₁.erase a + t, s₂), fst ⟨t, a, hr, _⟩, _⟩
    · rw [add_commₓ, ← add_assocₓ, singleton_add, cons_erase h]
      
    · rw [add_assocₓ s₁, erase_add_left_pos _ h, add_right_commₓ, add_assocₓ]
      
    
  · refine' ⟨(s₁, (s₂ + t).erase a), snd ⟨t, a, hr, _⟩, _⟩
    · rw [add_commₓ, singleton_add, cons_erase h]
      
    · rw [add_assocₓ, erase_add_right_pos _ h]
      
    

/-- A multiset is accessible under `cut_expand` if all its singleton subsets are,
  assuming `r` is irreflexive. -/
theorem acc_of_singleton [IsIrrefl α r] {s : Multiset α} :
    (∀, ∀ a ∈ s, ∀, Acc (CutExpand r) {a}) → Acc (CutExpand r) s := by
  refine' Multiset.induction _ _ s
  · exact fun _ => (Acc.intro 0) fun s h => (not_cut_expand_zero s h).elim
    
  · intro a s ih hacc
    rw [← s.singleton_add a]
    exact
      ((hacc a <| s.mem_cons_self a).GameAdd <| ih fun a ha => hacc a <| mem_cons_of_mem ha).of_fibration _
        (cut_expand_fibration r)
    

/-- A singleton `{a}` is accessible under `cut_expand r` if `a` is accessible under `r`,
  assuming `r` is irreflexive. -/
theorem _root_.acc.cut_expand [IsIrrefl α r] {a : α} (hacc : Acc r a) : Acc (CutExpand r) {a} := by
  induction' hacc with a h ih
  refine' Acc.intro _ fun s => _
  classical
  rw [cut_expand_iff]
  rintro ⟨t, a, hr, rfl | ⟨⟨⟩⟩, rfl⟩
  refine' acc_of_singleton fun a' => _
  rw [erase_singleton, zero_addₓ]
  exact ih a' ∘ hr a'

/-- `cut_expand r` is well-founded when `r` is. -/
theorem _root_.well_founded.cut_expand (hr : WellFounded r) : WellFounded (CutExpand r) :=
  ⟨by
    let h := hr.is_irrefl
    exact fun s => acc_of_singleton fun a _ => (hr.apply a).CutExpand⟩

end Hydra

end Relation

