/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Data.Set.Pairwise
import Mathbin.Data.SetLike.Basic

/-!
# Chains and flags

This file defines chains for an arbitrary relation and flags for an order and proves Hausdorff's
Maximality Principle.

## Main declarations

* `is_chain s`: A chain `s` is a set of comparable elements.
* `max_chain_spec`: Hausdorff's Maximality Principle.
* `flag`: The type of flags, aka maximal chains, of an order.

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/


open Classical Set

variable {α β : Type _}

/-! ### Chains -/


section Chain

variable (r : α → α → Prop)

-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => r

/-- A chain is a set `s` satisfying `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ s`. -/
def IsChain (s : Set α) : Prop :=
  s.Pairwise fun x y => x ≺ y ∨ y ≺ x

/-- `super_chain s t` means that `t` is a chain that strictly includes `s`. -/
def SuperChain (s t : Set α) : Prop :=
  IsChain r t ∧ s ⊂ t

/-- A chain `s` is a maximal chain if there does not exists a chain strictly including `s`. -/
def IsMaxChain (s : Set α) : Prop :=
  IsChain r s ∧ ∀ ⦃t⦄, IsChain r t → s ⊆ t → s = t

variable {r} {c c₁ c₂ c₃ s t : Set α} {a b x y : α}

theorem is_chain_empty : IsChain r ∅ :=
  Set.pairwise_empty _

theorem Set.Subsingleton.is_chain (hs : s.Subsingleton) : IsChain r s :=
  hs.Pairwise _

theorem IsChain.mono : s ⊆ t → IsChain r t → IsChain r s :=
  Set.Pairwise.mono

theorem IsChain.mono_rel {r' : α → α → Prop} (h : IsChain r s) (h_imp : ∀ x y, r x y → r' x y) : IsChain r' s :=
  h.mono' fun x y => Or.imp (h_imp x y) (h_imp y x)

/-- This can be used to turn `is_chain (≥)` into `is_chain (≤)` and vice-versa. -/
theorem IsChain.symm (h : IsChain r s) : IsChain (flip r) s :=
  h.mono' fun _ _ => Or.symm

theorem is_chain_of_trichotomous [IsTrichotomous α r] (s : Set α) : IsChain r s := fun a _ b _ hab =>
  (trichotomous_of r a b).imp_right fun h => h.resolve_left hab

theorem IsChain.insert (hs : IsChain r s) (ha : ∀, ∀ b ∈ s, ∀, a ≠ b → a ≺ b ∨ b ≺ a) : IsChain r (insert a s) :=
  hs.insert_of_symmetric (fun _ _ => Or.symm) ha

theorem is_chain_univ_iff : IsChain r (Univ : Set α) ↔ IsTrichotomous α r := by
  refine' ⟨fun h => ⟨fun a b => _⟩, fun h => @is_chain_of_trichotomous _ _ h univ⟩
  rw [Or.left_comm, or_iff_not_imp_left]
  exact h trivialₓ trivialₓ

theorem IsChain.image (r : α → α → Prop) (s : β → β → Prop) (f : α → β) (h : ∀ x y, r x y → s (f x) (f y)) {c : Set α}
    (hrc : IsChain r c) : IsChain s (f '' c) := fun x ⟨a, ha₁, ha₂⟩ y ⟨b, hb₁, hb₂⟩ =>
  ha₂ ▸ hb₂ ▸ fun hxy => (hrc ha₁ hb₁ <| ne_of_apply_ne f hxy).imp (h _ _) (h _ _)

section Total

variable [IsRefl α r]

theorem IsChain.total (h : IsChain r s) (hx : x ∈ s) (hy : y ∈ s) : x ≺ y ∨ y ≺ x :=
  (eq_or_ne x y).elim (fun e => Or.inl <| e ▸ refl _) (h hx hy)

theorem IsChain.directed_on (H : IsChain r s) : DirectedOn r s := fun x hx y hy =>
  ((H.Total hx hy).elim fun h => ⟨y, hy, h, refl _⟩) fun h => ⟨x, hx, refl _, h⟩

protected theorem IsChain.directed {f : β → α} {c : Set β} (h : IsChain (f ⁻¹'o r) c) :
    Directed r fun x : { a : β // a ∈ c } => f x := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
  (by_cases fun hab : a = b => by
      simp only [← hab, ← exists_prop, ← and_selfₓ, ← Subtype.exists] <;> exact ⟨b, hb, refl _⟩)
    fun hab => ((h ha hb hab).elim fun h => ⟨⟨b, hb⟩, h, refl _⟩) fun h => ⟨⟨a, ha⟩, refl _, h⟩

end Total

theorem IsMaxChain.is_chain (h : IsMaxChain r s) : IsChain r s :=
  h.1

theorem IsMaxChain.not_super_chain (h : IsMaxChain r s) : ¬SuperChain r s t := fun ht => ht.2.Ne <| h.2 ht.1 ht.2.1

theorem IsMaxChain.bot_mem [LE α] [OrderBot α] (h : IsMaxChain (· ≤ ·) s) : ⊥ ∈ s :=
  (h.2 (h.1.insert fun a _ _ => Or.inl bot_le) <| subset_insert _ _).symm ▸ mem_insert _ _

theorem IsMaxChain.top_mem [LE α] [OrderTop α] (h : IsMaxChain (· ≤ ·) s) : ⊤ ∈ s :=
  (h.2 (h.1.insert fun a _ _ => Or.inr le_top) <| subset_insert _ _).symm ▸ mem_insert _ _

open Classical

/-- Given a set `s`, if there exists a chain `t` strictly including `s`, then `succ_chain s`
is one of these chains. Otherwise it is `s`. -/
def SuccChain (r : α → α → Prop) (s : Set α) : Set α :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then some h else s

theorem succ_chain_spec (h : ∃ t, IsChain r s ∧ SuperChain r s t) : SuperChain r s (SuccChain r s) := by
  let ⟨t, hc'⟩ := h
  have : IsChain r s ∧ SuperChain r s (some h) := @some_spec _ (fun t => IsChain r s ∧ SuperChain r s t) _
  simp [← SuccChain, ← dif_pos, ← h, ← this.right]

theorem IsChain.succ (hs : IsChain r s) : IsChain r (SuccChain r s) :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then (succ_chain_spec h).1
  else by
    simp [← SuccChain, ← dif_neg, ← h]
    exact hs

theorem IsChain.super_chain_succ_chain (hs₁ : IsChain r s) (hs₂ : ¬IsMaxChain r s) : SuperChain r s (SuccChain r s) :=
  by
  simp [← IsMaxChain, ← not_and_distrib, ← not_forall_not] at hs₂
  obtain ⟨t, ht, hst⟩ := hs₂.neg_resolve_left hs₁
  exact succ_chain_spec ⟨t, hs₁, ht, ssubset_iff_subset_ne.2 hst⟩

theorem subset_succ_chain : s ⊆ SuccChain r s :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then (succ_chain_spec h).2.1
  else by
    simp [← SuccChain, ← dif_neg, ← h, ← subset.rfl]

/-- Predicate for whether a set is reachable from `∅` using `succ_chain` and `⋃₀`. -/
inductive ChainClosure (r : α → α → Prop) : Set α → Prop
  | succ : ∀ {s}, ChainClosure s → ChainClosure (SuccChain r s)
  | union : ∀ {s}, (∀, ∀ a ∈ s, ∀, ChainClosure a) → ChainClosure (⋃₀s)

/-- An explicit maximal chain. `max_chain` is taken to be the union of all sets in `chain_closure`.
-/
def MaxChain (r : α → α → Prop) :=
  ⋃₀SetOf (ChainClosure r)

theorem chain_closure_empty : ChainClosure r ∅ := by
  have : ChainClosure r (⋃₀∅) := ChainClosure.union fun a h => h.rec _
  simpa using this

theorem chain_closure_max_chain : ChainClosure r (MaxChain r) :=
  ChainClosure.union fun s => id

private theorem chain_closure_succ_total_aux (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (h : ∀ ⦃c₃⦄, ChainClosure r c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ SuccChain r c₃ ⊆ c₂) : SuccChain r c₂ ⊆ c₁ ∨ c₁ ⊆ c₂ := by
  induction hc₁
  case succ c₃ hc₃ ih =>
    cases' ih with ih ih
    · exact Or.inl (ih.trans subset_succ_chain)
      
    · exact (h hc₃ ih).imp_left fun h => h ▸ subset.rfl
      
  case union s hs ih =>
    refine' or_iff_not_imp_left.2 fun hn => sUnion_subset fun a ha => _
    exact (ih a ha).resolve_left fun h => hn <| h.trans <| subset_sUnion_of_mem ha

private theorem chain_closure_succ_total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂) (h : c₁ ⊆ c₂) :
    c₂ = c₁ ∨ SuccChain r c₁ ⊆ c₂ := by
  induction hc₂ generalizing c₁ hc₁ h
  case succ c₂ hc₂ ih =>
    refine' ((chain_closure_succ_total_aux hc₁ hc₂) fun c₁ => ih).imp h.antisymm' fun h₁ => _
    obtain rfl | h₂ := ih hc₁ h₁
    · exact subset.rfl
      
    · exact h₂.trans subset_succ_chain
      
  case union s hs ih =>
    apply Or.imp_left h.antisymm'
    apply Classical.by_contradiction
    simp [← not_or_distrib, ← sUnion_subset_iff, ← not_forall]
    intro c₃ hc₃ h₁ h₂
    obtain h | h := chain_closure_succ_total_aux hc₁ (hs c₃ hc₃) fun c₄ => ih _ hc₃
    · exact h₁ (subset_succ_chain.trans h)
      
    obtain h' | h' := ih c₃ hc₃ hc₁ h
    · exact h₁ h'.subset
      
    · exact h₂ (h'.trans <| subset_sUnion_of_mem hc₃)
      

theorem ChainClosure.total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂) : c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
  ((chain_closure_succ_total_aux hc₂ hc₁) fun c₃ hc₃ => chain_closure_succ_total hc₃ hc₁).imp_left
    subset_succ_chain.trans

theorem ChainClosure.succ_fixpoint (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂) (hc : SuccChain r c₂ = c₂) :
    c₁ ⊆ c₂ := by
  induction hc₁
  case succ s₁ hc₁ h =>
    exact (chain_closure_succ_total hc₁ hc₂ h).elim (fun h => h ▸ hc.subset) id
  case union s hs ih =>
    exact sUnion_subset ih

theorem ChainClosure.succ_fixpoint_iff (hc : ChainClosure r c) : SuccChain r c = c ↔ c = MaxChain r :=
  ⟨fun h => (subset_sUnion_of_mem hc).antisymm <| chain_closure_max_chain.succ_fixpoint hc h, fun h =>
    subset_succ_chain.antisymm' <| (subset_sUnion_of_mem hc.succ).trans h.symm.Subset⟩

theorem ChainClosure.is_chain (hc : ChainClosure r c) : IsChain r c := by
  induction hc
  case succ c hc h =>
    exact h.succ
  case union s hs h =>
    change ∀, ∀ c ∈ s, ∀, IsChain r c at h
    exact fun c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq =>
      ((hs _ ht₁).Total <| hs _ ht₂).elim (fun ht => h t₂ ht₂ (ht hc₁) hc₂ hneq) fun ht => h t₁ ht₁ hc₁ (ht hc₂) hneq

/-- **Hausdorff's maximality principle**

There exists a maximal totally ordered set of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
theorem max_chain_spec : IsMaxChain r (MaxChain r) :=
  Classical.by_contradiction fun h =>
    let ⟨h₁, H⟩ := chain_closure_max_chain.IsChain.super_chain_succ_chain h
    H.Ne (chain_closure_max_chain.succ_fixpoint_iff.mpr rfl).symm

end Chain

/-! ### Flags -/


/-- The type of flags, aka maximal chains, of an order. -/
structure Flag (α : Type _) [LE α] where
  Carrier : Set α
  Chain' : IsChain (· ≤ ·) carrier
  max_chain' : ∀ ⦃s⦄, IsChain (· ≤ ·) s → carrier ⊆ s → carrier = s

namespace Flag

section LE

variable [LE α] {s t : Flag α} {a : α}

instance : SetLike (Flag α) α where
  coe := Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

@[ext]
theorem ext : (s : Set α) = t → s = t :=
  SetLike.ext'

@[simp]
theorem mem_coe_iff : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl

@[simp]
theorem coe_mk (s : Set α) (h₁ h₂) : (mk s h₁ h₂ : Set α) = s :=
  rfl

@[simp]
theorem mk_coe (s : Flag α) : mk (s : Set α) s.Chain' s.max_chain' = s :=
  ext rfl

theorem chain_le (s : Flag α) : IsChain (· ≤ ·) (s : Set α) :=
  s.Chain'

protected theorem max_chain (s : Flag α) : IsMaxChain (· ≤ ·) (s : Set α) :=
  ⟨s.chain_le, s.max_chain'⟩

theorem top_mem [OrderTop α] (s : Flag α) : (⊤ : α) ∈ s :=
  s.MaxChain.top_mem

theorem bot_mem [OrderBot α] (s : Flag α) : (⊥ : α) ∈ s :=
  s.MaxChain.bot_mem

end LE

section Preorderₓ

variable [Preorderₓ α] {a b : α}

protected theorem le_or_le (s : Flag α) (ha : a ∈ s) (hb : b ∈ s) : a ≤ b ∨ b ≤ a :=
  s.chain_le.Total ha hb

instance [OrderTop α] (s : Flag α) : OrderTop s :=
  Subtype.orderTop s.top_mem

instance [OrderBot α] (s : Flag α) : OrderBot s :=
  Subtype.orderBot s.bot_mem

instance [BoundedOrder α] (s : Flag α) : BoundedOrder s :=
  Subtype.boundedOrder s.bot_mem s.top_mem

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α]

theorem chain_lt (s : Flag α) : IsChain (· < ·) (s : Set α) := fun a ha b hb h =>
  (s.le_or_le ha hb).imp h.lt_of_le h.lt_of_le'

instance [DecidableEq α] [@DecidableRel α (· ≤ ·)] [@DecidableRel α (· < ·)] (s : Flag α) : LinearOrderₓ s :=
  { Subtype.partialOrder _ with le_total := fun a b => s.le_or_le a.2 b.2, DecidableEq := Subtype.decidableEq,
    decidableLe := Subtype.decidableLe, decidableLt := Subtype.decidableLt }

end PartialOrderₓ

instance [LinearOrderₓ α] : Unique (Flag α) where
  default := ⟨Univ, is_chain_of_trichotomous _, fun s _ => s.subset_univ.antisymm'⟩
  uniq := fun s => SetLike.coe_injective <| s.3 (is_chain_of_trichotomous _) <| subset_univ _

end Flag

