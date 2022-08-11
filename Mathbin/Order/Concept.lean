/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Set.Lattice

/-!
# Formal concept analysis

This file defines concept lattices. A concept of a relation `r : α → β → Prop` is a pair of sets
`s : set α` and `t : set β` such that `s` is the set of all `a : α` that are related to all elements
of `t`, and `t` is the set of all `b : β` that are related to all elements of `s`.

Ordering the concepts of a relation `r` by inclusion on the first component gives rise to a
*concept lattice*. Every concept lattice is complete and in fact every complete lattice arises as
the concept lattice of its `≤`.

## Implementation notes

Concept lattices are usually defined from a *context*, that is the triple `(α, β, r)`, but the type
of `r` determines `α` and `β` already, so we do not define contexts as a separate object.

## TODO

Prove the fundamental theorem of concept lattices.

## References

* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]

## Tags

concept, formal concept analysis, intent, extend, attribute
-/


open Function OrderDual Set

variable {ι : Sort _} {α β γ : Type _} {κ : ι → Sort _} (r : α → β → Prop) {s s₁ s₂ : Set α} {t t₁ t₂ : Set β}

/-! ### Intent and extent -/


/-- The intent closure of `s : set α` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `s`. -/
def IntentClosure (s : Set α) : Set β :=
  { b | ∀ ⦃a⦄, a ∈ s → r a b }

/-- The extent closure of `t : set β` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `t`. -/
def ExtentClosure (t : Set β) : Set α :=
  { a | ∀ ⦃b⦄, b ∈ t → r a b }

variable {r}

theorem subset_intent_closure_iff_subset_extent_closure : t ⊆ IntentClosure r s ↔ s ⊆ ExtentClosure r t :=
  ⟨fun h a ha b hb => h hb ha, fun h b hb a ha => h ha hb⟩

variable (r)

theorem gc_intent_closure_extent_closure : GaloisConnection (to_dual ∘ IntentClosure r) (ExtentClosure r ∘ of_dual) :=
  fun s t => subset_intent_closure_iff_subset_extent_closure

theorem intent_closure_swap (t : Set β) : IntentClosure (swap r) t = ExtentClosure r t :=
  rfl

theorem extent_closure_swap (s : Set α) : ExtentClosure (swap r) s = IntentClosure r s :=
  rfl

@[simp]
theorem intent_closure_empty : IntentClosure r ∅ = univ :=
  eq_univ_of_forall fun _ _ => False.elim

@[simp]
theorem extent_closure_empty : ExtentClosure r ∅ = univ :=
  intent_closure_empty _

@[simp]
theorem intent_closure_union (s₁ s₂ : Set α) : IntentClosure r (s₁ ∪ s₂) = IntentClosure r s₁ ∩ IntentClosure r s₂ :=
  Set.ext fun _ => ball_or_left_distrib

@[simp]
theorem extent_closure_union (t₁ t₂ : Set β) : ExtentClosure r (t₁ ∪ t₂) = ExtentClosure r t₁ ∩ ExtentClosure r t₂ :=
  intent_closure_union _ _ _

@[simp]
theorem intent_closure_Union (f : ι → Set α) : IntentClosure r (⋃ i, f i) = ⋂ i, IntentClosure r (f i) :=
  (gc_intent_closure_extent_closure r).l_supr

@[simp]
theorem extent_closure_Union (f : ι → Set β) : ExtentClosure r (⋃ i, f i) = ⋂ i, ExtentClosure r (f i) :=
  intent_closure_Union _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem intent_closure_Union₂ (f : ∀ i, κ i → Set α) :
    IntentClosure r (⋃ (i) (j), f i j) = ⋂ (i) (j), IntentClosure r (f i j) :=
  (gc_intent_closure_extent_closure r).l_supr₂

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem extent_closure_Union₂ (f : ∀ i, κ i → Set β) :
    ExtentClosure r (⋃ (i) (j), f i j) = ⋂ (i) (j), ExtentClosure r (f i j) :=
  intent_closure_Union₂ _ _

theorem subset_extent_closure_intent_closure (s : Set α) : s ⊆ ExtentClosure r (IntentClosure r s) :=
  (gc_intent_closure_extent_closure r).le_u_l _

theorem subset_intent_closure_extent_closure (t : Set β) : t ⊆ IntentClosure r (ExtentClosure r t) :=
  subset_extent_closure_intent_closure _ t

@[simp]
theorem intent_closure_extent_closure_intent_closure (s : Set α) :
    IntentClosure r (ExtentClosure r <| IntentClosure r s) = IntentClosure r s :=
  (gc_intent_closure_extent_closure r).l_u_l_eq_l _

@[simp]
theorem extent_closure_intent_closure_extent_closure (t : Set β) :
    ExtentClosure r (IntentClosure r <| ExtentClosure r t) = ExtentClosure r t :=
  intent_closure_extent_closure_intent_closure _ t

theorem intent_closure_anti : Antitone (IntentClosure r) :=
  (gc_intent_closure_extent_closure r).monotone_l

theorem extent_closure_anti : Antitone (ExtentClosure r) :=
  intent_closure_anti _

/-! ### Concepts -/


variable (α β)

/-- The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and `t` is the set of
all elements that are `r`-related to all of `s`. -/
structure Concept extends Set α × Set β where
  closure_fst : IntentClosure r fst = snd
  closure_snd : ExtentClosure r snd = fst

namespace Concept

variable {r α β} {c d : Concept α β r}

attribute [simp] closure_fst closure_snd

@[ext]
theorem ext (h : c.fst = d.fst) : c = d := by
  obtain ⟨⟨s₁, t₁⟩, h₁, _⟩ := c
  obtain ⟨⟨s₂, t₂⟩, h₂, _⟩ := d
  dsimp'  at h₁ h₂ h
  subst h
  subst h₁
  subst h₂

theorem ext' (h : c.snd = d.snd) : c = d := by
  obtain ⟨⟨s₁, t₁⟩, _, h₁⟩ := c
  obtain ⟨⟨s₂, t₂⟩, _, h₂⟩ := d
  dsimp'  at h₁ h₂ h
  subst h
  subst h₁
  subst h₂

theorem fst_injective : Injective fun c : Concept α β r => c.fst := fun c d => ext

theorem snd_injective : Injective fun c : Concept α β r => c.snd := fun c d => ext'

instance : HasSup (Concept α β r) :=
  ⟨fun c d =>
    { fst := ExtentClosure r (c.snd ∩ d.snd), snd := c.snd ∩ d.snd,
      closure_fst := by
        rw [← c.closure_fst, ← d.closure_fst, ← intent_closure_union, intent_closure_extent_closure_intent_closure],
      closure_snd := rfl }⟩

instance : HasInf (Concept α β r) :=
  ⟨fun c d =>
    { fst := c.fst ∩ d.fst, snd := IntentClosure r (c.fst ∩ d.fst), closure_fst := rfl,
      closure_snd := by
        rw [← c.closure_snd, ← d.closure_snd, ← extent_closure_union, extent_closure_intent_closure_extent_closure] }⟩

instance : SemilatticeInf (Concept α β r) :=
  (fst_injective.SemilatticeInf _) fun _ _ => rfl

@[simp]
theorem fst_subset_fst_iff : c.fst ⊆ d.fst ↔ c ≤ d :=
  Iff.rfl

@[simp]
theorem fst_ssubset_fst_iff : c.fst ⊂ d.fst ↔ c < d :=
  Iff.rfl

@[simp]
theorem snd_subset_snd_iff : c.snd ⊆ d.snd ↔ d ≤ c := by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← fst_subset_fst_iff, ← c.closure_snd, ← d.closure_snd]
    exact extent_closure_anti _ h
    
  · rw [← c.closure_fst, ← d.closure_fst]
    exact intent_closure_anti _ h
    

@[simp]
theorem snd_ssubset_snd_iff : c.snd ⊂ d.snd ↔ d < c := by
  rw [ssubset_iff_subset_not_subset, lt_iff_le_not_leₓ, snd_subset_snd_iff, snd_subset_snd_iff]

theorem strict_mono_fst : StrictMono (Prod.fst ∘ to_prod : Concept α β r → Set α) := fun c d => fst_ssubset_fst_iff.2

theorem strict_anti_snd : StrictAnti (Prod.snd ∘ to_prod : Concept α β r → Set β) := fun c d => snd_ssubset_snd_iff.2

instance : Lattice (Concept α β r) :=
  { Concept.semilatticeInf with sup := (·⊔·), le_sup_left := fun c d => snd_subset_snd_iff.1 <| inter_subset_left _ _,
    le_sup_right := fun c d => snd_subset_snd_iff.1 <| inter_subset_right _ _,
    sup_le := fun c d e => by
      simp_rw [← snd_subset_snd_iff]
      exact subset_inter }

instance : BoundedOrder (Concept α β r) where
  top := ⟨⟨Univ, IntentClosure r Univ⟩, rfl, eq_univ_of_forall fun a b hb => hb trivialₓ⟩
  le_top := fun _ => subset_univ _
  bot := ⟨⟨ExtentClosure r Univ, Univ⟩, eq_univ_of_forall fun b a ha => ha trivialₓ, rfl⟩
  bot_le := fun _ => snd_subset_snd_iff.1 <| subset_univ _

instance : HasSupₓ (Concept α β r) :=
  ⟨fun S =>
    { fst := ExtentClosure r (⋂ c ∈ S, (c : Concept _ _ _).snd), snd := ⋂ c ∈ S, (c : Concept _ _ _).snd,
      closure_fst := by
        simp_rw [← closure_fst, ← intent_closure_Union₂, intent_closure_extent_closure_intent_closure],
      closure_snd := rfl }⟩

instance : HasInfₓ (Concept α β r) :=
  ⟨fun S =>
    { fst := ⋂ c ∈ S, (c : Concept _ _ _).fst, snd := IntentClosure r (⋂ c ∈ S, (c : Concept _ _ _).fst),
      closure_fst := rfl,
      closure_snd := by
        simp_rw [← closure_snd, ← extent_closure_Union₂, extent_closure_intent_closure_extent_closure] }⟩

instance : CompleteLattice (Concept α β r) :=
  { Concept.lattice, Concept.boundedOrder with sup := sup,
    le_Sup := fun S c hc => snd_subset_snd_iff.1 <| bInter_subset_of_mem hc,
    Sup_le := fun S c hc => snd_subset_snd_iff.1 <| subset_Inter₂ fun d hd => snd_subset_snd_iff.2 <| hc d hd,
    inf := inf, Inf_le := fun S c => bInter_subset_of_mem, le_Inf := fun S c => subset_Inter₂ }

@[simp]
theorem top_fst : (⊤ : Concept α β r).fst = univ :=
  rfl

@[simp]
theorem top_snd : (⊤ : Concept α β r).snd = IntentClosure r Univ :=
  rfl

@[simp]
theorem bot_fst : (⊥ : Concept α β r).fst = ExtentClosure r Univ :=
  rfl

@[simp]
theorem bot_snd : (⊥ : Concept α β r).snd = univ :=
  rfl

@[simp]
theorem sup_fst (c d : Concept α β r) : (c⊔d).fst = ExtentClosure r (c.snd ∩ d.snd) :=
  rfl

@[simp]
theorem sup_snd (c d : Concept α β r) : (c⊔d).snd = c.snd ∩ d.snd :=
  rfl

@[simp]
theorem inf_fst (c d : Concept α β r) : (c⊓d).fst = c.fst ∩ d.fst :=
  rfl

@[simp]
theorem inf_snd (c d : Concept α β r) : (c⊓d).snd = IntentClosure r (c.fst ∩ d.fst) :=
  rfl

@[simp]
theorem Sup_fst (S : Set (Concept α β r)) : (sup S).fst = ExtentClosure r (⋂ c ∈ S, (c : Concept _ _ _).snd) :=
  rfl

@[simp]
theorem Sup_snd (S : Set (Concept α β r)) : (sup S).snd = ⋂ c ∈ S, (c : Concept _ _ _).snd :=
  rfl

@[simp]
theorem Inf_fst (S : Set (Concept α β r)) : (inf S).fst = ⋂ c ∈ S, (c : Concept _ _ _).fst :=
  rfl

@[simp]
theorem Inf_snd (S : Set (Concept α β r)) : (inf S).snd = IntentClosure r (⋂ c ∈ S, (c : Concept _ _ _).fst) :=
  rfl

instance : Inhabited (Concept α β r) :=
  ⟨⊥⟩

/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps]
def swap (c : Concept α β r) : Concept β α (swap r) :=
  ⟨c.toProd.swap, c.closure_snd, c.closure_fst⟩

@[simp]
theorem swap_swap (c : Concept α β r) : c.swap.swap = c :=
  ext rfl

@[simp]
theorem swap_le_swap_iff : c.swap ≤ d.swap ↔ d ≤ c :=
  snd_subset_snd_iff

@[simp]
theorem swap_lt_swap_iff : c.swap < d.swap ↔ d < c :=
  snd_ssubset_snd_iff

/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps]
def swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  toFun := swap ∘ of_dual
  invFun := to_dual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := fun c d => swap_le_swap_iff

end Concept

