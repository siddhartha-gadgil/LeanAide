/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Set.Countable
import Mathbin.Logic.Encodable.Lattice
import Mathbin.Order.ConditionallyCompleteLattice
import Mathbin.Order.Disjointed
import Mathbin.Order.SymmDiff

/-!
# Measurable spaces and measurable functions

This file defines measurable spaces and measurable functions.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them.

Do not add measurability lemmas (which could be tagged with
@[measurability]) to this file, since the measurability tactic is downstream
from here. Use `measure_theory.measurable_space` instead.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function
-/


open Set Encodable Function Equivₓ

open Classical

variable {α β γ δ δ' : Type _} {ι : Sort _} {s t u : Set α}

/-- A measurable space is a space equipped with a σ-algebra. -/
structure MeasurableSpace (α : Type _) where
  MeasurableSet' : Set α → Prop
  measurable_set_empty : measurable_set' ∅
  measurable_set_compl : ∀ s, measurable_set' s → measurable_set' (sᶜ)
  measurable_set_Union : ∀ f : ℕ → Set α, (∀ i, measurable_set' (f i)) → measurable_set' (⋃ i, f i)

attribute [class] MeasurableSpace

instance [h : MeasurableSpace α] : MeasurableSpace αᵒᵈ :=
  h

section

/-- `measurable_set s` means that `s` is measurable (in the ambient measure space on `α`) -/
def MeasurableSet [MeasurableSpace α] : Set α → Prop :=
  ‹MeasurableSpace α›.MeasurableSet'

-- mathport name: «exprmeasurable_set[ ]»
localized [MeasureTheory] notation "measurable_set[" m "]" => @MeasurableSet _ m

@[simp]
theorem MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α) :=
  ‹MeasurableSpace α›.measurable_set_empty

variable {m : MeasurableSpace α}

include m

theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet (sᶜ) :=
  ‹MeasurableSpace α›.measurable_set_compl s

theorem MeasurableSet.of_compl (h : MeasurableSet (sᶜ)) : MeasurableSet s :=
  compl_compl s ▸ h.compl

@[simp]
theorem MeasurableSet.compl_iff : MeasurableSet (sᶜ) ↔ MeasurableSet s :=
  ⟨MeasurableSet.of_compl, MeasurableSet.compl⟩

@[simp]
theorem MeasurableSet.univ : MeasurableSet (Univ : Set α) := by
  simpa using (@MeasurableSet.empty α _).compl

@[nontriviality]
theorem Subsingleton.measurable_set [Subsingleton α] {s : Set α} : MeasurableSet s :=
  Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

theorem MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : MeasurableSet t := by
  rwa [← h]

theorem MeasurableSet.bUnion_decode₂ [Encodable β] ⦃f : β → Set α⦄ (h : ∀ b, MeasurableSet (f b)) (n : ℕ) :
    MeasurableSet (⋃ b ∈ decode₂ β n, f b) :=
  Encodable.Union_decode₂_cases MeasurableSet.empty h

theorem MeasurableSet.Union [Encodable β] ⦃f : β → Set α⦄ (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  by
  rw [← Encodable.Union_decode₂]
  exact ‹MeasurableSpace α›.measurable_set_Union _ (MeasurableSet.bUnion_decode₂ h)

theorem MeasurableSet.bUnion {f : β → Set α} {s : Set β} (hs : s.Countable) (h : ∀, ∀ b ∈ s, ∀, MeasurableSet (f b)) :
    MeasurableSet (⋃ b ∈ s, f b) := by
  rw [bUnion_eq_Union]
  have := hs.to_encodable
  exact
    MeasurableSet.Union
      (by
        simpa using h)

theorem Set.Finite.measurable_set_bUnion {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀, ∀ b ∈ s, ∀, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  MeasurableSet.bUnion hs.Countable h

theorem Finset.measurable_set_bUnion {f : β → Set α} (s : Finset β) (h : ∀, ∀ b ∈ s, ∀, MeasurableSet (f b)) :
    MeasurableSet (⋃ b ∈ s, f b) :=
  s.finite_to_set.measurable_set_bUnion h

theorem MeasurableSet.sUnion {s : Set (Set α)} (hs : s.Countable) (h : ∀, ∀ t ∈ s, ∀, MeasurableSet t) :
    MeasurableSet (⋃₀s) := by
  rw [sUnion_eq_bUnion]
  exact MeasurableSet.bUnion hs h

theorem Set.Finite.measurable_set_sUnion {s : Set (Set α)} (hs : s.Finite) (h : ∀, ∀ t ∈ s, ∀, MeasurableSet t) :
    MeasurableSet (⋃₀s) :=
  MeasurableSet.sUnion hs.Countable h

theorem MeasurableSet.Union_Prop {p : Prop} {f : p → Set α} (hf : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋃ b, f b) := by
  by_cases' p <;> simp [← h, ← hf, ← MeasurableSet.empty]

theorem MeasurableSet.Inter [Encodable β] {f : β → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.compl_iff.1 <| by
    rw [compl_Inter]
    exact MeasurableSet.Union fun b => (h b).compl

section Fintype

attribute [local instance] Fintype.toEncodable

theorem MeasurableSet.Union_fintype [Fintype β] {f : β → Set α} (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋃ b, f b) :=
  MeasurableSet.Union h

theorem MeasurableSet.Inter_fintype [Fintype β] {f : β → Set α} (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋂ b, f b) :=
  MeasurableSet.Inter h

end Fintype

theorem MeasurableSet.bInter {f : β → Set α} {s : Set β} (hs : s.Countable) (h : ∀, ∀ b ∈ s, ∀, MeasurableSet (f b)) :
    MeasurableSet (⋂ b ∈ s, f b) :=
  MeasurableSet.compl_iff.1 <| by
    rw [compl_Inter₂]
    exact MeasurableSet.bUnion hs fun b hb => (h b hb).compl

theorem Set.Finite.measurable_set_bInter {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀, ∀ b ∈ s, ∀, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  MeasurableSet.bInter hs.Countable h

theorem Finset.measurable_set_bInter {f : β → Set α} (s : Finset β) (h : ∀, ∀ b ∈ s, ∀, MeasurableSet (f b)) :
    MeasurableSet (⋂ b ∈ s, f b) :=
  s.finite_to_set.measurable_set_bInter h

theorem MeasurableSet.sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀, ∀ t ∈ s, ∀, MeasurableSet t) :
    MeasurableSet (⋂₀ s) := by
  rw [sInter_eq_bInter]
  exact MeasurableSet.bInter hs h

theorem Set.Finite.measurable_set_sInter {s : Set (Set α)} (hs : s.Finite) (h : ∀, ∀ t ∈ s, ∀, MeasurableSet t) :
    MeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs.Countable h

theorem MeasurableSet.Inter_Prop {p : Prop} {f : p → Set α} (hf : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋂ b, f b) := by
  by_cases' p <;> simp [← h, ← hf, ← MeasurableSet.univ]

@[simp]
theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∪ s₂) :=
  by
  rw [union_eq_Union]
  exact MeasurableSet.Union (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp]
theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∩ s₂) :=
  by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl

@[simp]
theorem MeasurableSet.diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ \ s₂) :=
  h₁.inter h₂.compl

@[simp]
theorem MeasurableSet.symm_diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ∆ s₂) :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp]
theorem MeasurableSet.ite {t s₁ s₂ : Set α} (ht : MeasurableSet t) (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (t.ite s₁ s₂) :=
  (h₁.inter ht).union (h₂.diff ht)

@[simp]
theorem MeasurableSet.cond {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) {i : Bool} :
    MeasurableSet (cond i s₁ s₂) := by
  cases i
  exacts[h₂, h₁]

@[simp]
theorem MeasurableSet.disjointed {f : ℕ → Set α} (h : ∀ i, MeasurableSet (f i)) (n) : MeasurableSet (disjointed f n) :=
  disjointedRecₓ (fun t i ht => MeasurableSet.diff ht <| h _) (h n)

@[simp]
theorem MeasurableSet.const (p : Prop) : MeasurableSet { a : α | p } := by
  by_cases' p <;> simp [← h, ← MeasurableSet.empty] <;> apply MeasurableSet.univ

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
theorem nonempty_measurable_superset (s : Set α) : Nonempty { t // s ⊆ t ∧ MeasurableSet t } :=
  ⟨⟨Univ, subset_univ s, MeasurableSet.univ⟩⟩

end

open MeasureTheory

@[ext]
theorem MeasurableSpace.ext :
    ∀ {m₁ m₂ : MeasurableSpace α}, (∀ s : Set α, measurable_set[m₁] s ↔ measurable_set[m₂] s) → m₁ = m₂
  | ⟨s₁, _, _, _⟩, ⟨s₂, _, _, _⟩, h => by
    have : s₁ = s₂ := funext fun x => propext <| h x
    subst this

@[ext]
theorem MeasurableSpace.ext_iff {m₁ m₂ : MeasurableSpace α} :
    m₁ = m₂ ↔ ∀ s : Set α, measurable_set[m₁] s ↔ measurable_set[m₂] s :=
  ⟨by
    rintro rfl
    intro s
    rfl, MeasurableSpace.ext⟩

/-- A typeclass mixin for `measurable_space`s such that each singleton is measurable. -/
class MeasurableSingletonClass (α : Type _) [MeasurableSpace α] : Prop where
  measurable_set_singleton : ∀ x, MeasurableSet ({x} : Set α)

export MeasurableSingletonClass (measurable_set_singleton)

attribute [simp] measurable_set_singleton

section MeasurableSingletonClass

variable [MeasurableSpace α] [MeasurableSingletonClass α]

theorem measurable_set_eq {a : α} : MeasurableSet { x | x = a } :=
  measurable_set_singleton a

theorem MeasurableSet.insert {s : Set α} (hs : MeasurableSet s) (a : α) : MeasurableSet (insert a s) :=
  (measurable_set_singleton a).union hs

@[simp]
theorem measurable_set_insert {a : α} {s : Set α} : MeasurableSet (insert a s) ↔ MeasurableSet s :=
  ⟨fun h =>
    if ha : a ∈ s then by
      rwa [← insert_eq_of_mem ha]
    else insert_diff_self_of_not_mem ha ▸ h.diff (measurable_set_singleton _),
    fun h => h.insert a⟩

theorem Set.Subsingleton.measurable_set {s : Set α} (hs : s.Subsingleton) : MeasurableSet s :=
  hs.induction_on MeasurableSet.empty measurable_set_singleton

theorem Set.Finite.measurable_set {s : Set α} (hs : s.Finite) : MeasurableSet s :=
  (Finite.induction_on hs MeasurableSet.empty) fun a s ha hsf hsm => hsm.insert _

protected theorem Finset.measurable_set (s : Finset α) : MeasurableSet (↑s : Set α) :=
  s.finite_to_set.MeasurableSet

theorem Set.Countable.measurable_set {s : Set α} (hs : s.Countable) : MeasurableSet s := by
  rw [← bUnion_of_singleton s]
  exact MeasurableSet.bUnion hs fun b hb => measurable_set_singleton b

end MeasurableSingletonClass

namespace MeasurableSpace

section CompleteLattice

instance : LE (MeasurableSpace α) where le := fun m₁ m₂ => ∀ s, measurable_set[m₁] s → measurable_set[m₂] s

theorem le_def {α} {a b : MeasurableSpace α} : a ≤ b ↔ a.MeasurableSet' ≤ b.MeasurableSet' :=
  Iff.rfl

instance : PartialOrderₓ (MeasurableSpace α) :=
  { MeasurableSpace.hasLe, PartialOrderₓ.lift (@MeasurableSet α) fun m₁ m₂ h => ext fun s => h ▸ Iff.rfl with
    lt := fun m₁ m₂ => m₁ ≤ m₂ ∧ ¬m₂ ≤ m₁ }

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive GenerateMeasurable (s : Set (Set α)) : Set α → Prop
  | basic : ∀, ∀ u ∈ s, ∀, generate_measurable u
  | Empty : generate_measurable ∅
  | compl : ∀ s, generate_measurable s → generate_measurable (sᶜ)
  | union : ∀ f : ℕ → Set α, (∀ n, generate_measurable (f n)) → generate_measurable (⋃ i, f i)

/-- Construct the smallest measure space containing a collection of basic sets -/
def generateFrom (s : Set (Set α)) : MeasurableSpace α where
  MeasurableSet' := GenerateMeasurable s
  measurable_set_empty := GenerateMeasurable.empty
  measurable_set_compl := GenerateMeasurable.compl
  measurable_set_Union := GenerateMeasurable.union

theorem measurable_set_generate_from {s : Set (Set α)} {t : Set α} (ht : t ∈ s) : @MeasurableSet _ (generateFrom s) t :=
  GenerateMeasurable.basic t ht

@[elab_as_eliminator]
theorem generate_from_induction (p : Set α → Prop) (C : Set (Set α)) (hC : ∀, ∀ t ∈ C, ∀, p t) (h_empty : p ∅)
    (h_compl : ∀ t, p t → p (tᶜ)) (h_Union : ∀ f : ℕ → Set α, (∀ n, p (f n)) → p (⋃ i, f i)) {s : Set α}
    (hs : measurable_set[generateFrom C] s) : p s := by
  induction hs
  exacts[hC _ hs_H, h_empty, h_compl _ hs_ih, h_Union hs_f hs_ih]

theorem generate_from_le {s : Set (Set α)} {m : MeasurableSpace α} (h : ∀, ∀ t ∈ s, ∀, measurable_set[m] t) :
    generateFrom s ≤ m := fun t (ht : GenerateMeasurable s t) =>
  ht.recOn h (measurable_set_empty m) (fun s _ hs => measurable_set_compl m s hs) fun f _ hf =>
    measurable_set_Union m f hf

theorem generate_from_le_iff {s : Set (Set α)} (m : MeasurableSpace α) :
    generateFrom s ≤ m ↔ s ⊆ { t | measurable_set[m] t } :=
  Iff.intro (fun h u hu => h _ <| measurable_set_generate_from hu) fun h => generate_from_le h

@[simp]
theorem generate_from_measurable_set [MeasurableSpace α] : generateFrom { s : Set α | MeasurableSet s } = ‹_› :=
  (le_antisymmₓ (generate_from_le fun _ => id)) fun s => measurable_set_generate_from

/-- If `g` is a collection of subsets of `α` such that the `σ`-algebra generated from `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra. -/
protected def mkOfClosure (g : Set (Set α)) (hg : { t | measurable_set[generateFrom g] t } = g) :
    MeasurableSpace α where
  MeasurableSet' := fun s => s ∈ g
  measurable_set_empty := hg ▸ measurable_set_empty _
  measurable_set_compl := hg ▸ measurable_set_compl _
  measurable_set_Union := hg ▸ measurable_set_Union _

theorem mk_of_closure_sets {s : Set (Set α)} {hs : { t | measurable_set[generateFrom s] t } = s} :
    MeasurableSpace.mkOfClosure s hs = generateFrom s :=
  MeasurableSpace.ext fun t =>
    show t ∈ s ↔ _ by
      conv_lhs => rw [← hs]
      rfl

/-- We get a Galois insertion between `σ`-algebras on `α` and `set (set α)` by using `generate_from`
  on one side and the collection of measurable sets on the other side. -/
def giGenerateFrom : GaloisInsertion (@generateFrom α) fun m => { t | @MeasurableSet α m t } where
  gc := fun s => generate_from_le_iff
  le_l_u := fun m s => measurable_set_generate_from
  choice := fun g hg => MeasurableSpace.mkOfClosure g <| le_antisymmₓ hg <| (generate_from_le_iff _).1 le_rfl
  choice_eq := fun g hg => mk_of_closure_sets

instance : CompleteLattice (MeasurableSpace α) :=
  giGenerateFrom.liftCompleteLattice

instance : Inhabited (MeasurableSpace α) :=
  ⟨⊤⟩

@[mono]
theorem generate_from_mono {s t : Set (Set α)} (h : s ⊆ t) : generateFrom s ≤ generateFrom t :=
  giGenerateFrom.gc.monotone_l h

theorem generate_from_sup_generate_from {s t : Set (Set α)} : generateFrom s⊔generateFrom t = generateFrom (s ∪ t) :=
  (@giGenerateFrom α).gc.l_sup.symm

@[simp]
theorem generate_from_insert_univ (S : Set (Set α)) : generateFrom (insert Set.Univ S) = generateFrom S := by
  refine' le_antisymmₓ _ (generate_from_mono (Set.subset_insert _ _))
  rw [generate_from_le_iff]
  intro t ht
  cases ht
  · rw [ht]
    exact MeasurableSet.univ
    
  · exact measurable_set_generate_from ht
    

@[simp]
theorem generate_from_insert_empty (S : Set (Set α)) : generateFrom (insert ∅ S) = generateFrom S := by
  refine' le_antisymmₓ _ (generate_from_mono (Set.subset_insert _ _))
  rw [generate_from_le_iff]
  intro t ht
  cases ht
  · rw [ht]
    exact @MeasurableSet.empty _ (generate_from S)
    
  · exact measurable_set_generate_from ht
    

theorem measurable_set_bot_iff {s : Set α} : @MeasurableSet α ⊥ s ↔ s = ∅ ∨ s = univ :=
  let b : MeasurableSpace α :=
    { MeasurableSet' := fun s => s = ∅ ∨ s = univ, measurable_set_empty := Or.inl rfl,
      measurable_set_compl := by
        simp (config := { contextual := true })[← or_imp_distrib],
      measurable_set_Union := fun f hf =>
        Classical.by_cases
          (fun h : ∃ i, f i = univ =>
            let ⟨i, hi⟩ := h
            Or.inr <| eq_univ_of_univ_subset <| hi ▸ le_supr f i)
          fun h : ¬∃ i, f i = univ =>
          Or.inl <|
            eq_empty_of_subset_empty <|
              Union_subset fun i =>
                (hf i).elim
                  (by
                    simp (config := { contextual := true }))
                  fun hi => False.elim <| h ⟨i, hi⟩ }
  have : b = ⊥ :=
    bot_unique fun s hs =>
      hs.elim (fun s => s.symm ▸ @measurable_set_empty _ ⊥) fun s => s.symm ▸ @MeasurableSet.univ _ ⊥
  this ▸ Iff.rfl

@[simp]
theorem measurable_set_top {s : Set α} : @MeasurableSet _ ⊤ s :=
  trivialₓ

@[simp]
theorem measurable_set_inf {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    @MeasurableSet _ (m₁⊓m₂) s ↔ @MeasurableSet _ m₁ s ∧ @MeasurableSet _ m₂ s :=
  Iff.rfl

@[simp]
theorem measurable_set_Inf {ms : Set (MeasurableSpace α)} {s : Set α} :
    @MeasurableSet _ (inf ms) s ↔ ∀, ∀ m ∈ ms, ∀, @MeasurableSet _ m s :=
  show s ∈ ⋂₀ _ ↔ _ by
    simp

@[simp]
theorem measurable_set_infi {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    @MeasurableSet _ (infi m) s ↔ ∀ i, @MeasurableSet _ (m i) s := by
  rw [infi, measurable_set_Inf, forall_range_iff]

theorem measurable_set_sup {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    measurable_set[m₁⊔m₂] s ↔ GenerateMeasurable (measurable_set[m₁] ∪ measurable_set[m₂]) s :=
  Iff.refl _

theorem measurable_set_Sup {ms : Set (MeasurableSpace α)} {s : Set α} :
    measurable_set[sup ms] s ↔ GenerateMeasurable { s : Set α | ∃ m ∈ ms, measurable_set[m] s } s := by
  change @measurable_set' _ (generate_from <| ⋃₀_) _ ↔ _
  simp [← generate_from, set_of_exists]

theorem measurable_set_supr {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    @MeasurableSet _ (supr m) s ↔ GenerateMeasurable { s : Set α | ∃ i, measurable_set[m i] s } s := by
  simp only [← supr, ← measurable_set_Sup, ← exists_range_iff]

end CompleteLattice

end MeasurableSpace

section MeasurableFunctions

open MeasurableSpace

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)

-- mathport name: «exprmeasurable[ ]»
localized [MeasureTheory] notation "measurable[" m "]" => @Measurable _ _ m _

theorem measurable_id {ma : MeasurableSpace α} : Measurable (@id α) := fun t => id

theorem measurable_id' {ma : MeasurableSpace α} : Measurable fun a : α => a :=
  measurable_id

theorem Measurable.comp {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {g : β → γ}
    {f : α → β} (hg : Measurable g) (hf : Measurable f) : Measurable (g ∘ f) := fun t ht => hf (hg ht)

@[simp]
theorem measurable_const {ma : MeasurableSpace α} {mb : MeasurableSpace β} {a : α} : Measurable fun b : β => a :=
  fun s hs => MeasurableSet.const (a ∈ s)

theorem Measurable.le {α} {m m0 : MeasurableSpace α} {mb : MeasurableSpace β} (hm : m ≤ m0) {f : α → β}
    (hf : measurable[m] f) : measurable[m0] f := fun s hs => hm _ (hf hs)

end MeasurableFunctions

