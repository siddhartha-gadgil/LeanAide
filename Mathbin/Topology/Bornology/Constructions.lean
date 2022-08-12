/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Topology.Bornology.Basic

/-!
# Bornology structure on products and subtypes

In this file we define `bornology` and `bounded_space` instances on `α × β`, `Π i, π i`, and
`{x // p x}`. We also prove basic lemmas about `bornology.cobounded` and `bornology.is_bounded`
on these types.
-/


open Set Filter Bornology Function

open Filter

variable {α β ι : Type _} {π : ι → Type _} [Fintype ι] [Bornology α] [Bornology β] [∀ i, Bornology (π i)]

instance : Bornology (α × β) where
  cobounded := (cobounded α).coprod (cobounded β)
  le_cofinite := @coprod_cofinite α β ▸ coprod_mono ‹Bornology α›.le_cofinite ‹Bornology β›.le_cofinite

instance : Bornology (∀ i, π i) where
  cobounded := Filter.coprodₓ fun i => cobounded (π i)
  le_cofinite := @Coprod_cofinite ι π _ ▸ Filter.Coprod_mono fun i => Bornology.le_cofinite _

/-- Inverse image of a bornology. -/
@[reducible]
def Bornology.induced {α β : Type _} [Bornology β] (f : α → β) : Bornology α where
  cobounded := comap f (cobounded β)
  le_cofinite := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)

instance {p : α → Prop} : Bornology (Subtype p) :=
  Bornology.induced (coe : Subtype p → α)

namespace Bornology

/-!
### Bounded sets in `α × β`
-/


theorem cobounded_prod : cobounded (α × β) = (cobounded α).coprod (cobounded β) :=
  rfl

theorem is_bounded_image_fst_and_snd {s : Set (α × β)} :
    IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded s :=
  compl_mem_coprod.symm

variable {s : Set α} {t : Set β} {S : ∀ i, Set (π i)}

theorem IsBounded.fst_of_prod (h : IsBounded (s ×ˢ t)) (ht : t.Nonempty) : IsBounded s :=
  fst_image_prod s ht ▸ (is_bounded_image_fst_and_snd.2 h).1

theorem IsBounded.snd_of_prod (h : IsBounded (s ×ˢ t)) (hs : s.Nonempty) : IsBounded t :=
  snd_image_prod hs t ▸ (is_bounded_image_fst_and_snd.2 h).2

theorem IsBounded.prod (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ×ˢ t) :=
  is_bounded_image_fst_and_snd.1 ⟨hs.Subset <| fst_image_prod_subset _ _, ht.Subset <| snd_image_prod_subset _ _⟩

theorem is_bounded_prod_of_nonempty (hne : Set.Nonempty (s ×ˢ t)) : IsBounded (s ×ˢ t) ↔ IsBounded s ∧ IsBounded t :=
  ⟨fun h => ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, fun h => h.1.Prod h.2⟩

theorem is_bounded_prod : IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBounded t := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
    
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp
    
  simp only [← hs.ne_empty, ← ht.ne_empty, ← is_bounded_prod_of_nonempty (hs.prod ht), ← false_orₓ]

theorem is_bounded_prod_self : IsBounded (s ×ˢ s) ↔ IsBounded s := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
    
  exact (is_bounded_prod_of_nonempty (hs.prod hs)).trans (and_selfₓ _)

/-!
### Bounded sets in `Π i, π i`
-/


theorem cobounded_pi : cobounded (∀ i, π i) = Filter.coprodₓ fun i => cobounded (π i) :=
  rfl

theorem forall_is_bounded_image_eval_iff {s : Set (∀ i, π i)} : (∀ i, IsBounded (eval i '' s)) ↔ IsBounded s :=
  compl_mem_Coprod.symm

theorem IsBounded.pi (h : ∀ i, IsBounded (S i)) : IsBounded (pi Univ S) :=
  forall_is_bounded_image_eval_iff.1 fun i => (h i).Subset eval_image_univ_pi_subset

theorem is_bounded_pi_of_nonempty (hne : (pi Univ S).Nonempty) : IsBounded (pi Univ S) ↔ ∀ i, IsBounded (S i) :=
  ⟨fun H i => @eval_image_univ_pi _ _ _ i hne ▸ forall_is_bounded_image_eval_iff.2 H i, IsBounded.pi⟩

theorem is_bounded_pi : IsBounded (pi Univ S) ↔ (∃ i, S i = ∅) ∨ ∀ i, IsBounded (S i) := by
  by_cases' hne : ∃ i, S i = ∅
  · simp [← hne, ← univ_pi_eq_empty_iff.2 hne]
    
  · simp only [← hne, ← false_orₓ]
    simp only [← not_exists, Ne.def, ← ne_empty_iff_nonempty, univ_pi_nonempty_iff] at hne
    exact is_bounded_pi_of_nonempty hne
    

/-!
### Bounded sets in `{x // p x}`
-/


theorem is_bounded_induced {α β : Type _} [Bornology β] {f : α → β} {s : Set α} :
    @IsBounded α (Bornology.induced f) s ↔ IsBounded (f '' s) :=
  compl_mem_comap

theorem is_bounded_image_subtype_coe {p : α → Prop} {s : Set { x // p x }} :
    IsBounded (coe '' s : Set α) ↔ IsBounded s :=
  is_bounded_induced.symm

end Bornology

/-!
### Bounded spaces
-/


open Bornology

instance [BoundedSpace α] [BoundedSpace β] : BoundedSpace (α × β) := by
  simp [cobounded_eq_bot_iff, ← cobounded_prod]

instance [∀ i, BoundedSpace (π i)] : BoundedSpace (∀ i, π i) := by
  simp [cobounded_eq_bot_iff, ← cobounded_pi]

theorem bounded_space_induced_iff {α β : Type _} [Bornology β] {f : α → β} :
    @BoundedSpace α (Bornology.induced f) ↔ IsBounded (Range f) := by
  rw [← is_bounded_univ, is_bounded_induced, image_univ]

theorem bounded_space_subtype_iff {p : α → Prop} : BoundedSpace (Subtype p) ↔ IsBounded { x | p x } := by
  rw [bounded_space_induced_iff, Subtype.range_coe_subtype]

theorem bounded_space_coe_set_iff {s : Set α} : BoundedSpace s ↔ IsBounded s :=
  bounded_space_subtype_iff

alias bounded_space_subtype_iff ↔ _ Bornology.IsBounded.bounded_space_subtype

alias bounded_space_coe_set_iff ↔ _ Bornology.IsBounded.bounded_space_coe

instance [BoundedSpace α] {p : α → Prop} : BoundedSpace (Subtype p) :=
  (IsBounded.all { x | p x }).bounded_space_subtype

