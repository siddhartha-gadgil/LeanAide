/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Data.Finset.Lattice
import Mathbin.Data.Set.Sigma

/-!
# Finite sets in a sigma type

This file defines a few `finset` constructions on `Σ i, α i`.

## Main declarations

* `finset.sigma`: Given a finset `s` in `ι` and finsets `t i` in each `α i`, `s.sigma t` is the
  finset of the dependent sum `Σ i, α i`
* `finset.sigma_lift`: Lifts maps `α i → β i → finset (γ i)` to a map
  `Σ i, α i → Σ i, β i → finset (Σ i, γ i)`.

## TODO

`finset.sigma_lift` can be generalized to any alternative functor. But to make the generalization
worth it, we must first refactor the functor library so that the `alternative` instance for `finset`
is computable and universe-polymorphic.
-/


open Function Multiset

variable {ι : Type _}

namespace Finset

section Sigma

variable {α : ι → Type _} {β : Type _} (s s₁ s₂ : Finset ι) (t t₁ t₂ : ∀ i, Finset (α i))

/-- `s.sigma t` is the finset of dependent pairs `⟨i, a⟩` such that `i ∈ s` and `a ∈ t i`. -/
protected def sigma : Finset (Σi, α i) :=
  ⟨_, s.Nodup.Sigma fun i => (t i).Nodup⟩

variable {s s₁ s₂ t t₁ t₂}

@[simp]
theorem mem_sigma {a : Σi, α i} : a ∈ s.Sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1 :=
  mem_sigma

@[simp, norm_cast]
theorem coe_sigma (s : Finset ι) (t : ∀ i, Finset (α i)) :
    (s.Sigma t : Set (Σi, α i)) = (s : Set ι).Sigma fun i => t i :=
  Set.ext fun _ => mem_sigma

@[simp]
theorem sigma_nonempty : (s.Sigma t).Nonempty ↔ ∃ i ∈ s, (t i).Nonempty := by
  simp [← Finset.Nonempty]

@[simp]
theorem sigma_eq_empty : s.Sigma t = ∅ ↔ ∀, ∀ i ∈ s, ∀, t i = ∅ := by
  simp only [not_nonempty_iff_eq_empty, ← sigma_nonempty, ← not_exists]

@[mono]
theorem sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.Sigma t₁ ⊆ s₂.Sigma t₂ := fun ⟨i, a⟩ h =>
  let ⟨hi, ha⟩ := mem_sigma.1 h
  mem_sigma.2 ⟨hs hi, ht i ha⟩

theorem sigma_eq_bUnion [DecidableEq (Σi, α i)] (s : Finset ι) (t : ∀ i, Finset (α i)) :
    s.Sigma t = s.bUnion fun i => (t i).map <| Embedding.sigmaMk i := by
  ext ⟨x, y⟩
  simp [← And.left_comm]

variable (s t) (f : (Σi, α i) → β)

theorem sup_sigma [SemilatticeSup β] [OrderBot β] : (s.Sigma t).sup f = s.sup fun i => (t i).sup fun b => f ⟨i, b⟩ := by
  refine' (sup_le _).antisymm (sup_le fun i hi => sup_le fun b hb => le_sup <| mem_sigma.2 ⟨hi, hb⟩)
  rintro ⟨i, b⟩ hb
  rw [mem_sigma] at hb
  refine' le_transₓ _ (le_sup hb.1)
  convert le_sup hb.2

theorem inf_sigma [SemilatticeInf β] [OrderTop β] : (s.Sigma t).inf f = s.inf fun i => (t i).inf fun b => f ⟨i, b⟩ :=
  @sup_sigma _ _ βᵒᵈ _ _ _ _ _

end Sigma

section SigmaLift

variable {α β γ : ι → Type _} [DecidableEq ι]

/-- Lifts maps `α i → β i → finset (γ i)` to a map `Σ i, α i → Σ i, β i → finset (Σ i, γ i)`. -/
def sigmaLift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α) (b : Sigma β) : Finset (Sigma γ) :=
  dite (a.1 = b.1) (fun h => (f (h.rec a.2) b.2).map <| Embedding.sigmaMk _) fun _ => ∅

theorem mem_sigma_lift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α) (b : Sigma β) (x : Sigma γ) :
    x ∈ sigmaLift f a b ↔ ∃ (ha : a.1 = x.1)(hb : b.1 = x.1), x.2 ∈ f (ha.rec a.2) (hb.rec b.2) := by
  obtain ⟨⟨i, a⟩, j, b⟩ := a, b
  obtain rfl | h := Decidable.eq_or_ne i j
  · constructor
    · simp_rw [sigma_lift, dif_pos rfl, mem_map, embedding.sigma_mk_apply]
      rintro ⟨x, hx, rfl⟩
      exact ⟨rfl, rfl, hx⟩
      
    · rintro ⟨⟨⟩, ⟨⟩, hx⟩
      rw [sigma_lift, dif_pos rfl, mem_map]
      exact
        ⟨_, hx, by
          simp [← Sigma.ext_iff]⟩
      
    
  · rw [sigma_lift, dif_neg h]
    refine' iff_of_false (not_mem_empty _) _
    rintro ⟨⟨⟩, ⟨⟩, _⟩
    exact h rfl
    

theorem mk_mem_sigma_lift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (i : ι) (a : α i) (b : β i) (x : γ i) :
    (⟨i, x⟩ : Sigma γ) ∈ sigmaLift f ⟨i, a⟩ ⟨i, b⟩ ↔ x ∈ f a b := by
  rw [sigma_lift, dif_pos rfl, mem_map]
  refine' ⟨_, fun hx => ⟨_, hx, rfl⟩⟩
  rintro ⟨x, hx, _, rfl⟩
  exact hx

theorem not_mem_sigma_lift_of_ne_left (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α) (b : Sigma β) (x : Sigma γ)
    (h : a.1 ≠ x.1) : x ∉ sigmaLift f a b := by
  rw [mem_sigma_lift]
  exact fun H => h H.fst

theorem not_mem_sigma_lift_of_ne_right (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) {a : Sigma α} (b : Sigma β) {x : Sigma γ}
    (h : b.1 ≠ x.1) : x ∉ sigmaLift f a b := by
  rw [mem_sigma_lift]
  exact fun H => h H.snd.fst

variable {f g : ∀ ⦃i⦄, α i → β i → Finset (γ i)} {a : Σi, α i} {b : Σi, β i}

theorem sigma_lift_nonempty : (sigmaLift f a b).Nonempty ↔ ∃ h : a.1 = b.1, (f (h.rec a.2) b.2).Nonempty := by
  simp_rw [nonempty_iff_ne_empty]
  convert dite_ne_right_iff
  ext h
  simp_rw [← nonempty_iff_ne_empty]
  exact map_nonempty.symm

theorem sigma_lift_eq_empty : sigmaLift f a b = ∅ ↔ ∀ h : a.1 = b.1, f (h.rec a.2) b.2 = ∅ := by
  convert dite_eq_right_iff
  exact forall_congr_eq fun h => propext map_eq_empty.symm

theorem sigma_lift_mono (h : ∀ ⦃i⦄ ⦃a : α i⦄ ⦃b : β i⦄, f a b ⊆ g a b) (a : Σi, α i) (b : Σi, β i) :
    sigmaLift f a b ⊆ sigmaLift g a b := by
  rintro x hx
  rw [mem_sigma_lift] at hx⊢
  obtain ⟨ha, hb, hx⟩ := hx
  exact ⟨ha, hb, h hx⟩

variable (f a b)

theorem card_sigma_lift : (sigmaLift f a b).card = dite (a.1 = b.1) (fun h => (f (h.rec a.2) b.2).card) fun _ => 0 := by
  convert apply_dite _ _ _ _
  ext h
  exact (card_map _).symm

end SigmaLift

end Finset

