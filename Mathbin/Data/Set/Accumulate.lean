/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Data.Set.Lattice

/-!
# Accumulate

The function `accumulate` takes a set `s` and returns `⋃ y ≤ x, s y`.
-/


variable {α β γ : Type _} {s : α → Set β} {t : α → Set γ}

namespace Set

/-- `accumulate s` is the union of `s y` for `y ≤ x`. -/
def Accumulate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋃ y ≤ x, s y

variable {s}

theorem accumulate_def [LE α] {x : α} : Accumulate s x = ⋃ y ≤ x, s y :=
  rfl

@[simp]
theorem mem_accumulate [LE α] {x : α} {z : β} : z ∈ Accumulate s x ↔ ∃ y ≤ x, z ∈ s y :=
  mem_Union₂

theorem subset_accumulate [Preorderₓ α] {x : α} : s x ⊆ Accumulate s x := fun z => mem_bUnion le_rfl

theorem monotone_accumulate [Preorderₓ α] : Monotone (Accumulate s) := fun x y hxy =>
  bUnion_subset_bUnion_left fun z hz => le_transₓ hz hxy

theorem bUnion_accumulate [Preorderₓ α] (x : α) : (⋃ y ≤ x, Accumulate s y) = ⋃ y ≤ x, s y := by
  apply subset.antisymm
  · exact Union₂_subset fun y hy => monotone_accumulate hy
    
  · exact Union₂_mono fun y hy => subset_accumulate
    

theorem Union_accumulate [Preorderₓ α] : (⋃ x, Accumulate s x) = ⋃ x, s x := by
  apply subset.antisymm
  · simp only [← subset_def, ← mem_Union, ← exists_imp_distrib, ← mem_accumulate]
    intro z x x' hx'x hz
    exact ⟨x', hz⟩
    
  · exact Union_mono fun i => subset_accumulate
    

end Set

