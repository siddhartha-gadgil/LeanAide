/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Data.Finset.Basic
import Mathbin.Data.Set.Pairwise
import Mathbin.Logic.Encodable.Basic

/-!
# Lattice operations on encodable types

Lemmas about lattice and set operations on encodable types

## Implementation Notes

This is a separate file, to avoid unnecessary imports in basic files.

Previously some of these results were in the `measure_theory` folder.
-/


open Set

namespace Encodable

variable {α : Type _} {β : Type _} [Encodable β]

theorem supr_decode₂ [CompleteLattice α] (f : β → α) : (⨆ (i : ℕ) (b ∈ decode₂ β i), f b) = ⨆ b, f b := by
  rw [supr_comm]
  simp [← mem_decode₂]

theorem Union_decode₂ (f : β → Set α) : (⋃ (i : ℕ) (b ∈ decode₂ β i), f b) = ⋃ b, f b :=
  supr_decode₂ f

@[elab_as_eliminator]
theorem Union_decode₂_cases {f : β → Set α} {C : Set α → Prop} (H0 : C ∅) (H1 : ∀ b, C (f b)) {n} :
    C (⋃ b ∈ decode₂ β n, f b) :=
  match decode₂ β n with
  | none => by
    simp
    apply H0
  | some b => by
    convert H1 b
    simp [← ext_iff]

theorem Union_decode₂_disjoint_on {f : β → Set α} (hd : Pairwise (Disjoint on f)) :
    Pairwise (Disjoint on fun i => ⋃ b ∈ decode₂ β i, f b) := by
  rintro i j ij x
  suffices ∀ a, encode a = i → x ∈ f a → ∀ b, encode b = j → x ∉ f b by
    simpa [← decode₂_eq_some]
  rintro a rfl ha b rfl hb
  exact hd a b (mt (congr_arg encode) ij) ⟨ha, hb⟩

end Encodable

namespace Finset

theorem nonempty_encodable {α} (t : Finset α) : Nonempty <| Encodable { i // i ∈ t } := by
  classical
  induction' t using Finset.induction with x t hx ih
  · refine' ⟨⟨fun _ => 0, fun _ => none, fun ⟨x, y⟩ => y.rec _⟩⟩
    
  · cases' ih with ih
    exact ⟨Encodable.ofEquiv _ (Finset.subtypeInsertEquivOption hx)⟩
    

end Finset

