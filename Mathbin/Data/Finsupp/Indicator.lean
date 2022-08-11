/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finsupp.Basic

/-!
# Building finitely supported functions off finsets

This file defines `finsupp.indicator` to help create finsupps from finsets.

## Main declarations

* `finsupp.indicator`: Turns a map from a `finset` into a `finsupp` from the entire type.
-/


noncomputable section

open Finset Function

open Classical

variable {ι α : Type _}

namespace Finsupp

variable [Zero α] {s : Finset ι} (f : ∀, ∀ i ∈ s, ∀, α) {i : ι}

/-- Create an element of `ι →₀ α` from a finset `s` and a function `f` defined on this finset. -/
def indicator (s : Finset ι) (f : ∀, ∀ i ∈ s, ∀, α) : ι →₀ α where
  toFun := fun i => if H : i ∈ s then f i H else 0
  Support := (s.attach.filter fun i : s => f i.1 i.2 ≠ 0).map <| Embedding.subtype _
  mem_support_to_fun := fun i => by
    rw [mem_map, dite_ne_right_iff]
    exact
      ⟨fun ⟨⟨j, hj⟩, hf, rfl⟩ => ⟨hj, (mem_filter.1 hf).2⟩, fun ⟨hi, hf⟩ =>
        ⟨⟨i, hi⟩, mem_filter.2 <| ⟨mem_attach _ _, hf⟩, rfl⟩⟩

theorem indicator_of_mem (hi : i ∈ s) (f : ∀, ∀ i ∈ s, ∀, α) : indicator s f i = f i hi :=
  dif_pos hi

theorem indicator_of_not_mem (hi : i ∉ s) (f : ∀, ∀ i ∈ s, ∀, α) : indicator s f i = 0 :=
  dif_neg hi

variable (s i)

@[simp]
theorem indicator_apply : indicator s f i = if hi : i ∈ s then f i hi else 0 :=
  rfl

theorem indicator_injective : Injective fun f : ∀, ∀ i ∈ s, ∀, α => indicator s f := by
  intro a b h
  ext i hi
  rw [← indicator_of_mem hi a, ← indicator_of_mem hi b]
  exact congr_fun h i

theorem support_indicator_subset : ((indicator s f).Support : Set ι) ⊆ s := by
  intro i hi
  rw [mem_coe, mem_support_iff] at hi
  by_contra
  exact hi (indicator_of_not_mem h _)

end Finsupp

