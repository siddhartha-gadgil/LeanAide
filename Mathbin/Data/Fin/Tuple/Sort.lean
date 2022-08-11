/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Data.Fin.Basic
import Mathbin.Data.Finset.Sort
import Mathbin.Data.Prod.Lex

/-!

# Sorting tuples by their values

Given an `n`-tuple `f : fin n → α` where `α` is ordered,
we may want to turn it into a sorted `n`-tuple.
This file provides an API for doing so, with the sorted `n`-tuple given by
`f ∘ tuple.sort f`.

## Main declarations

* `tuple.sort`: given `f : fin n → α`, produces a permutation on `fin n`
* `tuple.monotone_sort`: `f ∘ tuple.sort f` is `monotone`

-/


namespace Tuple

variable {n : ℕ}

variable {α : Type _} [LinearOrderₓ α]

/-- `graph f` produces the finset of pairs `(f i, i)`
equipped with the lexicographic order.
-/
def graph (f : Finₓ n → α) : Finset (α ×ₗ Finₓ n) :=
  Finset.univ.Image fun i => (f i, i)

/-- Given `p : α ×ₗ (fin n) := (f i, i)` with `p ∈ graph f`,
`graph.proj p` is defined to be `f i`.
-/
def graph.proj {f : Finₓ n → α} : graph f → α := fun p => p.1.1

@[simp]
theorem graph.card (f : Finₓ n → α) : (graph f).card = n := by
  rw [graph, Finset.card_image_of_injective]
  · exact Finset.card_fin _
    
  · intro _ _
    simp
    

/-- `graph_equiv₁ f` is the natural equivalence between `fin n` and `graph f`,
mapping `i` to `(f i, i)`. -/
def graphEquiv₁ (f : Finₓ n → α) : Finₓ n ≃ graph f where
  toFun := fun i =>
    ⟨(f i, i), by
      simp [← graph]⟩
  invFun := fun p => p.1.2
  left_inv := fun i => by
    simp
  right_inv := fun ⟨⟨x, i⟩, h⟩ => by
    simpa [← graph] using h

@[simp]
theorem proj_equiv₁' (f : Finₓ n → α) : graph.proj ∘ graphEquiv₁ f = f :=
  rfl

/-- `graph_equiv₂ f` is an equivalence between `fin n` and `graph f` that respects the order.
-/
def graphEquiv₂ (f : Finₓ n → α) : Finₓ n ≃o graph f :=
  Finset.orderIsoOfFin _
    (by
      simp )

/-- `sort f` is the permutation that orders `fin n` according to the order of the outputs of `f`. -/
def sort (f : Finₓ n → α) : Equivₓ.Perm (Finₓ n) :=
  (graphEquiv₂ f).toEquiv.trans (graphEquiv₁ f).symm

theorem self_comp_sort (f : Finₓ n → α) : f ∘ sort f = graph.proj ∘ graphEquiv₂ f :=
  show graph.proj ∘ (graphEquiv₁ f ∘ (graphEquiv₁ f).symm) ∘ (graphEquiv₂ f).toEquiv = _ by
    simp

theorem monotone_proj (f : Finₓ n → α) : Monotone (graph.proj : graph f → α) := by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (h | h)
  · exact le_of_ltₓ ‹_›
    
  · simp [← graph.proj]
    

theorem monotone_sort (f : Finₓ n → α) : Monotone (f ∘ sort f) := by
  rw [self_comp_sort]
  exact (monotone_proj f).comp (graph_equiv₂ f).Monotone

end Tuple

