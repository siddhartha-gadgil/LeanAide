/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathbin.Algebra.Tropical.Lattice
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.List.MinMax

/-!

# Tropicalization of finitary operations

This file provides the "big-op" or notation-based finitary operations on tropicalized types.
This allows easy conversion between sums to Infs and prods to sums. Results here are important
for expressing that evaluation of tropical polynomials are the minimum over a finite piecewise
collection of linear functions.

## Main declarations

* `untrop_sum`

## Implementation notes

No concrete (semi)ring is used here, only ones with inferrable order/lattice structure, to support
real, rat, ereal, and others (erat is not yet defined).

Minima over `list α` are defined as producing a value in `with_top α` so proofs about lists do not
directly transfer to minima over multisets or finsets.

-/


open BigOperators

variable {R S : Type _}

open Tropical Finset

theorem List.trop_sum [AddMonoidₓ R] (l : List R) : trop l.Sum = List.prod (l.map trop) := by
  induction' l with hd tl IH
  · simp
    
  · simp [IH]
    

theorem Multiset.trop_sum [AddCommMonoidₓ R] (s : Multiset R) : trop s.Sum = Multiset.prod (s.map trop) :=
  Quotientₓ.induction_on s
    (by
      simpa using List.trop_sum)

theorem trop_sum [AddCommMonoidₓ R] (s : Finset S) (f : S → R) : trop (∑ i in s, f i) = ∏ i in s, trop (f i) := by
  cases s
  convert Multiset.trop_sum _
  simp

theorem List.untrop_prod [AddMonoidₓ R] (l : List (Tropical R)) : untrop l.Prod = List.sum (l.map untrop) := by
  induction' l with hd tl IH
  · simp
    
  · simp [IH]
    

theorem Multiset.untrop_prod [AddCommMonoidₓ R] (s : Multiset (Tropical R)) :
    untrop s.Prod = Multiset.sum (s.map untrop) :=
  Quotientₓ.induction_on s
    (by
      simpa using List.untrop_prod)

theorem untrop_prod [AddCommMonoidₓ R] (s : Finset S) (f : S → Tropical R) :
    untrop (∏ i in s, f i) = ∑ i in s, untrop (f i) := by
  cases s
  convert Multiset.untrop_prod _
  simp

theorem List.trop_minimum [LinearOrderₓ R] (l : List R) : trop l.minimum = List.sum (l.map (trop ∘ coe)) := by
  induction' l with hd tl IH
  · simp
    
  · simp [← List.minimum_cons, IH]
    

theorem Multiset.trop_inf [LinearOrderₓ R] [OrderTop R] (s : Multiset R) : trop s.inf = Multiset.sum (s.map trop) := by
  induction' s using Multiset.induction with s x IH
  · simp
    
  · simp [IH]
    

theorem Finset.trop_inf [LinearOrderₓ R] [OrderTop R] (s : Finset S) (f : S → R) :
    trop (s.inf f) = ∑ i in s, trop (f i) := by
  cases s
  convert Multiset.trop_inf _
  simp

theorem trop_Inf_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S → WithTop R) :
    trop (inf (f '' s)) = ∑ i in s, trop (f i) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [← Set.image_empty, ← coe_empty, ← sum_empty, ← WithTop.cInf_empty, ← trop_top]
    
  rw [← inf'_eq_cInf_image _ h, inf'_eq_inf, s.trop_inf]

theorem trop_infi [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → WithTop R) :
    trop (⨅ i : S, f i) = ∑ i : S, trop (f i) := by
  rw [infi, ← Set.image_univ, ← coe_univ, trop_Inf_image]

theorem Multiset.untrop_sum [LinearOrderₓ R] [OrderTop R] (s : Multiset (Tropical R)) :
    untrop s.Sum = Multiset.inf (s.map untrop) := by
  induction' s using Multiset.induction with s x IH
  · simp
    
  · simpa [IH]
    

theorem Finset.untrop_sum' [LinearOrderₓ R] [OrderTop R] (s : Finset S) (f : S → Tropical R) :
    untrop (∑ i in s, f i) = s.inf (untrop ∘ f) := by
  cases s
  convert Multiset.untrop_sum _
  simpa

theorem untrop_sum_eq_Inf_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S → Tropical (WithTop R)) :
    untrop (∑ i in s, f i) = inf (untrop ∘ f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [← Set.image_empty, ← coe_empty, ← sum_empty, ← WithTop.cInf_empty, ← untrop_zero]
    
  rw [← inf'_eq_cInf_image _ h, inf'_eq_inf, Finset.untrop_sum']

theorem untrop_sum [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → Tropical (WithTop R)) :
    untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) := by
  rw [infi, ← Set.image_univ, ← coe_univ, untrop_sum_eq_Inf_image]

/-- Note we cannot use `i ∈ s` instead of `i : s` here
as it is simply not true on conditionally complete lattices! -/
theorem Finset.untrop_sum [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S → Tropical (WithTop R)) :
    untrop (∑ i in s, f i) = ⨅ i : s, untrop (f i) := by
  simpa [untrop_sum] using sum_attach.symm

