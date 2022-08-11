/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Finset.Sort
import Mathbin.Data.Fintype.Basic

/-!
# Sorting a finite type

This file provides two equivalences for linearly ordered fintypes:
* `mono_equiv_of_fin`: Order isomorphism between `α` and `fin (card α)`.
* `fin_sum_equiv_of_finset`: Equivalence between `α` and `fin m ⊕ fin n` where `m` and `n` are
  respectively the cardinalities of some `finset α` and its complement.
-/


open Finset

/-- Given a linearly ordered fintype `α` of cardinal `k`, the order isomorphism
`mono_equiv_of_fin α h` is the increasing bijection between `fin k` and `α`. Here, `h` is a proof
that the cardinality of `α` is `k`. We use this instead of an isomorphism `fin (card α) ≃o α` to
avoid casting issues in further uses of this function. -/
def monoEquivOfFin (α : Type _) [Fintype α] [LinearOrderₓ α] {k : ℕ} (h : Fintype.card α = k) : Finₓ k ≃o α :=
  (univ.orderIsoOfFin h).trans <| (OrderIso.setCongr _ _ coe_univ).trans OrderIso.Set.univ

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrderₓ α] {m n : ℕ} {s : Finset α}

/-- If `α` is a linearly ordered fintype, `s : finset α` has cardinality `m` and its complement has
cardinality `n`, then `fin m ⊕ fin n ≃ α`. The equivalence sends elements of `fin m` to
elements of `s` and elements of `fin n` to elements of `sᶜ` while preserving order on each
"half" of `fin m ⊕ fin n` (using `set.order_iso_of_fin`). -/
def finSumEquivOfFinset (hm : s.card = m) (hn : sᶜ.card = n) : Sum (Finₓ m) (Finₓ n) ≃ α :=
  calc
    Sum (Finₓ m) (Finₓ n) ≃ Sum (s : Set α) (sᶜ : Set α) :=
      Equivₓ.sumCongr (s.orderIsoOfFin hm).toEquiv <| (sᶜ.orderIsoOfFin hn).toEquiv.trans <| Equivₓ.Set.ofEq s.coe_compl
    _ ≃ α := Equivₓ.Set.sumCompl _
    

@[simp]
theorem fin_sum_equiv_of_finset_inl (hm : s.card = m) (hn : sᶜ.card = n) (i : Finₓ m) :
    finSumEquivOfFinset hm hn (Sum.inl i) = s.orderEmbOfFin hm i :=
  rfl

@[simp]
theorem fin_sum_equiv_of_finset_inr (hm : s.card = m) (hn : sᶜ.card = n) (i : Finₓ n) :
    finSumEquivOfFinset hm hn (Sum.inr i) = sᶜ.orderEmbOfFin hn i :=
  rfl

