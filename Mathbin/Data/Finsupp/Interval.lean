/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.Finsupp
import Mathbin.Data.Finset.LocallyFinite
import Mathbin.Data.Finsupp.Order

/-!
# Finite intervals of finitely supported functions

This file provides the `locally_finite_order` instance for `ι →₀ α` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.

## Main declarations

* `finsupp.range_singleton`: Postcomposition with `has_singleton.singleton` on `finset` as a
  `finsupp`.
* `finsupp.range_Icc`: Postcomposition with `finset.Icc` as a `finsupp`.

Both these definitions use the fact that `0 = {0}` to ensure that the resulting function is finitely
supported.
-/


noncomputable section

open Finset Finsupp Function

open BigOperators Classical Pointwise

variable {ι α : Type _}

namespace Finsupp

section RangeSingleton

variable [Zero α] {f : ι →₀ α} {i : ι} {a : α}

/-- Pointwise `finset.singleton` bundled as a `finsupp`. -/
@[simps]
def rangeSingleton (f : ι →₀ α) : ι →₀ Finset α where
  toFun := fun i => {f i}
  Support := f.Support
  mem_support_to_fun := fun i => by
    rw [← not_iff_not, not_mem_support_iff, not_ne_iff]
    exact singleton_injective.eq_iff.symm

theorem mem_range_singleton_apply_iff : a ∈ f.rangeSingleton i ↔ a = f i :=
  mem_singleton

end RangeSingleton

section RangeIcc

variable [Zero α] [PartialOrderₓ α] [LocallyFiniteOrder α] {f g : ι →₀ α} {i : ι} {a : α}

/-- Pointwise `finset.Icc` bundled as a `finsupp`. -/
@[simps]
def rangeIcc (f g : ι →₀ α) : ι →₀ Finset α where
  toFun := fun i => icc (f i) (g i)
  Support := f.Support ∪ g.Support
  mem_support_to_fun := fun i => by
    rw [mem_union, ← not_iff_not, not_or_distrib, not_mem_support_iff, not_mem_support_iff, not_ne_iff]
    exact Icc_eq_singleton_iff.symm

theorem mem_range_Icc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i :=
  mem_Icc

end RangeIcc

variable [PartialOrderₓ α] [Zero α] [LocallyFiniteOrder α] (f g : ι →₀ α)

instance : LocallyFiniteOrder (ι →₀ α) :=
  LocallyFiniteOrder.ofIcc (ι →₀ α) (fun f g => (f.Support ∪ g.Support).Finsupp <| f.rangeIcc g) fun f g x => by
    refine' (mem_finsupp_iff_of_support_subset <| subset.rfl).trans _
    simp_rw [mem_range_Icc_apply_iff]
    exact forall_and_distrib

theorem card_Icc : (icc f g).card = ∏ i in f.Support ∪ g.Support, (icc (f i) (g i)).card :=
  card_finsupp _ _

theorem card_Ico : (ico f g).card = (∏ i in f.Support ∪ g.Support, (icc (f i) (g i)).card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

theorem card_Ioc : (ioc f g).card = (∏ i in f.Support ∪ g.Support, (icc (f i) (g i)).card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

theorem card_Ioo : (ioo f g).card = (∏ i in f.Support ∪ g.Support, (icc (f i) (g i)).card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end Finsupp

