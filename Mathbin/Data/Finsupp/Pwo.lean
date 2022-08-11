/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Mathbin.Data.Finsupp.Order
import Mathbin.Order.WellFoundedSet

/-!
# Partial well ordering on finsupps

This file contains the fact that finitely supported functions from a fintype are
partially well ordered when the codomain is a linear order that is well ordered.
It is in a separate file for now so as to not add imports to the file `order.well_founded_set`.

## Main statements

* `finsupp.is_pwo` - finitely supported functions from a fintype are partially well ordered when
  the codomain is a linear order that is well ordered

## Tags

Dickson, order, partial well order
-/


/-- A version of **Dickson's lemma** any subset of functions `σ →₀ α` is partially well
ordered, when `σ` is a `fintype` and `α` is a linear well order.
This version uses finsupps on a fintype as it is intended for use with `mv_power_series`.
-/
theorem Finsupp.is_pwo {α σ : Type _} [Zero α] [LinearOrderₓ α] [IsWellOrder α (· < ·)] [Fintype σ] (S : Set (σ →₀ α)) :
    S.IsPwo := by
  rw [← finsupp.equiv_fun_on_fintype.symm.image_preimage S]
  refine' Set.PartiallyWellOrderedOn.image_of_monotone_on (Pi.is_pwo _) fun a b ha hb => id

