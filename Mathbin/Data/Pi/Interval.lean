/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.LocallyFinite
import Mathbin.Data.Fintype.Card

/-!
# Intervals in a pi type

This file shows that (dependent) functions to locally finite orders equipped with the pointwise
order are locally finite and calculates the cardinality of their intervals.
-/


open Finset Fintype

open BigOperators

variable {ι : Type _} {α : ι → Type _} [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (α i)] [∀ i, PartialOrderₓ (α i)]
  [∀ i, LocallyFiniteOrder (α i)]

namespace Pi

instance : LocallyFiniteOrder (∀ i, α i) :=
  LocallyFiniteOrder.ofIcc _ (fun a b => pi_finset fun i => icc (a i) (b i)) fun a b x => by
    simp_rw [mem_pi_finset, mem_Icc]
    exact forall_and_distrib

variable (a b : ∀ i, α i)

theorem card_Icc : (icc a b).card = ∏ i, (icc (a i) (b i)).card :=
  card_pi_finset _

theorem card_Ico : (ico a b).card = (∏ i, (icc (a i) (b i)).card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

theorem card_Ioc : (ioc a b).card = (∏ i, (icc (a i) (b i)).card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

theorem card_Ioo : (ioo a b).card = (∏ i, (icc (a i) (b i)).card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end Pi

