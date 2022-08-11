/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Sigma.Order
import Mathbin.Order.LocallyFinite

/-!
# Finite intervals in a sigma type

This file provides the `locally_finite_order` instance for the disjoint sum of orders `Σ i, α i` and
calculates the cardinality of its finite intervals.

## TODO

Do the same for the lexicographical order
-/


open Finset Function

namespace Sigma

variable {ι : Type _} {α : ι → Type _}

/-! ### Disjoint sum of orders -/


section Disjoint

variable [DecidableEq ι] [∀ i, Preorderₓ (α i)] [∀ i, LocallyFiniteOrder (α i)]

instance : LocallyFiniteOrder (Σi, α i) where
  finsetIcc := sigmaLift fun _ => icc
  finsetIco := sigmaLift fun _ => ico
  finsetIoc := sigmaLift fun _ => ioc
  finsetIoo := sigmaLift fun _ => ioo
  finset_mem_Icc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigma_lift, le_def, mem_Icc, exists_and_distrib_left, ← exists_and_distrib_right, ← exists_prop]
    exact
      bex_congr fun _ _ => by
        constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ico := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ico, exists_and_distrib_left, ← exists_and_distrib_right, ←
      exists_prop]
    exact
      bex_congr fun _ _ => by
        constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ioc, exists_and_distrib_left, ← exists_and_distrib_right, ←
      exists_prop]
    exact
      bex_congr fun _ _ => by
        constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioo := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigma_lift, lt_def, mem_Ioo, exists_and_distrib_left, ← exists_and_distrib_right, ← exists_prop]
    exact
      bex_congr fun _ _ => by
        constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩

section

variable (a b : Σi, α i)

theorem card_Icc : (icc a b).card = if h : a.1 = b.1 then (icc (h.rec a.2) b.2).card else 0 :=
  card_sigma_lift _ _ _

theorem card_Ico : (ico a b).card = if h : a.1 = b.1 then (ico (h.rec a.2) b.2).card else 0 :=
  card_sigma_lift _ _ _

theorem card_Ioc : (ioc a b).card = if h : a.1 = b.1 then (ioc (h.rec a.2) b.2).card else 0 :=
  card_sigma_lift _ _ _

theorem card_Ioo : (ioo a b).card = if h : a.1 = b.1 then (ioo (h.rec a.2) b.2).card else 0 :=
  card_sigma_lift _ _ _

end

variable (i : ι) (a b : α i)

@[simp]
theorem Icc_mk_mk : icc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (icc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
theorem Ico_mk_mk : ico (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (ico a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
theorem Ioc_mk_mk : ioc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (ioc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
theorem Ioo_mk_mk : ioo (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (ioo a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

end Disjoint

end Sigma

