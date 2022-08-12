/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Pnat.Basic

/-!
# Finite intervals of positive naturals

This file proves that `ℕ+` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Pnat

instance : LocallyFiniteOrder ℕ+ :=
  Subtype.locallyFiniteOrder _

namespace Pnat

variable (a b : ℕ+)

theorem Icc_eq_finset_subtype : icc a b = (icc (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl

theorem Ico_eq_finset_subtype : ico a b = (ico (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl

theorem Ioc_eq_finset_subtype : ioc a b = (ioc (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl

theorem Ioo_eq_finset_subtype : ioo a b = (ioo (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl

theorem map_subtype_embedding_Icc : (icc a b).map (Function.Embedding.subtype _) = icc (a : ℕ) b :=
  map_subtype_embedding_Icc _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ico : (ico a b).map (Function.Embedding.subtype _) = ico (a : ℕ) b :=
  map_subtype_embedding_Ico _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ioc : (ioc a b).map (Function.Embedding.subtype _) = ioc (a : ℕ) b :=
  map_subtype_embedding_Ioc _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ioo : (ioo a b).map (Function.Embedding.subtype _) = ioo (a : ℕ) b :=
  map_subtype_embedding_Ioo _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx

@[simp]
theorem card_Icc : (icc a b).card = b + 1 - a := by
  rw [← Nat.card_Icc, ← map_subtype_embedding_Icc, card_map]

@[simp]
theorem card_Ico : (ico a b).card = b - a := by
  rw [← Nat.card_Ico, ← map_subtype_embedding_Ico, card_map]

@[simp]
theorem card_Ioc : (ioc a b).card = b - a := by
  rw [← Nat.card_Ioc, ← map_subtype_embedding_Ioc, card_map]

@[simp]
theorem card_Ioo : (ioo a b).card = b - a - 1 := by
  rw [← Nat.card_Ioo, ← map_subtype_embedding_Ioo, card_map]

@[simp]
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_of_finset]

@[simp]
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_of_finset]

@[simp]
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_of_finset]

@[simp]
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_of_finset]

end Pnat

