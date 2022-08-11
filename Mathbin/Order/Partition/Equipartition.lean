/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Data.Set.Equitable
import Mathbin.Order.Partition.Finpartition

/-!
# Finite equipartitions

This file defines finite equipartitions, the partitions whose parts all are the same size up to a
difference of `1`.

## Main declarations

* `finpartition.is_equipartition`: Predicate for a `finpartition` to be an equipartition.
-/


open Finset Fintype

namespace Finpartition

variable {α : Type _} [DecidableEq α] {s t : Finset α} (P : Finpartition s)

/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
def IsEquipartition : Prop :=
  (P.parts : Set (Finset α)).EquitableOn card

theorem is_equipartition_iff_card_parts_eq_average :
    P.IsEquipartition ↔
      ∀ a : Finset α, a ∈ P.parts → a.card = s.card / P.parts.card ∨ a.card = s.card / P.parts.card + 1 :=
  by
  simp_rw [is_equipartition, Finset.equitable_on_iff, P.sum_card_parts]

variable {P}

theorem _root_.set.subsingleton.is_equipartition (h : (P.parts : Set (Finset α)).Subsingleton) : P.IsEquipartition :=
  h.EquitableOn _

theorem IsEquipartition.card_parts_eq_average (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card = s.card / P.parts.card ∨ t.card = s.card / P.parts.card + 1 :=
  P.is_equipartition_iff_card_parts_eq_average.1 hP _ ht

theorem IsEquipartition.average_le_card_part (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    s.card / P.parts.card ≤ t.card := by
  rw [← P.sum_card_parts]
  exact equitable_on.le hP ht

theorem IsEquipartition.card_part_le_average_add_one (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card ≤ s.card / P.parts.card + 1 := by
  rw [← P.sum_card_parts]
  exact equitable_on.le_add_one hP ht

/-! ### Discrete and indiscrete finpartition -/


variable (s)

theorem bot_is_equipartition : (⊥ : Finpartition s).IsEquipartition :=
  Set.equitable_on_iff_exists_eq_eq_add_one.2
    ⟨1, by
      simp ⟩

theorem top_is_equipartition : (⊤ : Finpartition s).IsEquipartition :=
  (parts_top_subsingleton _).IsEquipartition

theorem indiscrete_is_equipartition {hs : s ≠ ∅} : (indiscrete hs).IsEquipartition := by
  rw [is_equipartition, indiscrete_parts, coe_singleton]
  exact Set.equitable_on_singleton s _

end Finpartition

