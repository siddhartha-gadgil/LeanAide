/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Order.ConditionallyCompleteLattice
import Mathbin.Data.Int.LeastGreatest

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/


open Int

open Classical

noncomputable section

instance : ConditionallyCompleteLinearOrder ℤ :=
  { Int.linearOrder, LinearOrderₓ.toLattice with
    sup := fun s =>
      if h : s.Nonempty ∧ BddAbove s then greatestOfBdd (Classical.some h.2) (Classical.some_spec h.2) h.1 else 0,
    inf := fun s =>
      if h : s.Nonempty ∧ BddBelow s then leastOfBdd (Classical.some h.2) (Classical.some_spec h.2) h.1 else 0,
    le_cSup := by
      intro s n hs hns
      have : s.nonempty ∧ BddAbove s := ⟨⟨n, hns⟩, hs⟩
      rw [dif_pos this]
      exact (greatest_of_bdd _ _ _).2.2 n hns,
    cSup_le := by
      intro s n hs hns
      have : s.nonempty ∧ BddAbove s := ⟨hs, ⟨n, hns⟩⟩
      rw [dif_pos this]
      exact hns (greatest_of_bdd _ (Classical.some_spec this.2) _).2.1,
    cInf_le := by
      intro s n hs hns
      have : s.nonempty ∧ BddBelow s := ⟨⟨n, hns⟩, hs⟩
      rw [dif_pos this]
      exact (least_of_bdd _ _ _).2.2 n hns,
    le_cInf := by
      intro s n hs hns
      have : s.nonempty ∧ BddBelow s := ⟨hs, ⟨n, hns⟩⟩
      rw [dif_pos this]
      exact hns (least_of_bdd _ (Classical.some_spec this.2) _).2.1 }

namespace Int

theorem cSup_eq_greatest_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀, ∀ z ∈ s, ∀, z ≤ b)
    (Hinh : ∃ z : ℤ, z ∈ s) : sup s = greatestOfBdd b Hb Hinh := by
  convert dif_pos _ using 1
  · convert coe_greatest_of_bdd_eq _ (Classical.some_spec (⟨b, Hb⟩ : BddAbove s)) _
    
  · exact ⟨Hinh, b, Hb⟩
    

@[simp]
theorem cSup_empty : sup (∅ : Set ℤ) = 0 :=
  dif_neg
    (by
      simp )

theorem cSup_of_not_bdd_above {s : Set ℤ} (h : ¬BddAbove s) : sup s = 0 :=
  dif_neg
    (by
      simp [← h])

theorem cInf_eq_least_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀, ∀ z ∈ s, ∀, b ≤ z)
    (Hinh : ∃ z : ℤ, z ∈ s) : inf s = leastOfBdd b Hb Hinh := by
  convert dif_pos _ using 1
  · convert coe_least_of_bdd_eq _ (Classical.some_spec (⟨b, Hb⟩ : BddBelow s)) _
    
  · exact ⟨Hinh, b, Hb⟩
    

@[simp]
theorem cInf_empty : inf (∅ : Set ℤ) = 0 :=
  dif_neg
    (by
      simp )

theorem cInf_of_not_bdd_below {s : Set ℤ} (h : ¬BddBelow s) : inf s = 0 :=
  dif_neg
    (by
      simp [← h])

theorem cSup_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddAbove s) : sup s ∈ s := by
  convert (greatest_of_bdd _ (Classical.some_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩

theorem cInf_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddBelow s) : inf s ∈ s := by
  convert (least_of_bdd _ (Classical.some_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩

end Int

