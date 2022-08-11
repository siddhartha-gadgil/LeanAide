/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.List.Sort
import Mathbin.Data.Multiset.Basic
import Mathbin.Data.String.Basic

/-!
# Construct a sorted list from a multiset.
-/


namespace Multiset

open List

variable {α : Type _}

section Sort

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]

/-- `sort s` constructs a sorted list from the multiset `s`.
  (Uses merge sort algorithm.) -/
def sort (s : Multiset α) : List α :=
  (Quot.liftOn s (mergeSort r)) fun a b h =>
    eq_of_perm_of_sorted ((perm_merge_sort _ _).trans <| h.trans (perm_merge_sort _ _).symm) (sorted_merge_sort r _)
      (sorted_merge_sort r _)

@[simp]
theorem coe_sort (l : List α) : sort r l = mergeSort r l :=
  rfl

@[simp]
theorem sort_sorted (s : Multiset α) : Sorted r (sort r s) :=
  (Quot.induction_on s) fun l => sorted_merge_sort r _

@[simp]
theorem sort_eq (s : Multiset α) : ↑(sort r s) = s :=
  (Quot.induction_on s) fun l => Quot.sound <| perm_merge_sort _ _

@[simp]
theorem mem_sort {s : Multiset α} {a : α} : a ∈ sort r s ↔ a ∈ s := by
  rw [← mem_coe, sort_eq]

@[simp]
theorem length_sort {s : Multiset α} : (sort r s).length = s.card :=
  Quot.induction_on s <| length_merge_sort _

@[simp]
theorem sort_zero : sort r 0 = [] :=
  List.merge_sort_nil r

@[simp]
theorem sort_singleton (a : α) : sort r {a} = [a] :=
  List.merge_sort_singleton r a

end Sort

instance [HasRepr α] : HasRepr (Multiset α) :=
  ⟨fun s => "{" ++ Stringₓ.intercalate ", " ((s.map reprₓ).sort (· ≤ ·)) ++ "}"⟩

end Multiset

