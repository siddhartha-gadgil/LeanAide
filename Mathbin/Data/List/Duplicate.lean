/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Chris Hughes
-/
import Mathbin.Data.List.Nodup

/-!
# List duplicates

## Main definitions

* `list.duplicate x l : Prop` is an inductive property that holds when `x` is a duplicate in `l`

## Implementation details

In this file, `x ∈+ l` notation is shorthand for `list.duplicate x l`.

-/


variable {α : Type _}

namespace List

/-- Property that an element `x : α` of `l : list α` can be found in the list more than once. -/
inductive Duplicate (x : α) : List α → Prop
  | cons_mem {l : List α} : x ∈ l → duplicate (x :: l)
  | cons_duplicate {y : α} {l : List α} : duplicate l → duplicate (y :: l)

-- mathport name: «expr ∈+ »
local infixl:50 " ∈+ " => List.Duplicate

variable {l : List α} {x : α}

theorem Memₓ.duplicate_cons_self (h : x ∈ l) : x ∈+ x :: l :=
  Duplicate.cons_mem h

theorem Duplicate.duplicate_cons (h : x ∈+ l) (y : α) : x ∈+ y :: l :=
  Duplicate.cons_duplicate h

theorem Duplicate.mem (h : x ∈+ l) : x ∈ l := by
  induction' h with l' h y l' h hm
  · exact mem_cons_self _ _
    
  · exact mem_cons_of_mem _ hm
    

theorem Duplicate.mem_cons_self (h : x ∈+ x :: l) : x ∈ l := by
  cases' h with _ h _ _ h
  · exact h
    
  · exact h.mem
    

@[simp]
theorem duplicate_cons_self_iff : x ∈+ x :: l ↔ x ∈ l :=
  ⟨Duplicate.mem_cons_self, Memₓ.duplicate_cons_self⟩

theorem Duplicate.ne_nil (h : x ∈+ l) : l ≠ [] := fun H => (mem_nil_iffₓ x).mp (H ▸ h.Mem)

@[simp]
theorem not_duplicate_nil (x : α) : ¬x ∈+ [] := fun H => H.ne_nil rfl

theorem Duplicate.ne_singleton (h : x ∈+ l) (y : α) : l ≠ [y] := by
  induction' h with l' h z l' h hm
  · simp [← ne_nil_of_mem h]
    
  · simp [← ne_nil_of_mem h.mem]
    

@[simp]
theorem not_duplicate_singleton (x y : α) : ¬x ∈+ [y] := fun H => H.ne_singleton _ rfl

theorem Duplicate.elim_nil (h : x ∈+ []) : False :=
  not_duplicate_nil x h

theorem Duplicate.elim_singleton {y : α} (h : x ∈+ [y]) : False :=
  not_duplicate_singleton x y h

theorem duplicate_cons_iff {y : α} : x ∈+ y :: l ↔ y = x ∧ x ∈ l ∨ x ∈+ l := by
  refine' ⟨fun h => _, fun h => _⟩
  · cases' h with _ hm _ _ hm
    · exact Or.inl ⟨rfl, hm⟩
      
    · exact Or.inr hm
      
    
  · rcases h with (⟨rfl | h⟩ | h)
    · simpa
      
    · exact h.cons_duplicate
      
    

theorem Duplicate.of_duplicate_cons {y : α} (h : x ∈+ y :: l) (hx : x ≠ y) : x ∈+ l := by
  simpa [← duplicate_cons_iff, ← hx.symm] using h

theorem duplicate_cons_iff_of_ne {y : α} (hne : x ≠ y) : x ∈+ y :: l ↔ x ∈+ l := by
  simp [← duplicate_cons_iff, ← hne.symm]

theorem Duplicate.mono_sublist {l' : List α} (hx : x ∈+ l) (h : l <+ l') : x ∈+ l' := by
  induction' h with l₁ l₂ y h IH l₁ l₂ y h IH
  · exact hx
    
  · exact (IH hx).duplicate_cons _
    
  · rw [duplicate_cons_iff] at hx⊢
    rcases hx with (⟨rfl, hx⟩ | hx)
    · simp [← h.subset hx]
      
    · simp [← IH hx]
      
    

/-- The contrapositive of `list.nodup_iff_sublist`. -/
theorem duplicate_iff_sublist : x ∈+ l ↔ [x, x] <+ l := by
  induction' l with y l IH
  · simp
    
  · by_cases' hx : x = y
    · simp [← hx, ← cons_sublist_cons_iff, ← singleton_sublist]
      
    · rw [duplicate_cons_iff_of_ne hx, IH]
      refine' ⟨sublist_cons_of_sublist y, fun h => _⟩
      cases h
      · assumption
        
      · contradiction
        
      
    

theorem nodup_iff_forall_not_duplicate : Nodupₓ l ↔ ∀ x : α, ¬x ∈+ l := by
  simp_rw [nodup_iff_sublist, duplicate_iff_sublist]

theorem exists_duplicate_iff_not_nodup : (∃ x : α, x ∈+ l) ↔ ¬Nodupₓ l := by
  simp [← nodup_iff_forall_not_duplicate]

theorem Duplicate.not_nodup (h : x ∈+ l) : ¬Nodupₓ l := fun H => nodup_iff_forall_not_duplicate.mp H _ h

theorem duplicate_iff_two_le_count [DecidableEq α] : x ∈+ l ↔ 2 ≤ count x l := by
  simp [← duplicate_iff_sublist, ← le_count_iff_repeat_sublist]

instance decidableDuplicate [DecidableEq α] (x : α) : ∀ l : List α, Decidable (x ∈+ l)
  | [] => isFalse (not_duplicate_nil x)
  | y :: l =>
    match decidable_duplicate l with
    | is_true h => isTrue (h.duplicate_cons y)
    | is_false h =>
      if hx : y = x ∧ x ∈ l then isTrue (hx.left.symm ▸ hx.right.duplicate_cons_self)
      else
        isFalse
          (by
            simpa [← duplicate_cons_iff, ← h] using hx)

end List

