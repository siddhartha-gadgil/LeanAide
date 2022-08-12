/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Multiset.Nodup

/-!
# Erasing duplicates in a multiset.
-/


namespace Multiset

open List

variable {α β : Type _} [DecidableEq α]

/-! ### dedup -/


/-- `dedup s` removes duplicates from `s`, yielding a `nodup` multiset. -/
def dedup (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.dedup : Multiset α)) fun s t p => Quot.sound p.dedup

@[simp]
theorem coe_dedup (l : List α) : @dedup α _ l = l.dedup :=
  rfl

@[simp]
theorem dedup_zero : @dedup α _ 0 = 0 :=
  rfl

@[simp]
theorem mem_dedup {a : α} {s : Multiset α} : a ∈ dedup s ↔ a ∈ s :=
  (Quot.induction_on s) fun l => mem_dedup

@[simp]
theorem dedup_cons_of_mem {a : α} {s : Multiset α} : a ∈ s → dedup (a ::ₘ s) = dedup s :=
  (Quot.induction_on s) fun l m => @congr_arg _ _ _ _ coe <| dedup_cons_of_mem m

@[simp]
theorem dedup_cons_of_not_mem {a : α} {s : Multiset α} : a ∉ s → dedup (a ::ₘ s) = a ::ₘ dedup s :=
  (Quot.induction_on s) fun l m => congr_arg coe <| dedup_cons_of_not_mem m

theorem dedup_le (s : Multiset α) : dedup s ≤ s :=
  (Quot.induction_on s) fun l => (dedup_sublist _).Subperm

theorem dedup_subset (s : Multiset α) : dedup s ⊆ s :=
  subset_of_le <| dedup_le _

theorem subset_dedup (s : Multiset α) : s ⊆ dedup s := fun a => mem_dedup.2

@[simp]
theorem dedup_subset' {s t : Multiset α} : dedup s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans (subset_dedup _), Subset.trans (dedup_subset _)⟩

@[simp]
theorem subset_dedup' {s t : Multiset α} : s ⊆ dedup t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h (dedup_subset _), fun h => Subset.trans h (subset_dedup _)⟩

@[simp]
theorem nodup_dedup (s : Multiset α) : Nodup (dedup s) :=
  Quot.induction_on s nodup_dedup

theorem dedup_eq_self {s : Multiset α} : dedup s = s ↔ Nodup s :=
  ⟨fun e => e ▸ nodup_dedup s, (Quot.induction_on s) fun l h => congr_arg coe h.dedup⟩

alias dedup_eq_self ↔ _ nodup.dedup

theorem dedup_eq_zero {s : Multiset α} : dedup s = 0 ↔ s = 0 :=
  ⟨fun h => eq_zero_of_subset_zero <| h ▸ subset_dedup _, fun h => h.symm ▸ dedup_zero⟩

@[simp]
theorem dedup_singleton {a : α} : dedup ({a} : Multiset α) = {a} :=
  (nodup_singleton _).dedup

theorem le_dedup {s t : Multiset α} : s ≤ dedup t ↔ s ≤ t ∧ Nodup s :=
  ⟨fun h => ⟨le_transₓ h (dedup_le _), nodup_of_le h (nodup_dedup _)⟩, fun ⟨l, d⟩ =>
    (le_iff_subset d).2 <| Subset.trans (subset_of_le l) (subset_dedup _)⟩

theorem dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ ∀ a, a ∈ s ↔ a ∈ t := by
  simp [← nodup.ext]

theorem dedup_map_dedup_eq [DecidableEq β] (f : α → β) (s : Multiset α) : dedup (map f (dedup s)) = dedup (map f s) :=
  by
  simp [← dedup_ext]

@[simp]
theorem dedup_nsmul {s : Multiset α} {n : ℕ} (h0 : n ≠ 0) : (n • s).dedup = s.dedup := by
  ext a
  by_cases' h : a ∈ s <;> simp [← h, ← h0]

theorem Nodup.le_dedup_iff_le {s t : Multiset α} (hno : s.Nodup) : s ≤ t.dedup ↔ s ≤ t := by
  simp [← le_dedup, ← hno]

end Multiset

theorem Multiset.Nodup.le_nsmul_iff_le {α : Type _} {s t : Multiset α} {n : ℕ} (h : s.Nodup) (hn : n ≠ 0) :
    s ≤ n • t ↔ s ≤ t := by
  classical
  rw [← h.le_dedup_iff_le, Iff.comm, ← h.le_dedup_iff_le]
  simp [← hn]

