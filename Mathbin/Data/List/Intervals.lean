/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.List.Lattice
import Mathbin.Data.List.Range

/-!
# Intervals in ℕ

This file defines intervals of naturals. `list.Ico m n` is the list of integers greater than `m`
and strictly less than `n`.

## TODO
- Define `Ioo` and `Icc`, state basic lemmas about them.
- Also do the versions for integers?
- One could generalise even further, defining 'locally finite partial orders', for which
  `set.Ico a b` is `[finite]`, and 'locally finite total orders', for which there is a list model.
- Once the above is done, get rid of `data.int.range` (and maybe `list.range'`?).
-/


open Nat

namespace List

/-- `Ico n m` is the list of natural numbers `n ≤ x < m`.
(Ico stands for "interval, closed-open".)

See also `data/set/intervals.lean` for `set.Ico`, modelling intervals in general preorders, and
`multiset.Ico` and `finset.Ico` for `n ≤ x < m` as a multiset or as a finset.
 -/
def ico (n m : ℕ) : List ℕ :=
  range' n (m - n)

namespace Ico

theorem zero_bot (n : ℕ) : ico 0 n = range n := by
  rw [Ico, tsub_zero, range_eq_range']

@[simp]
theorem length (n m : ℕ) : length (ico n m) = m - n := by
  dsimp' [← Ico]
  simp only [← length_range']

theorem pairwise_lt (n m : ℕ) : Pairwiseₓ (· < ·) (ico n m) := by
  dsimp' [← Ico]
  simp only [← pairwise_lt_range']

theorem nodup (n m : ℕ) : Nodupₓ (ico n m) := by
  dsimp' [← Ico]
  simp only [← nodup_range']

@[simp]
theorem mem {n m l : ℕ} : l ∈ ico n m ↔ n ≤ l ∧ l < m := by
  suffices n ≤ l ∧ l < n + (m - n) ↔ n ≤ l ∧ l < m by
    simp [← Ico, ← this]
  cases' le_totalₓ n m with hnm hmn
  · rw [add_tsub_cancel_of_le hnm]
    
  · rw [tsub_eq_zero_iff_le.mpr hmn, add_zeroₓ]
    exact
      and_congr_right fun hnl => Iff.intro (fun hln => (not_le_of_gtₓ hln hnl).elim) fun hlm => lt_of_lt_of_leₓ hlm hmn
    

theorem eq_nil_of_le {n m : ℕ} (h : m ≤ n) : ico n m = [] := by
  simp [← Ico, ← tsub_eq_zero_iff_le.mpr h]

theorem map_add (n m k : ℕ) : (ico n m).map ((· + ·) k) = ico (n + k) (m + k) := by
  rw [Ico, Ico, map_add_range', add_tsub_add_eq_tsub_right, add_commₓ n k]

theorem map_sub (n m k : ℕ) (h₁ : k ≤ n) : ((ico n m).map fun x => x - k) = ico (n - k) (m - k) := by
  rw [Ico, Ico, tsub_tsub_tsub_cancel_right h₁, map_sub_range' _ _ _ h₁]

@[simp]
theorem self_empty {n : ℕ} : ico n n = [] :=
  eq_nil_of_le (le_reflₓ n)

@[simp]
theorem eq_empty_iff {n m : ℕ} : ico n m = [] ↔ m ≤ n :=
  Iff.intro
    (fun h =>
      tsub_eq_zero_iff_le.mp <| by
        rw [← length, h, List.length])
    eq_nil_of_le

theorem append_consecutive {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) : ico n m ++ ico m l = ico n l := by
  dunfold Ico
  convert range'_append _ _ _
  · exact (add_tsub_cancel_of_le hnm).symm
    
  · rwa [← add_tsub_assoc_of_le hnm, tsub_add_cancel_of_le]
    

@[simp]
theorem inter_consecutive (n m l : ℕ) : ico n m ∩ ico m l = [] := by
  apply eq_nil_iff_forall_not_mem.2
  intro a
  simp only [← and_imp, ← not_and, ← not_ltₓ, ← List.mem_inter, ← List.ico.mem]
  intro h₁ h₂ h₃
  exfalso
  exact not_lt_of_geₓ h₃ h₂

@[simp]
theorem bag_inter_consecutive (n m l : ℕ) : List.bagInterₓ (ico n m) (ico m l) = [] :=
  (bag_inter_nil_iff_inter_nil _ _).2 (inter_consecutive n m l)

@[simp]
theorem succ_singleton {n : ℕ} : ico n (n + 1) = [n] := by
  dsimp' [← Ico]
  simp [← add_tsub_cancel_left]

theorem succ_top {n m : ℕ} (h : n ≤ m) : ico n (m + 1) = ico n m ++ [m] := by
  rwa [← succ_singleton, append_consecutive]
  exact Nat.le_succₓ _

theorem eq_cons {n m : ℕ} (h : n < m) : ico n m = n :: ico (n + 1) m := by
  rw [← append_consecutive (Nat.le_succₓ n) h, succ_singleton]
  rfl

@[simp]
theorem pred_singleton {m : ℕ} (h : 0 < m) : ico (m - 1) m = [m - 1] := by
  dsimp' [← Ico]
  rw [tsub_tsub_cancel_of_le (succ_le_of_lt h)]
  simp

theorem chain'_succ (n m : ℕ) : Chain' (fun a b => b = succ a) (ico n m) := by
  by_cases' n < m
  · rw [eq_cons h]
    exact chain_succ_range' _ _
    
  · rw [eq_nil_of_le (le_of_not_gtₓ h)]
    trivial
    

@[simp]
theorem not_mem_top {n m : ℕ} : m ∉ ico n m := by
  simp

theorem filter_lt_of_top_le {n m l : ℕ} (hml : m ≤ l) : ((ico n m).filter fun x => x < l) = ico n m :=
  filter_eq_self.2 fun k hk => lt_of_lt_of_leₓ (mem.1 hk).2 hml

theorem filter_lt_of_le_bot {n m l : ℕ} (hln : l ≤ n) : ((ico n m).filter fun x => x < l) = [] :=
  filter_eq_nil.2 fun k hk => not_lt_of_le <| le_transₓ hln <| (mem.1 hk).1

theorem filter_lt_of_ge {n m l : ℕ} (hlm : l ≤ m) : ((ico n m).filter fun x => x < l) = ico n l := by
  cases' le_totalₓ n l with hnl hln
  · rw [← append_consecutive hnl hlm, filter_append, filter_lt_of_top_le (le_reflₓ l), filter_lt_of_le_bot (le_reflₓ l),
      append_nil]
    
  · rw [eq_nil_of_le hln, filter_lt_of_le_bot hln]
    

@[simp]
theorem filter_lt (n m l : ℕ) : ((ico n m).filter fun x => x < l) = ico n (min m l) := by
  cases' le_totalₓ m l with hml hlm
  · rw [min_eq_leftₓ hml, filter_lt_of_top_le hml]
    
  · rw [min_eq_rightₓ hlm, filter_lt_of_ge hlm]
    

theorem filter_le_of_le_bot {n m l : ℕ} (hln : l ≤ n) : ((ico n m).filter fun x => l ≤ x) = ico n m :=
  filter_eq_self.2 fun k hk => le_transₓ hln (mem.1 hk).1

theorem filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : ((ico n m).filter fun x => l ≤ x) = [] :=
  filter_eq_nil.2 fun k hk => not_le_of_gtₓ (lt_of_lt_of_leₓ (mem.1 hk).2 hml)

theorem filter_le_of_le {n m l : ℕ} (hnl : n ≤ l) : ((ico n m).filter fun x => l ≤ x) = ico l m := by
  cases' le_totalₓ l m with hlm hml
  · rw [← append_consecutive hnl hlm, filter_append, filter_le_of_top_le (le_reflₓ l), filter_le_of_le_bot (le_reflₓ l),
      nil_append]
    
  · rw [eq_nil_of_le hml, filter_le_of_top_le hml]
    

@[simp]
theorem filter_le (n m l : ℕ) : ((ico n m).filter fun x => l ≤ x) = ico (max n l) m := by
  cases' le_totalₓ n l with hnl hln
  · rw [max_eq_rightₓ hnl, filter_le_of_le hnl]
    
  · rw [max_eq_leftₓ hln, filter_le_of_le_bot hln]
    

theorem filter_lt_of_succ_bot {n m : ℕ} (hnm : n < m) : ((ico n m).filter fun x => x < n + 1) = [n] := by
  have r : min m (n + 1) = n + 1 := (@inf_eq_right _ _ m (n + 1)).mpr hnm
  simp [← filter_lt n m (n + 1), ← r]

@[simp]
theorem filter_le_of_bot {n m : ℕ} (hnm : n < m) : ((ico n m).filter fun x => x ≤ n) = [n] := by
  rw [← filter_lt_of_succ_bot hnm]
  exact filter_congr' fun _ _ => lt_succ_iff.symm

/-- For any natural numbers n, a, and b, one of the following holds:
1. n < a
2. n ≥ b
3. n ∈ Ico a b
-/
theorem trichotomy (n a b : ℕ) : n < a ∨ b ≤ n ∨ n ∈ ico a b := by
  by_cases' h₁ : n < a
  · left
    exact h₁
    
  · right
    by_cases' h₂ : n ∈ Ico a b
    · right
      exact h₂
      
    · left
      simp only [← Ico.mem, ← not_and, ← not_ltₓ] at *
      exact h₂ h₁
      
    

end Ico

end List

