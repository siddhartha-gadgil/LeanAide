/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison
-/
import Mathbin.Data.List.Chain
import Mathbin.Data.List.Nodup
import Mathbin.Data.List.OfFn
import Mathbin.Data.List.Zip

/-!
# Ranges of naturals as lists

This file shows basic results about `list.iota`, `list.range`, `list.range'` (all defined in
`data.list.defs`) and defines `list.fin_range`.
`fin_range n` is the list of elements of `fin n`.
`iota n = [1, ..., n]` and `range n = [0, ..., n - 1]` are basic list constructions used for
tactics. `range' a b = [a, ..., a + b - 1]` is there to help prove properties about them.
Actual maths should use `list.Ico` instead.
-/


universe u

open Nat

namespace List

variable {α : Type u}

@[simp]
theorem length_range' : ∀ s n : ℕ, length (range' s n) = n
  | s, 0 => rfl
  | s, n + 1 => congr_arg succ (length_range' _ _)

@[simp]
theorem range'_eq_nil {s n : ℕ} : range' s n = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_range']

@[simp]
theorem mem_range' {m : ℕ} : ∀ {s n : ℕ}, m ∈ range' s n ↔ s ≤ m ∧ m < s + n
  | s, 0 => (false_iffₓ _).2 fun ⟨H1, H2⟩ => not_le_of_lt H2 H1
  | s, succ n =>
    have : m = s → m < s + n + 1 := fun e => e ▸ lt_succ_of_leₓ (Nat.le_add_rightₓ _ _)
    have l : m = s ∨ s + 1 ≤ m ↔ s ≤ m := by
      simpa only [← eq_comm] using (@Decidable.le_iff_eq_or_lt _ _ _ s m).symm
    (mem_cons_iff _ _ _).trans <| by
      simp only [← mem_range', ← or_and_distrib_left, ← or_iff_right_of_imp this, ← l, ← add_right_commₓ] <;> rfl

theorem map_add_range' (a) : ∀ s n : ℕ, map ((· + ·) a) (range' s n) = range' (a + s) n
  | s, 0 => rfl
  | s, n + 1 => congr_arg (cons _) (map_add_range' (s + 1) n)

theorem map_sub_range' (a) : ∀ (s n : ℕ) (h : a ≤ s), map (fun x => x - a) (range' s n) = range' (s - a) n
  | s, 0, _ => rfl
  | s, n + 1, h => by
    convert congr_arg (cons (s - a)) (map_sub_range' (s + 1) n (Nat.le_succ_of_leₓ h))
    rw [Nat.succ_subₓ h]
    rfl

theorem chain_succ_range' : ∀ s n : ℕ, Chain (fun a b => b = succ a) s (range' (s + 1) n)
  | s, 0 => Chain.nil
  | s, n + 1 => (chain_succ_range' (s + 1) n).cons rfl

theorem chain_lt_range' (s n : ℕ) : Chain (· < ·) s (range' (s + 1) n) :=
  (chain_succ_range' s n).imp fun a b e => e.symm ▸ lt_succ_selfₓ _

theorem pairwise_lt_range' : ∀ s n : ℕ, Pairwiseₓ (· < ·) (range' s n)
  | s, 0 => Pairwiseₓ.nil
  | s, n + 1 => (chain_iff_pairwise fun a b c => lt_transₓ).1 (chain_lt_range' s n)

theorem nodup_range' (s n : ℕ) : Nodupₓ (range' s n) :=
  (pairwise_lt_range' s n).imp fun a b => ne_of_ltₓ

@[simp]
theorem range'_append : ∀ s m n : ℕ, range' s m ++ range' (s + m) n = range' s (n + m)
  | s, 0, n => rfl
  | s, m + 1, n =>
    show s :: (range' (s + 1) m ++ range' (s + m + 1) n) = s :: range' (s + 1) (n + m) by
      rw [add_right_commₓ, range'_append]

theorem range'_sublist_right {s m n : ℕ} : range' s m <+ range' s n ↔ m ≤ n :=
  ⟨fun h => by
    simpa only [← length_range'] using length_le_of_sublist h, fun h => by
    rw [← tsub_add_cancel_of_le h, ← range'_append] <;> apply sublist_append_left⟩

theorem range'_subset_right {s m n : ℕ} : range' s m ⊆ range' s n ↔ m ≤ n :=
  ⟨fun h =>
    le_of_not_ltₓ fun hn =>
      lt_irreflₓ (s + n) <| (mem_range'.1 <| h <| mem_range'.2 ⟨Nat.le_add_rightₓ _ _, Nat.add_lt_add_leftₓ hn s⟩).2,
    fun h => (range'_sublist_right.2 h).Subset⟩

theorem nth_range' : ∀ (s) {m n : ℕ}, m < n → nth (range' s n) m = some (s + m)
  | s, 0, n + 1, _ => rfl
  | s, m + 1, n + 1, h =>
    (nth_range' (s + 1) (lt_of_add_lt_add_right h)).trans <| by
      rw [add_right_commₓ] <;> rfl

@[simp]
theorem nth_le_range' {n m} (i) (H : i < (range' n m).length) : nthLe (range' n m) i H = n + i :=
  Option.some.injₓ <| by
    rw [← nth_le_nth _,
      nth_range' _
        (by
          simpa using H)]

theorem range'_concat (s n : ℕ) : range' s (n + 1) = range' s n ++ [s + n] := by
  rw [add_commₓ n 1] <;> exact (range'_append s n 1).symm

theorem range_core_range' : ∀ s n : ℕ, rangeCore s (range' s n) = range' 0 (n + s)
  | 0, n => rfl
  | s + 1, n => by
    rw [show n + (s + 1) = n + 1 + s from add_right_commₓ n s 1] <;> exact range_core_range' s (n + 1)

theorem range_eq_range' (n : ℕ) : range n = range' 0 n :=
  (range_core_range' n 0).trans <| by
    rw [zero_addₓ]

theorem range_succ_eq_map (n : ℕ) : range (n + 1) = 0 :: map succ (range n) := by
  rw [range_eq_range', range_eq_range', range', add_commₓ, ← map_add_range'] <;> congr <;> exact funext one_add

theorem range'_eq_map_range (s n : ℕ) : range' s n = map ((· + ·) s) (range n) := by
  rw [range_eq_range', map_add_range'] <;> rfl

@[simp]
theorem length_range (n : ℕ) : length (range n) = n := by
  simp only [← range_eq_range', ← length_range']

@[simp]
theorem range_eq_nil {n : ℕ} : range n = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_range]

theorem pairwise_lt_range (n : ℕ) : Pairwiseₓ (· < ·) (range n) := by
  simp only [← range_eq_range', ← pairwise_lt_range']

theorem nodup_range (n : ℕ) : Nodupₓ (range n) := by
  simp only [← range_eq_range', ← nodup_range']

theorem range_sublist {m n : ℕ} : range m <+ range n ↔ m ≤ n := by
  simp only [← range_eq_range', ← range'_sublist_right]

theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n := by
  simp only [← range_eq_range', ← range'_subset_right]

@[simp]
theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n := by
  simp only [← range_eq_range', ← mem_range', ← Nat.zero_leₓ, ← true_andₓ, ← zero_addₓ]

@[simp]
theorem not_mem_range_self {n : ℕ} : n ∉ range n :=
  mt mem_range.1 <| lt_irreflₓ _

@[simp]
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := by
  simp only [← succ_pos', ← lt_add_iff_pos_right, ← mem_range]

theorem nth_range {m n : ℕ} (h : m < n) : nth (range n) m = some m := by
  simp only [← range_eq_range', ← nth_range' _ h, ← zero_addₓ]

theorem range_succ (n : ℕ) : range (succ n) = range n ++ [n] := by
  simp only [← range_eq_range', ← range'_concat, ← zero_addₓ]

@[simp]
theorem range_zero : range 0 = [] :=
  rfl

theorem chain'_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) : Chain' r (range n.succ) ↔ ∀, ∀ m < n, ∀, r m m.succ := by
  rw [range_succ]
  induction' n with n hn
  · simp
    
  · rw [range_succ]
    simp only [← append_assoc, ← singleton_append, ← chain'_append_cons_cons, ← chain'_singleton, ← and_trueₓ]
    rw [hn, forall_lt_succ]
    

theorem chain_range_succ (r : ℕ → ℕ → Prop) (n a : ℕ) : Chain r a (range n.succ) ↔ r a 0 ∧ ∀, ∀ m < n, ∀, r m m.succ :=
  by
  rw [range_succ_eq_map, chain_cons, And.congr_right_iff, ← chain'_range_succ, range_succ_eq_map]
  exact fun _ => Iff.rfl

theorem range_add (a : ℕ) : ∀ b, range (a + b) = range a ++ (range b).map fun x => a + x
  | 0 => by
    rw [add_zeroₓ, range_zero, map_nil, append_nil]
  | b + 1 => by
    rw [Nat.add_succ, range_succ, range_add b, range_succ, map_append, map_singleton, append_assoc]

theorem iota_eq_reverse_range' : ∀ n : ℕ, iota n = reverse (range' 1 n)
  | 0 => rfl
  | n + 1 => by
    simp only [← iota, ← range'_concat, ← iota_eq_reverse_range' n, ← reverse_append, ← add_commₓ] <;> rfl

@[simp]
theorem length_iota (n : ℕ) : length (iota n) = n := by
  simp only [← iota_eq_reverse_range', ← length_reverse, ← length_range']

theorem pairwise_gt_iota (n : ℕ) : Pairwiseₓ (· > ·) (iota n) := by
  simp only [← iota_eq_reverse_range', ← pairwise_reverse, ← pairwise_lt_range']

theorem nodup_iota (n : ℕ) : Nodupₓ (iota n) := by
  simp only [← iota_eq_reverse_range', ← nodup_reverse, ← nodup_range']

theorem mem_iota {m n : ℕ} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n := by
  simp only [← iota_eq_reverse_range', ← mem_reverse, ← mem_range', ← add_commₓ, ← lt_succ_iff]

theorem reverse_range' : ∀ s n : ℕ, reverse (range' s n) = map (fun i => s + n - 1 - i) (range n)
  | s, 0 => rfl
  | s, n + 1 => by
    rw [range'_concat, reverse_append, range_succ_eq_map] <;>
      simpa only [← show s + (n + 1) - 1 = s + n from rfl, ← (· ∘ ·), ← fun a i =>
        show a - 1 - i = a - succ i from pred_sub _ _, ← reverse_singleton, ← map_cons, ← tsub_zero, ← cons_append, ←
        nil_append, ← eq_self_iff_true, ← true_andₓ, ← map_map] using reverse_range' s n

/-- All elements of `fin n`, from `0` to `n-1`. -/
def finRange (n : ℕ) : List (Finₓ n) :=
  (range n).pmap Finₓ.mk fun _ => List.mem_range.1

@[simp]
theorem fin_range_zero : finRange 0 = [] :=
  rfl

@[simp]
theorem mem_fin_range {n : ℕ} (a : Finₓ n) : a ∈ finRange n :=
  mem_pmap.2 ⟨a.1, mem_range.2 a.2, Finₓ.eta _ _⟩

theorem nodup_fin_range (n : ℕ) : (finRange n).Nodup :=
  (nodup_range _).pmap fun _ _ _ _ => Finₓ.veq_of_eq

@[simp]
theorem length_fin_range (n : ℕ) : (finRange n).length = n := by
  rw [fin_range, length_pmap, length_range]

@[simp]
theorem fin_range_eq_nil {n : ℕ} : finRange n = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_fin_range]

@[simp]
theorem map_coe_fin_range (n : ℕ) : (finRange n).map coe = List.range n := by
  simp_rw [fin_range, map_pmap, Finₓ.mk, Subtype.coe_mk, pmap_eq_map]
  exact List.map_id _

theorem fin_range_succ_eq_map (n : ℕ) : finRange n.succ = 0 :: (finRange n).map Finₓ.succ := by
  apply map_injective_iff.mpr Subtype.coe_injective
  rw [map_cons, map_coe_fin_range, range_succ_eq_map, Finₓ.coe_zero, ← map_coe_fin_range, map_map, map_map,
    Function.comp, Function.comp]
  congr 2 with x
  exact (Finₓ.coe_succ _).symm

@[to_additive]
theorem prod_range_succ {α : Type u} [Monoidₓ α] (f : ℕ → α) (n : ℕ) :
    ((range n.succ).map f).Prod = ((range n).map f).Prod * f n := by
  rw [range_succ, map_append, map_singleton, prod_append, prod_cons, prod_nil, mul_oneₓ]

/-- A variant of `prod_range_succ` which pulls off the first
  term in the product rather than the last.-/
@[to_additive "A variant of `sum_range_succ` which pulls off the first term in the sum\n  rather than the last."]
theorem prod_range_succ' {α : Type u} [Monoidₓ α] (f : ℕ → α) (n : ℕ) :
    ((range n.succ).map f).Prod = f 0 * ((range n).map fun i => f (succ i)).Prod :=
  Nat.recOn n
    (show 1 * f 0 = f 0 * 1 by
      rw [one_mulₓ, mul_oneₓ])
    fun _ hd => by
    rw [List.prod_range_succ, hd, mul_assoc, ← List.prod_range_succ]

@[simp]
theorem enum_from_map_fst : ∀ (n) (l : List α), map Prod.fst (enumFrom n l) = range' n l.length
  | n, [] => rfl
  | n, a :: l => congr_arg (cons _) (enum_from_map_fst _ _)

@[simp]
theorem enum_map_fst (l : List α) : map Prod.fst (enum l) = range l.length := by
  simp only [← enum, ← enum_from_map_fst, ← range_eq_range']

theorem enum_eq_zip_range (l : List α) : l.enum = (range l.length).zip l :=
  zip_of_prod (enum_map_fst _) (enum_map_snd _)

@[simp]
theorem unzip_enum_eq_prod (l : List α) : l.enum.unzip = (range l.length, l) := by
  simp only [← enum_eq_zip_range, ← unzip_zip, ← length_range]

theorem enum_from_eq_zip_range' (l : List α) {n : ℕ} : l.enumFrom n = (range' n l.length).zip l :=
  zip_of_prod (enum_from_map_fst _ _) (enum_from_map_snd _ _)

@[simp]
theorem unzip_enum_from_eq_prod (l : List α) {n : ℕ} : (l.enumFrom n).unzip = (range' n l.length, l) := by
  simp only [← enum_from_eq_zip_range', ← unzip_zip, ← length_range']

@[simp]
theorem nth_le_range {n} (i) (H : i < (range n).length) : nthLe (range n) i H = i :=
  Option.some.injₓ <| by
    rw [← nth_le_nth _,
      nth_range
        (by
          simpa using H)]

@[simp]
theorem nth_le_fin_range {n : ℕ} {i : ℕ} (h) : (finRange n).nthLe i h = ⟨i, length_fin_range n ▸ h⟩ := by
  simp only [← fin_range, ← nth_le_range, ← nth_le_pmap, ← Finₓ.mk_eq_subtype_mk]

theorem of_fn_eq_pmap {α n} {f : Finₓ n → α} : ofFnₓ f = pmap (fun i hi => f ⟨i, hi⟩) (range n) fun _ => mem_range.1 :=
  by
  rw [pmap_eq_map_attach] <;>
    exact
      ext_le
        (by
          simp )
        fun i hi1 hi2 => by
        simp at hi1
        simp [← nth_le_of_fn f ⟨i, hi1⟩, -Subtype.val_eq_coe]

theorem of_fn_id (n) : ofFnₓ id = finRange n :=
  of_fn_eq_pmap

theorem of_fn_eq_map {α n} {f : Finₓ n → α} : ofFnₓ f = (finRange n).map f := by
  rw [← of_fn_id, map_of_fn, Function.right_id]

theorem nodup_of_fn {α n} {f : Finₓ n → α} (hf : Function.Injective f) : Nodupₓ (ofFnₓ f) := by
  rw [of_fn_eq_pmap]
  exact (nodup_range n).pmap fun _ _ _ _ H => Finₓ.veq_of_eq <| hf H

end List

