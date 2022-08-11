/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Scott Morrison, Eric Rodriguez
-/
import Mathbin.Data.Nat.Count
import Mathbin.Order.OrderIsoNat

/-!
# The `n`th Number Satisfying a Predicate

This file defines a function for "what is the `n`th number that satisifies a given predicate `p`",
and provides lemmas that deal with this function and its connection to `nat.count`.

## Main definitions

* `nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `nth p n = 0`.

## Main results

* `nat.nth_set_card`: For a fintely-often true `p`, gives the cardinality of the set of numbers
  satisfying `p` above particular values of `nth p`
* `nat.count_nth_gc`: Establishes a Galois connection between `nth p` and `count p`.
* `nat.nth_eq_order_iso_of_nat`: For an infinitely-ofter true predicate, `nth` agrees with the
  order-isomorphism of the subtype to the natural numbers.

There has been some discussion on the subject of whether both of `nth` and
`nat.subtype.order_iso_of_nat` should exist. See discussion
[here](https://github.com/leanprover-community/mathlib/pull/9457#pullrequestreview-767221180).
Future work should address how lemmas that use these should be written.

-/


open Finset

namespace Nat

variable (p : ℕ → Prop)

/-- Find the `n`-th natural number satisfying `p` (indexed from `0`, so `nth p 0` is the first
natural number satisfying `p`), or `0` if there is no such number. See also
`subtype.order_iso_of_nat` for the order isomorphism with ℕ when `p` is infinitely often true. -/
noncomputable def nth : ℕ → ℕ
  | n => inf { i : ℕ | p i ∧ ∀, ∀ k < n, ∀, nth k < i }

theorem nth_zero : nth p 0 = inf { i : ℕ | p i } := by
  rw [nth]
  simp

@[simp]
theorem nth_zero_of_zero (h : p 0) : nth p 0 = 0 := by
  simp [← nth_zero, ← h]

theorem nth_zero_of_exists [DecidablePred p] (h : ∃ n, p n) : nth p 0 = Nat.findₓ h := by
  rw [nth_zero]
  convert Nat.Inf_def h

theorem nth_set_card_aux {n : ℕ} (hp : (SetOf p).Finite) (hp' : { i : ℕ | p i ∧ ∀, ∀ t < n, ∀, nth p t < i }.Finite)
    (hle : n ≤ hp.toFinset.card) : hp'.toFinset.card = hp.toFinset.card - n := by
  induction' n with k hk
  · congr
    simp only [← IsEmpty.forall_iff, ← Nat.not_lt_zeroₓ, ← forall_const, ← and_trueₓ]
    
  have hp'' : { i : ℕ | p i ∧ ∀ t, t < k → nth p t < i }.Finite := by
    refine' hp.subset fun x hx => _
    rw [Set.mem_set_of_eq] at hx
    exact hx.left
  have hle' := Nat.sub_pos_of_ltₓ hle
  specialize hk hp'' (k.le_succ.trans hle)
  rw [Nat.sub_succ', ← hk]
  convert_to (Finset.erase hp''.to_finset (nth p k)).card = _
  · congr
    ext a
    simp only [← Set.Finite.mem_to_finset, ← Ne.def, ← Set.mem_set_of_eq, ← Finset.mem_erase]
    refine' ⟨fun ⟨hp, hlt⟩ => ⟨(hlt _ (lt_add_one k)).ne', ⟨hp, fun n hn => hlt n (hn.trans_le k.le_succ)⟩⟩, _⟩
    rintro ⟨hak : _ ≠ _, hp, hlt⟩
    refine' ⟨hp, fun n hn => _⟩
    rw [lt_succ_iff] at hn
    obtain hnk | rfl := hn.lt_or_eq
    · exact hlt _ hnk
      
    · refine' lt_of_le_of_neₓ _ (Ne.symm hak)
      rw [nth]
      apply Nat.Inf_le
      simpa [← hp] using hlt
      
    
  apply Finset.card_erase_of_mem
  rw [nth, Set.Finite.mem_to_finset]
  apply Inf_mem
  rwa [← hp''.nonempty_to_finset, ← Finset.card_pos, hk]

theorem nth_set_card {n : ℕ} (hp : (SetOf p).Finite) (hp' : { i : ℕ | p i ∧ ∀, ∀ k < n, ∀, nth p k < i }.Finite) :
    hp'.toFinset.card = hp.toFinset.card - n := by
  obtain hn | hn := le_or_ltₓ n hp.to_finset.card
  · exact nth_set_card_aux p hp _ hn
    
  rw [Nat.sub_eq_zero_of_leₓ hn.le]
  simp only [← Finset.card_eq_zero, ← Set.finite_to_finset_eq_empty_iff, Set.subset_empty_iff]
  convert_to _ ⊆ { i : ℕ | p i ∧ ∀ k : ℕ, k < hp.to_finset.card → nth p k < i }
  · symm
    rw [← Set.finite_to_finset_eq_empty_iff, ← Finset.card_eq_zero, ← Nat.sub_self hp.to_finset.card]
    · apply nth_set_card_aux p hp _ le_rfl
      
    · exact hp.subset fun x hx => hx.1
      
    
  exact fun x hx => ⟨hx.1, fun k hk => hx.2 _ (hk.trans hn)⟩

theorem nth_set_nonempty_of_lt_card {n : ℕ} (hp : (SetOf p).Finite) (hlt : n < hp.toFinset.card) :
    { i : ℕ | p i ∧ ∀, ∀ k < n, ∀, nth p k < i }.Nonempty := by
  have hp' : { i : ℕ | p i ∧ ∀ k : ℕ, k < n → nth p k < i }.Finite := hp.subset fun x hx => hx.1
  rw [← hp'.nonempty_to_finset, ← Finset.card_pos, nth_set_card p hp]
  exact Nat.sub_pos_of_ltₓ hlt

theorem nth_mem_of_lt_card_finite_aux (n : ℕ) (hp : (SetOf p).Finite) (hlt : n < hp.toFinset.card) :
    nth p n ∈ { i : ℕ | p i ∧ ∀, ∀ k < n, ∀, nth p k < i } := by
  rw [nth]
  apply Inf_mem
  exact nth_set_nonempty_of_lt_card _ _ hlt

theorem nth_mem_of_lt_card_finite {n : ℕ} (hp : (SetOf p).Finite) (hlt : n < hp.toFinset.card) : p (nth p n) :=
  (nth_mem_of_lt_card_finite_aux p n hp hlt).1

theorem nth_strict_mono_of_finite {m n : ℕ} (hp : (SetOf p).Finite) (hlt : n < hp.toFinset.card) (hmn : m < n) :
    nth p m < nth p n :=
  (nth_mem_of_lt_card_finite_aux p _ hp hlt).2 _ hmn

theorem nth_mem_of_infinite_aux (hp : (SetOf p).Infinite) (n : ℕ) :
    nth p n ∈ { i : ℕ | p i ∧ ∀, ∀ k < n, ∀, nth p k < i } := by
  rw [nth]
  apply Inf_mem
  let s : Set ℕ := ⋃ k < n, { i : ℕ | nth p k ≥ i }
  convert_to (SetOf p \ s).Nonempty
  · ext i
    simp
    
  refine' (hp.diff <| (Set.finite_lt_nat _).bUnion _).Nonempty
  exact fun k h => Set.finite_le_nat _

theorem nth_mem_of_infinite (hp : (SetOf p).Infinite) (n : ℕ) : p (nth p n) :=
  (nth_mem_of_infinite_aux p hp n).1

theorem nth_strict_mono (hp : (SetOf p).Infinite) : StrictMono (nth p) := fun a b =>
  (nth_mem_of_infinite_aux p hp b).2 _

theorem nth_injective_of_infinite (hp : (SetOf p).Infinite) : Function.Injective (nth p) := by
  intro m n h
  wlog h' : m ≤ n
  rw [le_iff_lt_or_eqₓ] at h'
  obtain h' | rfl := h'
  · simpa [← h] using nth_strict_mono p hp h'
    
  · rfl
    

theorem nth_monotone (hp : (SetOf p).Infinite) : Monotone (nth p) :=
  (nth_strict_mono p hp).Monotone

theorem nth_mono_of_finite {a b : ℕ} (hp : (SetOf p).Finite) (hb : b < hp.toFinset.card) (hab : a ≤ b) :
    nth p a ≤ nth p b := by
  obtain rfl | h := hab.eq_or_lt
  · exact le_rfl
    
  · exact (nth_strict_mono_of_finite p hp hb h).le
    

theorem le_nth_of_lt_nth_succ_finite {k a : ℕ} (hp : (SetOf p).Finite) (hlt : k.succ < hp.toFinset.card)
    (h : a < nth p k.succ) (ha : p a) : a ≤ nth p k := by
  by_contra' hak
  refine' h.not_le _
  rw [nth]
  apply Nat.Inf_le
  refine' ⟨ha, fun n hn => lt_of_le_of_ltₓ _ hak⟩
  exact nth_mono_of_finite p hp (k.le_succ.trans_lt hlt) (le_of_lt_succ hn)

theorem le_nth_of_lt_nth_succ_infinite {k a : ℕ} (hp : (SetOf p).Infinite) (h : a < nth p k.succ) (ha : p a) :
    a ≤ nth p k := by
  by_contra' hak
  refine' h.not_le _
  rw [nth]
  apply Nat.Inf_le
  exact ⟨ha, fun n hn => (nth_monotone p hp (le_of_lt_succ hn)).trans_lt hak⟩

section Count

variable [DecidablePred p]

@[simp]
theorem count_nth_zero : count p (nth p 0) = 0 := by
  rw [count_eq_card_filter_range, Finset.card_eq_zero, nth_zero]
  ext a
  simp_rw [not_mem_empty, mem_filter, mem_range, iff_falseₓ]
  rintro ⟨ha, hp⟩
  exact ha.not_le (Nat.Inf_le hp)

theorem filter_range_nth_eq_insert_of_finite (hp : (SetOf p).Finite) {k : ℕ} (hlt : k.succ < hp.toFinset.card) :
    Finset.filter p (Finset.range (nth p k.succ)) = insert (nth p k) (Finset.filter p (Finset.range (nth p k))) := by
  ext a
  simp_rw [mem_insert, mem_filter, mem_range]
  constructor
  · rintro ⟨ha, hpa⟩
    refine' or_iff_not_imp_left.mpr fun h => ⟨lt_of_le_of_neₓ _ h, hpa⟩
    exact le_nth_of_lt_nth_succ_finite p hp hlt ha hpa
    
  · rintro (ha | ⟨ha, hpa⟩)
    · rw [ha]
      refine' ⟨nth_strict_mono_of_finite p hp hlt (lt_add_one _), _⟩
      apply nth_mem_of_lt_card_finite p hp
      exact k.le_succ.trans_lt hlt
      
    refine' ⟨ha.trans _, hpa⟩
    exact nth_strict_mono_of_finite p hp hlt (lt_add_one _)
    

theorem count_nth_of_lt_card_finite {n : ℕ} (hp : (SetOf p).Finite) (hlt : n < hp.toFinset.card) :
    count p (nth p n) = n := by
  induction' n with k hk
  · exact count_nth_zero _
    
  · rw [count_eq_card_filter_range, filter_range_nth_eq_insert_of_finite p hp hlt, Finset.card_insert_of_not_mem, ←
      count_eq_card_filter_range, hk (lt_of_succ_lt hlt)]
    simp
    

theorem filter_range_nth_eq_insert_of_infinite (hp : (SetOf p).Infinite) (k : ℕ) :
    (Finset.range (nth p k.succ)).filter p = insert (nth p k) ((Finset.range (nth p k)).filter p) := by
  ext a
  simp_rw [mem_insert, mem_filter, mem_range]
  constructor
  · rintro ⟨ha, hpa⟩
    rw [nth] at ha
    refine' or_iff_not_imp_left.mpr fun hne => ⟨(le_of_not_ltₓ fun h => _).lt_of_ne hne, hpa⟩
    exact ha.not_le (Nat.Inf_le ⟨hpa, fun b hb => (nth_monotone p hp (le_of_lt_succ hb)).trans_lt h⟩)
    
  · rintro (rfl | ⟨ha, hpa⟩)
    · exact ⟨nth_strict_mono p hp (lt_succ_self k), nth_mem_of_infinite p hp _⟩
      
    · exact ⟨ha.trans (nth_strict_mono p hp (lt_succ_self k)), hpa⟩
      
    

theorem count_nth_of_infinite (hp : (SetOf p).Infinite) (n : ℕ) : count p (nth p n) = n := by
  induction' n with k hk
  · exact count_nth_zero _
    
  · rw [count_eq_card_filter_range, filter_range_nth_eq_insert_of_infinite p hp, Finset.card_insert_of_not_mem, ←
      count_eq_card_filter_range, hk]
    simp
    

@[simp]
theorem nth_count {n : ℕ} (hpn : p n) : nth p (count p n) = n := by
  obtain hp | hp := em (SetOf p).Finite
  · refine' count_injective _ hpn _
    · apply nth_mem_of_lt_card_finite p hp
      exact count_lt_card hp hpn
      
    · exact count_nth_of_lt_card_finite _ _ (count_lt_card hp hpn)
      
    
  · apply count_injective (nth_mem_of_infinite _ hp _) hpn
    apply count_nth_of_infinite p hp
    

theorem nth_count_eq_Inf {n : ℕ} : nth p (count p n) = inf { i : ℕ | p i ∧ n ≤ i } := by
  rw [nth]
  congr
  ext a
  simp only [← Set.mem_set_of_eq, ← And.congr_right_iff]
  intro hpa
  refine' ⟨fun h => _, fun hn k hk => lt_of_lt_of_leₓ _ hn⟩
  · by_contra ha
    simp only [← not_leₓ] at ha
    have hn : nth p (count p a) < a := h _ (count_strict_mono hpa ha)
    rwa [nth_count p hpa, lt_self_iff_false] at hn
    
  · apply (count_monotone p).reflect_lt
    convert hk
    obtain hp | hp : (SetOf p).Finite ∨ (SetOf p).Infinite := em (SetOf p).Finite
    · rw [count_nth_of_lt_card_finite _ hp]
      exact hk.trans ((count_monotone _ hn).trans_lt (count_lt_card hp hpa))
      
    · apply count_nth_of_infinite p hp
      
    

theorem nth_count_le (hp : (SetOf p).Infinite) (n : ℕ) : n ≤ nth p (count p n) := by
  rw [nth_count_eq_Inf]
  suffices h : Inf { i : ℕ | p i ∧ n ≤ i } ∈ { i : ℕ | p i ∧ n ≤ i }
  · exact h.2
    
  apply Inf_mem
  obtain ⟨m, hp, hn⟩ := hp.exists_nat_lt n
  exact ⟨m, hp, hn.le⟩

theorem count_nth_gc (hp : (SetOf p).Infinite) : GaloisConnection (count p) (nth p) := by
  rintro x y
  rw [nth, le_cInf_iff ⟨0, fun _ _ => Nat.zero_leₓ _⟩ ⟨nth p y, nth_mem_of_infinite_aux p hp y⟩]
  dsimp'
  refine' ⟨_, fun h => _⟩
  · rintro hy n ⟨hn, h⟩
    obtain hy' | rfl := hy.lt_or_eq
    · exact (nth_count_le p hp x).trans (h (count p x) hy').le
      
    · specialize h (count p n)
      replace hn : nth p (count p n) = n := nth_count _ hn
      replace h : count p x ≤ count p n := by
        rwa [hn, lt_self_iff_false, imp_false, not_ltₓ] at h
      refine' (nth_count_le p hp x).trans _
      rw [← hn]
      exact nth_monotone p hp h
      
    
  · rw [← count_nth_of_infinite p hp y]
    exact count_monotone _ (h (nth p y) ⟨nth_mem_of_infinite p hp y, fun k hk => nth_strict_mono p hp hk⟩)
    

theorem count_le_iff_le_nth (hp : (SetOf p).Infinite) {a b : ℕ} : count p a ≤ b ↔ a ≤ nth p b :=
  count_nth_gc p hp _ _

theorem lt_nth_iff_count_lt (hp : (SetOf p).Infinite) {a b : ℕ} : a < count p b ↔ nth p a < b :=
  lt_iff_lt_of_le_iff_le <| count_le_iff_le_nth p hp

theorem nth_lt_of_lt_count (n k : ℕ) (h : k < count p n) : nth p k < n := by
  obtain hp | hp := em (SetOf p).Finite
  · refine' (count_monotone p).reflect_lt _
    rwa [count_nth_of_lt_card_finite p hp]
    refine' h.trans_le _
    rw [count_eq_card_filter_range]
    exact Finset.card_le_of_subset fun x hx => hp.mem_to_finset.2 (mem_filter.1 hx).2
    
  · rwa [← lt_nth_iff_count_lt _ hp]
    

theorem le_nth_of_count_le (n k : ℕ) (h : n ≤ nth p k) : count p n ≤ k := by
  by_contra hc
  apply not_lt.mpr h
  apply nth_lt_of_lt_count
  simpa using hc

end Count

theorem nth_zero_of_nth_zero (h₀ : ¬p 0) {a b : ℕ} (hab : a ≤ b) (ha : nth p a = 0) : nth p b = 0 := by
  rw [nth, Inf_eq_zero] at ha⊢
  cases ha
  · exact (h₀ ha.1).elim
    
  · refine' Or.inr (Set.eq_empty_of_subset_empty fun x hx => _)
    rw [← ha]
    exact ⟨hx.1, fun k hk => hx.2 k <| hk.trans_le hab⟩
    

/-- When `p` is true infinitely often, `nth` agrees with `nat.subtype.order_iso_of_nat`. -/
theorem nth_eq_order_iso_of_nat (i : Infinite (SetOf p)) (n : ℕ) : nth p n = Nat.Subtype.orderIsoOfNat (SetOf p) n := by
  classical
  have hi := set.infinite_coe_iff.mp i
  induction' n with k hk <;> simp only [← subtype.order_iso_of_nat_apply, ← subtype.of_nat, ← nat_zero_eq_zero]
  · rw [Nat.Subtype.coe_bot, nth_zero_of_exists]
    
  · simp only [← Nat.Subtype.succ, ← Set.mem_set_of_eq, ← Subtype.coe_mk, ← Subtype.val_eq_coe]
    rw [subtype.order_iso_of_nat_apply] at hk
    set b := nth p k.succ - nth p k - 1 with hb
    replace hb : p (↑(subtype.of_nat (SetOf p) k) + b + 1)
    · rw [hb, ← hk, tsub_right_comm]
      have hn11 : nth p k.succ - 1 + 1 = nth p k.succ := by
        rw [tsub_add_cancel_iff_le]
        exact succ_le_of_lt (pos_of_gt (nth_strict_mono p hi (lt_add_one k)))
      rw [add_tsub_cancel_of_le]
      · rw [hn11]
        apply nth_mem_of_infinite p hi
        
      · rw [← lt_succ_iff, ← Nat.add_one, hn11]
        apply nth_strict_mono p hi
        exact lt_add_one k
        
      
    have H : ∃ n : ℕ, p (↑(subtype.of_nat (SetOf p) k) + n + 1) := ⟨b, hb⟩
    set t := Nat.findₓ H with ht
    obtain ⟨hp, hmin⟩ := (Nat.find_eq_iff _).mp ht
    rw [← ht, ← hk] at hp hmin⊢
    rw [nth, Inf_def ⟨_, nth_mem_of_infinite_aux p hi k.succ⟩, Nat.find_eq_iff]
    refine'
      ⟨⟨by
          convert hp, fun r hr => _⟩,
        fun n hn => _⟩
    · rw [lt_succ_iff] at hr⊢
      exact
        (nth_monotone p hi hr).trans
          (by
            simp )
      
    simp only [← exists_prop, ← not_and, ← not_ltₓ, ← Set.mem_set_of_eq, ← not_forall]
    refine' fun hpn => ⟨k, lt_add_one k, _⟩
    by_contra' hlt
    replace hn : n - nth p k - 1 < t
    · rw [tsub_lt_iff_left]
      · rw [tsub_lt_iff_left hlt.le]
        convert hn using 1
        ac_rfl
        
      exact le_tsub_of_add_le_left (succ_le_of_lt hlt)
      
    refine' hmin (n - nth p k - 1) hn _
    convert hpn
    have hn11 : n - 1 + 1 = n := Nat.sub_add_cancelₓ (pos_of_gt hlt)
    rwa [tsub_right_comm, add_tsub_cancel_of_le]
    rwa [← hn11, lt_succ_iff] at hlt
    

end Nat

