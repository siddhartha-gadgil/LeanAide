/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Multiset.Sort
import Mathbin.Data.List.NodupEquivFin

/-!
# Construct a sorted list from a finset.
-/


namespace Finset

open Multiset Nat

variable {α β : Type _}

/-! ### sort -/


section Sort

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]

/-- `sort s` constructs a sorted list from the unordered set `s`.
  (Uses merge sort algorithm.) -/
def sort (s : Finset α) : List α :=
  sort r s.1

@[simp]
theorem sort_sorted (s : Finset α) : List.Sorted r (sort r s) :=
  sort_sorted _ _

@[simp]
theorem sort_eq (s : Finset α) : ↑(sort r s) = s.1 :=
  sort_eq _ _

@[simp]
theorem sort_nodup (s : Finset α) : (sort r s).Nodup :=
  (by
    rw [sort_eq] <;> exact s.2 : @Multiset.Nodup α (sort r s))

@[simp]
theorem sort_to_finset [DecidableEq α] (s : Finset α) : (sort r s).toFinset = s :=
  List.to_finset_eq (sort_nodup r s) ▸ eq_of_veq (sort_eq r s)

@[simp]
theorem mem_sort {s : Finset α} {a : α} : a ∈ sort r s ↔ a ∈ s :=
  Multiset.mem_sort _

@[simp]
theorem length_sort {s : Finset α} : (sort r s).length = s.card :=
  Multiset.length_sort _

@[simp]
theorem sort_empty : sort r ∅ = [] :=
  Multiset.sort_zero r

@[simp]
theorem sort_singleton (a : α) : sort r {a} = [a] :=
  Multiset.sort_singleton r a

theorem sort_perm_to_list (s : Finset α) : sort r s ~ s.toList := by
  rw [← Multiset.coe_eq_coe]
  simp only [← coe_to_list, ← sort_eq]

end Sort

section SortLinearOrder

variable [LinearOrderₓ α]

theorem sort_sorted_lt (s : Finset α) : List.Sorted (· < ·) (sort (· ≤ ·) s) :=
  (sort_sorted _ _).imp₂ (@lt_of_le_of_neₓ _ _) (sort_nodup _ _)

theorem sorted_zero_eq_min'_aux (s : Finset α) (h : 0 < (s.sort (· ≤ ·)).length) (H : s.Nonempty) :
    (s.sort (· ≤ ·)).nthLe 0 h = s.min' H := by
  let l := s.sort (· ≤ ·)
  apply le_antisymmₓ
  · have : s.min' H ∈ l := (Finset.mem_sort (· ≤ ·)).mpr (s.min'_mem H)
    obtain ⟨i, i_lt, hi⟩ : ∃ (i : _)(hi : i < l.length), l.nth_le i hi = s.min' H := List.mem_iff_nth_le.1 this
    rw [← hi]
    exact (s.sort_sorted (· ≤ ·)).rel_nth_le_of_le _ _ (Nat.zero_leₓ i)
    
  · have : l.nth_le 0 h ∈ s := (Finset.mem_sort (· ≤ ·)).1 (List.nth_le_mem l 0 h)
    exact s.min'_le _ this
    

theorem sorted_zero_eq_min' {s : Finset α} {h : 0 < (s.sort (· ≤ ·)).length} :
    (s.sort (· ≤ ·)).nthLe 0 h =
      s.min'
        (card_pos.1 <| by
          rwa [length_sort] at h) :=
  sorted_zero_eq_min'_aux _ _ _

theorem min'_eq_sorted_zero {s : Finset α} {h : s.Nonempty} :
    s.min' h =
      (s.sort (· ≤ ·)).nthLe 0
        (by
          rw [length_sort]
          exact card_pos.2 h) :=
  (sorted_zero_eq_min'_aux _ _ _).symm

theorem sorted_last_eq_max'_aux (s : Finset α) (h : (s.sort (· ≤ ·)).length - 1 < (s.sort (· ≤ ·)).length)
    (H : s.Nonempty) : (s.sort (· ≤ ·)).nthLe ((s.sort (· ≤ ·)).length - 1) h = s.max' H := by
  let l := s.sort (· ≤ ·)
  apply le_antisymmₓ
  · have : l.nth_le ((s.sort (· ≤ ·)).length - 1) h ∈ s := (Finset.mem_sort (· ≤ ·)).1 (List.nth_le_mem l _ h)
    exact s.le_max' _ this
    
  · have : s.max' H ∈ l := (Finset.mem_sort (· ≤ ·)).mpr (s.max'_mem H)
    obtain ⟨i, i_lt, hi⟩ : ∃ (i : _)(hi : i < l.length), l.nth_le i hi = s.max' H := List.mem_iff_nth_le.1 this
    rw [← hi]
    have : i ≤ l.length - 1 := Nat.le_pred_of_ltₓ i_lt
    exact (s.sort_sorted (· ≤ ·)).rel_nth_le_of_le _ _ (Nat.le_pred_of_ltₓ i_lt)
    

theorem sorted_last_eq_max' {s : Finset α} {h : (s.sort (· ≤ ·)).length - 1 < (s.sort (· ≤ ·)).length} :
    (s.sort (· ≤ ·)).nthLe ((s.sort (· ≤ ·)).length - 1) h =
      s.max'
        (by
          rw [length_sort] at h
          exact card_pos.1 (lt_of_le_of_ltₓ bot_le h)) :=
  sorted_last_eq_max'_aux _ _ _

theorem max'_eq_sorted_last {s : Finset α} {h : s.Nonempty} :
    s.max' h =
      (s.sort (· ≤ ·)).nthLe ((s.sort (· ≤ ·)).length - 1)
        (by
          simpa using Nat.sub_ltₓ (card_pos.mpr h) zero_lt_one) :=
  (sorted_last_eq_max'_aux _ _ _).symm

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `order_iso_of_fin s h`
is the increasing bijection between `fin k` and `s` as an `order_iso`. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of an iso `fin s.card ≃o s` to avoid
casting issues in further uses of this function. -/
def orderIsoOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Finₓ k ≃o s :=
  OrderIso.trans (Finₓ.cast ((length_sort (· ≤ ·)).trans h).symm) <|
    (s.sort_sorted_lt.nthLeIso _).trans <| OrderIso.setCongr _ _ <| Set.ext fun x => mem_sort _

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `order_emb_of_fin s h` is
the increasing bijection between `fin k` and `s` as an order embedding into `α`. Here, `h` is a
proof that the cardinality of `s` is `k`. We use this instead of an embedding `fin s.card ↪o α` to
avoid casting issues in further uses of this function. -/
def orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Finₓ k ↪o α :=
  (orderIsoOfFin s h).toOrderEmbedding.trans (OrderEmbedding.subtype _)

@[simp]
theorem coe_order_iso_of_fin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Finₓ k) :
    ↑(orderIsoOfFin s h i) = orderEmbOfFin s h i :=
  rfl

theorem order_iso_of_fin_symm_apply (s : Finset α) {k : ℕ} (h : s.card = k) (x : s) :
    ↑((s.orderIsoOfFin h).symm x) = (s.sort (· ≤ ·)).indexOf x :=
  rfl

theorem order_emb_of_fin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Finₓ k) :
    s.orderEmbOfFin h i =
      (s.sort (· ≤ ·)).nthLe i
        (by
          rw [length_sort, h]
          exact i.2) :=
  rfl

@[simp]
theorem order_emb_of_fin_mem (s : Finset α) {k : ℕ} (h : s.card = k) (i : Finₓ k) : s.orderEmbOfFin h i ∈ s :=
  (s.orderIsoOfFin h i).2

@[simp]
theorem range_order_emb_of_fin (s : Finset α) {k : ℕ} (h : s.card = k) : Set.Range (s.orderEmbOfFin h) = s := by
  simp [← order_emb_of_fin, ← Set.range_comp coe (s.order_iso_of_fin h)]

/-- The bijection `order_emb_of_fin s h` sends `0` to the minimum of `s`. -/
theorem order_emb_of_fin_zero {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (h.symm ▸ hz)) := by
  simp only [← order_emb_of_fin_apply, ← Subtype.coe_mk, ← sorted_zero_eq_min']

/-- The bijection `order_emb_of_fin s h` sends `k-1` to the maximum of `s`. -/
theorem order_emb_of_fin_last {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨k - 1, Buffer.lt_aux_2 hz⟩ = s.max' (card_pos.mp (h.symm ▸ hz)) := by
  simp [← order_emb_of_fin_apply, ← max'_eq_sorted_last, ← h]

/-- `order_emb_of_fin {a} h` sends any argument to `a`. -/
@[simp]
theorem order_emb_of_fin_singleton (a : α) (i : Finₓ 1) : orderEmbOfFin {a} (card_singleton a) i = a := by
  rw [Subsingleton.elimₓ i ⟨0, zero_lt_one⟩, order_emb_of_fin_zero _ zero_lt_one, min'_singleton]

/-- Any increasing map `f` from `fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `order_emb_of_fin s h`. -/
theorem order_emb_of_fin_unique {s : Finset α} {k : ℕ} (h : s.card = k) {f : Finₓ k → α} (hfs : ∀ x, f x ∈ s)
    (hmono : StrictMono f) : f = s.orderEmbOfFin h := by
  apply Finₓ.strict_mono_unique hmono (s.order_emb_of_fin h).StrictMono
  rw [range_order_emb_of_fin, ← Set.image_univ, ← coe_fin_range, ← coe_image, coe_inj]
  refine' eq_of_subset_of_card_le (fun x hx => _) _
  · rcases mem_image.1 hx with ⟨x, hx, rfl⟩
    exact hfs x
    
  · rw [h, card_image_of_injective _ hmono.injective, fin_range_card]
    

/-- An order embedding `f` from `fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `order_emb_of_fin s h`. -/
theorem order_emb_of_fin_unique' {s : Finset α} {k : ℕ} (h : s.card = k) {f : Finₓ k ↪o α} (hfs : ∀ x, f x ∈ s) :
    f = s.orderEmbOfFin h :=
  RelEmbedding.ext <| Function.funext_iffₓ.1 <| order_emb_of_fin_unique h hfs f.StrictMono

/-- Two parametrizations `order_emb_of_fin` of the same set take the same value on `i` and `j` if
and only if `i = j`. Since they can be defined on a priori not defeq types `fin k` and `fin l`
(although necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j : ℕ)`. -/
@[simp]
theorem order_emb_of_fin_eq_order_emb_of_fin_iff {k l : ℕ} {s : Finset α} {i : Finₓ k} {j : Finₓ l} {h : s.card = k}
    {h' : s.card = l} : s.orderEmbOfFin h i = s.orderEmbOfFin h' j ↔ (i : ℕ) = (j : ℕ) := by
  substs k l
  exact (s.order_emb_of_fin rfl).eq_iff_eq.trans (Finₓ.ext_iff _ _)

/-- Given a finset `s` of size at least `k` in a linear order `α`, the map `order_emb_of_card_le`
is an order embedding from `fin k` to `α` whose image is contained in `s`. Specifically, it maps
`fin k` to an initial segment of `s`. -/
def orderEmbOfCardLe (s : Finset α) {k : ℕ} (h : k ≤ s.card) : Finₓ k ↪o α :=
  (Finₓ.castLe h).trans (s.orderEmbOfFin rfl)

theorem order_emb_of_card_le_mem (s : Finset α) {k : ℕ} (h : k ≤ s.card) (a) : orderEmbOfCardLe s h a ∈ s := by
  simp only [← order_emb_of_card_le, ← RelEmbedding.coe_trans, ← Finset.order_emb_of_fin_mem]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » s)
theorem card_le_of_interleaved {s t : Finset α} (h : ∀ (x y) (_ : x ∈ s) (_ : y ∈ s), x < y → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ t.card + 1 := by
  have h1 : ∀ i : Finₓ (s.card - 1), ↑i + 1 < (s.sort (· ≤ ·)).length := by
    intro i
    rw [Finset.length_sort, ← lt_tsub_iff_right]
    exact i.2
  have h0 : ∀ i : Finₓ (s.card - 1), ↑i < (s.sort (· ≤ ·)).length := fun i => lt_of_le_of_ltₓ (Nat.le_succₓ i) (h1 i)
  have p := fun i : Finₓ (s.card - 1) =>
    h ((s.sort (· ≤ ·)).nthLe i (h0 i)) ((Finset.mem_sort (· ≤ ·)).mp (List.nth_le_mem _ _ (h0 i)))
      ((s.sort (· ≤ ·)).nthLe (i + 1) (h1 i)) ((Finset.mem_sort (· ≤ ·)).mp (List.nth_le_mem _ _ (h1 i)))
      (s.sort_sorted_lt.rel_nth_le_of_lt (h0 i) (h1 i) (Nat.lt_succ_selfₓ i))
  let f : Finₓ (s.card - 1) → t := fun i => ⟨Classical.some (p i), (exists_prop.mp (Classical.some_spec (p i))).1⟩
  have hf : ∀ i j : Finₓ (s.card - 1), i < j → f i < f j := fun i j hij =>
    subtype.coe_lt_coe.mp
      ((exists_prop.mp (Classical.some_spec (p i))).2.2.trans
        (lt_of_le_of_ltₓ ((s.sort_sorted (· ≤ ·)).rel_nth_le_of_le (h1 i) (h0 j) (nat.succ_le_iff.mpr hij))
          (exists_prop.mp (Classical.some_spec (p j))).2.1))
  have key :=
    Fintype.card_le_of_embedding
      (Function.Embedding.mk f fun i j hij =>
        le_antisymmₓ (not_lt.mp (mt (hf j i) (not_lt.mpr (le_of_eqₓ hij))))
          (not_lt.mp (mt (hf i j) (not_lt.mpr (ge_of_eq hij)))))
  rwa [Fintype.card_fin, Fintype.card_coe, tsub_le_iff_right] at key

end SortLinearOrder

instance [HasRepr α] : HasRepr (Finset α) :=
  ⟨fun s => reprₓ s.1⟩

end Finset

