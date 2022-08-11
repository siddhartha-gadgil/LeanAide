/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Finset.Lattice

/-!
# The powerset of a finset
-/


namespace Finset

open Function Multiset

variable {α : Type _} {s t : Finset α}

/-! ### powerset -/


section Powerset

/-- When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as finsets). -/
def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨(s.1.Powerset.pmap Finset.mk) fun t h => nodup_of_le (mem_powerset.1 h) s.Nodup,
    s.Nodup.Powerset.pmap fun a ha b hb => congr_arg Finset.val⟩

@[simp]
theorem mem_powerset {s t : Finset α} : s ∈ powerset t ↔ s ⊆ t := by
  cases s <;>
    simp only [← powerset, ← mem_mk, ← mem_pmap, ← mem_powerset, ← exists_prop, ← exists_eq_right] <;> rw [← val_le_iff]

@[simp, norm_cast]
theorem coe_powerset (s : Finset α) : (s.Powerset : Set (Finset α)) = coe ⁻¹' (s : Set α).Powerset := by
  ext
  simp

@[simp]
theorem empty_mem_powerset (s : Finset α) : ∅ ∈ powerset s :=
  mem_powerset.2 (empty_subset _)

@[simp]
theorem mem_powerset_self (s : Finset α) : s ∈ powerset s :=
  mem_powerset.2 Subset.rfl

theorem powerset_nonempty (s : Finset α) : s.Powerset.Nonempty :=
  ⟨∅, empty_mem_powerset _⟩

@[simp]
theorem powerset_mono {s t : Finset α} : powerset s ⊆ powerset t ↔ s ⊆ t :=
  ⟨fun h => mem_powerset.1 <| h <| mem_powerset_self _, fun st u h =>
    mem_powerset.2 <| Subset.trans (mem_powerset.1 h) st⟩

theorem powerset_injective : Injective (powerset : Finset α → Finset (Finset α)) :=
  (injective_of_le_imp_le _) fun s t => powerset_mono.1

@[simp]
theorem powerset_inj : powerset s = powerset t ↔ s = t :=
  powerset_injective.eq_iff

@[simp]
theorem powerset_empty : (∅ : Finset α).Powerset = {∅} :=
  rfl

@[simp]
theorem powerset_eq_singleton_empty : s.Powerset = {∅} ↔ s = ∅ := by
  rw [← powerset_empty, powerset_inj]

/-- **Number of Subsets of a Set** -/
@[simp]
theorem card_powerset (s : Finset α) : card (powerset s) = 2 ^ card s :=
  (card_pmap _ _ _).trans (card_powerset s.1)

theorem not_mem_of_mem_powerset_of_not_mem {s t : Finset α} {a : α} (ht : t ∈ s.Powerset) (h : a ∉ s) : a ∉ t := by
  apply mt _ h
  apply mem_powerset.1 ht

theorem powerset_insert [DecidableEq α] (s : Finset α) (a : α) :
    powerset (insert a s) = s.Powerset ∪ s.Powerset.Image (insert a) := by
  ext t
  simp only [← exists_prop, ← mem_powerset, ← mem_image, ← mem_union, ← subset_insert_iff]
  by_cases' h : a ∈ t
  · constructor
    · exact fun H => Or.inr ⟨_, H, insert_erase h⟩
      
    · intro H
      cases H
      · exact subset.trans (erase_subset a t) H
        
      · rcases H with ⟨u, hu⟩
        rw [← hu.2]
        exact subset.trans (erase_insert_subset a u) hu.1
        
      
    
  · have : ¬∃ u : Finset α, u ⊆ s ∧ insert a u = t := by
      simp [← Ne.symm (ne_insert_of_not_mem _ _ h)]
    simp [← Finset.erase_eq_of_not_mem h, ← this]
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for any subset. -/
instance decidableExistsOfDecidableSubsets {s : Finset α} {p : ∀ (t) (_ : t ⊆ s), Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∃ (t : _)(h : t ⊆ s), p t h) :=
  decidableOfIff (∃ (t : _)(hs : t ∈ s.Powerset), p t (mem_powerset.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_powerset.2 hs, hp⟩⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for every subset. -/
instance decidableForallOfDecidableSubsets {s : Finset α} {p : ∀ (t) (_ : t ⊆ s), Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∀ (t) (h : t ⊆ s), p t h) :=
  decidableOfIff (∀ (t) (h : t ∈ s.Powerset), p t (mem_powerset.1 h))
    ⟨fun h t hs => h t (mem_powerset.2 hs), fun h _ _ => h _ _⟩

/-- A version of `finset.decidable_exists_of_decidable_subsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableExistsOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop} (hu : ∀ (t) (h : t ⊆ s), Decidable (p t)) :
    Decidable (∃ (t : _)(h : t ⊆ s), p t) :=
  @Finset.decidableExistsOfDecidableSubsets _ _ _ hu

/-- A version of `finset.decidable_forall_of_decidable_subsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableForallOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop} (hu : ∀ (t) (h : t ⊆ s), Decidable (p t)) :
    Decidable (∀ (t) (h : t ⊆ s), p t) :=
  @Finset.decidableForallOfDecidableSubsets _ _ _ hu

end Powerset

section Ssubsets

variable [DecidableEq α]

/-- For `s` a finset, `s.ssubsets` is the finset comprising strict subsets of `s`. -/
def ssubsets (s : Finset α) : Finset (Finset α) :=
  erase (powerset s) s

@[simp]
theorem mem_ssubsets {s t : Finset α} : t ∈ s.ssubsets ↔ t ⊂ s := by
  rw [ssubsets, mem_erase, mem_powerset, ssubset_iff_subset_ne, And.comm]

theorem empty_mem_ssubsets {s : Finset α} (h : s.Nonempty) : ∅ ∈ s.ssubsets := by
  rw [mem_ssubsets, ssubset_iff_subset_ne]
  exact ⟨empty_subset s, h.ne_empty.symm⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊂ » s)
/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for any ssubset. -/
instance decidableExistsOfDecidableSsubsets {s : Finset α} {p : ∀ (t) (_ : t ⊂ s), Prop}
    [∀ (t) (h : t ⊂ s), Decidable (p t h)] : Decidable (∃ t h, p t h) :=
  decidableOfIff (∃ (t : _)(hs : t ∈ s.ssubsets), p t (mem_ssubsets.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_ssubsets.2 hs, hp⟩⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊂ » s)
/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for every ssubset. -/
instance decidableForallOfDecidableSsubsets {s : Finset α} {p : ∀ (t) (_ : t ⊂ s), Prop}
    [∀ (t) (h : t ⊂ s), Decidable (p t h)] : Decidable (∀ t h, p t h) :=
  decidableOfIff (∀ (t) (h : t ∈ s.ssubsets), p t (mem_ssubsets.1 h))
    ⟨fun h t hs => h t (mem_ssubsets.2 hs), fun h _ _ => h _ _⟩

/-- A version of `finset.decidable_exists_of_decidable_ssubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableExistsOfDecidableSsubsets' {s : Finset α} {p : Finset α → Prop} (hu : ∀ (t) (h : t ⊂ s), Decidable (p t)) :
    Decidable (∃ (t : _)(h : t ⊂ s), p t) :=
  @Finset.decidableExistsOfDecidableSsubsets _ _ _ _ hu

/-- A version of `finset.decidable_forall_of_decidable_ssubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableForallOfDecidableSsubsets' {s : Finset α} {p : Finset α → Prop} (hu : ∀ (t) (h : t ⊂ s), Decidable (p t)) :
    Decidable (∀ (t) (h : t ⊂ s), p t) :=
  @Finset.decidableForallOfDecidableSsubsets _ _ _ _ hu

end Ssubsets

section PowersetLen

/-- Given an integer `n` and a finset `s`, then `powerset_len n s` is the finset of subsets of `s`
of cardinality `n`. -/
def powersetLen (n : ℕ) (s : Finset α) : Finset (Finset α) :=
  ⟨((s.1.powersetLen n).pmap Finset.mk) fun t h => nodup_of_le (mem_powerset_len.1 h).1 s.2,
    s.2.powersetLen.pmap fun a ha b hb => congr_arg Finset.val⟩

/-- **Formula for the Number of Combinations** -/
theorem mem_powerset_len {n} {s t : Finset α} : s ∈ powersetLen n t ↔ s ⊆ t ∧ card s = n := by
  cases s <;> simp [← powerset_len, ← val_le_iff.symm] <;> rfl

@[simp]
theorem powerset_len_mono {n} {s t : Finset α} (h : s ⊆ t) : powersetLen n s ⊆ powersetLen n t := fun u h' =>
  mem_powerset_len.2 <| And.imp (fun h₂ => Subset.trans h₂ h) id (mem_powerset_len.1 h')

/-- **Formula for the Number of Combinations** -/
@[simp]
theorem card_powerset_len (n : ℕ) (s : Finset α) : card (powersetLen n s) = Nat.choose (card s) n :=
  (card_pmap _ _ _).trans (card_powerset_len n s.1)

@[simp]
theorem powerset_len_zero (s : Finset α) : Finset.powersetLen 0 s = {∅} := by
  ext
  rw [mem_powerset_len, mem_singleton, card_eq_zero]
  refine'
    ⟨fun h => h.2, fun h => by
      rw [h]
      exact ⟨empty_subset s, rfl⟩⟩

@[simp]
theorem powerset_len_empty (n : ℕ) {s : Finset α} (h : s.card < n) : powersetLen n s = ∅ :=
  Finset.card_eq_zero.mp
    (by
      rw [card_powerset_len, Nat.choose_eq_zero_of_lt h])

theorem powerset_len_eq_filter {n} {s : Finset α} : powersetLen n s = (powerset s).filter fun x => x.card = n := by
  ext
  simp [← mem_powerset_len]

theorem powerset_len_succ_insert [DecidableEq α] {x : α} {s : Finset α} (h : x ∉ s) (n : ℕ) :
    powersetLen n.succ (insert x s) = powersetLen n.succ s ∪ (powersetLen n s).Image (insert x) := by
  rw [powerset_len_eq_filter, powerset_insert, filter_union, ← powerset_len_eq_filter]
  congr
  rw [powerset_len_eq_filter, image_filter]
  congr 1
  ext t
  simp only [← mem_powerset, ← mem_filter, ← Function.comp_app, ← And.congr_right_iff]
  intro ht
  have : x ∉ t := fun H => h (ht H)
  simp [← card_insert_of_not_mem this, ← Nat.succ_inj']

theorem powerset_len_nonempty {n : ℕ} {s : Finset α} (h : n < s.card) : (powersetLen n s).Nonempty := by
  classical
  induction' s using Finset.induction_on with x s hx IH generalizing n
  · simpa using h
    
  · cases n
    · simp
      
    · rw [card_insert_of_not_mem hx, Nat.succ_lt_succ_iff] at h
      rw [powerset_len_succ_insert hx]
      refine' nonempty.mono _ ((IH h).Image (insert x))
      convert subset_union_right _ _
      
    

@[simp]
theorem powerset_len_self (s : Finset α) : powersetLen s.card s = {s} := by
  ext
  rw [mem_powerset_len, mem_singleton]
  constructor
  · exact fun ⟨hs, hc⟩ => eq_of_subset_of_card_le hs hc.Ge
    
  · rintro rfl
    simp
    

theorem powerset_card_bUnion [DecidableEq (Finset α)] (s : Finset α) :
    Finset.powerset s = (range (s.card + 1)).bUnion fun i => powersetLen i s := by
  refine' ext fun a => ⟨fun ha => _, fun ha => _⟩
  · rw [mem_bUnion]
    exact
      ⟨a.card, mem_range.mpr (Nat.lt_succ_of_leₓ (card_le_of_subset (mem_powerset.mp ha))),
        mem_powerset_len.mpr ⟨mem_powerset.mp ha, rfl⟩⟩
    
  · rcases mem_bUnion.mp ha with ⟨i, hi, ha⟩
    exact mem_powerset.mpr (mem_powerset_len.mp ha).1
    

theorem powerset_len_sup [DecidableEq α] (u : Finset α) (n : ℕ) (hn : n < u.card) : (powersetLen n.succ u).sup id = u :=
  by
  apply le_antisymmₓ
  · simp_rw [Finset.sup_le_iff, mem_powerset_len]
    rintro x ⟨h, -⟩
    exact h
    
  · rw [sup_eq_bUnion, le_iff_subset, subset_iff]
    cases' (Nat.succ_le_of_ltₓ hn).eq_or_lt with h' h'
    · simp [← h']
      
    · intro x hx
      simp only [← mem_bUnion, ← exists_prop, ← id.def]
      obtain ⟨t, ht⟩ : ∃ t, t ∈ powerset_len n (u.erase x) := powerset_len_nonempty _
      · refine' ⟨insert x t, _, mem_insert_self _ _⟩
        rw [← insert_erase hx, powerset_len_succ_insert (not_mem_erase _ _)]
        exact mem_union_right _ (mem_image_of_mem _ ht)
        
      · rwa [card_erase_of_mem hx, lt_tsub_iff_right]
        
      
    

@[simp]
theorem powerset_len_card_add (s : Finset α) {i : ℕ} (hi : 0 < i) : s.powersetLen (s.card + i) = ∅ :=
  Finset.powerset_len_empty _ (lt_add_of_pos_right (Finset.card s) hi)

@[simp]
theorem map_val_val_powerset_len (s : Finset α) (i : ℕ) : (s.powersetLen i).val.map Finset.val = s.1.powersetLen i := by
  simp [← Finset.powersetLen, ← map_pmap, ← pmap_eq_map, ← map_id']

theorem powerset_len_map {β : Type _} (f : α ↪ β) (n : ℕ) (s : Finset α) :
    powersetLen n (s.map f) = (powersetLen n s).map (mapEmbedding f).toEmbedding :=
  eq_of_veq <|
    Multiset.map_injective (@eq_of_veq _) <| by
      simp_rw [map_val_val_powerset_len, map_val, Multiset.map_map, Function.comp, RelEmbedding.coe_fn_to_embedding,
        map_embedding_apply, map_val, ← Multiset.map_map _ val, map_val_val_powerset_len, Multiset.powerset_len_map]

end PowersetLen

end Finset

