/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathbin.Data.List.Range

/-!
# Lemmas about list.*_with_index functions.

Some specification lemmas for `list.map_with_index`, `list.mmap_with_index`, `list.foldl_with_index`
and `list.foldr_with_index`.
-/


universe u v

open Function

namespace List

variable {α : Type u} {β : Type v}

section MapWithIndex

@[simp]
theorem map_with_index_nil {α β} (f : ℕ → α → β) : mapWithIndex f [] = [] :=
  rfl

theorem map_with_index_core_eq (l : List α) (f : ℕ → α → β) (n : ℕ) :
    l.mapWithIndexCore f n = l.mapWithIndex fun i a => f (i + n) a := by
  induction' l with hd tl hl generalizing f n
  · simpa
    
  · rw [map_with_index]
    simp [← map_with_index_core, ← hl, ← add_left_commₓ, ← add_assocₓ, ← add_commₓ]
    

theorem map_with_index_eq_enum_map (l : List α) (f : ℕ → α → β) : l.mapWithIndex f = l.enum.map (Function.uncurry f) :=
  by
  induction' l with hd tl hl generalizing f
  · simp [← List.enum_eq_zip_range]
    
  · rw [map_with_index, map_with_index_core, map_with_index_core_eq, hl]
    simp [← enum_eq_zip_range, ← range_succ_eq_map, ← zip_with_map_left, ← map_uncurry_zip_eq_zip_with]
    

@[simp]
theorem map_with_index_cons {α β} (l : List α) (f : ℕ → α → β) (a : α) :
    mapWithIndex f (a :: l) = f 0 a :: mapWithIndex (fun i => f (i + 1)) l := by
  simp [← map_with_index_eq_enum_map, ← enum_eq_zip_range, ← map_uncurry_zip_eq_zip_with, ← range_succ_eq_map, ←
    zip_with_map_left]

@[simp]
theorem length_map_with_index {α β} (l : List α) (f : ℕ → α → β) : (l.mapWithIndex f).length = l.length := by
  induction' l with hd tl IH generalizing f
  · simp
    
  · simp [← IH]
    

@[simp]
theorem nth_le_map_with_index {α β} (l : List α) (f : ℕ → α → β) (i : ℕ) (h : i < l.length)
    (h' : i < (l.mapWithIndex f).length := h.trans_le (l.length_map_with_index f).Ge) :
    (l.mapWithIndex f).nthLe i h' = f i (l.nthLe i h) := by
  simp [← map_with_index_eq_enum_map, ← enum_eq_zip_range]

theorem map_with_index_eq_of_fn {α β} (l : List α) (f : ℕ → α → β) :
    l.mapWithIndex f = ofFnₓ fun i : Finₓ l.length => f (i : ℕ) (l.nthLe i i.is_lt) := by
  induction' l with hd tl IH generalizing f
  · simp
    
  · simpa [← IH]
    

end MapWithIndex

section FoldrWithIndex

/-- Specification of `foldr_with_index_aux`. -/
def foldrWithIndexAuxSpec (f : ℕ → α → β → β) (start : ℕ) (b : β) (as : List α) : β :=
  foldr (uncurry f) b <| enumFrom start as

theorem foldr_with_index_aux_spec_cons (f : ℕ → α → β → β) (start b a as) :
    foldrWithIndexAuxSpec f start b (a :: as) = f start a (foldrWithIndexAuxSpec f (start + 1) b as) :=
  rfl

theorem foldr_with_index_aux_eq_foldr_with_index_aux_spec (f : ℕ → α → β → β) (start b as) :
    foldrWithIndexAux f start b as = foldrWithIndexAuxSpec f start b as := by
  induction as generalizing start
  · rfl
    
  · simp only [← foldr_with_index_aux, ← foldr_with_index_aux_spec_cons, *]
    

theorem foldr_with_index_eq_foldr_enum (f : ℕ → α → β → β) (b : β) (as : List α) :
    foldrWithIndex f b as = foldr (uncurry f) b (enum as) := by
  simp only [← foldr_with_index, ← foldr_with_index_aux_spec, ← foldr_with_index_aux_eq_foldr_with_index_aux_spec, ←
    enum]

end FoldrWithIndex

theorem indexes_values_eq_filter_enum (p : α → Prop) [DecidablePred p] (as : List α) :
    indexesValues p as = filterₓ (p ∘ Prod.snd) (enum as) := by
  simp [← indexes_values, ← foldr_with_index_eq_foldr_enum, ← uncurry, ← filter_eq_foldr]

theorem find_indexes_eq_map_indexes_values (p : α → Prop) [DecidablePred p] (as : List α) :
    findIndexes p as = map Prod.fst (indexesValues p as) := by
  simp only [← indexes_values_eq_filter_enum, ← map_filter_eq_foldr, ← find_indexes, ← foldr_with_index_eq_foldr_enum, ←
    uncurry]

section FoldlWithIndex

/-- Specification of `foldl_with_index_aux`. -/
def foldlWithIndexAuxSpec (f : ℕ → α → β → α) (start : ℕ) (a : α) (bs : List β) : α :=
  foldlₓ (fun a (p : ℕ × β) => f p.fst a p.snd) a <| enumFrom start bs

theorem foldl_with_index_aux_spec_cons (f : ℕ → α → β → α) (start a b bs) :
    foldlWithIndexAuxSpec f start a (b :: bs) = foldlWithIndexAuxSpec f (start + 1) (f start a b) bs :=
  rfl

theorem foldl_with_index_aux_eq_foldl_with_index_aux_spec (f : ℕ → α → β → α) (start a bs) :
    foldlWithIndexAux f start a bs = foldlWithIndexAuxSpec f start a bs := by
  induction bs generalizing start a
  · rfl
    
  · simp [← foldl_with_index_aux, ← foldl_with_index_aux_spec_cons, *]
    

theorem foldl_with_index_eq_foldl_enum (f : ℕ → α → β → α) (a : α) (bs : List β) :
    foldlWithIndex f a bs = foldlₓ (fun a (p : ℕ × β) => f p.fst a p.snd) a (enum bs) := by
  simp only [← foldl_with_index, ← foldl_with_index_aux_spec, ← foldl_with_index_aux_eq_foldl_with_index_aux_spec, ←
    enum]

end FoldlWithIndex

section MfoldWithIndex

variable {m : Type u → Type v} [Monadₓ m]

theorem mfoldr_with_index_eq_mfoldr_enum {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) :
    mfoldrWithIndex f b as = mfoldr (uncurry f) b (enum as) := by
  simp only [← mfoldr_with_index, ← mfoldr_eq_foldr, ← foldr_with_index_eq_foldr_enum, ← uncurry]

theorem mfoldl_with_index_eq_mfoldl_enum [IsLawfulMonad m] {α β} (f : ℕ → β → α → m β) (b : β) (as : List α) :
    mfoldlWithIndex f b as = mfoldl (fun b (p : ℕ × α) => f p.fst b p.snd) b (enum as) := by
  rw [mfoldl_with_index, mfoldl_eq_foldl, foldl_with_index_eq_foldl_enum]

end MfoldWithIndex

section MmapWithIndex

variable {m : Type u → Type v} [Applicativeₓ m]

/-- Specification of `mmap_with_index_aux`. -/
def mmapWithIndexAuxSpec {α β} (f : ℕ → α → m β) (start : ℕ) (as : List α) : m (List β) :=
  List.traverseₓₓ (uncurry f) <| enumFrom start as

-- Note: `traverse` the class method would require a less universe-polymorphic
-- `m : Type u → Type u`.
theorem mmap_with_index_aux_spec_cons {α β} (f : ℕ → α → m β) (start : ℕ) (a : α) (as : List α) :
    mmapWithIndexAuxSpec f start (a :: as) = List.cons <$> f start a <*> mmapWithIndexAuxSpec f (start + 1) as :=
  rfl

theorem mmap_with_index_aux_eq_mmap_with_index_aux_spec {α β} (f : ℕ → α → m β) (start : ℕ) (as : List α) :
    mmapWithIndexAuxₓ f start as = mmapWithIndexAuxSpec f start as := by
  induction as generalizing start
  · rfl
    
  · simp [← mmap_with_index_aux, ← mmap_with_index_aux_spec_cons, *]
    

theorem mmap_with_index_eq_mmap_enum {α β} (f : ℕ → α → m β) (as : List α) :
    mmapWithIndex f as = List.traverseₓₓ (uncurry f) (enum as) := by
  simp only [← mmap_with_index, ← mmap_with_index_aux_spec, ← mmap_with_index_aux_eq_mmap_with_index_aux_spec, ← enum]

end MmapWithIndex

section MmapWithIndex'

variable {m : Type u → Type v} [Applicativeₓ m] [IsLawfulApplicative m]

theorem mmap_with_index'_aux_eq_mmap_with_index_aux {α} (f : ℕ → α → m PUnit) (start : ℕ) (as : List α) :
    mmapWithIndex'Auxₓ f start as = mmapWithIndexAuxₓ f start as *> pure PUnit.unit := by
  induction as generalizing start <;>
    simp' [← mmap_with_index'_aux, ← mmap_with_index_aux, *, ← seq_right_eq, ← const, -comp_const] with functor_norm

theorem mmap_with_index'_eq_mmap_with_index {α} (f : ℕ → α → m PUnit) (as : List α) :
    mmapWithIndex' f as = mmapWithIndex f as *> pure PUnit.unit := by
  apply mmap_with_index'_aux_eq_mmap_with_index_aux

end MmapWithIndex'

end List

