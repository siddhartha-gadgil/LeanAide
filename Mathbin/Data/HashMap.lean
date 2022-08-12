/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Data.Array.Lemmas
import Mathbin.Data.List.Join
import Mathbin.Data.List.Range
import Mathbin.Data.Pnat.Basic

/-!
# Hash maps

Defines a hash map data structure, representing a finite key-value map
with a value type that may depend on the key type.  The structure
requires a `nat`-valued hash function to associate keys to buckets.

## Main definitions

* `hash_map`: constructed with `mk_hash_map`.

## Implementation details

A hash map with key type `α` and (dependent) value type `β : α → Type*`
consists of an array of *buckets*, which are lists containing
key/value pairs for that bucket.  The hash function is taken modulo `n`
to assign keys to their respective bucket.  Because of this, some care
should be put into the hash function to ensure it evenly distributes
keys.

The bucket array is an `array`.  These have special VM support for
in-place modification if there is only ever one reference to them.  If
one takes special care to never keep references to old versions of a
hash map alive after updating it, then the hash map will be modified
in-place.  In this documentation, when we say a hash map is modified
in-place, we are assuming the API is being used in this manner.

When inserting (`hash_map.insert`), if the number of stored pairs (the
*size*) is going to exceed the number of buckets, then a new hash map
is first created with double the number of buckets and everything in
the old hash map is reinserted along with the new key/value pair.
Otherwise, the bucket array is modified in-place.  The amortized
running time of inserting $$n$$ elements into a hash map is $$O(n)$$.

When removing (`hash_map.erase`), the hash map is modified in-place.
The implementation does not reduce the number of buckets in the hash
map if the size gets too low.

## Tags

hash map

-/


universe u v w

/-- `bucket_array α β` is the underlying data type for `hash_map α β`,
  an array of linked lists of key-value pairs. -/
def BucketArray (α : Type u) (β : α → Type v) (n : ℕ+) :=
  Arrayₓ n (List (Σa, β a))

/-- Make a hash_map index from a `nat` hash value and a (positive) buffer size -/
def HashMap.mkIdx (n : ℕ+) (i : Nat) : Finₓ n :=
  ⟨i % n, Nat.mod_ltₓ _ n.2⟩

namespace BucketArray

section

parameter {α : Type u}{β : α → Type v}(hash_fn : α → Nat)

variable {n : ℕ+} (data : BucketArray α β n)

instance : Inhabited (BucketArray α β n) :=
  ⟨mkArray _ []⟩

/-- Read the bucket corresponding to an element -/
def read (a : α) : List (Σa, β a) :=
  let bidx := HashMap.mkIdx n (hash_fn a)
  data.read bidx

/-- Write the bucket corresponding to an element -/
def write (a : α) (l : List (Σa, β a)) : BucketArray α β n :=
  let bidx := HashMap.mkIdx n (hash_fn a)
  data.write bidx l

/-- Modify (read, apply `f`, and write) the bucket corresponding to an element -/
def modify (a : α) (f : List (Σa, β a) → List (Σa, β a)) : BucketArray α β n :=
  let bidx := HashMap.mkIdx n (hash_fn a)
  Arrayₓ.write data bidx (f (Arrayₓ.read data bidx))

/-- The list of all key-value pairs in the bucket list -/
def asList : List (Σa, β a) :=
  data.toList.join

theorem mem_as_list {a : Σa, β a} : a ∈ data.asList ↔ ∃ i, a ∈ Arrayₓ.read data i := by
  have :
    (∃ (l : List (Σa : α, β a))(i : Finₓ n.val), a ∈ l ∧ Arrayₓ.read data i = l) ↔
      ∃ i : Finₓ n.val, a ∈ Arrayₓ.read data i :=
    by
    rw [exists_swap] <;>
      exact
        exists_congr fun i => by
          simp
  simp [← as_list] <;> simpa [← Arrayₓ.Mem.def, ← and_comm]

/-- Fold a function `f` over the key-value pairs in the bucket list -/
def foldl {δ : Type w} (d : δ) (f : δ → ∀ a, β a → δ) : δ :=
  data.foldl d fun b d => b.foldl (fun r a => f r a.1 a.2) d

theorem foldl_eq {δ : Type w} (d : δ) (f : δ → ∀ a, β a → δ) :
    data.foldl d f = data.asList.foldl (fun r a => f r a.1 a.2) d := by
  rw [foldl, as_list, List.foldl_join, ← Arrayₓ.to_list_foldl]

end

end BucketArray

namespace HashMap

section

parameter {α : Type u}{β : α → Type v}(hash_fn : α → Nat)

/-- Insert the pair `⟨a, b⟩` into the correct location in the bucket array
  (without checking for duplication) -/
def reinsertAux {n} (data : BucketArray α β n) (a : α) (b : β a) : BucketArray α β n :=
  data.modify hash_fn a fun l => ⟨a, b⟩ :: l

theorem mk_as_list (n : ℕ+) : BucketArray.asList (mkArray n [] : BucketArray α β n) = [] :=
  List.eq_nil_iff_forall_not_memₓ.mpr fun x m =>
    let ⟨i, h⟩ := (BucketArray.mem_as_list _).1 m
    h

parameter [DecidableEq α]

/-- Search a bucket for a key `a` and return the value -/
def findAux (a : α) : List (Σa, β a) → Option (β a)
  | [] => none
  | ⟨a', b⟩ :: t => if h : a' = a then some (Eq.recOnₓ h b) else find_aux t

theorem find_aux_iff {a : α} {b : β a} :
    ∀ {l : List (Σa, β a)}, (l.map Sigma.fst).Nodup → (find_aux a l = some b ↔ Sigma.mk a b ∈ l)
  | [], nd =>
    ⟨fun n => by
      injection n, False.elim⟩
  | ⟨a', b'⟩ :: t, nd => by
    by_cases' a' = a
    · clear find_aux_iff
      subst h
      suffices b' = b ↔ b' = b ∨ Sigma.mk a' b ∈ t by
        simpa [← find_aux, ← eq_comm]
      refine' (or_iff_left_of_imp fun m => _).symm
      have : a' ∉ t.map Sigma.fst := nd.not_mem
      exact this.elim (List.mem_map_of_memₓ Sigma.fst m)
      
    · have : Sigma.mk a b ≠ ⟨a', b'⟩ := by
        intro e
        injection e with e
        exact h e.symm
      simp at nd
      simp [← find_aux, ← h, ← Ne.symm h, ← find_aux_iff, ← nd]
      

/-- Returns `tt` if the bucket `l` contains the key `a` -/
def containsAux (a : α) (l : List (Σa, β a)) : Bool :=
  (find_aux a l).isSome

theorem contains_aux_iff {a : α} {l : List (Σa, β a)} (nd : (l.map Sigma.fst).Nodup) :
    contains_aux a l ↔ a ∈ l.map Sigma.fst := by
  unfold contains_aux
  cases' h : find_aux a l with b <;> simp
  · intro (b : β a)(m : Sigma.mk a b ∈ l)
    rw [(find_aux_iff nd).2 m] at h
    contradiction
    
  · show ∃ b : β a, Sigma.mk a b ∈ l
    exact ⟨_, (find_aux_iff nd).1 h⟩
    

/-- Modify a bucket to replace a value in the list. Leaves the list
 unchanged if the key is not found. -/
def replaceAux (a : α) (b : β a) : List (Σa, β a) → List (Σa, β a)
  | [] => []
  | ⟨a', b'⟩ :: t => if a' = a then ⟨a, b⟩ :: t else ⟨a', b'⟩ :: replace_aux t

/-- Modify a bucket to remove a key, if it exists. -/
def eraseAux (a : α) : List (Σa, β a) → List (Σa, β a)
  | [] => []
  | ⟨a', b'⟩ :: t => if a' = a then t else ⟨a', b'⟩ :: erase_aux t

/-- The predicate `valid bkts sz` means that `bkts` satisfies the `hash_map`
  invariants: There are exactly `sz` elements in it, every pair is in the
  bucket determined by its key and the hash function, and no key appears
  multiple times in the list. -/
structure Valid {n} (bkts : BucketArray α β n) (sz : Nat) : Prop where
  len : bkts.asList.length = sz
  idx : ∀ {i} {a : Σa, β a}, a ∈ Arrayₓ.read bkts i → mkIdx n (hash_fn a.1) = i
  Nodup : ∀ i, ((Arrayₓ.read bkts i).map Sigma.fst).Nodup

theorem Valid.idx_enum {n} {bkts : BucketArray α β n} {sz : Nat} (v : valid bkts sz) {i l}
    (he : (i, l) ∈ bkts.toList.enum) {a} {b : β a} (hl : Sigma.mk a b ∈ l) : ∃ h, mkIdx n (hash_fn a) = ⟨i, h⟩ :=
  (Arrayₓ.mem_to_list_enum.mp he).imp fun h e => by
    subst e <;> exact v.idx hl

theorem Valid.idx_enum_1 {n} {bkts : BucketArray α β n} {sz : Nat} (v : valid bkts sz) {i l}
    (he : (i, l) ∈ bkts.toList.enum) {a} {b : β a} (hl : Sigma.mk a b ∈ l) : (mkIdx n (hash_fn a)).1 = i := by
  let ⟨h, e⟩ := v.idx_enum _ he hl
  rw [e] <;> rfl

theorem Valid.as_list_nodup {n} {bkts : BucketArray α β n} {sz : Nat} (v : valid bkts sz) :
    (bkts.asList.map Sigma.fst).Nodup := by
  suffices (bkts.to_list.map (List.map Sigma.fst)).Pairwise List.Disjoint by
    suffices ∀ l, Arrayₓ.Mem l bkts → (l.map Sigma.fst).Nodup by
      simpa [← BucketArray.asList, ← List.nodup_join, *]
    rintro l ⟨i, rfl⟩
    apply v.nodup
  rw [← List.enum_map_snd bkts.to_list, List.pairwise_map, List.pairwise_map]
  have : (bkts.to_list.enum.map Prod.fst).Nodup := by
    simp [← List.nodup_range]
  refine' List.Pairwiseₓ.imp_of_mem _ ((List.pairwise_map _).1 this)
  rw [Prod.forall]
  intro i l₁
  rw [Prod.forall]
  intro j l₂ me₁ me₂ ij
  simp [← List.Disjoint]
  intro a b ml₁ b' ml₂
  apply ij
  rwa [← v.idx_enum_1 _ me₁ ml₁, ← v.idx_enum_1 _ me₂ ml₂]

theorem mk_valid (n : ℕ+) : @valid n (mkArray n []) 0 :=
  ⟨by
    simp [← mk_as_list], fun i a h => by
    cases h, fun i => List.nodup_nil⟩

theorem Valid.find_aux_iff {n} {bkts : BucketArray α β n} {sz : Nat} (v : valid bkts sz) {a : α} {b : β a} :
    find_aux a (bkts.read hash_fn a) = some b ↔ Sigma.mk a b ∈ bkts.asList :=
  (find_aux_iff (v.Nodup _)).trans <| by
    rw [bkts.mem_as_list] <;> exact ⟨fun h => ⟨_, h⟩, fun ⟨i, h⟩ => (v.idx h).symm ▸ h⟩

theorem Valid.contains_aux_iff {n} {bkts : BucketArray α β n} {sz : Nat} (v : valid bkts sz) (a : α) :
    contains_aux a (bkts.read hash_fn a) ↔ a ∈ bkts.asList.map Sigma.fst := by
  simp [← contains_aux, ← Option.is_some_iff_exists, ← v.find_aux_iff hash_fn]

section

parameter
  {n : ℕ+}{bkts : BucketArray α β n}{bidx : Finₓ n}{f : List (Σa, β a) → List (Σa, β a)}(u v1 v2 w : List (Σa, β a))

-- mathport name: «exprL»
local notation "L" => Arrayₓ.read bkts bidx

private def bkts' : BucketArray α β n :=
  Arrayₓ.write bkts bidx (f L)

variable (hl : L = u ++ v1 ++ w) (hfl : f L = u ++ v2 ++ w)

include hl hfl

theorem append_of_modify : ∃ u' w', bkts.asList = u' ++ v1 ++ w' ∧ bkts'.asList = u' ++ v2 ++ w' := by
  unfold BucketArray.asList
  have h : (bidx : ℕ) < bkts.to_list.length := by
    simp only [← bidx.is_lt, ← Arrayₓ.to_list_length]
  refine' ⟨(bkts.to_list.take bidx).join ++ u, w ++ (bkts.to_list.drop (bidx + 1)).join, _, _⟩
  · conv => lhs rw [← List.take_append_dropₓ bidx bkts.to_list, List.drop_eq_nth_le_cons h]simp [← hl]
    simp
    
  · conv => lhs rw [bkts', Arrayₓ.write_to_list, List.update_nth_eq_take_cons_drop _ h]simp [← hfl]
    simp
    

variable (hvnd : (v2.map Sigma.fst).Nodup) (hal : ∀ a : Σa, β a, a ∈ v2 → mkIdx n (hash_fn a.1) = bidx)
  (djuv : (u.map Sigma.fst).Disjoint (v2.map Sigma.fst)) (djwv : (w.map Sigma.fst).Disjoint (v2.map Sigma.fst))

include hvnd hal djuv djwv

theorem Valid.modify {sz : ℕ} (v : valid bkts sz) :
    v1.length ≤ sz + v2.length ∧ valid bkts' (sz + v2.length - v1.length) := by
  rcases append_of_modify u v1 v2 w hl hfl with ⟨u', w', e₁, e₂⟩
  rw [← v.len, e₁]
  suffices valid bkts' (u' ++ v2 ++ w').length by
    simpa [← Ge, ← add_commₓ, ← add_left_commₓ, ← Nat.le_add_rightₓ, ← add_tsub_cancel_left]
  refine' ⟨congr_arg _ e₂, fun i a => _, fun i => _⟩
  · by_cases' bidx = i
    · subst i
      rw [bkts', Arrayₓ.read_write, hfl]
      have := @valid.idx _ _ _ v bidx a
      simp only [← hl, ← List.mem_appendₓ, ← or_imp_distrib, ← forall_and_distrib] at this⊢
      exact ⟨⟨this.1.1, hal _⟩, this.2⟩
      
    · rw [bkts', Arrayₓ.read_write_of_ne _ _ h]
      apply v.idx
      
    
  · by_cases' bidx = i
    · subst i
      rw [bkts', Arrayₓ.read_write, hfl]
      have := @valid.nodup _ _ _ v bidx
      simp [← hl, ← List.nodup_append] at this
      simp [← List.nodup_append, ← this, ← hvnd, ← djuv, ← djwv.symm]
      
    · rw [bkts', Arrayₓ.read_write_of_ne _ _ h]
      apply v.nodup
      
    

end

theorem Valid.replace_aux (a : α) (b : β a) :
    ∀ l : List (Σa, β a),
      a ∈ l.map Sigma.fst →
        ∃ (u w : List (Σa, β a))(b' : _), l = u ++ [⟨a, b'⟩] ++ w ∧ replace_aux a b l = u ++ [⟨a, b⟩] ++ w
  | [] => False.elim
  | ⟨a', b'⟩ :: t => by
    by_cases' e : a' = a
    · subst a'
      suffices
        ∃ (u w : List (Σa, β a))(b'' : β a),
          Sigma.mk a b' :: t = u ++ ⟨a, b''⟩ :: w ∧ replace_aux a b (⟨a, b'⟩ :: t) = u ++ ⟨a, b⟩ :: w
        by
        simpa
      refine' ⟨[], t, b', _⟩
      simp [← replace_aux]
      
    · suffices
        ∀ (x : β a) (_ : Sigma.mk a x ∈ t),
          ∃ (u w : _)(b'' : β a),
            Sigma.mk a' b' :: t = u ++ ⟨a, b''⟩ :: w ∧ Sigma.mk a' b' :: replace_aux a b t = u ++ ⟨a, b⟩ :: w
        by
        simpa [← replace_aux, ← Ne.symm e, ← e]
      intro x m
      have IH :
        ∀ (x : β a) (_ : Sigma.mk a x ∈ t),
          ∃ (u w : _)(b'' : β a), t = u ++ ⟨a, b''⟩ :: w ∧ replace_aux a b t = u ++ ⟨a, b⟩ :: w :=
        by
        simpa using valid.replace_aux t
      rcases IH x m with ⟨u, w, b'', hl, hfl⟩
      exact
        ⟨⟨a', b'⟩ :: u, w, b'', by
          simp [← hl, ← hfl.symm, ← Ne.symm e]⟩
      

theorem Valid.replace {n : ℕ+} {bkts : BucketArray α β n} {sz : ℕ} (a : α) (b : β a)
    (Hc : contains_aux a (bkts.read hash_fn a)) (v : valid bkts sz) :
    valid (bkts.modify hash_fn a (replace_aux a b)) sz := by
  have nd := v.nodup (mk_idx n (hash_fn a))
  rcases HashMap.Valid.replace_aux a b (Arrayₓ.read bkts (mk_idx n (hash_fn a))) ((contains_aux_iff nd).1 Hc) with
    ⟨u, w, b', hl, hfl⟩
  simp [← hl, ← List.nodup_append] at nd
  refine'
      (v.modify hash_fn u [⟨a, b'⟩] [⟨a, b⟩] w hl hfl (List.nodup_singleton _)
          (fun a' e => by
            simp at e <;> rw [e])
          (fun a' e1 e2 => _) fun a' e1 e2 => _).2 <;>
    · revert e1
      simp [-Sigma.exists] at e2
      subst a'
      simp [← nd]
      

theorem Valid.insert {n : ℕ+} {bkts : BucketArray α β n} {sz : ℕ} (a : α) (b : β a)
    (Hnc : ¬contains_aux a (bkts.read hash_fn a)) (v : valid bkts sz) : valid (reinsert_aux bkts a b) (sz + 1) := by
  have nd := v.nodup (mk_idx n (hash_fn a))
  refine'
    (v.modify hash_fn [] [] [⟨a, b⟩] (bkts.read hash_fn a) rfl rfl (List.nodup_singleton _)
        (fun a' e => by
          simp at e <;> rw [e])
        (fun a' => False.elim) fun a' e1 e2 => _).2
  simp [-Sigma.exists] at e2
  subst a'
  exact Hnc ((contains_aux_iff nd).2 e1)

theorem Valid.erase_aux (a : α) :
    ∀ l : List (Σa, β a),
      a ∈ l.map Sigma.fst → ∃ (u w : List (Σa, β a))(b : _), l = u ++ [⟨a, b⟩] ++ w ∧ erase_aux a l = u ++ [] ++ w
  | [] => False.elim
  | ⟨a', b'⟩ :: t => by
    by_cases' e : a' = a
    · subst a'
      simpa [← erase_aux, ← and_comm] using
        show ∃ (u w : _)(x : β a), t = u ++ w ∧ Sigma.mk a b' :: t = u ++ ⟨a, x⟩ :: w from
          ⟨[], t, b', by
            simp ⟩
      
    · simp [← erase_aux, ← e, ← Ne.symm e]
      suffices
        ∀ (b : β a) (_ : Sigma.mk a b ∈ t),
          ∃ (u w : _)(x : β a), Sigma.mk a' b' :: t = u ++ ⟨a, x⟩ :: w ∧ Sigma.mk a' b' :: erase_aux a t = u ++ w
        by
        simpa [← replace_aux, ← Ne.symm e, ← e]
      intro b m
      have IH :
        ∀ (x : β a) (_ : Sigma.mk a x ∈ t), ∃ (u w : _)(x : β a), t = u ++ ⟨a, x⟩ :: w ∧ erase_aux a t = u ++ w := by
        simpa using valid.erase_aux t
      rcases IH b m with ⟨u, w, b'', hl, hfl⟩
      exact
        ⟨⟨a', b'⟩ :: u, w, b'', by
          simp [← hl, ← hfl.symm]⟩
      

theorem Valid.erase {n} {bkts : BucketArray α β n} {sz} (a : α) (Hc : contains_aux a (bkts.read hash_fn a))
    (v : valid bkts sz) : valid (bkts.modify hash_fn a (erase_aux a)) (sz - 1) := by
  have nd := v.nodup (mk_idx n (hash_fn a))
  rcases HashMap.Valid.erase_aux a (Arrayₓ.read bkts (mk_idx n (hash_fn a))) ((contains_aux_iff nd).1 Hc) with
    ⟨u, w, b, hl, hfl⟩
  refine' (v.modify hash_fn u [⟨a, b⟩] [] w hl hfl List.nodup_nil _ _ _).2 <;> simp

end

end HashMap

/-- A hash map data structure, representing a finite key-value map
  with key type `α` and value type `β` (which may depend on `α`). -/
structure HashMap (α : Type u) [DecidableEq α] (β : α → Type v) where
  hashFn : α → Nat
  size : ℕ
  nbuckets : ℕ+
  buckets : BucketArray α β nbuckets
  is_valid : HashMap.Valid hash_fn buckets size

/-- Construct an empty hash map with buffer size `nbuckets` (default 8). -/
def mkHashMap {α : Type u} [DecidableEq α] {β : α → Type v} (hash_fn : α → Nat) (nbuckets := 8) : HashMap α β :=
  let n := if nbuckets = 0 then 8 else nbuckets
  let nz : n > 0 := by
    abstract 
      cases nbuckets <;> simp [← if_pos, ← Nat.succ_ne_zero]
  { hashFn, size := 0, nbuckets := ⟨n, nz⟩, buckets := mkArray n [], is_valid := HashMap.mk_valid _ _ }

namespace HashMap

variable {α : Type u} {β : α → Type v} [DecidableEq α]

/-- Return the value corresponding to a key, or `none` if not found -/
def find (m : HashMap α β) (a : α) : Option (β a) :=
  findAux a (m.buckets.read m.hashFn a)

/-- Return `tt` if the key exists in the map -/
def contains (m : HashMap α β) (a : α) : Bool :=
  (m.find a).isSome

instance : HasMem α (HashMap α β) :=
  ⟨fun a m => m.contains a⟩

/-- Fold a function over the key-value pairs in the map -/
def fold {δ : Type w} (m : HashMap α β) (d : δ) (f : δ → ∀ a, β a → δ) : δ :=
  m.buckets.foldl d f

/-- The list of key-value pairs in the map -/
def entries (m : HashMap α β) : List (Σa, β a) :=
  m.buckets.asList

/-- The list of keys in the map -/
def keys (m : HashMap α β) : List α :=
  m.entries.map Sigma.fst

theorem find_iff (m : HashMap α β) (a : α) (b : β a) : m.find a = some b ↔ Sigma.mk a b ∈ m.entries :=
  m.is_valid.find_aux_iff _

theorem contains_iff (m : HashMap α β) (a : α) : m.contains a ↔ a ∈ m.keys :=
  m.is_valid.contains_aux_iff _ _

theorem entries_empty (hash_fn : α → Nat) (n) : (@mkHashMap α _ β hash_fn n).entries = [] :=
  mk_as_list _

theorem keys_empty (hash_fn : α → Nat) (n) : (@mkHashMap α _ β hash_fn n).keys = [] := by
  dsimp' [← keys] <;> rw [entries_empty] <;> rfl

theorem find_empty (hash_fn : α → Nat) (n a) : (@mkHashMap α _ β hash_fn n).find a = none := by
  induction' h : (@mkHashMap α _ β hash_fn n).find a with <;> [rfl,
    · have := (find_iff _ _ _).1 h
      rw [entries_empty] at this
      contradiction
      ]

theorem not_contains_empty (hash_fn : α → Nat) (n a) : ¬(@mkHashMap α _ β hash_fn n).contains a := by
  apply bool_iff_false.2 <;> dsimp' [← contains] <;> rw [find_empty] <;> rfl

theorem insert_lemma (hash_fn : α → Nat) {n n'} {bkts : BucketArray α β n} {sz} (v : Valid hash_fn bkts sz) :
    Valid hash_fn (bkts.foldl (mkArray _ [] : BucketArray α β n') (reinsertAux hash_fn)) sz := by
  suffices
    ∀ (l : List (Σa, β a)) (t : BucketArray α β n') (sz),
      valid hash_fn t sz →
        ((l ++ t.asList).map Sigma.fst).Nodup →
          valid hash_fn (l.foldl (fun r (a : Σa, β a) => reinsert_aux hash_fn r a.1 a.2) t) (sz + l.length)
    by
    have p := this bkts.as_list _ _ (mk_valid _ _)
    rw [mk_as_list, List.append_nil, zero_addₓ, v.len] at p
    rw [BucketArray.foldl_eq]
    exact p (v.as_list_nodup _)
  intro l
  induction' l with c l IH <;> intro t sz v nd
  · exact v
    
  rw
    [show sz + (c :: l).length = sz + 1 + l.length by
      simp [← add_commₓ, ← add_assocₓ]]
  rcases show
      (l.map Sigma.fst).Nodup ∧
        ((BucketArray.asList t).map Sigma.fst).Nodup ∧
          c.fst ∉ l.map Sigma.fst ∧
            c.fst ∉ (BucketArray.asList t).map Sigma.fst ∧
              (l.map Sigma.fst).Disjoint ((BucketArray.asList t).map Sigma.fst)
      by
      simpa [← List.nodup_append, ← not_or_distrib, ← and_comm, ← And.left_comm] using nd with
    ⟨nd1, nd2, nm1, nm2, dj⟩
  have v' := v.insert _ _ c.2 fun Hc => nm2 <| (v.contains_aux_iff _ c.1).1 Hc
  apply IH _ _ v'
  suffices
    ∀ ⦃a : α⦄ (b : β a), Sigma.mk a b ∈ l → ∀ b' : β a, Sigma.mk a b' ∈ (reinsert_aux hash_fn t c.1 c.2).asList → False
    by
    simpa [← List.nodup_append, ← nd1, ← v'.as_list_nodup _, ← List.Disjoint]
  intro a b m1 b' m2
  rcases(reinsert_aux hash_fn t c.1 c.2).mem_as_list.1 m2 with ⟨i, im⟩
  have : Sigma.mk a b' ∉ Arrayₓ.read t i := by
    intro m3
    have : a ∈ List.map Sigma.fst t.as_list := List.mem_map_of_memₓ Sigma.fst (t.mem_as_list.2 ⟨_, m3⟩)
    exact dj (List.mem_map_of_memₓ Sigma.fst m1) this
  by_cases' h : mk_idx n' (hash_fn c.1) = i
  · subst h
    have e : Sigma.mk a b' = ⟨c.1, c.2⟩ := by
      simpa [← reinsert_aux, ← BucketArray.modify, ← Arrayₓ.read_write, ← this] using im
    injection e with e
    subst a
    exact nm1.elim (@List.mem_map_of_memₓ _ _ Sigma.fst _ _ m1)
    
  · apply this
    simpa [← reinsert_aux, ← BucketArray.modify, ← Arrayₓ.read_write_of_ne _ _ h] using im
    

/-- Insert a key-value pair into the map. (Modifies `m` in-place when applicable) -/
def insert : ∀ (m : HashMap α β) (a : α) (b : β a), HashMap α β
  | ⟨hash_fn, size, n, buckets, v⟩, a, b =>
    let bkt := buckets.read hash_fn a
    if hc : containsAux a bkt then
      { hashFn, size, nbuckets := n, buckets := buckets.modify hash_fn a (replaceAux a b),
        is_valid := v.replace _ a b hc }
    else
      let size' := size + 1
      let buckets' := buckets.modify hash_fn a fun l => ⟨a, b⟩ :: l
      let valid' := v.insert _ a b hc
      if size' ≤ n then { hashFn, size := size', nbuckets := n, buckets := buckets', is_valid := valid' }
      else
        let n' : ℕ+ :=
          ⟨n * 2,
            mul_pos n.2
              (by
                decide)⟩
        let buckets'' : BucketArray α β n' := buckets'.foldl (mkArray _ []) (reinsertAux hash_fn)
        { hashFn, size := size', nbuckets := n', buckets := buckets'', is_valid := insert_lemma _ valid' }

theorem mem_insert :
    ∀ (m : HashMap α β) (a b a' b'),
      (Sigma.mk a' b' : Sigma β) ∈ (m.insert a b).entries ↔ if a = a' then HEq b b' else Sigma.mk a' b' ∈ m.entries
  | ⟨hash_fn, size, n, bkts, v⟩, a, b, a', b' => by
    let bkt := bkts.read hash_fn a
    have nd : (bkt.map Sigma.fst).Nodup := v.nodup (mk_idx n (hash_fn a))
    have lem :
      ∀ (bkts' : BucketArray α β n) (v1 u w) (hl : BucketArray.asList bkts = u ++ v1 ++ w)
        (hfl : BucketArray.asList bkts' = u ++ [⟨a, b⟩] ++ w)
        (veq : v1 = [] ∧ ¬contains_aux a bkt ∨ ∃ b'', v1 = [⟨a, b''⟩]),
        Sigma.mk a' b' ∈ bkts'.asList ↔ if a = a' then HEq b b' else Sigma.mk a' b' ∈ bkts.as_list :=
      by
      intro bkts' v1 u w hl hfl veq
      rw [hl, hfl]
      by_cases' h : a = a'
      · subst a'
        suffices b = b' ∨ Sigma.mk a b' ∈ u ∨ Sigma.mk a b' ∈ w ↔ b = b' by
          simpa [← eq_comm, ← Or.left_comm]
        refine' or_iff_left_of_imp (Not.elim <| not_or_distrib.2 _)
        rcases veq with (⟨rfl, Hnc⟩ | ⟨b'', rfl⟩)
        · have na := (not_iff_not_of_iff <| v.contains_aux_iff _ _).1 Hnc
          simp [← hl, ← not_or_distrib] at na
          simp [← na]
          
        · have nd' := v.as_list_nodup _
          simp [← hl, ← List.nodup_append] at nd'
          simp [← nd']
          
        
      · suffices Sigma.mk a' b' ∉ v1 by
          simp [← h, ← Ne.symm h, ← this]
        rcases veq with (⟨rfl, Hnc⟩ | ⟨b'', rfl⟩) <;> simp [← Ne.symm h]
        
    by_cases' Hc : (contains_aux a bkt : Prop)
    · rcases HashMap.Valid.replace_aux a b (Arrayₓ.read bkts (mk_idx n (hash_fn a))) ((contains_aux_iff nd).1 Hc) with
        ⟨u', w', b'', hl', hfl'⟩
      rcases append_of_modify u' [⟨a, b''⟩] [⟨a, b⟩] w' hl' hfl' with ⟨u, w, hl, hfl⟩
      simpa [← insert, ← @dif_pos (contains_aux a bkt) _ Hc] using lem _ _ u w hl hfl (Or.inr ⟨b'', rfl⟩)
      
    · let size' := size + 1
      let bkts' := bkts.modify hash_fn a fun l => ⟨a, b⟩ :: l
      have mi : Sigma.mk a' b' ∈ bkts'.as_list ↔ if a = a' then HEq b b' else Sigma.mk a' b' ∈ bkts.as_list :=
        let ⟨u, w, hl, hfl⟩ := append_of_modify [] [] [⟨a, b⟩] _ rfl rfl
        lem bkts' _ u w hl hfl <| Or.inl ⟨rfl, Hc⟩
      simp [← insert, ← @dif_neg (contains_aux a bkt) _ Hc]
      by_cases' h : size' ≤ n
      · simpa [← show size' ≤ n from h] using mi
        
      · let n' : ℕ+ :=
          ⟨n * 2,
            mul_pos n.2
              (by
                decide)⟩
        let bkts'' : BucketArray α β n' := bkts'.foldl (mkArray _ []) (reinsert_aux hash_fn)
        suffices Sigma.mk a' b' ∈ bkts''.as_list ↔ Sigma.mk a' b' ∈ bkts'.as_list.reverse by
          simpa [← show ¬size' ≤ n from h, ← mi]
        rw [show bkts'' = bkts'.as_list.foldl _ _ from bkts'.foldl_eq _ _, ← List.foldr_reverse]
        induction' bkts'.as_list.reverse with a l IH
        · simp [← mk_as_list]
          
        · cases' a with a'' b''
          let B :=
            l.foldr (fun (y : Sigma β) (x : BucketArray α β n') => reinsert_aux hash_fn x y.1 y.2) (mkArray n' [])
          rcases append_of_modify [] [] [⟨a'', b''⟩] _ rfl rfl with ⟨u, w, hl, hfl⟩
          simp [← IH.symm, ← Or.left_comm, ← show B.as_list = _ from hl, ←
            show (reinsert_aux hash_fn B a'' b'').asList = _ from hfl]
          
        
      

theorem find_insert_eq (m : HashMap α β) (a : α) (b : β a) : (m.insert a b).find a = some b :=
  (find_iff (m.insert a b) a b).2 <|
    (mem_insert m a b a b).2 <| by
      rw [if_pos rfl]

theorem find_insert_ne (m : HashMap α β) (a a' : α) (b : β a) (h : a ≠ a') : (m.insert a b).find a' = m.find a' :=
  Option.eq_of_eq_some fun b' =>
    let t := mem_insert m a b a' b'
    (find_iff _ _ _).trans <|
      Iff.trans
        (by
          rwa [if_neg h] at t)
        (find_iff _ _ _).symm

theorem find_insert (m : HashMap α β) (a' a : α) (b : β a) :
    (m.insert a b).find a' = if h : a = a' then some (Eq.recOnₓ h b) else m.find a' :=
  if h : a = a' then by
    rw [dif_pos h] <;>
      exact
        match a', h with
        | _, rfl => find_insert_eq m a b
  else by
    rw [dif_neg h] <;> exact find_insert_ne m a a' b h

/-- Insert a list of key-value pairs into the map. (Modifies `m` in-place when applicable) -/
def insertAll (l : List (Σa, β a)) (m : HashMap α β) : HashMap α β :=
  l.foldl (fun m ⟨a, b⟩ => insert m a b) m

/-- Construct a hash map from a list of key-value pairs. -/
def ofList (l : List (Σa, β a)) (hash_fn) : HashMap α β :=
  insertAll l (mkHashMap hash_fn (2 * l.length))

/-- Remove a key from the map. (Modifies `m` in-place when applicable) -/
def erase (m : HashMap α β) (a : α) : HashMap α β :=
  match m with
  | ⟨hash_fn, size, n, buckets, v⟩ =>
    if hc : containsAux a (buckets.read hash_fn a) then
      { hashFn, size := size - 1, nbuckets := n, buckets := buckets.modify hash_fn a (eraseAux a),
        is_valid := v.erase _ a hc }
    else m

theorem mem_erase :
    ∀ (m : HashMap α β) (a a' b'),
      (Sigma.mk a' b' : Sigma β) ∈ (m.erase a).entries ↔ a ≠ a' ∧ Sigma.mk a' b' ∈ m.entries
  | ⟨hash_fn, size, n, bkts, v⟩, a, a', b' => by
    let bkt := bkts.read hash_fn a
    by_cases' Hc : (contains_aux a bkt : Prop)
    · let bkts' := bkts.modify hash_fn a (erase_aux a)
      suffices Sigma.mk a' b' ∈ bkts'.as_list ↔ a ≠ a' ∧ Sigma.mk a' b' ∈ bkts.as_list by
        simpa [← erase, ← @dif_pos (contains_aux a bkt) _ Hc]
      have nd := v.nodup (mk_idx n (hash_fn a))
      rcases valid.erase_aux a bkt ((contains_aux_iff nd).1 Hc) with ⟨u', w', b, hl', hfl'⟩
      rcases append_of_modify u' [⟨a, b⟩] [] _ hl' hfl' with ⟨u, w, hl, hfl⟩
      suffices ∀ _ : Sigma.mk a' b' ∈ u ∨ Sigma.mk a' b' ∈ w, a ≠ a' by
        have :
          Sigma.mk a' b' ∈ u ∨ Sigma.mk a' b' ∈ w ↔
            (¬a = a' ∧ a' = a) ∧ HEq b' b ∨ ¬a = a' ∧ (Sigma.mk a' b' ∈ u ∨ Sigma.mk a' b' ∈ w) :=
          by
          simp [← eq_comm, ← not_and_self_iff, ← and_iff_right_of_imp this]
        simpa [← hl, ← show bkts'.as_list = _ from hfl, ← and_or_distrib_left, ← and_comm, ← And.left_comm, ←
          Or.left_comm]
      rintro m rfl
      revert m
      apply not_or_distrib.2
      have nd' := v.as_list_nodup _
      simp [← hl, ← List.nodup_append] at nd'
      simp [← nd']
      
    · suffices ∀ _ : Sigma.mk a' b' ∈ BucketArray.asList bkts, a ≠ a' by
        simp [← erase, ← @dif_neg (contains_aux a bkt) _ Hc, ← entries, ← and_iff_right_of_imp this]
      rintro m rfl
      exact Hc ((v.contains_aux_iff _ _).2 (List.mem_map_of_memₓ Sigma.fst m))
      

theorem find_erase_eq (m : HashMap α β) (a : α) : (m.erase a).find a = none := by
  cases' h : (m.erase a).find a with b
  · rfl
    
  exact absurd rfl ((mem_erase m a a b).1 ((find_iff (m.erase a) a b).1 h)).left

theorem find_erase_ne (m : HashMap α β) (a a' : α) (h : a ≠ a') : (m.erase a).find a' = m.find a' :=
  Option.eq_of_eq_some fun b' =>
    (find_iff _ _ _).trans <| (mem_erase m a a' b').trans <| (and_iff_right h).trans (find_iff _ _ _).symm

theorem find_erase (m : HashMap α β) (a' a : α) : (m.erase a).find a' = if a = a' then none else m.find a' :=
  if h : a = a' then by
    subst a' <;> simp [← find_erase_eq m a]
  else by
    rw [if_neg h] <;> exact find_erase_ne m a a' h

section Stringₓ

variable [HasToString α] [∀ a, HasToString (β a)]

open Prod

private def key_data_to_string (a : α) (b : β a) (first : Bool) : Stringₓ :=
  (if first then "" else ", ") ++ s! "{a } ← {b}"

private def to_string (m : HashMap α β) : Stringₓ :=
  "⟨" ++ fst (fold m ("", true) fun p a b => (fst p ++ keyDataToString a b (snd p), false)) ++ "⟩"

instance : HasToString (HashMap α β) :=
  ⟨toString⟩

end Stringₓ

section Format

open Format Prod

variable [has_to_format α] [∀ a, has_to_format (β a)]

private unsafe def format_key_data (a : α) (b : β a) (first : Bool) : format :=
  (if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt a ++ space ++ to_fmt "←" ++ space ++ to_fmt b

private unsafe def to_format (m : HashMap α β) : format :=
  Groupₓ <|
    to_fmt "⟨" ++ nest 1 (fst (fold m (to_fmt "", true) fun p a b => (fst p ++ format_key_data a b (snd p), false))) ++
      to_fmt "⟩"

unsafe instance : has_to_format (HashMap α β) :=
  ⟨to_format⟩

end Format

/-- `hash_map` with key type `nat` and value type that may vary. -/
instance {β : ℕ → Type _} : Inhabited (HashMap ℕ β) :=
  ⟨mkHashMap id⟩

end HashMap

