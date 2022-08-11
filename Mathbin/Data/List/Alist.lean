/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
import Mathbin.Data.List.Sigma

/-!
# Association Lists

This file defines association lists. An association list is a list where every element consists of
a key and a value, and no two entries have the same key. The type of the value is allowed to be
dependent on the type of the key.

This type dependence is implemented using `sigma`: The elements of the list are of type `sigma β`,
for some type index `β`.

## Main definitions

Association lists are represented by the `alist` structure. This file defines this structure and
provides ways to access, modify, and combine `alist`s.

* `alist.keys` returns a list of keys of the alist.
* `alist.has_mem` returns membership in the set of keys.
* `alist.erase` removes a certain key.
* `alist.insert` adds a key-value mapping to the list.
* `alist.union` combines two association lists.

## References

* <https://en.wikipedia.org/wiki/Association_list>

-/


universe u v w

open List

variable {α : Type u} {β : α → Type v}

/-- `alist β` is a key-value map stored as a `list` (i.e. a linked list).
  It is a wrapper around certain `list` functions with the added constraint
  that the list have unique keys. -/
structure Alist (β : α → Type v) : Type max u v where
  entries : List (Sigma β)
  Nodupkeys : entries.Nodupkeys

/-- Given `l : list (sigma β)`, create a term of type `alist β` by removing
entries with duplicate keys. -/
def List.toAlist [DecidableEq α] {β : α → Type v} (l : List (Sigma β)) : Alist β where
  entries := _
  Nodupkeys := nodupkeys_dedupkeys l

namespace Alist

@[ext]
theorem ext : ∀ {s t : Alist β}, s.entries = t.entries → s = t
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩, H => by
    congr

theorem ext_iff {s t : Alist β} : s = t ↔ s.entries = t.entries :=
  ⟨congr_arg _, ext⟩

instance [DecidableEq α] [∀ a, DecidableEq (β a)] : DecidableEq (Alist β) := fun xs ys => by
  rw [ext_iff] <;> infer_instance

/-! ### keys -/


/-- The list of keys of an association list. -/
def keys (s : Alist β) : List α :=
  s.entries.keys

theorem keys_nodup (s : Alist β) : s.keys.Nodup :=
  s.Nodupkeys

/-! ### mem -/


/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : HasMem α (Alist β) :=
  ⟨fun a s => a ∈ s.keys⟩

theorem mem_keys {a : α} {s : Alist β} : a ∈ s ↔ a ∈ s.keys :=
  Iff.rfl

theorem mem_of_perm {a : α} {s₁ s₂ : Alist β} (p : s₁.entries ~ s₂.entries) : a ∈ s₁ ↔ a ∈ s₂ :=
  (p.map Sigma.fst).mem_iff

/-! ### empty -/


/-- The empty association list. -/
instance : HasEmptyc (Alist β) :=
  ⟨⟨[], nodupkeys_nil⟩⟩

instance : Inhabited (Alist β) :=
  ⟨∅⟩

theorem not_mem_empty (a : α) : a ∉ (∅ : Alist β) :=
  not_mem_nilₓ a

@[simp]
theorem empty_entries : (∅ : Alist β).entries = [] :=
  rfl

@[simp]
theorem keys_empty : (∅ : Alist β).keys = [] :=
  rfl

/-! ### singleton -/


/-- The singleton association list. -/
def singleton (a : α) (b : β a) : Alist β :=
  ⟨[⟨a, b⟩], nodupkeys_singleton _⟩

@[simp]
theorem singleton_entries (a : α) (b : β a) : (singleton a b).entries = [Sigma.mk a b] :=
  rfl

@[simp]
theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] :=
  rfl

/-! ### lookup -/


section

variable [DecidableEq α]

/-- Look up the value associated to a key in an association list. -/
def lookup (a : α) (s : Alist β) : Option (β a) :=
  s.entries.lookup a

@[simp]
theorem lookup_empty (a) : lookup a (∅ : Alist β) = none :=
  rfl

theorem lookup_is_some {a : α} {s : Alist β} : (s.lookup a).isSome ↔ a ∈ s :=
  lookup_is_some

theorem lookup_eq_none {a : α} {s : Alist β} : lookup a s = none ↔ a ∉ s :=
  lookup_eq_none

theorem perm_lookup {a : α} {s₁ s₂ : Alist β} (p : s₁.entries ~ s₂.entries) : s₁.lookup a = s₂.lookup a :=
  perm_lookup _ s₁.Nodupkeys s₂.Nodupkeys p

instance (a : α) (s : Alist β) : Decidable (a ∈ s) :=
  decidableOfIff _ lookup_is_some

/-! ### replace -/


/-- Replace a key with a given value in an association list.
  If the key is not present it does nothing. -/
def replace (a : α) (b : β a) (s : Alist β) : Alist β :=
  ⟨kreplace a b s.entries, (kreplace_nodupkeys a b).2 s.Nodupkeys⟩

@[simp]
theorem keys_replace (a : α) (b : β a) (s : Alist β) : (replace a b s).keys = s.keys :=
  keys_kreplace _ _ _

@[simp]
theorem mem_replace {a a' : α} {b : β a} {s : Alist β} : a' ∈ replace a b s ↔ a' ∈ s := by
  rw [mem_keys, keys_replace, ← mem_keys]

theorem perm_replace {a : α} {b : β a} {s₁ s₂ : Alist β} :
    s₁.entries ~ s₂.entries → (replace a b s₁).entries ~ (replace a b s₂).entries :=
  Perm.kreplace s₁.Nodupkeys

end

/-- Fold a function over the key-value pairs in the map. -/
def foldl {δ : Type w} (f : δ → ∀ a, β a → δ) (d : δ) (m : Alist β) : δ :=
  m.entries.foldl (fun r a => f r a.1 a.2) d

/-! ### erase -/


section

variable [DecidableEq α]

/-- Erase a key from the map. If the key is not present, do nothing. -/
def erase (a : α) (s : Alist β) : Alist β :=
  ⟨s.entries.kerase a, s.Nodupkeys.kerase a⟩

@[simp]
theorem keys_erase (a : α) (s : Alist β) : (erase a s).keys = s.keys.erase a :=
  keys_kerase

@[simp]
theorem mem_erase {a a' : α} {s : Alist β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s := by
  rw [mem_keys, keys_erase, s.keys_nodup.mem_erase_iff, ← mem_keys]

theorem perm_erase {a : α} {s₁ s₂ : Alist β} : s₁.entries ~ s₂.entries → (erase a s₁).entries ~ (erase a s₂).entries :=
  Perm.kerase s₁.Nodupkeys

@[simp]
theorem lookup_erase (a) (s : Alist β) : lookup a (erase a s) = none :=
  lookup_kerase a s.Nodupkeys

@[simp]
theorem lookup_erase_ne {a a'} {s : Alist β} (h : a ≠ a') : lookup a (erase a' s) = lookup a s :=
  lookup_kerase_ne h

theorem erase_erase (a a' : α) (s : Alist β) : (s.erase a).erase a' = (s.erase a').erase a :=
  ext <| kerase_kerase

/-! ### insert -/


/-- Insert a key-value pair into an association list and erase any existing pair
  with the same key. -/
def insert (a : α) (b : β a) (s : Alist β) : Alist β :=
  ⟨kinsert a b s.entries, kinsert_nodupkeys a b s.Nodupkeys⟩

@[simp]
theorem insert_entries {a} {b : β a} {s : Alist β} : (insert a b s).entries = Sigma.mk a b :: kerase a s.entries :=
  rfl

theorem insert_entries_of_neg {a} {b : β a} {s : Alist β} (h : a ∉ s) : (insert a b s).entries = ⟨a, b⟩ :: s.entries :=
  by
  rw [insert_entries, kerase_of_not_mem_keys h]

@[simp]
theorem mem_insert {a a'} {b' : β a'} (s : Alist β) : a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
  mem_keys_kinsert

@[simp]
theorem keys_insert {a} {b : β a} (s : Alist β) : (insert a b s).keys = a :: s.keys.erase a := by
  simp [← insert, ← keys, ← keys_kerase]

theorem perm_insert {a} {b : β a} {s₁ s₂ : Alist β} (p : s₁.entries ~ s₂.entries) :
    (insert a b s₁).entries ~ (insert a b s₂).entries := by
  simp only [← insert_entries] <;> exact p.kinsert s₁.nodupkeys

@[simp]
theorem lookup_insert {a} {b : β a} (s : Alist β) : lookup a (insert a b s) = some b := by
  simp only [← lookup, ← insert, ← lookup_kinsert]

@[simp]
theorem lookup_insert_ne {a a'} {b' : β a'} {s : Alist β} (h : a ≠ a') : lookup a (insert a' b' s) = lookup a s :=
  lookup_kinsert_ne h

@[simp]
theorem lookup_to_alist {a} (s : List (Sigma β)) : lookup a s.toAlist = s.lookup a := by
  rw [List.toAlist, lookup, lookup_dedupkeys]

@[simp]
theorem insert_insert {a} {b b' : β a} (s : Alist β) : (s.insert a b).insert a b' = s.insert a b' := by
  ext : 1 <;> simp only [← Alist.insert_entries, ← List.kerase_cons_eq] <;> constructorm* _ ∧ _ <;> rfl

theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : Alist β) (h : a ≠ a') :
    ((s.insert a b).insert a' b').entries ~ ((s.insert a' b').insert a b).entries := by
  simp only [← insert_entries] <;>
    rw [kerase_cons_ne, kerase_cons_ne, kerase_comm] <;> [apply perm.swap, exact h, exact h.symm]

@[simp]
theorem insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = singleton a b :=
  ext <| by
    simp only [← Alist.insert_entries, ← List.kerase_cons_eq, ← and_selfₓ, ← Alist.singleton_entries, ← heq_iff_eq, ←
      eq_self_iff_true]

@[simp]
theorem entries_to_alist (xs : List (Sigma β)) : (List.toAlist xs).entries = dedupkeys xs :=
  rfl

theorem to_alist_cons (a : α) (b : β a) (xs : List (Sigma β)) : List.toAlist (⟨a, b⟩ :: xs) = insert a b xs.toAlist :=
  rfl

/-! ### extract -/


/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : Alist β) : Option (β a) × Alist β :=
  have : (kextract a s.entries).2.Nodupkeys := by
    rw [kextract_eq_lookup_kerase] <;> exact s.nodupkeys.kerase _
  match kextract a s.entries, this with
  | (b, l), h => (b, ⟨l, h⟩)

@[simp]
theorem extract_eq_lookup_erase (a : α) (s : Alist β) : extract a s = (lookup a s, erase a s) := by
  simp [← extract] <;> constructor <;> rfl

/-! ### union -/


/-- `s₁ ∪ s₂` is the key-based union of two association lists. It is
left-biased: if there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`.
-/
def union (s₁ s₂ : Alist β) : Alist β :=
  ⟨s₁.entries.kunion s₂.entries, s₁.Nodupkeys.kunion s₂.Nodupkeys⟩

instance : HasUnion (Alist β) :=
  ⟨union⟩

@[simp]
theorem union_entries {s₁ s₂ : Alist β} : (s₁ ∪ s₂).entries = kunion s₁.entries s₂.entries :=
  rfl

@[simp]
theorem empty_union {s : Alist β} : (∅ : Alist β) ∪ s = s :=
  ext rfl

@[simp]
theorem union_empty {s : Alist β} : s ∪ (∅ : Alist β) = s :=
  ext <| by
    simp

@[simp]
theorem mem_union {a} {s₁ s₂ : Alist β} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  mem_keys_kunion

theorem perm_union {s₁ s₂ s₃ s₄ : Alist β} (p₁₂ : s₁.entries ~ s₂.entries) (p₃₄ : s₃.entries ~ s₄.entries) :
    (s₁ ∪ s₃).entries ~ (s₂ ∪ s₄).entries := by
  simp [← p₁₂.kunion s₃.nodupkeys p₃₄]

theorem union_erase (a : α) (s₁ s₂ : Alist β) : erase a (s₁ ∪ s₂) = erase a s₁ ∪ erase a s₂ :=
  ext kunion_kerase.symm

@[simp]
theorem lookup_union_left {a} {s₁ s₂ : Alist β} : a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
  lookup_kunion_left

@[simp]
theorem lookup_union_right {a} {s₁ s₂ : Alist β} : a ∉ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
  lookup_kunion_right

@[simp]
theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : Alist β} :
    b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
  mem_lookup_kunion

theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : Alist β} :
    b ∈ lookup a (s₁ ∪ s₃) → a ∉ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
  mem_lookup_kunion_middle

theorem insert_union {a} {b : β a} {s₁ s₂ : Alist β} : insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ := by
  ext <;> simp

theorem union_assoc {s₁ s₂ s₃ : Alist β} : (s₁ ∪ s₂ ∪ s₃).entries ~ (s₁ ∪ (s₂ ∪ s₃)).entries :=
  lookup_ext (Alist.nodupkeys _) (Alist.nodupkeys _)
    (by
      simp [← Decidable.not_or_iff_and_not, ← or_assoc, ← and_or_distrib_left, ← and_assoc])

end

/-! ### disjoint -/


/-- Two associative lists are disjoint if they have no common keys. -/
def Disjoint (s₁ s₂ : Alist β) : Prop :=
  ∀, ∀ k ∈ s₁.keys, ∀, ¬k ∈ s₂.keys

variable [DecidableEq α]

theorem union_comm_of_disjoint {s₁ s₂ : Alist β} (h : Disjoint s₁ s₂) : (s₁ ∪ s₂).entries ~ (s₂ ∪ s₁).entries :=
  lookup_ext (Alist.nodupkeys _) (Alist.nodupkeys _)
    (by
      intros
      simp
      constructor <;> intro h'
      cases h'
      · right
        refine' ⟨_, h'⟩
        apply h
        rw [keys, ← List.lookup_is_some, h']
        exact rfl
        
      · left
        rw [h'.2]
        
      cases h'
      · right
        refine' ⟨_, h'⟩
        intro h''
        apply h _ h''
        rw [keys, ← List.lookup_is_some, h']
        exact rfl
        
      · left
        rw [h'.2]
        )

end Alist

