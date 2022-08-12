/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sean Leather
-/
import Mathbin.Data.List.Range
import Mathbin.Data.List.Perm

/-!
# Utilities for lists of sigmas

This file includes several ways of interacting with `list (sigma β)`, treated as a key-value store.

If `α : Type*` and `β : α → Type*`, then we regard `s : sigma β` as having key `s.1 : α` and value
`s.2 : β s.1`. Hence, `list (sigma β)` behaves like a key-value store.

## Main Definitions

- `list.keys` extracts the list of keys.
- `list.nodupkeys` determines if the store has duplicate keys.
- `list.lookup`/`lookup_all` accesses the value(s) of a particular key.
- `list.kreplace` replaces the first value with a given key by a given value.
- `list.kerase` removes a value.
- `list.kinsert` inserts a value.
- `list.kunion` computes the union of two stores.
- `list.kextract` returns a value with a given key and the rest of the values.
-/


universe u v

namespace List

variable {α : Type u} {β : α → Type v} {l l₁ l₂ : List (Sigma β)}

/-! ### `keys` -/


/-- List of keys from a list of key-value pairs -/
def keys : List (Sigma β) → List α :=
  map Sigma.fst

@[simp]
theorem keys_nil : @keys α β [] = [] :=
  rfl

@[simp]
theorem keys_cons {s} {l : List (Sigma β)} : (s :: l).keys = s.1 :: l.keys :=
  rfl

theorem mem_keys_of_mem {s : Sigma β} {l : List (Sigma β)} : s ∈ l → s.1 ∈ l.keys :=
  mem_map_of_memₓ Sigma.fst

theorem exists_of_mem_keys {a} {l : List (Sigma β)} (h : a ∈ l.keys) : ∃ b : β a, Sigma.mk a b ∈ l :=
  let ⟨⟨a', b'⟩, m, e⟩ := exists_of_mem_mapₓ h
  Eq.recOnₓ e (Exists.introₓ b' m)

theorem mem_keys {a} {l : List (Sigma β)} : a ∈ l.keys ↔ ∃ b : β a, Sigma.mk a b ∈ l :=
  ⟨exists_of_mem_keys, fun ⟨b, h⟩ => mem_keys_of_mem h⟩

theorem not_mem_keys {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ b : β a, Sigma.mk a b ∉ l :=
  (not_iff_not_of_iff mem_keys).trans not_exists

theorem not_eq_key {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ s : Sigma β, s ∈ l → a ≠ s.1 :=
  Iff.intro
    (fun h₁ s h₂ e =>
      absurd (mem_keys_of_mem h₂)
        (by
          rwa [e] at h₁))
    fun f h₁ =>
    let ⟨b, h₂⟩ := exists_of_mem_keys h₁
    f _ h₂ rfl

/-! ### `nodupkeys` -/


/-- Determines whether the store uses a key several times. -/
def Nodupkeys (l : List (Sigma β)) : Prop :=
  l.keys.Nodup

theorem nodupkeys_iff_pairwise {l} : Nodupkeys l ↔ Pairwiseₓ (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  pairwise_map _

theorem Nodupkeys.pairwise_ne {l} (h : Nodupkeys l) : Pairwiseₓ (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  nodupkeys_iff_pairwise.1 h

@[simp]
theorem nodupkeys_nil : @Nodupkeys α β [] :=
  pairwise.nil

@[simp]
theorem nodupkeys_cons {s : Sigma β} {l : List (Sigma β)} : Nodupkeys (s :: l) ↔ s.1 ∉ l.keys ∧ Nodupkeys l := by
  simp [← keys, ← nodupkeys]

theorem Nodupkeys.eq_of_fst_eq {l : List (Sigma β)} (nd : Nodupkeys l) {s s' : Sigma β} (h : s ∈ l) (h' : s' ∈ l) :
    s.1 = s'.1 → s = s' :=
  @Pairwiseₓ.forall_of_forall _ (fun s s' : Sigma β => s.1 = s'.1 → s = s') _ (fun s s' H h => (H h.symm).symm)
    (fun x h _ => rfl) ((nodupkeys_iff_pairwise.1 nd).imp fun s s' h h' => (h h').elim) _ h _ h'

theorem Nodupkeys.eq_of_mk_mem {a : α} {b b' : β a} {l : List (Sigma β)} (nd : Nodupkeys l) (h : Sigma.mk a b ∈ l)
    (h' : Sigma.mk a b' ∈ l) : b = b' := by
  cases nd.eq_of_fst_eq h h' rfl <;> rfl

theorem nodupkeys_singleton (s : Sigma β) : Nodupkeys [s] :=
  nodup_singleton _

theorem Nodupkeys.sublist {l₁ l₂ : List (Sigma β)} (h : l₁ <+ l₂) : Nodupkeys l₂ → Nodupkeys l₁ :=
  nodup.sublist <| h.map _

protected theorem Nodupkeys.nodup {l : List (Sigma β)} : Nodupkeys l → Nodupₓ l :=
  Nodupₓ.of_map _

theorem perm_nodupkeys {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : Nodupkeys l₁ ↔ Nodupkeys l₂ :=
  (h.map _).nodup_iff

theorem nodupkeys_join {L : List (List (Sigma β))} :
    Nodupkeys (join L) ↔ (∀, ∀ l ∈ L, ∀, Nodupkeys l) ∧ Pairwiseₓ Disjoint (L.map keys) := by
  rw [nodupkeys_iff_pairwise, pairwise_join, pairwise_map]
  refine'
    and_congr
      (ball_congr fun l h => by
        simp [← nodupkeys_iff_pairwise])
      _
  apply iff_of_eq
  congr with l₁ l₂
  simp [← keys, ← disjoint_iff_ne]

theorem nodup_enum_map_fst (l : List α) : (l.enum.map Prod.fst).Nodup := by
  simp [← List.nodup_range]

theorem mem_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.Nodup) (nd₁ : l₁.Nodup) (h : ∀ x, x ∈ l₀ ↔ x ∈ l₁) : l₀ ~ l₁ := by
  induction' l₀ with x xs generalizing l₁ <;> cases' l₁ with y ys
  · constructor
    
  iterate 2 
    first |
      specialize h x|
      specialize h y
    simp at h
    cases h
  simp at nd₀ nd₁
  classical
  obtain rfl | h' := eq_or_ne x y
  · constructor
    refine' l₀_ih nd₀.2 nd₁.2 fun a => _
    specialize h a
    simp at h
    obtain rfl | h' := eq_or_ne a x
    · exact iff_of_false nd₀.1 nd₁.1
      
    · simpa [← h'] using h
      
    
  · trans x :: y :: ys.erase x
    · constructor
      refine' l₀_ih nd₀.2 ((nd₁.2.erase _).cons fun h => nd₁.1 <| mem_of_mem_erase h) fun a => _
      · specialize h a
        simp at h
        obtain rfl | h' := eq_or_ne a x
        · exact iff_of_false nd₀.1 fun h => h.elim h' nd₁.2.not_mem_erase
          
        · rw [or_iff_right h'] at h
          rw [h, mem_cons_iff]
          exact or_congr_right' (mem_erase_of_ne h').symm
          
        
      
    trans y :: x :: ys.erase x
    · constructor
      
    · constructor
      symm
      apply perm_cons_erase
      specialize h x
      simp [← h'] at h
      exact h
      
    

variable [DecidableEq α]

/-! ### `lookup` -/


/-- `lookup a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists. -/
def lookupₓ (a : α) : List (Sigma β) → Option (β a)
  | [] => none
  | ⟨a', b⟩ :: l => if h : a' = a then some (Eq.recOnₓ h b) else lookup l

@[simp]
theorem lookup_nil (a : α) : lookupₓ a [] = @none (β a) :=
  rfl

@[simp]
theorem lookup_cons_eq (l) (a : α) (b : β a) : lookupₓ a (⟨a, b⟩ :: l) = some b :=
  dif_pos rfl

@[simp]
theorem lookup_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → lookupₓ a (s :: l) = lookupₓ a l
  | ⟨a', b⟩, h => dif_neg h.symm

theorem lookup_is_some {a : α} : ∀ {l : List (Sigma β)}, (lookupₓ a l).isSome ↔ a ∈ l.keys
  | [] => by
    simp
  | ⟨a', b⟩ :: l => by
    by_cases' h : a = a'
    · subst a'
      simp
      
    · simp [← h, ← lookup_is_some]
      

theorem lookup_eq_none {a : α} {l : List (Sigma β)} : lookupₓ a l = none ↔ a ∉ l.keys := by
  simp [lookup_is_some, ← Option.is_none_iff_eq_none]

theorem of_mem_lookup {a : α} {b : β a} : ∀ {l : List (Sigma β)}, b ∈ lookupₓ a l → Sigma.mk a b ∈ l
  | ⟨a', b'⟩ :: l, H => by
    by_cases' h : a = a'
    · subst a'
      simp at H
      simp [← H]
      
    · simp [← h] at H
      exact Or.inr (of_mem_lookup H)
      

theorem mem_lookup {a} {b : β a} {l : List (Sigma β)} (nd : l.Nodupkeys) (h : Sigma.mk a b ∈ l) : b ∈ lookupₓ a l := by
  cases' option.is_some_iff_exists.mp (lookup_is_some.mpr (mem_keys_of_mem h)) with b' h'
  cases nd.eq_of_mk_mem h (of_mem_lookup h')
  exact h'

theorem map_lookup_eq_find (a : α) : ∀ l : List (Sigma β), (lookupₓ a l).map (Sigma.mk a) = find (fun s => a = s.1) l
  | [] => rfl
  | ⟨a', b'⟩ :: l => by
    by_cases' h : a = a'
    · subst a'
      simp
      
    · simp [← h, ← map_lookup_eq_find]
      

theorem mem_lookup_iff {a : α} {b : β a} {l : List (Sigma β)} (nd : l.Nodupkeys) : b ∈ lookupₓ a l ↔ Sigma.mk a b ∈ l :=
  ⟨of_mem_lookup, mem_lookup nd⟩

theorem perm_lookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.Nodupkeys) (nd₂ : l₂.Nodupkeys) (p : l₁ ~ l₂) :
    lookupₓ a l₁ = lookupₓ a l₂ := by
  ext b <;> simp [← mem_lookup_iff, ← nd₁, ← nd₂] <;> exact p.mem_iff

theorem lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.Nodupkeys) (nd₁ : l₁.Nodupkeys)
    (h : ∀ x y, y ∈ l₀.lookup x ↔ y ∈ l₁.lookup x) : l₀ ~ l₁ :=
  mem_ext nd₀.Nodup nd₁.Nodup fun ⟨a, b⟩ => by
    rw [← mem_lookup_iff, ← mem_lookup_iff, h] <;> assumption

/-! ### `lookup_all` -/


/-- `lookup_all a l` is the list of all values in `l` corresponding to the key `a`. -/
def lookupAll (a : α) : List (Sigma β) → List (β a)
  | [] => []
  | ⟨a', b⟩ :: l => if h : a' = a then Eq.recOnₓ h b :: lookup_all l else lookup_all l

@[simp]
theorem lookup_all_nil (a : α) : lookupAll a [] = @nil (β a) :=
  rfl

@[simp]
theorem lookup_all_cons_eq (l) (a : α) (b : β a) : lookupAll a (⟨a, b⟩ :: l) = b :: lookupAll a l :=
  dif_pos rfl

@[simp]
theorem lookup_all_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → lookupAll a (s :: l) = lookupAll a l
  | ⟨a', b⟩, h => dif_neg h.symm

theorem lookup_all_eq_nil {a : α} : ∀ {l : List (Sigma β)}, lookupAll a l = [] ↔ ∀ b : β a, Sigma.mk a b ∉ l
  | [] => by
    simp
  | ⟨a', b⟩ :: l => by
    by_cases' h : a = a'
    · subst a'
      simp
      
    · simp [← h, ← lookup_all_eq_nil]
      

theorem head_lookup_all (a : α) : ∀ l : List (Sigma β), head' (lookupAll a l) = lookupₓ a l
  | [] => by
    simp
  | ⟨a', b⟩ :: l => by
    by_cases' h : a = a' <;>
      [· subst h
        simp
        ,
      simp [*]]

theorem mem_lookup_all {a : α} {b : β a} : ∀ {l : List (Sigma β)}, b ∈ lookupAll a l ↔ Sigma.mk a b ∈ l
  | [] => by
    simp
  | ⟨a', b'⟩ :: l => by
    by_cases' h : a = a' <;>
      [· subst h
        simp [*]
        ,
      simp [*]]

theorem lookup_all_sublist (a : α) : ∀ l : List (Sigma β), (lookupAll a l).map (Sigma.mk a) <+ l
  | [] => by
    simp
  | ⟨a', b'⟩ :: l => by
    by_cases' h : a = a'
    · subst h
      simp
      exact (lookup_all_sublist l).cons2 _ _ _
      
    · simp [← h]
      exact (lookup_all_sublist l).cons _ _ _
      

theorem lookup_all_length_le_one (a : α) {l : List (Sigma β)} (h : l.Nodupkeys) : length (lookupAll a l) ≤ 1 := by
  have := nodup.sublist ((lookup_all_sublist a l).map _) h <;>
    rw [map_map] at this <;> rwa [← nodup_repeat, ← map_const _ a]

theorem lookup_all_eq_lookup (a : α) {l : List (Sigma β)} (h : l.Nodupkeys) : lookupAll a l = (lookupₓ a l).toList := by
  rw [← head_lookup_all]
  have := lookup_all_length_le_one a h
  revert this
  rcases lookup_all a l with (_ | ⟨b, _ | ⟨c, l⟩⟩) <;>
    intro <;>
      try
        rfl
  exact
    absurd this
      (by
        decide)

theorem lookup_all_nodup (a : α) {l : List (Sigma β)} (h : l.Nodupkeys) : (lookupAll a l).Nodup := by
  rw [lookup_all_eq_lookup a h] <;> apply Option.to_list_nodup

theorem perm_lookup_all (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.Nodupkeys) (nd₂ : l₂.Nodupkeys) (p : l₁ ~ l₂) :
    lookupAll a l₁ = lookupAll a l₂ := by
  simp [← lookup_all_eq_lookup, ← nd₁, ← nd₂, ← perm_lookup a nd₁ nd₂ p]

/-! ### `kreplace` -/


/-- Replaces the first value with key `a` by `b`. -/
def kreplace (a : α) (b : β a) : List (Sigma β) → List (Sigma β) :=
  lookmap fun s => if a = s.1 then some ⟨a, b⟩ else none

theorem kreplace_of_forall_not (a : α) (b : β a) {l : List (Sigma β)} (H : ∀ b : β a, Sigma.mk a b ∉ l) :
    kreplace a b l = l :=
  lookmap_of_forall_not _ <| by
    rintro ⟨a', b'⟩ h
    dsimp'
    split_ifs
    · subst a'
      exact H _ h
      
    · rfl
      

theorem kreplace_self {a : α} {b : β a} {l : List (Sigma β)} (nd : Nodupkeys l) (h : Sigma.mk a b ∈ l) :
    kreplace a b l = l := by
  refine' (lookmap_congr _).trans (lookmap_id' (Option.guard fun s => a = s.1) _ _)
  · rintro ⟨a', b'⟩ h'
    dsimp' [← Option.guard]
    split_ifs
    · subst a'
      exact ⟨rfl, heq_of_eq <| nd.eq_of_mk_mem h h'⟩
      
    · rfl
      
    
  · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    dsimp' [← Option.guard]
    split_ifs
    · exact id
      
    · rintro ⟨⟩
      
    

theorem keys_kreplace (a : α) (b : β a) : ∀ l : List (Sigma β), (kreplace a b l).keys = l.keys :=
  lookmap_map_eq _ _ <| by
    rintro ⟨a₁, b₂⟩ ⟨a₂, b₂⟩ <;> dsimp' <;> split_ifs <;> simp (config := { contextual := true })[← h]

theorem kreplace_nodupkeys (a : α) (b : β a) {l : List (Sigma β)} : (kreplace a b l).Nodupkeys ↔ l.Nodupkeys := by
  simp [← nodupkeys, ← keys_kreplace]

theorem Perm.kreplace {a : α} {b : β a} {l₁ l₂ : List (Sigma β)} (nd : l₁.Nodupkeys) :
    l₁ ~ l₂ → kreplace a b l₁ ~ kreplace a b l₂ :=
  perm_lookmap _ <| by
    refine' nd.pairwise_ne.imp _
    intro x y h z h₁ w h₂
    split_ifs  at h₁ h₂ <;> cases h₁ <;> cases h₂
    exact (h (h_2.symm.trans h_1)).elim

/-! ### `kerase` -/


/-- Remove the first pair with the key `a`. -/
def kerase (a : α) : List (Sigma β) → List (Sigma β) :=
  erasep fun s => a = s.1

@[simp]
theorem kerase_nil {a} : @kerase _ β _ a [] = [] :=
  rfl

@[simp]
theorem kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β)} (h : a = s.1) : kerase a (s :: l) = l := by
  simp [← kerase, ← h]

@[simp]
theorem kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β)} (h : a ≠ s.1) : kerase a (s :: l) = s :: kerase a l := by
  simp [← kerase, ← h]

@[simp]
theorem kerase_of_not_mem_keys {a} {l : List (Sigma β)} (h : a ∉ l.keys) : kerase a l = l := by
  induction' l with _ _ ih <;> [rfl,
    · simp [← not_or_distrib] at h
      simp [← h.1, ← ih h.2]
      ]

theorem kerase_sublist (a : α) (l : List (Sigma β)) : kerase a l <+ l :=
  erasep_sublist _

theorem kerase_keys_subset (a) (l : List (Sigma β)) : (kerase a l).keys ⊆ l.keys :=
  ((kerase_sublist a l).map _).Subset

theorem mem_keys_of_mem_keys_kerase {a₁ a₂} {l : List (Sigma β)} : a₁ ∈ (kerase a₂ l).keys → a₁ ∈ l.keys :=
  @kerase_keys_subset _ _ _ _ _ _

theorem exists_of_kerase {a : α} {l : List (Sigma β)} (h : a ∈ l.keys) :
    ∃ (b : β a)(l₁ l₂ : List (Sigma β)), a ∉ l₁.keys ∧ l = l₁ ++ ⟨a, b⟩ :: l₂ ∧ kerase a l = l₁ ++ l₂ := by
  induction l
  case list.nil =>
    cases h
  case list.cons hd tl ih =>
    by_cases' e : a = hd.1
    · subst e
      exact
        ⟨hd.2, [], tl, by
          simp , by
          cases hd <;> rfl, by
          simp ⟩
      
    · simp at h
      cases h
      case or.inl h =>
        exact absurd h e
      case or.inr h =>
        rcases ih h with ⟨b, tl₁, tl₂, h₁, h₂, h₃⟩
        exact
          ⟨b, hd :: tl₁, tl₂, not_mem_cons_of_ne_of_not_mem e h₁, by
            rw [h₂] <;> rfl, by
            simp [← e, ← h₃]⟩
      

@[simp]
theorem mem_keys_kerase_of_ne {a₁ a₂} {l : List (Sigma β)} (h : a₁ ≠ a₂) : a₁ ∈ (kerase a₂ l).keys ↔ a₁ ∈ l.keys :=
  (Iff.intro mem_keys_of_mem_keys_kerase) fun p =>
    if q : a₂ ∈ l.keys then
      match l, kerase a₂ l, exists_of_kerase q, p with
      | _, _, ⟨_, _, _, _, rfl, rfl⟩, p => by
        simpa [← keys, ← h] using p
    else by
      simp [← q, ← p]

theorem keys_kerase {a} {l : List (Sigma β)} : (kerase a l).keys = l.keys.erase a := by
  rw [keys, kerase, ← erasep_map Sigma.fst l, erase_eq_erasep]

theorem kerase_kerase {a a'} {l : List (Sigma β)} : (kerase a' l).kerase a = (kerase a l).kerase a' := by
  by_cases' a = a'
  · subst a'
    
  induction' l with x xs
  · rfl
    
  · by_cases' a' = x.1
    · subst a'
      simp [← kerase_cons_ne h, ← kerase_cons_eq rfl]
      
    by_cases' h' : a = x.1
    · subst a
      simp [← kerase_cons_eq rfl, ← kerase_cons_ne (Ne.symm h)]
      
    · simp [← kerase_cons_ne, *]
      
    

theorem Nodupkeys.kerase (a : α) : Nodupkeys l → (kerase a l).Nodupkeys :=
  nodupkeys.sublist <| kerase_sublist _ _

theorem Perm.kerase {a : α} {l₁ l₂ : List (Sigma β)} (nd : l₁.Nodupkeys) : l₁ ~ l₂ → kerase a l₁ ~ kerase a l₂ :=
  Perm.erasep _ <|
    (nodupkeys_iff_pairwise.1 nd).imp <| by
      rintro x y h rfl <;> exact h

@[simp]
theorem not_mem_keys_kerase (a) {l : List (Sigma β)} (nd : l.Nodupkeys) : a ∉ (kerase a l).keys := by
  induction l
  case list.nil =>
    simp
  case list.cons hd tl ih =>
    simp at nd
    by_cases' h : a = hd.1
    · subst h
      simp [← nd.1]
      
    · simp [← h, ← ih nd.2]
      

@[simp]
theorem lookup_kerase (a) {l : List (Sigma β)} (nd : l.Nodupkeys) : lookupₓ a (kerase a l) = none :=
  lookup_eq_none.mpr (not_mem_keys_kerase a nd)

@[simp]
theorem lookup_kerase_ne {a a'} {l : List (Sigma β)} (h : a ≠ a') : lookupₓ a (kerase a' l) = lookupₓ a l := by
  induction l
  case list.nil =>
    rfl
  case list.cons hd tl ih =>
    cases' hd with ah bh
    by_cases' h₁ : a = ah <;> by_cases' h₂ : a' = ah
    · substs h₁ h₂
      cases Ne.irrefl h
      
    · subst h₁
      simp [← h₂]
      
    · subst h₂
      simp [← h]
      
    · simp [← h₁, ← h₂, ← ih]
      

theorem kerase_append_left {a} : ∀ {l₁ l₂ : List (Sigma β)}, a ∈ l₁.keys → kerase a (l₁ ++ l₂) = kerase a l₁ ++ l₂
  | [], _, h => by
    cases h
  | s :: l₁, l₂, h₁ =>
    if h₂ : a = s.1 then by
      simp [← h₂]
    else by
      simp at h₁ <;> cases h₁ <;> [exact absurd h₁ h₂, simp [← h₂, ← kerase_append_left h₁]]

theorem kerase_append_right {a} : ∀ {l₁ l₂ : List (Sigma β)}, a ∉ l₁.keys → kerase a (l₁ ++ l₂) = l₁ ++ kerase a l₂
  | [], _, h => rfl
  | _ :: l₁, l₂, h => by
    simp [← not_or_distrib] at h <;> simp [← h.1, ← kerase_append_right h.2]

theorem kerase_comm (a₁ a₂) (l : List (Sigma β)) : kerase a₂ (kerase a₁ l) = kerase a₁ (kerase a₂ l) :=
  if h : a₁ = a₂ then by
    simp [← h]
  else
    if ha₁ : a₁ ∈ l.keys then
      if ha₂ : a₂ ∈ l.keys then
        match l, kerase a₁ l, exists_of_kerase ha₁, ha₂ with
        | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, a₂_in_l₁_app_l₂ =>
          if h' : a₂ ∈ l₁.keys then by
            simp [← kerase_append_left h', ← kerase_append_right (mt (mem_keys_kerase_of_ne h).mp a₁_nin_l₁)]
          else by
            simp [← kerase_append_right h', ← kerase_append_right a₁_nin_l₁, ←
              @kerase_cons_ne _ _ _ a₂ ⟨a₁, b₁⟩ _ (Ne.symm h)]
      else by
        simp [← ha₂, ← mt mem_keys_of_mem_keys_kerase ha₂]
    else by
      simp [← ha₁, ← mt mem_keys_of_mem_keys_kerase ha₁]

theorem sizeof_kerase {α} {β : α → Type _} [DecidableEq α] [SizeOf (Sigma β)] (x : α) (xs : List (Sigma β)) :
    sizeof (List.kerase x xs) ≤ sizeof xs := by
  unfold_wf
  induction' xs with y ys
  · simp
    
  · by_cases' x = y.1 <;> simp [*, ← List.sizeof]
    

/-! ### `kinsert` -/


/-- Insert the pair `⟨a, b⟩` and erase the first pair with the key `a`. -/
def kinsert (a : α) (b : β a) (l : List (Sigma β)) : List (Sigma β) :=
  ⟨a, b⟩ :: kerase a l

@[simp]
theorem kinsert_def {a} {b : β a} {l : List (Sigma β)} : kinsert a b l = ⟨a, b⟩ :: kerase a l :=
  rfl

theorem mem_keys_kinsert {a a'} {b' : β a'} {l : List (Sigma β)} : a ∈ (kinsert a' b' l).keys ↔ a = a' ∨ a ∈ l.keys :=
  by
  by_cases' h : a = a' <;> simp [← h]

theorem kinsert_nodupkeys (a) (b : β a) {l : List (Sigma β)} (nd : l.Nodupkeys) : (kinsert a b l).Nodupkeys :=
  nodupkeys_cons.mpr ⟨not_mem_keys_kerase a nd, nd.kerase a⟩

theorem Perm.kinsert {a} {b : β a} {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.Nodupkeys) (p : l₁ ~ l₂) :
    kinsert a b l₁ ~ kinsert a b l₂ :=
  (p.kerase nd₁).cons _

theorem lookup_kinsert {a} {b : β a} (l : List (Sigma β)) : lookupₓ a (kinsert a b l) = some b := by
  simp only [← kinsert, ← lookup_cons_eq]

theorem lookup_kinsert_ne {a a'} {b' : β a'} {l : List (Sigma β)} (h : a ≠ a') :
    lookupₓ a (kinsert a' b' l) = lookupₓ a l := by
  simp [← h]

/-! ### `kextract` -/


/-- Finds the first entry with a given key `a` and returns its value (as an `option` because there
might be no entry with key `a`) alongside with the rest of the entries. -/
def kextract (a : α) : List (Sigma β) → Option (β a) × List (Sigma β)
  | [] => (none, [])
  | s :: l =>
    if h : s.1 = a then (some (Eq.recOnₓ h s.2), l)
    else
      let (b', l') := kextract l
      (b', s :: l')

@[simp]
theorem kextract_eq_lookup_kerase (a : α) : ∀ l : List (Sigma β), kextract a l = (lookupₓ a l, kerase a l)
  | [] => rfl
  | ⟨a', b⟩ :: l => by
    simp [← kextract]
    dsimp'
    split_ifs
    · subst a'
      simp [← kerase]
      
    · simp [← kextract, ← Ne.symm h, ← kextract_eq_lookup_kerase l, ← kerase]
      

/-! ### `dedupkeys` -/


/-- Remove entries with duplicate keys from `l : list (sigma β)`. -/
def dedupkeys : List (Sigma β) → List (Sigma β) :=
  List.foldr (fun x => kinsert x.1 x.2) []

theorem dedupkeys_cons {x : Sigma β} (l : List (Sigma β)) : dedupkeys (x :: l) = kinsert x.1 x.2 (dedupkeys l) :=
  rfl

theorem nodupkeys_dedupkeys (l : List (Sigma β)) : Nodupkeys (dedupkeys l) := by
  dsimp' [← dedupkeys]
  generalize hl : nil = l'
  have : nodupkeys l' := by
    rw [← hl]
    apply nodup_nil
  clear hl
  induction' l with x xs
  · apply this
    
  · cases x
    simp [← dedupkeys]
    constructor
    · simp [← keys_kerase]
      apply l_ih.not_mem_erase
      
    · exact l_ih.kerase _
      
    

theorem lookup_dedupkeys (a : α) (l : List (Sigma β)) : lookupₓ a (dedupkeys l) = lookupₓ a l := by
  induction l
  rfl
  cases' l_hd with a' b
  by_cases' a = a'
  · subst a'
    rw [dedupkeys_cons, lookup_kinsert, lookup_cons_eq]
    
  · rw [dedupkeys_cons, lookup_kinsert_ne h, l_ih, lookup_cons_ne]
    exact h
    

theorem sizeof_dedupkeys {α} {β : α → Type _} [DecidableEq α] [SizeOf (Sigma β)] (xs : List (Sigma β)) :
    sizeof (List.dedupkeys xs) ≤ sizeof xs := by
  unfold_wf
  induction' xs with x xs
  · simp [← List.dedupkeys]
    
  · simp only [← dedupkeys_cons, ← List.sizeof, ← kinsert_def, ← add_le_add_iff_left, ← Sigma.eta]
    trans
    apply sizeof_kerase
    assumption
    

/-! ### `kunion` -/


/-- `kunion l₁ l₂` is the append to l₁ of l₂ after, for each key in l₁, the
first matching pair in l₂ is erased. -/
def kunion : List (Sigma β) → List (Sigma β) → List (Sigma β)
  | [], l₂ => l₂
  | s :: l₁, l₂ => s :: kunion l₁ (kerase s.1 l₂)

@[simp]
theorem nil_kunion {l : List (Sigma β)} : kunion [] l = l :=
  rfl

@[simp]
theorem kunion_nil : ∀ {l : List (Sigma β)}, kunion l [] = l
  | [] => rfl
  | _ :: l => by
    rw [kunion, kerase_nil, kunion_nil]

@[simp]
theorem kunion_cons {s} {l₁ l₂ : List (Sigma β)} : kunion (s :: l₁) l₂ = s :: kunion l₁ (kerase s.1 l₂) :=
  rfl

@[simp]
theorem mem_keys_kunion {a} {l₁ l₂ : List (Sigma β)} : a ∈ (kunion l₁ l₂).keys ↔ a ∈ l₁.keys ∨ a ∈ l₂.keys := by
  induction l₁ generalizing l₂
  case list.nil =>
    simp
  case list.cons s l₁ ih =>
    by_cases' h : a = s.1 <;> [simp [← h], simp [← h, ← ih]]

@[simp]
theorem kunion_kerase {a} : ∀ {l₁ l₂ : List (Sigma β)}, kunion (kerase a l₁) (kerase a l₂) = kerase a (kunion l₁ l₂)
  | [], _ => rfl
  | s :: _, l => by
    by_cases' h : a = s.1 <;> simp [← h, ← kerase_comm a s.1 l, ← kunion_kerase]

theorem Nodupkeys.kunion (nd₁ : l₁.Nodupkeys) (nd₂ : l₂.Nodupkeys) : (kunion l₁ l₂).Nodupkeys := by
  induction l₁ generalizing l₂
  case list.nil =>
    simp only [← nil_kunion, ← nd₂]
  case list.cons s l₁ ih =>
    simp at nd₁
    simp [← not_or_distrib, ← nd₁.1, ← nd₂, ← ih nd₁.2 (nd₂.kerase s.1)]

theorem Perm.kunion_right {l₁ l₂ : List (Sigma β)} (p : l₁ ~ l₂) (l) : kunion l₁ l ~ kunion l₂ l := by
  induction p generalizing l
  case list.perm.nil =>
    rfl
  case list.perm.cons hd tl₁ tl₂ p ih =>
    simp [← ih (kerase hd.1 l), ← perm.cons]
  case list.perm.swap s₁ s₂ l =>
    simp [← kerase_comm, ← perm.swap]
  case list.perm.trans l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ =>
    exact perm.trans (ih₁₂ l) (ih₂₃ l)

theorem Perm.kunion_left : ∀ (l) {l₁ l₂ : List (Sigma β)}, l₁.Nodupkeys → l₁ ~ l₂ → kunion l l₁ ~ kunion l l₂
  | [], _, _, _, p => p
  | s :: l, l₁, l₂, nd₁, p => by
    simp [← ((p.kerase nd₁).kunion_left l <| nd₁.kerase s.1).cons s]

theorem Perm.kunion {l₁ l₂ l₃ l₄ : List (Sigma β)} (nd₃ : l₃.Nodupkeys) (p₁₂ : l₁ ~ l₂) (p₃₄ : l₃ ~ l₄) :
    kunion l₁ l₃ ~ kunion l₂ l₄ :=
  (p₁₂.kunion_right l₃).trans (p₃₄.kunion_left l₂ nd₃)

@[simp]
theorem lookup_kunion_left {a} {l₁ l₂ : List (Sigma β)} (h : a ∈ l₁.keys) : lookupₓ a (kunion l₁ l₂) = lookupₓ a l₁ :=
  by
  induction' l₁ with s _ ih generalizing l₂ <;> simp at h <;> cases h <;> cases' s with a'
  · subst h
    simp
    
  · rw [kunion_cons]
    by_cases' h' : a = a'
    · subst h'
      simp
      
    · simp [← h', ← ih h]
      
    

@[simp]
theorem lookup_kunion_right {a} {l₁ l₂ : List (Sigma β)} (h : a ∉ l₁.keys) : lookupₓ a (kunion l₁ l₂) = lookupₓ a l₂ :=
  by
  induction l₁ generalizing l₂
  case list.nil =>
    simp
  case list.cons _ _ ih =>
    simp [← not_or_distrib] at h
    simp [← h.1, ← ih h.2]

@[simp]
theorem mem_lookup_kunion {a} {b : β a} {l₁ l₂ : List (Sigma β)} :
    b ∈ lookupₓ a (kunion l₁ l₂) ↔ b ∈ lookupₓ a l₁ ∨ a ∉ l₁.keys ∧ b ∈ lookupₓ a l₂ := by
  induction l₁ generalizing l₂
  case list.nil =>
    simp
  case list.cons s _ ih =>
    cases' s with a'
    by_cases' h₁ : a = a'
    · subst h₁
      simp
      
    · let h₂ := @ih (kerase a' l₂)
      simp [← h₁] at h₂
      simp [← h₁, ← h₂]
      

theorem mem_lookup_kunion_middle {a} {b : β a} {l₁ l₂ l₃ : List (Sigma β)} (h₁ : b ∈ lookupₓ a (kunion l₁ l₃))
    (h₂ : a ∉ keys l₂) : b ∈ lookupₓ a (kunion (kunion l₁ l₂) l₃) :=
  match mem_lookup_kunion.mp h₁ with
  | Or.inl h => mem_lookup_kunion.mpr (Or.inl (mem_lookup_kunion.mpr (Or.inl h)))
  | Or.inr h => mem_lookup_kunion.mpr <| Or.inr ⟨mt mem_keys_kunion.mp (not_or_distrib.mpr ⟨h.1, h₂⟩), h.2⟩

end List

