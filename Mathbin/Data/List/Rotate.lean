/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yakov Pechersky
-/
import Mathbin.Data.List.Perm
import Mathbin.Data.List.Range

/-!
# List rotation

This file proves basic results about `list.rotate`, the list rotation.

## Main declarations

* `is_rotated l₁ l₂`: States that `l₁` is a rotated version of `l₂`.
* `cyclic_permutations l`: The list of all cyclic permutants of `l`, up to the length of `l`.

## Tags

rotated, rotation, permutation, cycle
-/


universe u

variable {α : Type u}

open Nat

namespace List

theorem rotate_mod (l : List α) (n : ℕ) : l.rotate (n % l.length) = l.rotate n := by
  simp [← rotate]

@[simp]
theorem rotate_nil (n : ℕ) : ([] : List α).rotate n = [] := by
  simp [← rotate]

@[simp]
theorem rotate_zero (l : List α) : l.rotate 0 = l := by
  simp [← rotate]

@[simp]
theorem rotate'_nil (n : ℕ) : ([] : List α).rotate' n = [] := by
  cases n <;> rfl

@[simp]
theorem rotate'_zero (l : List α) : l.rotate' 0 = l := by
  cases l <;> rfl

theorem rotate'_cons_succ (l : List α) (a : α) (n : ℕ) : (a :: l : List α).rotate' n.succ = (l ++ [a]).rotate' n := by
  simp [← rotate']

@[simp]
theorem length_rotate' : ∀ (l : List α) (n : ℕ), (l.rotate' n).length = l.length
  | [], n => rfl
  | a :: l, 0 => rfl
  | a :: l, n + 1 => by
    rw [List.rotate'ₓ, length_rotate' (l ++ [a]) n] <;> simp

theorem rotate'_eq_drop_append_take : ∀ {l : List α} {n : ℕ}, n ≤ l.length → l.rotate' n = l.drop n ++ l.take n
  | [], n, h => by
    simp [← drop_append_of_le_length h]
  | l, 0, h => by
    simp [← take_append_of_le_length h]
  | a :: l, n + 1, h => by
    have hnl : n ≤ l.length := le_of_succ_le_succₓ h
    have hnl' : n ≤ (l ++ [a]).length := by
      rw [length_append, length_cons, List.length, zero_addₓ] <;> exact le_of_succ_le h
    rw [rotate'_cons_succ, rotate'_eq_drop_append_take hnl', drop, take, drop_append_of_le_length hnl,
        take_append_of_le_length hnl] <;>
      simp

theorem rotate'_rotate' : ∀ (l : List α) (n m : ℕ), (l.rotate' n).rotate' m = l.rotate' (n + m)
  | a :: l, 0, m => by
    simp
  | [], n, m => by
    simp
  | a :: l, n + 1, m => by
    rw [rotate'_cons_succ, rotate'_rotate', add_right_commₓ, rotate'_cons_succ]

@[simp]
theorem rotate'_length (l : List α) : rotate'ₓ l l.length = l := by
  rw [rotate'_eq_drop_append_take le_rfl] <;> simp

@[simp]
theorem rotate'_length_mul (l : List α) : ∀ n : ℕ, l.rotate' (l.length * n) = l
  | 0 => by
    simp
  | n + 1 =>
    calc
      l.rotate' (l.length * (n + 1)) = (l.rotate' (l.length * n)).rotate' (l.rotate' (l.length * n)).length := by
        simp [-rotate'_length, ← Nat.mul_succ, ← rotate'_rotate']
      _ = l := by
        rw [rotate'_length, rotate'_length_mul]
      

theorem rotate'_mod (l : List α) (n : ℕ) : l.rotate' (n % l.length) = l.rotate' n :=
  calc
    l.rotate' (n % l.length) =
        (l.rotate' (n % l.length)).rotate' ((l.rotate' (n % l.length)).length * (n / l.length)) :=
      by
      rw [rotate'_length_mul]
    _ = l.rotate' n := by
      rw [rotate'_rotate', length_rotate', Nat.mod_add_divₓ]
    

theorem rotate_eq_rotate' (l : List α) (n : ℕ) : l.rotate n = l.rotate' n :=
  if h : l.length = 0 then by
    simp_all [← length_eq_zero]
  else by
    rw [← rotate'_mod, rotate'_eq_drop_append_take (le_of_ltₓ (Nat.mod_ltₓ _ (Nat.pos_of_ne_zeroₓ h)))] <;>
      simp [← rotate]

theorem rotate_cons_succ (l : List α) (a : α) (n : ℕ) : (a :: l : List α).rotate n.succ = (l ++ [a]).rotate n := by
  rw [rotate_eq_rotate', rotate_eq_rotate', rotate'_cons_succ]

@[simp]
theorem mem_rotate : ∀ {l : List α} {a : α} {n : ℕ}, a ∈ l.rotate n ↔ a ∈ l
  | [], _, n => by
    simp
  | a :: l, _, 0 => by
    simp
  | a :: l, _, n + 1 => by
    simp [← rotate_cons_succ, ← mem_rotate, ← Or.comm]

@[simp]
theorem length_rotate (l : List α) (n : ℕ) : (l.rotate n).length = l.length := by
  rw [rotate_eq_rotate', length_rotate']

theorem rotate_eq_drop_append_take {l : List α} {n : ℕ} : n ≤ l.length → l.rotate n = l.drop n ++ l.take n := by
  rw [rotate_eq_rotate'] <;> exact rotate'_eq_drop_append_take

theorem rotate_eq_drop_append_take_mod {l : List α} {n : ℕ} :
    l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length) := by
  cases' l.length.zero_le.eq_or_lt with hl hl
  · simp [← eq_nil_of_length_eq_zero hl.symm]
    
  rw [← rotate_eq_drop_append_take (n.mod_lt hl).le, rotate_mod]

@[simp]
theorem rotate_append_length_eq (l l' : List α) : (l ++ l').rotate l.length = l' ++ l := by
  rw [rotate_eq_rotate']
  induction l generalizing l'
  · simp
    
  · simp [← rotate', ← l_ih]
    

theorem rotate_rotate (l : List α) (n m : ℕ) : (l.rotate n).rotate m = l.rotate (n + m) := by
  rw [rotate_eq_rotate', rotate_eq_rotate', rotate_eq_rotate', rotate'_rotate']

@[simp]
theorem rotate_length (l : List α) : rotateₓ l l.length = l := by
  rw [rotate_eq_rotate', rotate'_length]

@[simp]
theorem rotate_length_mul (l : List α) (n : ℕ) : l.rotate (l.length * n) = l := by
  rw [rotate_eq_rotate', rotate'_length_mul]

theorem prod_rotate_eq_one_of_prod_eq_one [Groupₓ α] : ∀ {l : List α} (hl : l.Prod = 1) (n : ℕ), (l.rotate n).Prod = 1
  | [], _, _ => by
    simp
  | a :: l, hl, n => by
    have : n % List.length (a :: l) ≤ List.length (a :: l) :=
      le_of_ltₓ
        (Nat.mod_ltₓ _
          (by
            decide))
    rw [← List.take_append_dropₓ (n % List.length (a :: l)) (a :: l)] at hl <;>
      rw [← rotate_mod, rotate_eq_drop_append_take this, List.prod_append, mul_eq_one_iff_inv_eq, ←
        one_mulₓ (List.prod _)⁻¹, ← hl, List.prod_append, mul_assoc, mul_inv_selfₓ, mul_oneₓ]

theorem rotate_perm (l : List α) (n : ℕ) : l.rotate n ~ l := by
  rw [rotate_eq_rotate']
  induction' n with n hn generalizing l
  · simp
    
  · cases' l with hd tl
    · simp
      
    · rw [rotate'_cons_succ]
      exact (hn _).trans (perm_append_singleton _ _)
      
    

@[simp]
theorem nodup_rotate {l : List α} {n : ℕ} : Nodupₓ (l.rotate n) ↔ Nodupₓ l :=
  (rotate_perm l n).nodup_iff

@[simp]
theorem rotate_eq_nil_iff {l : List α} {n : ℕ} : l.rotate n = [] ↔ l = [] := by
  induction' n with n hn generalizing l
  · simp
    
  · cases' l with hd tl
    · simp
      
    · simp [← rotate_cons_succ, ← hn]
      
    

@[simp]
theorem nil_eq_rotate_iff {l : List α} {n : ℕ} : [] = l.rotate n ↔ [] = l := by
  rw [eq_comm, rotate_eq_nil_iff, eq_comm]

@[simp]
theorem rotate_singleton (x : α) (n : ℕ) : [x].rotate n = [x] := by
  induction' n with n hn
  · simp
    
  · rwa [rotate_cons_succ]
    

@[simp]
theorem rotate_eq_singleton_iff {l : List α} {n : ℕ} {x : α} : l.rotate n = [x] ↔ l = [x] := by
  induction' n with n hn generalizing l
  · simp
    
  · cases' l with hd tl
    · simp
      
    · simp [← rotate_cons_succ, ← hn, ← append_eq_cons_iff, ← and_comm]
      
    

@[simp]
theorem singleton_eq_rotate_iff {l : List α} {n : ℕ} {x : α} : [x] = l.rotate n ↔ [x] = l := by
  rw [eq_comm, rotate_eq_singleton_iff, eq_comm]

theorem zip_with_rotate_distrib {α β γ : Type _} (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)
    (h : l.length = l'.length) : (zipWithₓ f l l').rotate n = zipWithₓ f (l.rotate n) (l'.rotate n) := by
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod, h,
    zip_with_append, ← zip_with_distrib_drop, ← zip_with_distrib_take, List.length_zip_with, h, min_selfₓ]
  rw [length_drop, length_drop, h]

attribute [local simp] rotate_cons_succ

@[simp]
theorem zip_with_rotate_one {β : Type _} (f : α → α → β) (x y : α) (l : List α) :
    zipWithₓ f (x :: y :: l) ((x :: y :: l).rotate 1) = f x y :: zipWithₓ f (y :: l) (l ++ [x]) := by
  simp

theorem nth_le_rotate_one (l : List α) (k : ℕ) (hk : k < (l.rotate 1).length) :
    (l.rotate 1).nthLe k hk = l.nthLe ((k + 1) % l.length) (mod_ltₓ _ (length_rotate l 1 ▸ k.zero_le.trans_lt hk)) := by
  cases' l with hd tl
  · simp
    
  · have : k ≤ tl.length := by
      refine' Nat.le_of_lt_succₓ _
      simpa using hk
    rcases this.eq_or_lt with (rfl | hk')
    · simp [← nth_le_append_right le_rfl]
      
    · simpa [← nth_le_append _ hk', ← length_cons, ← Nat.mod_eq_of_ltₓ (Nat.succ_lt_succₓ hk')]
      
    

theorem nth_le_rotate (l : List α) (n k : ℕ) (hk : k < (l.rotate n).length) :
    (l.rotate n).nthLe k hk = l.nthLe ((k + n) % l.length) (mod_ltₓ _ (length_rotate l n ▸ k.zero_le.trans_lt hk)) := by
  induction' n with n hn generalizing l k
  · have hk' : k < l.length := by
      simpa using hk
    simp [← Nat.mod_eq_of_ltₓ hk']
    
  · simp [← Nat.succ_eq_add_one, rotate_rotate, ← nth_le_rotate_one, ← hn l, ← add_commₓ, ← add_left_commₓ]
    

/-- A variant of `nth_le_rotate` useful for rewrites. -/
theorem nth_le_rotate' (l : List α) (n k : ℕ) (hk : k < l.length) :
    (l.rotate n).nthLe ((l.length - n % l.length + k) % l.length)
        ((Nat.mod_ltₓ _ (k.zero_le.trans_lt hk)).trans_le (length_rotate _ _).Ge) =
      l.nthLe k hk :=
  by
  rw [nth_le_rotate]
  congr
  set m := l.length
  rw [mod_add_mod, add_assocₓ, add_left_commₓ, add_commₓ, add_mod, add_mod _ n]
  cases' (n % m).zero_le.eq_or_lt with hn hn
  · simpa [hn] using Nat.mod_eq_of_ltₓ hk
    
  · have mpos : 0 < m := k.zero_le.trans_lt hk
    have hm : m - n % m < m := tsub_lt_self mpos hn
    have hn' : n % m < m := Nat.mod_ltₓ _ mpos
    simpa [← mod_eq_of_lt hm, ← tsub_add_cancel_of_le hn'.le] using Nat.mod_eq_of_ltₓ hk
    

theorem rotate_injective (n : ℕ) : Function.Injective fun l : List α => l.rotate n := by
  rintro l l' (h : l.rotate n = l'.rotate n)
  have hle : l.length = l'.length := (l.length_rotate n).symm.trans (h.symm ▸ l'.length_rotate n)
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod] at h
  obtain ⟨hd, ht⟩ := append_inj h _
  · rw [← take_append_drop _ l, ht, hd, take_append_drop]
    
  · rw [length_drop, length_drop, hle]
    

-- possibly easier to find in doc-gen, otherwise not that useful.
theorem rotate_eq_rotate {l l' : List α} {n : ℕ} : l.rotate n = l'.rotate n ↔ l = l' :=
  (rotate_injective n).eq_iff

theorem rotate_eq_iff {l l' : List α} {n : ℕ} : l.rotate n = l' ↔ l = l'.rotate (l'.length - n % l'.length) := by
  rw [← @rotate_eq_rotate _ l _ n, rotate_rotate, ← rotate_mod l', add_mod]
  cases' l'.length.zero_le.eq_or_lt with hl hl
  · rw [eq_nil_of_length_eq_zero hl.symm, rotate_nil, rotate_eq_nil_iff]
    
  · cases' (Nat.zero_leₓ (n % l'.length)).eq_or_lt with hn hn
    · simp [hn]
      
    · rw [mod_eq_of_lt (tsub_lt_self hl hn), tsub_add_cancel_of_le, mod_self, rotate_zero]
      exact (Nat.mod_ltₓ _ hl).le
      
    

theorem reverse_rotate (l : List α) (n : ℕ) : (l.rotate n).reverse = l.reverse.rotate (l.length - n % l.length) := by
  rw [← length_reverse l, ← rotate_eq_iff]
  induction' n with n hn generalizing l
  · simp
    
  · cases' l with hd tl
    · simp
      
    · rw [rotate_cons_succ, Nat.succ_eq_add_one, ← rotate_rotate, hn]
      simp
      
    

theorem rotate_reverse (l : List α) (n : ℕ) : l.reverse.rotate n = (l.rotate (l.length - n % l.length)).reverse := by
  rw [← reverse_reverse l]
  simp_rw [reverse_rotate, reverse_reverse, rotate_eq_iff, rotate_rotate, length_rotate, length_reverse]
  rw [← length_reverse l]
  set k := n % l.reverse.length with hk
  cases' hk' : k with k'
  · simp [-length_reverse, rotate_rotate]
    
  · cases' l with x l
    · simp
      
    · have : k'.succ < (x :: l).length := by
        simp [hk', ← hk, ← Nat.mod_ltₓ]
      rw [Nat.mod_eq_of_ltₓ, tsub_add_cancel_of_le, rotate_length]
      · exact tsub_le_self
        
      · exact
          tsub_lt_self
            (by
              simp )
            Nat.succ_pos'
        
      
    

theorem map_rotate {β : Type _} (f : α → β) (l : List α) (n : ℕ) : map f (l.rotate n) = (map f l).rotate n := by
  induction' n with n hn IH generalizing l
  · simp
    
  · cases' l with hd tl
    · simp
      
    · simp [← hn]
      
    

theorem Nodupₓ.rotate_eq_self_iff {l : List α} (hl : l.Nodup) {n : ℕ} : l.rotate n = l ↔ n % l.length = 0 ∨ l = [] := by
  constructor
  · intro h
    cases' l.length.zero_le.eq_or_lt with hl' hl'
    · simp [length_eq_zero, hl']
      
    left
    rw [nodup_iff_nth_le_inj] at hl
    refine' hl _ _ (mod_lt _ hl') hl' _
    rw [← nth_le_rotate' _ n]
    simp_rw [h, tsub_add_cancel_of_le (mod_lt _ hl').le, mod_self]
    
  · rintro (h | h)
    · rw [← rotate_mod, h]
      exact rotate_zero l
      
    · simp [← h]
      
    

theorem Nodupₓ.rotate_congr {l : List α} (hl : l.Nodup) (hn : l ≠ []) (i j : ℕ) (h : l.rotate i = l.rotate j) :
    i % l.length = j % l.length := by
  have hi : i % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hn)
  have hj : j % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hn)
  refine' (nodup_iff_nth_le_inj.mp hl) _ _ hi hj _
  rw [← nth_le_rotate' l i, ← nth_le_rotate' l j]
  simp [← tsub_add_cancel_of_le, ← hi.le, ← hj.le, ← h]

section IsRotated

variable (l l' : List α)

/-- `is_rotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutations
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`. -/
def IsRotated : Prop :=
  ∃ n, l.rotate n = l'

-- mathport name: «expr ~r »
infixr:1000 " ~r " => IsRotated

variable {l l'}

@[refl]
theorem IsRotated.refl (l : List α) : l ~r l :=
  ⟨0, by
    simp ⟩

@[symm]
theorem IsRotated.symm (h : l ~r l') : l' ~r l := by
  obtain ⟨n, rfl⟩ := h
  cases' l with hd tl
  · simp
    
  · use (hd :: tl).length * n - n
    rw [rotate_rotate, add_tsub_cancel_of_le, rotate_length_mul]
    exact
      Nat.le_mul_of_pos_left
        (by
          simp )
    

theorem is_rotated_comm : l ~r l' ↔ l' ~r l :=
  ⟨IsRotated.symm, IsRotated.symm⟩

@[simp]
protected theorem IsRotated.forall (l : List α) (n : ℕ) : l.rotate n ~r l :=
  IsRotated.symm ⟨n, rfl⟩

@[trans]
theorem IsRotated.trans : ∀ {l l' l'' : List α}, l ~r l' → l' ~r l'' → l ~r l''
  | _, _, _, ⟨n, rfl⟩, ⟨m, rfl⟩ =>
    ⟨n + m, by
      rw [rotate_rotate]⟩

theorem IsRotated.eqv : Equivalenceₓ (@IsRotated α) :=
  mk_equivalence _ IsRotated.refl (fun _ _ => IsRotated.symm) fun _ _ _ => IsRotated.trans

/-- The relation `list.is_rotated l l'` forms a `setoid` of cycles. -/
def IsRotated.setoid (α : Type _) : Setoidₓ (List α) where
  R := IsRotated
  iseqv := IsRotated.eqv

theorem IsRotated.perm (h : l ~r l') : l ~ l' :=
  Exists.elim h fun _ hl => hl ▸ (rotate_perm _ _).symm

theorem IsRotated.nodup_iff (h : l ~r l') : Nodupₓ l ↔ Nodupₓ l' :=
  h.Perm.nodup_iff

theorem IsRotated.mem_iff (h : l ~r l') {a : α} : a ∈ l ↔ a ∈ l' :=
  h.Perm.mem_iff

@[simp]
theorem is_rotated_nil_iff : l ~r [] ↔ l = [] :=
  ⟨fun ⟨n, hn⟩ => by
    simpa using hn, fun h =>
    h ▸ by
      rfl⟩

@[simp]
theorem is_rotated_nil_iff' : [] ~r l ↔ [] = l := by
  rw [is_rotated_comm, is_rotated_nil_iff, eq_comm]

@[simp]
theorem is_rotated_singleton_iff {x : α} : l ~r [x] ↔ l = [x] :=
  ⟨fun ⟨n, hn⟩ => by
    simpa using hn, fun h =>
    h ▸ by
      rfl⟩

@[simp]
theorem is_rotated_singleton_iff' {x : α} : [x] ~r l ↔ [x] = l := by
  rw [is_rotated_comm, is_rotated_singleton_iff, eq_comm]

theorem is_rotated_concat (hd : α) (tl : List α) : (tl ++ [hd]) ~r (hd :: tl) :=
  IsRotated.symm
    ⟨1, by
      simp ⟩

theorem is_rotated_append : (l ++ l') ~r (l' ++ l) :=
  ⟨l.length, by
    simp ⟩

theorem IsRotated.reverse (h : l ~r l') : l.reverse ~r l'.reverse := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨_, (reverse_rotate _ _).symm⟩

theorem is_rotated_reverse_comm_iff : l.reverse ~r l' ↔ l ~r l'.reverse := by
  constructor <;>
    · intro h
      simpa using h.reverse
      

@[simp]
theorem is_rotated_reverse_iff : l.reverse ~r l'.reverse ↔ l ~r l' := by
  simp [← is_rotated_reverse_comm_iff]

theorem is_rotated_iff_mod : l ~r l' ↔ ∃ n ≤ l.length, l.rotate n = l' := by
  refine' ⟨fun h => _, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
  obtain ⟨n, rfl⟩ := h
  cases' l with hd tl
  · simp
    
  · refine' ⟨n % (hd :: tl).length, _, rotate_mod _ _⟩
    refine' (Nat.mod_ltₓ _ _).le
    simp
    

theorem is_rotated_iff_mem_map_range : l ~r l' ↔ l' ∈ (List.range (l.length + 1)).map l.rotate := by
  simp_rw [mem_map, mem_range, is_rotated_iff_mod]
  exact ⟨fun ⟨n, hn, h⟩ => ⟨n, Nat.lt_succ_of_leₓ hn, h⟩, fun ⟨n, hn, h⟩ => ⟨n, Nat.le_of_lt_succₓ hn, h⟩⟩

@[congr]
theorem IsRotated.map {β : Type _} {l₁ l₂ : List α} (h : l₁ ~r l₂) (f : α → β) : map f l₁ ~r map f l₂ := by
  obtain ⟨n, rfl⟩ := h
  rw [map_rotate]
  use n

/-- List of all cyclic permutations of `l`.
The `cyclic_permutations` of a nonempty list `l` will always contain `list.length l` elements.
This implies that under certain conditions, there are duplicates in `list.cyclic_permutations l`.
The `n`th entry is equal to `l.rotate n`, proven in `list.nth_le_cyclic_permutations`.
The proof that every cyclic permutant of `l` is in the list is `list.mem_cyclic_permutations_iff`.

     cyclic_permutations [1, 2, 3, 2, 4] =
       [[1, 2, 3, 2, 4], [2, 3, 2, 4, 1], [3, 2, 4, 1, 2],
        [2, 4, 1, 2, 3], [4, 1, 2, 3, 2]] -/
def cyclicPermutations : List α → List (List α)
  | [] => [[]]
  | l@(_ :: _) => init (zipWithₓ (· ++ ·) (tails l) (inits l))

@[simp]
theorem cyclic_permutations_nil : cyclicPermutations ([] : List α) = [[]] :=
  rfl

theorem cyclic_permutations_cons (x : α) (l : List α) :
    cyclicPermutations (x :: l) = init (zipWithₓ (· ++ ·) (tails (x :: l)) (inits (x :: l))) :=
  rfl

theorem cyclic_permutations_of_ne_nil (l : List α) (h : l ≠ []) :
    cyclicPermutations l = init (zipWithₓ (· ++ ·) (tails l) (inits l)) := by
  obtain ⟨hd, tl, rfl⟩ := exists_cons_of_ne_nil h
  exact cyclic_permutations_cons _ _

theorem length_cyclic_permutations_cons (x : α) (l : List α) : length (cyclicPermutations (x :: l)) = length l + 1 := by
  simp [← cyclic_permutations_of_ne_nil]

@[simp]
theorem length_cyclic_permutations_of_ne_nil (l : List α) (h : l ≠ []) : length (cyclicPermutations l) = length l := by
  simp [← cyclic_permutations_of_ne_nil _ h]

@[simp]
theorem nth_le_cyclic_permutations (l : List α) (n : ℕ) (hn : n < length (cyclicPermutations l)) :
    nthLe (cyclicPermutations l) n hn = l.rotate n := by
  obtain rfl | h := eq_or_ne l []
  · simp
    
  · rw [length_cyclic_permutations_of_ne_nil _ h] at hn
    simp [← init_eq_take, ← cyclic_permutations_of_ne_nil _ h, ← nth_le_take', ← rotate_eq_drop_append_take hn.le]
    

theorem mem_cyclic_permutations_self (l : List α) : l ∈ cyclicPermutations l := by
  cases' l with x l
  · simp
    
  · rw [mem_iff_nth_le]
    refine'
      ⟨0, by
        simp , _⟩
    simp
    

theorem length_mem_cyclic_permutations (l : List α) (h : l' ∈ cyclicPermutations l) : length l' = length l := by
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem h
  simp

@[simp]
theorem mem_cyclic_permutations_iff {l l' : List α} : l ∈ cyclicPermutations l' ↔ l ~r l' := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := nth_le_of_mem h
    simp
    
  · intro h
    obtain ⟨k, rfl⟩ := h.symm
    rw [mem_iff_nth_le]
    simp only [← exists_prop, ← nth_le_cyclic_permutations]
    cases' l' with x l
    · simp
      
    · refine' ⟨k % length (x :: l), _, rotate_mod _ _⟩
      simpa using Nat.mod_ltₓ _ (zero_lt_succ _)
      
    

@[simp]
theorem cyclic_permutations_eq_nil_iff {l : List α} : cyclicPermutations l = [[]] ↔ l = [] := by
  refine'
    ⟨fun h => _, fun h => by
      simp [← h]⟩
  rw [eq_comm, ← is_rotated_nil_iff', ← mem_cyclic_permutations_iff, h, mem_singleton]

@[simp]
theorem cyclic_permutations_eq_singleton_iff {l : List α} {x : α} : cyclicPermutations l = [[x]] ↔ l = [x] := by
  refine'
    ⟨fun h => _, fun h => by
      simp [← cyclic_permutations, ← h, ← init_eq_take]⟩
  rw [eq_comm, ← is_rotated_singleton_iff', ← mem_cyclic_permutations_iff, h, mem_singleton]

/-- If a `l : list α` is `nodup l`, then all of its cyclic permutants are distinct. -/
theorem Nodupₓ.cyclic_permutations {l : List α} (hn : Nodupₓ l) : Nodupₓ (cyclicPermutations l) := by
  cases' l with x l
  · simp
    
  rw [nodup_iff_nth_le_inj]
  intro i j hi hj h
  simp only [← length_cyclic_permutations_cons] at hi hj
  rw [← mod_eq_of_lt hi, ← mod_eq_of_lt hj, ← length_cons x l]
  apply hn.rotate_congr
  · simp
    
  · simpa using h
    

@[simp]
theorem cyclic_permutations_rotate (l : List α) (k : ℕ) :
    (l.rotate k).cyclicPermutations = l.cyclicPermutations.rotate k := by
  have : (l.rotate k).cyclicPermutations.length = length (l.cyclic_permutations.rotate k) := by
    cases l
    · simp
      
    · rw [length_cyclic_permutations_of_ne_nil] <;> simp
      
  refine' ext_le this fun n hn hn' => _
  rw [nth_le_cyclic_permutations, nth_le_rotate, nth_le_cyclic_permutations, rotate_rotate, ← rotate_mod, add_commₓ]
  cases l <;> simp

theorem IsRotated.cyclic_permutations {l l' : List α} (h : l ~r l') : l.cyclicPermutations ~r l'.cyclicPermutations :=
  by
  obtain ⟨k, rfl⟩ := h
  exact
    ⟨k, by
      simp ⟩

@[simp]
theorem is_rotated_cyclic_permutations_iff {l l' : List α} : l.cyclicPermutations ~r l'.cyclicPermutations ↔ l ~r l' :=
  by
  by_cases' hl : l = []
  · simp [← hl, ← eq_comm]
    
  have hl' : l.cyclic_permutations.length = l.length := length_cyclic_permutations_of_ne_nil _ hl
  refine' ⟨fun h => _, is_rotated.cyclic_permutations⟩
  obtain ⟨k, hk⟩ := h
  refine' ⟨k % l.length, _⟩
  have hk' : k % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hl)
  rw [← nth_le_cyclic_permutations _ _ (hk'.trans_le hl'.ge), ← nth_le_rotate' _ k]
  simp [← hk, ← hl', ← tsub_add_cancel_of_le hk'.le]

section Decidable

variable [DecidableEq α]

instance isRotatedDecidable (l l' : List α) : Decidable (l ~r l') :=
  decidableOfIff' _ is_rotated_iff_mem_map_range

instance {l l' : List α} : Decidable (@Setoidₓ.R _ (IsRotated.setoid α) l l') :=
  List.isRotatedDecidable _ _

end Decidable

end IsRotated

end List

