/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Multiset.Basic

/-!
# The powerset of a multiset
-/


namespace Multiset

open List

variable {α : Type _}

/-! ### powerset -/


/-- A helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists_aux`), as multisets. -/
def powersetAux (l : List α) : List (Multiset α) :=
  0 :: sublistsAux l fun x y => x :: y

theorem powerset_aux_eq_map_coe {l : List α} : powersetAux l = (sublists l).map coe := by
  simp [← powerset_aux, ← sublists] <;>
    rw [←
        show (@sublists_aux₁ α (Multiset α) l fun x => [↑x]) = sublists_aux l fun x => List.cons ↑x from
          sublists_aux₁_eq_sublists_aux _ _,
        sublists_aux_cons_eq_sublists_aux₁, ← bind_ret_eq_map, sublists_aux₁_bind] <;>
      rfl

@[simp]
theorem mem_powerset_aux {l : List α} {s} : s ∈ powersetAux l ↔ s ≤ ↑l :=
  Quotientₓ.induction_on s <| by
    simp [← powerset_aux_eq_map_coe, ← subperm, ← And.comm]

/-- Helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists'`), as multisets. -/
def powersetAux' (l : List α) : List (Multiset α) :=
  (sublists' l).map coe

theorem powerset_aux_perm_powerset_aux' {l : List α} : powersetAux l ~ powersetAux' l := by
  rw [powerset_aux_eq_map_coe] <;> exact (sublists_perm_sublists' _).map _

@[simp]
theorem powerset_aux'_nil : powersetAux' (@nil α) = [0] :=
  rfl

@[simp]
theorem powerset_aux'_cons (a : α) (l : List α) :
    powersetAux' (a :: l) = powersetAux' l ++ List.map (cons a) (powersetAux' l) := by
  simp [← powerset_aux'] <;> rfl

theorem powerset_aux'_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux' l₁ ~ powersetAux' l₂ := by
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂
  · simp
    
  · simp
    exact IH.append (IH.map _)
    
  · simp
    apply perm.append_left
    rw [← append_assoc, ← append_assoc,
      (by
        funext s <;> simp [← cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
    
  · exact IH₁.trans IH₂
    

theorem powerset_aux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux l₁ ~ powersetAux l₂ :=
  powerset_aux_perm_powerset_aux'.trans <| (powerset_aux'_perm p).trans powerset_aux_perm_powerset_aux'.symm

/-- The power set of a multiset. -/
def powerset (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => (powersetAux l : Multiset (Multiset α))) fun l₁ l₂ h => Quot.sound (powerset_aux_perm h)

theorem powerset_coe (l : List α) : @powerset α l = ((sublists l).map coe : List (Multiset α)) :=
  congr_arg coe powerset_aux_eq_map_coe

@[simp]
theorem powerset_coe' (l : List α) : @powerset α l = ((sublists' l).map coe : List (Multiset α)) :=
  Quot.sound powerset_aux_perm_powerset_aux'

@[simp]
theorem powerset_zero : @powerset α 0 = {0} :=
  rfl

@[simp]
theorem powerset_cons (a : α) (s) : powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s) :=
  (Quotientₓ.induction_on s) fun l => by
    simp <;> rfl

@[simp]
theorem mem_powerset {s t : Multiset α} : s ∈ powerset t ↔ s ≤ t :=
  Quotientₓ.induction_on₂ s t <| by
    simp [← subperm, ← And.comm]

theorem map_single_le_powerset (s : Multiset α) : s.map singleton ≤ powerset s :=
  (Quotientₓ.induction_on s) fun l => by
    simp only [← powerset_coe, ← quot_mk_to_coe, ← coe_le, ← coe_map]
    show l.map (coe ∘ List.ret) <+~ (sublists l).map coe
    rw [← List.map_mapₓ]
    exact ((map_ret_sublist_sublists _).map _).Subperm

@[simp]
theorem card_powerset (s : Multiset α) : card (powerset s) = 2 ^ card s :=
  Quotientₓ.induction_on s <| by
    simp

theorem revzip_powerset_aux {l : List α} ⦃x⦄ (h : x ∈ revzipₓ (powersetAux l)) : x.1 + x.2 = ↑l := by
  rw [revzip, powerset_aux_eq_map_coe, ← map_reverse, zip_map, ← revzip] at h
  simp at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists _ _ _ h)

theorem revzip_powerset_aux' {l : List α} ⦃x⦄ (h : x ∈ revzipₓ (powersetAux' l)) : x.1 + x.2 = ↑l := by
  rw [revzip, powerset_aux', ← map_reverse, zip_map, ← revzip] at h
  simp at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists' _ _ _ h)

theorem revzip_powerset_aux_lemma [DecidableEq α] (l : List α) {l' : List (Multiset α)}
    (H : ∀ ⦃x : _ × _⦄, x ∈ revzipₓ l' → x.1 + x.2 = ↑l) : revzipₓ l' = l'.map fun x => (x, ↑l - x) := by
  have :
    forall₂ (fun (p : Multiset α × Multiset α) (s : Multiset α) => p = (s, ↑l - s)) (revzip l')
      ((revzip l').map Prod.fst) :=
    by
    rw [forall₂_map_right_iff, forall₂_same]
    rintro ⟨s, t⟩ h
    dsimp'
    rw [← H h, add_tsub_cancel_left]
  rw [← forall₂_eq_eq_eq, forall₂_map_right_iff]
  simpa

theorem revzip_powerset_aux_perm_aux' {l : List α} : revzipₓ (powersetAux l) ~ revzipₓ (powersetAux' l) := by
  have := Classical.decEq α
  rw [revzip_powerset_aux_lemma l revzip_powerset_aux, revzip_powerset_aux_lemma l revzip_powerset_aux']
  exact powerset_aux_perm_powerset_aux'.map _

theorem revzip_powerset_aux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : revzipₓ (powersetAux l₁) ~ revzipₓ (powersetAux l₂) :=
  by
  have := Classical.decEq α
  simp [← fun l : List α => revzip_powerset_aux_lemma l revzip_powerset_aux, ← coe_eq_coe.2 p]
  exact (powerset_aux_perm p).map _

/-! ### powerset_len -/


/-- Helper function for `powerset_len`. Given a list `l`, `powerset_len_aux n l` is the list
of sublists of length `n`, as multisets. -/
def powersetLenAux (n : ℕ) (l : List α) : List (Multiset α) :=
  sublistsLenAux n l coe []

theorem powerset_len_aux_eq_map_coe {n} {l : List α} : powersetLenAux n l = (sublistsLen n l).map coe := by
  rw [powerset_len_aux, sublists_len_aux_eq, append_nil]

@[simp]
theorem mem_powerset_len_aux {n} {l : List α} {s} : s ∈ powersetLenAux n l ↔ s ≤ ↑l ∧ card s = n :=
  Quotientₓ.induction_on s <| by
    simp [← powerset_len_aux_eq_map_coe, ← subperm] <;>
      exact fun l₁ =>
        ⟨fun ⟨l₂, ⟨s, e⟩, p⟩ => ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩, fun ⟨⟨l₂, p, s⟩, e⟩ =>
          ⟨_, ⟨s, p.length_eq.trans e⟩, p⟩⟩

@[simp]
theorem powerset_len_aux_zero (l : List α) : powersetLenAux 0 l = [0] := by
  simp [← powerset_len_aux_eq_map_coe]

@[simp]
theorem powerset_len_aux_nil (n : ℕ) : powersetLenAux (n + 1) (@nil α) = [] :=
  rfl

@[simp]
theorem powerset_len_aux_cons (n : ℕ) (a : α) (l : List α) :
    powersetLenAux (n + 1) (a :: l) = powersetLenAux (n + 1) l ++ List.map (cons a) (powersetLenAux n l) := by
  simp [← powerset_len_aux_eq_map_coe] <;> rfl

theorem powerset_len_aux_perm {n} {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetLenAux n l₁ ~ powersetLenAux n l₂ := by
  induction' n with n IHn generalizing l₁ l₂
  · simp
    
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂
  · rfl
    
  · simp
    exact IH.append ((IHn p).map _)
    
  · simp
    apply perm.append_left
    cases n
    · simp
      apply perm.swap
      
    simp
    rw [← append_assoc, ← append_assoc,
      (by
        funext s <;> simp [← cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
    
  · exact IH₁.trans IH₂
    

/-- `powerset_len n s` is the multiset of all submultisets of `s` of length `n`. -/
def powersetLen (n : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => (powersetLenAux n l : Multiset (Multiset α))) fun l₁ l₂ h =>
    Quot.sound (powerset_len_aux_perm h)

theorem powerset_len_coe' (n) (l : List α) : @powersetLen α n l = powersetLenAux n l :=
  rfl

theorem powerset_len_coe (n) (l : List α) : @powersetLen α n l = ((sublistsLen n l).map coe : List (Multiset α)) :=
  congr_arg coe powerset_len_aux_eq_map_coe

@[simp]
theorem powerset_len_zero_left (s : Multiset α) : powersetLen 0 s = {0} :=
  (Quotientₓ.induction_on s) fun l => by
    simp [← powerset_len_coe'] <;> rfl

theorem powerset_len_zero_right (n : ℕ) : @powersetLen α (n + 1) 0 = 0 :=
  rfl

@[simp]
theorem powerset_len_cons (n : ℕ) (a : α) (s) :
    powersetLen (n + 1) (a ::ₘ s) = powersetLen (n + 1) s + map (cons a) (powersetLen n s) :=
  (Quotientₓ.induction_on s) fun l => by
    simp [← powerset_len_coe'] <;> rfl

@[simp]
theorem mem_powerset_len {n : ℕ} {s t : Multiset α} : s ∈ powersetLen n t ↔ s ≤ t ∧ card s = n :=
  (Quotientₓ.induction_on t) fun l => by
    simp [← powerset_len_coe']

@[simp]
theorem card_powerset_len (n : ℕ) (s : Multiset α) : card (powersetLen n s) = Nat.choose (card s) n :=
  Quotientₓ.induction_on s <| by
    simp [← powerset_len_coe]

theorem powerset_len_le_powerset (n : ℕ) (s : Multiset α) : powersetLen n s ≤ powerset s :=
  (Quotientₓ.induction_on s) fun l => by
    simp [← powerset_len_coe] <;> exact ((sublists_len_sublist_sublists' _ _).map _).Subperm

theorem powerset_len_mono (n : ℕ) {s t : Multiset α} (h : s ≤ t) : powersetLen n s ≤ powersetLen n t :=
  (le_induction_on h) fun l₁ l₂ h => by
    simp [← powerset_len_coe] <;> exact ((sublists_len_sublist_of_sublist _ h).map _).Subperm

@[simp]
theorem powerset_len_empty {α : Type _} (n : ℕ) {s : Multiset α} (h : s.card < n) : powersetLen n s = 0 :=
  card_eq_zero.mp (Nat.choose_eq_zero_of_lt h ▸ card_powerset_len _ _)

@[simp]
theorem powerset_len_card_add (s : Multiset α) {i : ℕ} (hi : 0 < i) : s.powersetLen (s.card + i) = 0 :=
  powerset_len_empty _ (lt_add_of_pos_right (card s) hi)

theorem powerset_len_map {β : Type _} (f : α → β) (n : ℕ) (s : Multiset α) :
    powersetLen n (s.map f) = (powersetLen n s).map (map f) := by
  induction' s using Multiset.induction with t s ih generalizing n
  · cases n <;> simp [← powerset_len_zero_left, ← powerset_len_zero_right]
    
  · cases n <;> simp [← ih, ← map_comp_cons]
    

end Multiset

