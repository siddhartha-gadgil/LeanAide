/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Control.Traversable.Equiv
import Mathbin.Data.Vector.Basic

universe u v w

namespace DArray

variable {n : ℕ} {α : Finₓ n → Type u}

instance [∀ i, Inhabited (α i)] : Inhabited (DArray n α) :=
  ⟨⟨default⟩⟩

end DArray

namespace Arrayₓ

instance {n α} [Inhabited α] : Inhabited (Arrayₓ n α) :=
  DArray.inhabited

theorem to_list_of_heq {n₁ n₂ α} {a₁ : Arrayₓ n₁ α} {a₂ : Arrayₓ n₂ α} (hn : n₁ = n₂) (ha : HEq a₁ a₂) :
    a₁.toList = a₂.toList := by
  congr <;> assumption

-- rev_list
section RevList

variable {n : ℕ} {α : Type u} {a : Arrayₓ n α}

theorem rev_list_reverse_aux :
    ∀ (i) (h : i ≤ n) (t : List α),
      (a.iterateAux (fun _ => (· :: ·)) i h []).reverseCore t = a.revIterateAux (fun _ => (· :: ·)) i h t
  | 0, h, t => rfl
  | i + 1, h, t => rev_list_reverse_aux i _ _

@[simp]
theorem rev_list_reverse : a.revList.reverse = a.toList :=
  rev_list_reverse_aux _ _ _

@[simp]
theorem to_list_reverse : a.toList.reverse = a.revList := by
  rw [← rev_list_reverse, List.reverse_reverse]

end RevList

-- mem
section Mem

variable {n : ℕ} {α : Type u} {v : α} {a : Arrayₓ n α}

theorem Mem.def : v ∈ a ↔ ∃ i, a.read i = v :=
  Iff.rfl

theorem mem_rev_list_aux :
    ∀ {i} (h : i ≤ n), (∃ j : Finₓ n, (j : ℕ) < i ∧ read a j = v) ↔ v ∈ a.iterateAux (fun _ => (· :: ·)) i h []
  | 0, _ => ⟨fun ⟨i, n, _⟩ => absurd n i.val.not_lt_zero, False.elim⟩
  | i + 1, h =>
    let IH := mem_rev_list_aux (le_of_ltₓ h)
    ⟨fun ⟨j, ji1, e⟩ =>
      Or.elim (lt_or_eq_of_leₓ <| Nat.le_of_succ_le_succₓ ji1) (fun ji => List.mem_cons_of_memₓ _ <| IH.1 ⟨j, ji, e⟩)
        fun je => by
        simp [← DArray.iterateAux] <;>
          apply Or.inl <;> unfold read  at e <;> have H : j = ⟨i, h⟩ := Finₓ.eq_of_veq je <;> rwa [← H, e],
      fun m => by
      simp [← DArray.iterateAux, ← List.Memₓ] at m
      cases' m with e m'
      exact ⟨⟨i, h⟩, Nat.lt_succ_selfₓ _, Eq.symm e⟩
      exact
        let ⟨j, ji, e⟩ := IH.2 m'
        ⟨j, Nat.le_succ_of_leₓ ji, e⟩⟩

@[simp]
theorem mem_rev_list : v ∈ a.revList ↔ v ∈ a :=
  Iff.symm <|
    Iff.trans (exists_congr fun j => Iff.symm <| show j.1 < n ∧ read a j = v ↔ read a j = v from and_iff_right j.2)
      (mem_rev_list_aux _)

@[simp]
theorem mem_to_list : v ∈ a.toList ↔ v ∈ a := by
  rw [← rev_list_reverse] <;> exact list.mem_reverse.trans mem_rev_list

end Mem

-- foldr
section Foldr

variable {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : α → β → β} {a : Arrayₓ n α}

theorem rev_list_foldr_aux :
    ∀ {i} (h : i ≤ n),
      (DArray.iterateAux a (fun _ => (· :: ·)) i h []).foldr f b = DArray.iterateAux a (fun _ => f) i h b
  | 0, h => rfl
  | j + 1, h => congr_arg (f (read a ⟨j, h⟩)) (rev_list_foldr_aux _)

theorem rev_list_foldr : a.revList.foldr f b = a.foldl b f :=
  rev_list_foldr_aux _

end Foldr

-- foldl
section Foldl

variable {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : β → α → β} {a : Arrayₓ n α}

theorem to_list_foldl : a.toList.foldl f b = a.foldl b (Function.swap f) := by
  rw [← rev_list_reverse, List.foldl_reverse, rev_list_foldr]

end Foldl

-- length
section Length

variable {n : ℕ} {α : Type u}

theorem rev_list_length_aux (a : Arrayₓ n α) (i h) : (a.iterateAux (fun _ => (· :: ·)) i h []).length = i := by
  induction i <;> simp [*, ← DArray.iterateAux]

@[simp]
theorem rev_list_length (a : Arrayₓ n α) : a.revList.length = n :=
  rev_list_length_aux a _ _

@[simp]
theorem to_list_length (a : Arrayₓ n α) : a.toList.length = n := by
  rw [← rev_list_reverse, List.length_reverse, rev_list_length]

end Length

-- nth
section Nth

variable {n : ℕ} {α : Type u} {a : Arrayₓ n α}

theorem to_list_nth_le_aux (i : ℕ) (ih : i < n) :
    ∀ (j) {jh t h'},
      (∀ k tl, j + k = i → List.nthLe t k tl = a.read ⟨i, ih⟩) →
        (a.revIterateAux (fun _ => (· :: ·)) j jh t).nthLe i h' = a.read ⟨i, ih⟩
  | 0, _, _, _, al => al i _ <| zero_addₓ _
  | j + 1, jh, t, h', al =>
    (to_list_nth_le_aux j) fun k tl hjk =>
      show List.nthLe (a.read ⟨j, jh⟩ :: t) k tl = a.read ⟨i, ih⟩ from
        match k, hjk, tl with
        | 0, e, tl =>
          match i, e, ih with
          | _, rfl, _ => rfl
        | k' + 1, _, tl => by
          simp [← List.nthLe] <;>
            exact
              al _ _
                (by
                  simp [← add_commₓ, ← add_assocₓ, *] <;> cc)

theorem to_list_nth_le (i : ℕ) (h h') : List.nthLe a.toList i h' = a.read ⟨i, h⟩ :=
  to_list_nth_le_aux _ _ _ fun k tl => absurd tl k.not_lt_zero

@[simp]
theorem to_list_nth_le' (a : Arrayₓ n α) (i : Finₓ n) (h') : List.nthLe a.toList i h' = a.read i := by
  cases i <;> apply to_list_nth_le

theorem to_list_nth {i v} : List.nth a.toList i = some v ↔ ∃ h, a.read ⟨i, h⟩ = v := by
  rw [List.nth_eq_some]
  have ll := to_list_length a
  constructor <;> intro h <;> cases' h with h e <;> subst v
  · exact ⟨ll ▸ h, (to_list_nth_le _ _ _).symm⟩
    
  · exact ⟨ll.symm ▸ h, to_list_nth_le _ _ _⟩
    

theorem write_to_list {i v} : (a.write i v).toList = a.toList.updateNth i v :=
  (List.ext_le
      (by
        simp ))
    fun j h₁ h₂ => by
    have h₃ : j < n := by
      simpa using h₁
    rw [to_list_nth_le _ h₃]
    refine'
      let ⟨_, e⟩ := List.nth_eq_some.1 _
      e.symm
    by_cases' ij : (i : ℕ) = j
    · subst j
      rw [show (⟨(i : ℕ), h₃⟩ : Finₓ _) = i from Finₓ.eq_of_veq rfl, Arrayₓ.read_write, List.nth_update_nth_of_lt]
      simp [← h₃]
      
    · rw [List.nth_update_nth_ne _ _ ij, a.read_write_of_ne, to_list_nth.2 ⟨h₃, rfl⟩]
      exact Finₓ.ne_of_vne ij
      

end Nth

-- enum
section Enum

variable {n : ℕ} {α : Type u} {a : Arrayₓ n α}

theorem mem_to_list_enum {i v} : (i, v) ∈ a.toList.enum ↔ ∃ h, a.read ⟨i, h⟩ = v := by
  simp [← List.mem_iff_nth, ← to_list_nth, ← And.comm, ← And.assoc, ← And.left_comm]

end Enum

-- to_array
section ToArray

variable {n : ℕ} {α : Type u}

@[simp]
theorem to_list_to_array (a : Arrayₓ n α) : HEq a.toList.toArray a :=
  heq_of_heq_of_eq
      (@Eq.drecOn
        (fun m (e : a.toList.length = m) =>
          HEq (DArray.mk fun v => a.toList.nthLe v.1 v.2)
            ((@DArray.mk m fun _ => α) fun v => a.toList.nthLe v.1 <| e.symm ▸ v.2))
        a.to_list_length HEq.rfl) <|
    DArray.ext fun ⟨i, h⟩ => to_list_nth_le i h _

@[simp]
theorem to_array_to_list (l : List α) : l.toArray.toList = l :=
  (List.ext_le (to_list_length _)) fun n h1 h2 => to_list_nth_le _ h2 _

end ToArray

-- push_back
section PushBack

variable {n : ℕ} {α : Type u} {v : α} {a : Arrayₓ n α}

theorem push_back_rev_list_aux :
    ∀ i h h',
      DArray.iterateAux (a.pushBack v) (fun _ => (· :: ·)) i h [] = DArray.iterateAux a (fun _ => (· :: ·)) i h' []
  | 0, h, h' => rfl
  | i + 1, h, h' => by
    simp [← DArray.iterateAux]
    refine' ⟨_, push_back_rev_list_aux _ _ _⟩
    dsimp' [← read, ← DArray.read, ← push_back]
    rw [dif_neg]
    rfl
    exact ne_of_ltₓ h'

@[simp]
theorem push_back_rev_list : (a.pushBack v).revList = v :: a.revList := by
  unfold push_back rev_list foldl iterate DArray.iterate
  dsimp' [← DArray.iterateAux, ← read, ← DArray.read, ← push_back]
  rw [dif_pos (Eq.refl n)]
  apply congr_arg
  apply push_back_rev_list_aux

@[simp]
theorem push_back_to_list : (a.pushBack v).toList = a.toList ++ [v] := by
  rw [← rev_list_reverse, ← rev_list_reverse, push_back_rev_list, List.reverse_cons]

@[simp]
theorem read_push_back_left (i : Finₓ n) : (a.pushBack v).read i.cast_succ = a.read i := by
  cases' i with i hi
  have : ¬i = n := ne_of_ltₓ hi
  simp [← push_back, ← this, ← Finₓ.castSucc, ← Finₓ.castAdd, ← Finₓ.castLe, ← Finₓ.castLt, ← read, ← DArray.read]

@[simp]
theorem read_push_back_right : (a.pushBack v).read (Finₓ.last _) = v := by
  cases' hn : Finₓ.last n with k hk
  have : k = n := by
    simpa [← Finₓ.eq_iff_veq] using hn.symm
  simp [← push_back, ← this, ← Finₓ.castSucc, ← Finₓ.castAdd, ← Finₓ.castLe, ← Finₓ.castLt, ← read, ← DArray.read]

end PushBack

-- foreach
section Foreach

variable {n : ℕ} {α : Type u} {β : Type v} {i : Finₓ n} {f : Finₓ n → α → β} {a : Arrayₓ n α}

@[simp]
theorem read_foreach : (foreach a f).read i = f i (a.read i) :=
  rfl

end Foreach

-- map
section Map

variable {n : ℕ} {α : Type u} {β : Type v} {i : Finₓ n} {f : α → β} {a : Arrayₓ n α}

theorem read_map : (a.map f).read i = f (a.read i) :=
  read_foreach

end Map

-- map₂
section Map₂

variable {n : ℕ} {α : Type u} {i : Finₓ n} {f : α → α → α} {a₁ a₂ : Arrayₓ n α}

@[simp]
theorem read_map₂ : (map₂ f a₁ a₂).read i = f (a₁.read i) (a₂.read i) :=
  read_foreach

end Map₂

end Arrayₓ

namespace Equivₓ

/-- The natural equivalence between length-`n` heterogeneous arrays
and dependent functions from `fin n`. -/
def dArrayEquivFin {n : ℕ} (α : Finₓ n → Type _) : DArray n α ≃ ∀ i, α i :=
  ⟨DArray.read, DArray.mk, fun ⟨f⟩ => rfl, fun f => rfl⟩

/-- The natural equivalence between length-`n` arrays and functions from `fin n`. -/
def arrayEquivFin (n : ℕ) (α : Type _) : Arrayₓ n α ≃ (Finₓ n → α) :=
  dArrayEquivFin _

/-- The natural equivalence between length-`n` vectors and length-`n` arrays. -/
def vectorEquivArray (α : Type _) (n : ℕ) : Vector α n ≃ Arrayₓ n α :=
  (vectorEquivFin _ _).trans (arrayEquivFin _ _).symm

end Equivₓ

namespace Arrayₓ

open Function

variable {n : ℕ}

instance : Traversable (Arrayₓ n) :=
  @Equivₓ.traversable (flip Vector n) _ (fun α => Equivₓ.vectorEquivArray α n) _

instance : IsLawfulTraversable (Arrayₓ n) :=
  @Equivₓ.isLawfulTraversable (flip Vector n) _ (fun α => Equivₓ.vectorEquivArray α n) _ _

end Arrayₓ

