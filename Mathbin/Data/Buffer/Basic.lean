/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

General utility functions for buffers.
-/
import Leanbin.Data.Buffer
import Mathbin.Data.Array.Lemmas
import Mathbin.Control.Traversable.Instances

namespace Buffer

open Function

variable {α : Type _} {xs : List α}

instance : Inhabited (Buffer α) :=
  ⟨nil⟩

@[ext]
theorem ext : ∀ {b₁ b₂ : Buffer α}, toList b₁ = toList b₂ → b₁ = b₂
  | ⟨n₁, a₁⟩, ⟨n₂, a₂⟩, h => by
    simp [← to_list, ← to_array] at h
    have e : n₁ = n₂ := by
      rw [← Arrayₓ.to_list_length a₁, ← Arrayₓ.to_list_length a₂, h]
    subst e
    have h : HEq a₁ a₂.to_list.to_array := h ▸ a₁.to_list_to_array.symm
    rw [eq_of_heq (h.trans a₂.to_list_to_array)]

theorem ext_iff {b₁ b₂ : Buffer α} : b₁ = b₂ ↔ toList b₁ = toList b₂ :=
  ⟨fun h => h ▸ rfl, ext⟩

theorem size_eq_zero_iff {b : Buffer α} : b.size = 0 ↔ b = nil := by
  rcases b with ⟨_ | n, ⟨a⟩⟩
  · simp only [← size, ← nil, ← mkBuffer, ← true_andₓ, ← true_iffₓ, ← eq_self_iff_true, ← heq_iff_eq, ←
      Sigma.mk.inj_iff]
    ext i
    exact Finₓ.elim0 i
    
  · simp [← size, ← nil, ← mkBuffer, ← Nat.succ_ne_zero]
    

@[simp]
theorem size_nil : (@nil α).size = 0 := by
  rw [size_eq_zero_iff]

@[simp]
theorem to_list_nil : toList (@nil α) = [] :=
  rfl

instance (α) [DecidableEq α] : DecidableEq (Buffer α) := by
  run_tac
    tactic.mk_dec_eq_instance

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
@[simp]
theorem to_list_append_list {b : Buffer α} : toList (appendList b xs) = toList b ++ xs := by
  induction xs generalizing b <;> simp [*] <;> cases b <;> simp [← to_list, ← to_array]

@[simp]
theorem append_list_mk_buffer : appendList mkBuffer xs = Arrayₓ.toBuffer (List.toArrayₓ xs) := by
  ext x : 1 <;>
    simp [← Arrayₓ.toBuffer, ← to_list, ← to_list_append_list] <;>
      induction xs <;> [rfl, skip] <;> simp [← to_array] <;> rfl

@[simp]
theorem to_buffer_to_list (b : Buffer α) : b.toList.toBuffer = b := by
  cases b
  rw [to_list, to_array, List.toBuffer, append_list_mk_buffer]
  congr
  · simpa
    
  · apply Arrayₓ.to_list_to_array
    

@[simp]
theorem to_list_to_buffer (l : List α) : l.toBuffer.toList = l := by
  cases l
  · rfl
    
  · rw [List.toBuffer, to_list_append_list]
    rfl
    

@[simp]
theorem to_list_to_array (b : Buffer α) : b.toArray.toList = b.toList := by
  cases b
  simp [← to_list]

@[simp]
theorem append_list_nil (b : Buffer α) : b.appendList [] = b :=
  rfl

theorem to_buffer_cons (c : α) (l : List α) : (c :: l).toBuffer = [c].toBuffer.appendList l := by
  induction' l with hd tl hl
  · simp
    
  · apply ext
    simp [← hl]
    

@[simp]
theorem size_push_back (b : Buffer α) (a : α) : (b.pushBack a).size = b.size + 1 := by
  cases b
  simp [← size, ← push_back]

@[simp]
theorem size_append_list (b : Buffer α) (l : List α) : (b.appendList l).size = b.size + l.length := by
  induction' l with hd tl hl generalizing b
  · simp
    
  · simp [← append_list, ← hl, ← add_commₓ, ← add_assocₓ]
    

@[simp]
theorem size_to_buffer (l : List α) : l.toBuffer.size = l.length := by
  induction' l with hd tl hl
  · simpa
    
  · rw [to_buffer_cons]
    have : [hd].toBuffer.size = 1 := rfl
    simp [← add_commₓ, ← this]
    

@[simp]
theorem length_to_list (b : Buffer α) : b.toList.length = b.size := by
  rw [← to_buffer_to_list b, to_list_to_buffer, size_to_buffer]

theorem size_singleton (a : α) : [a].toBuffer.size = 1 :=
  rfl

theorem read_push_back_left (b : Buffer α) (a : α) {i : ℕ} (h : i < b.size) :
    (b.pushBack a).read
        ⟨i, by
          convert Nat.lt_succ_of_ltₓ h
          simp ⟩ =
      b.read ⟨i, h⟩ :=
  by
  cases b
  convert Arrayₓ.read_push_back_left _
  simp

@[simp]
theorem read_push_back_right (b : Buffer α) (a : α) :
    (b.pushBack a).read
        ⟨b.size, by
          simp ⟩ =
      a :=
  by
  cases b
  convert Arrayₓ.read_push_back_right

theorem read_append_list_left' (b : Buffer α) (l : List α) {i : ℕ} (h : i < (b.appendList l).size) (h' : i < b.size) :
    (b.appendList l).read ⟨i, h⟩ = b.read ⟨i, h'⟩ := by
  induction' l with hd tl hl generalizing b
  · rfl
    
  · have hb : i < ((b.push_back hd).appendList tl).size := by
      convert h using 1
    have hb' : i < (b.push_back hd).size := by
      convert Nat.lt_succ_of_ltₓ h'
      simp
    have : (append_list b (hd :: tl)).read ⟨i, h⟩ = read ((push_back b hd).appendList tl) ⟨i, hb⟩ := rfl
    simp [← this, ← hl _ hb hb', ← read_push_back_left _ _ h']
    

theorem read_append_list_left (b : Buffer α) (l : List α) {i : ℕ} (h : i < b.size) :
    (b.appendList l).read
        ⟨i, by
          simpa using Nat.lt_add_rightₓ _ _ _ h⟩ =
      b.read ⟨i, h⟩ :=
  read_append_list_left' b l _ h

@[simp]
theorem read_append_list_right (b : Buffer α) (l : List α) {i : ℕ} (h : i < l.length) :
    (b.appendList l).read
        ⟨b.size + i, by
          simp [← h]⟩ =
      l.nthLe i h :=
  by
  induction' l with hd tl hl generalizing b i
  · exact absurd i.zero_le (not_le_of_lt h)
    
  · convert_to ((b.push_back hd).appendList tl).read _ = _
    cases i
    · convert read_append_list_left _ _ _ <;> simp
      
    · rw [List.length, Nat.succ_lt_succ_iff] at h
      have : b.size + i.succ = (b.push_back hd).size + i := by
        simp [← add_commₓ, ← add_left_commₓ, ← Nat.succ_eq_add_one]
      convert hl (b.push_back hd) h using 1
      simpa [← Nat.add_succ, ← Nat.succ_add]
      
    

theorem read_to_buffer' (l : List α) {i : ℕ} (h : i < l.toBuffer.size) (h' : i < l.length) :
    l.toBuffer.read ⟨i, h⟩ = l.nthLe i h' := by
  cases' l with hd tl
  · simpa using h'
    
  · have hi : i < ([hd].toBuffer.appendList tl).size := by
      simpa [← add_commₓ] using h
    convert_to ([hd].toBuffer.appendList tl).read ⟨i, hi⟩ = _
    cases i
    · convert read_append_list_left _ _ _
      simp
      
    · rw [List.nthLe]
      convert read_append_list_right _ _ _
      simp [← Nat.succ_eq_add_one, ← add_commₓ]
      
    

@[simp]
theorem read_to_buffer (l : List α) (i) :
    l.toBuffer.read i =
      l.nthLe i
        (by
          convert i.property
          simp ) :=
  by
  convert read_to_buffer' _ _ _
  · simp
    
  · simpa using i.property
    

theorem nth_le_to_list' (b : Buffer α) {i : ℕ} (h h') : b.toList.nthLe i h = b.read ⟨i, h'⟩ := by
  have :
    b.to_list.to_buffer.read
        ⟨i, by
          simpa using h'⟩ =
      b.read ⟨i, h'⟩ :=
    by
    congr 1 <;> simp [← Finₓ.heq_ext_iff]
  simp [this]

theorem nth_le_to_list (b : Buffer α) {i : ℕ} (h) :
    b.toList.nthLe i h =
      b.read
        ⟨i, by
          simpa using h⟩ :=
  nth_le_to_list' _ _ _

theorem read_eq_nth_le_to_list (b : Buffer α) (i) :
    b.read i =
      b.toList.nthLe i
        (by
          simpa using i.is_lt) :=
  by
  simp [← nth_le_to_list]

theorem read_singleton (c : α) :
    [c].toBuffer.read
        ⟨0, by
          simp ⟩ =
      c :=
  by
  simp

/-- The natural equivalence between lists and buffers, using
`list.to_buffer` and `buffer.to_list`. -/
def listEquivBuffer (α : Type _) : List α ≃ Buffer α := by
  refine' { toFun := List.toBuffer, invFun := Buffer.toList.. } <;> simp [← left_inverse, ← Function.RightInverse]

instance : Traversable Buffer :=
  Equivₓ.traversable listEquivBuffer

instance : IsLawfulTraversable Buffer :=
  Equivₓ.isLawfulTraversable listEquivBuffer

/-- A convenience wrapper around `read` that just fails if the index is out of bounds.
-/
unsafe def read_t (b : Buffer α) (i : ℕ) : tactic α :=
  if h : i < b.size then return <| b.read (Finₓ.mk i h) else tactic.fail "invalid buffer access"

end Buffer

