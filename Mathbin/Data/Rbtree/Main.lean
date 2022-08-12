/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathbin.Data.Rbtree.Find
import Mathbin.Data.Rbtree.Insert
import Mathbin.Data.Rbtree.MinMax

universe u

namespace Rbnode

variable {α : Type u} {lt : α → α → Prop}

theorem is_searchable_of_well_formed {t : Rbnode α} [IsStrictWeakOrder α lt] :
    t.WellFormed lt → IsSearchable lt t none none := by
  intro h
  induction h
  · constructor
    simp [← lift]
    
  · subst h_n'
    apply is_searchable_insert
    assumption
    

open Color

theorem is_red_black_of_well_formed {t : Rbnode α} : t.WellFormed lt → ∃ c n, IsRedBlack t c n := by
  intro h
  induction h
  · exists black
    exists 0
    constructor
    
  · cases' h_ih with c ih
    cases' ih with n ih
    subst h_n'
    apply insert_is_red_black
    assumption
    

end Rbnode

namespace Rbtree

variable {α : Type u} {lt : α → α → Prop}

theorem balanced (t : Rbtree α lt) : t.depth max ≤ 2 * t.depth min + 1 := by
  cases' t with n p
  simp only [← depth]
  have := Rbnode.is_red_black_of_well_formed p
  cases' this with _ this
  cases' this with _ this
  apply Rbnode.balanced
  assumption

theorem not_mem_mk_rbtree : ∀ a : α, a ∉ mkRbtree α lt := by
  simp [← HasMem.Mem, ← Rbtree.Mem, ← Rbnode.Mem, ← mkRbtree]

theorem not_mem_of_empty {t : Rbtree α lt} (a : α) : t.Empty = tt → a ∉ t := by
  cases' t with n p <;> cases n <;> simp [← Empty, ← HasMem.Mem, ← Rbtree.Mem, ← Rbnode.Mem, ← false_implies_iff]

theorem mem_of_mem_of_eqv [IsStrictWeakOrder α lt] {t : Rbtree α lt} {a b : α} : a ∈ t → a ≈[lt]b → b ∈ t := by
  cases' t with n p <;>
    simp [← HasMem.Mem, ← Rbtree.Mem] <;>
      clear p <;>
        induction n <;>
          simp only [← Rbnode.Mem, ← StrictWeakOrder.Equiv, ← false_implies_iff] <;> intro h₁ h₂ <;> cases_type* or.1
  iterate 2 
    · have : Rbnode.Mem lt b n_lchild := n_ih_lchild h₁ h₂
      simp [← this]
      
    · simp [← incomp_trans_of lt h₂.swap h₁]
      
    · have : Rbnode.Mem lt b n_rchild := n_ih_rchild h₁ h₂
      simp [← this]
      

section Dec

variable [DecidableRel lt]

theorem insert_ne_mk_rbtree (t : Rbtree α lt) (a : α) : t.insert a ≠ mkRbtree α lt := by
  cases' t with n p
  simp [← insert, ← mkRbtree]
  intro h
  injection h with h'
  apply Rbnode.insert_ne_leaf lt n a h'

theorem find_correct [IsStrictWeakOrder α lt] (a : α) (t : Rbtree α lt) : a ∈ t ↔ ∃ b, t.find a = some b ∧ a ≈[lt]b :=
  by
  cases t
  apply Rbnode.find_correct
  apply Rbnode.is_searchable_of_well_formed
  assumption

theorem find_correct_of_total [IsStrictTotalOrder α lt] (a : α) (t : Rbtree α lt) : a ∈ t ↔ t.find a = some a :=
  Iff.intro
    (fun h =>
      match Iff.mp (find_correct a t) h with
      | ⟨b, HEq, heqv⟩ => by
        simp [← HEq, ← (eq_of_eqv_lt heqv).symm])
    fun h => Iff.mpr (find_correct a t) ⟨a, ⟨h, refl a⟩⟩

theorem find_correct_exact [IsStrictTotalOrder α lt] (a : α) (t : Rbtree α lt) : MemExact a t ↔ t.find a = some a := by
  cases t
  apply Rbnode.find_correct_exact
  apply Rbnode.is_searchable_of_well_formed
  assumption

theorem find_insert_of_eqv [IsStrictWeakOrder α lt] (t : Rbtree α lt) {x y} : x ≈[lt]y → (t.insert x).find y = some x :=
  by
  cases t
  intro h
  apply Rbnode.find_insert_of_eqv lt h
  apply Rbnode.is_searchable_of_well_formed
  assumption

theorem find_insert [IsStrictWeakOrder α lt] (t : Rbtree α lt) (x) : (t.insert x).find x = some x :=
  find_insert_of_eqv t (refl x)

theorem find_insert_of_disj [IsStrictWeakOrder α lt] {x y : α} (t : Rbtree α lt) :
    lt x y ∨ lt y x → (t.insert x).find y = t.find y := by
  cases t
  intro h
  apply Rbnode.find_insert_of_disj lt h
  apply Rbnode.is_searchable_of_well_formed
  assumption

theorem find_insert_of_not_eqv [IsStrictWeakOrder α lt] {x y : α} (t : Rbtree α lt) :
    ¬x ≈[lt]y → (t.insert x).find y = t.find y := by
  cases t
  intro h
  apply Rbnode.find_insert_of_not_eqv lt h
  apply Rbnode.is_searchable_of_well_formed
  assumption

theorem find_insert_of_ne [IsStrictTotalOrder α lt] {x y : α} (t : Rbtree α lt) :
    x ≠ y → (t.insert x).find y = t.find y := by
  cases t
  intro h
  have : ¬x ≈[lt]y := fun h' => h (eq_of_eqv_lt h')
  apply Rbnode.find_insert_of_not_eqv lt this
  apply Rbnode.is_searchable_of_well_formed
  assumption

theorem not_mem_of_find_none [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} : t.find a = none → a ∉ t := fun h =>
  Iff.mpr (not_iff_not_of_iff (find_correct a t)) <| by
    intro h
    cases' h with _ h
    cases' h with h₁ h₂
    rw [h] at h₁
    contradiction

theorem eqv_of_find_some [IsStrictWeakOrder α lt] {a b : α} {t : Rbtree α lt} : t.find a = some b → a ≈[lt]b := by
  cases t
  apply Rbnode.eqv_of_find_some
  apply Rbnode.is_searchable_of_well_formed
  assumption

theorem eq_of_find_some [IsStrictTotalOrder α lt] {a b : α} {t : Rbtree α lt} : t.find a = some b → a = b := fun h =>
  suffices a ≈[lt]b from eq_of_eqv_lt this
  eqv_of_find_some h

theorem mem_of_find_some [IsStrictWeakOrder α lt] {a b : α} {t : Rbtree α lt} : t.find a = some b → a ∈ t := fun h =>
  Iff.mpr (find_correct a t) ⟨b, ⟨h, eqv_of_find_some h⟩⟩

theorem find_eq_find_of_eqv [IsStrictWeakOrder α lt] {a b : α} (t : Rbtree α lt) : a ≈[lt]b → t.find a = t.find b := by
  cases t
  apply Rbnode.find_eq_find_of_eqv
  apply Rbnode.is_searchable_of_well_formed
  assumption

theorem contains_correct [IsStrictWeakOrder α lt] (a : α) (t : Rbtree α lt) : a ∈ t ↔ t.contains a = tt := by
  have h := find_correct a t
  simp [← h, ← contains]
  apply Iff.intro
  · intro h'
    cases' h' with _ h'
    cases h'
    simp [*]
    simp [← Option.isSome]
    
  · intro h'
    cases' heq : find t a with v
    simp [← HEq, ← Option.isSome] at h'
    contradiction
    exists v
    simp
    apply eqv_of_find_some HEq
    

theorem mem_insert_of_incomp {a b : α} (t : Rbtree α lt) : ¬lt a b ∧ ¬lt b a → a ∈ t.insert b := by
  cases t
  apply Rbnode.mem_insert_of_incomp

theorem mem_insert [IsIrrefl α lt] : ∀ (a : α) (t : Rbtree α lt), a ∈ t.insert a := by
  intros
  apply mem_insert_of_incomp
  constructor <;> apply irrefl_of lt

theorem mem_insert_of_equiv {a b : α} (t : Rbtree α lt) : a ≈[lt]b → a ∈ t.insert b := by
  cases t
  apply Rbnode.mem_insert_of_incomp

theorem mem_insert_of_mem [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} (b : α) : a ∈ t → a ∈ t.insert b := by
  cases t
  apply Rbnode.mem_insert_of_mem

theorem equiv_or_mem_of_mem_insert [IsStrictWeakOrder α lt] {a b : α} {t : Rbtree α lt} :
    a ∈ t.insert b → a ≈[lt]b ∨ a ∈ t := by
  cases t
  apply Rbnode.equiv_or_mem_of_mem_insert

theorem incomp_or_mem_of_mem_ins [IsStrictWeakOrder α lt] {a b : α} {t : Rbtree α lt} :
    a ∈ t.insert b → ¬lt a b ∧ ¬lt b a ∨ a ∈ t :=
  equiv_or_mem_of_mem_insert

theorem eq_or_mem_of_mem_ins [IsStrictTotalOrder α lt] {a b : α} {t : Rbtree α lt} : a ∈ t.insert b → a = b ∨ a ∈ t :=
  fun h =>
  suffices a ≈[lt]b ∨ a ∈ t by
    simp [← eqv_lt_iff_eq] at this <;> assumption
  incomp_or_mem_of_mem_ins h

end Dec

theorem mem_of_min_eq [IsIrrefl α lt] {a : α} {t : Rbtree α lt} : t.min = some a → a ∈ t := by
  cases t
  apply Rbnode.mem_of_min_eq

theorem mem_of_max_eq [IsIrrefl α lt] {a : α} {t : Rbtree α lt} : t.max = some a → a ∈ t := by
  cases t
  apply Rbnode.mem_of_max_eq

theorem eq_leaf_of_min_eq_none {t : Rbtree α lt} : t.min = none → t = mkRbtree α lt := by
  cases t
  intro h
  congr
  apply Rbnode.eq_leaf_of_min_eq_none h

theorem eq_leaf_of_max_eq_none {t : Rbtree α lt} : t.max = none → t = mkRbtree α lt := by
  cases t
  intro h
  congr
  apply Rbnode.eq_leaf_of_max_eq_none h

theorem min_is_minimal [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} :
    t.min = some a → ∀ {b}, b ∈ t → a ≈[lt]b ∨ lt a b := by
  classical
  cases t
  apply Rbnode.min_is_minimal
  apply Rbnode.is_searchable_of_well_formed
  assumption

theorem max_is_maximal [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} :
    t.max = some a → ∀ {b}, b ∈ t → a ≈[lt]b ∨ lt b a := by
  cases t
  apply Rbnode.max_is_maximal
  apply Rbnode.is_searchable_of_well_formed
  assumption

end Rbtree

