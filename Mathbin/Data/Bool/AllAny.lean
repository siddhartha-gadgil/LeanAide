/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.List.Basic

/-!
# Boolean quantifiers

This proves a few properties about `list.all` and `list.any`, which are the `bool` universal and
existential quantifiers. Their definitions are in core Lean.
-/


variable {α : Type _} {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

namespace List

@[simp]
theorem all_nil (p : α → Bool) : all [] p = tt :=
  rfl

@[simp]
theorem all_cons (p : α → Bool) (a : α) (l : List α) : all (a :: l) p = (p a && all l p) :=
  rfl

theorem all_iff_forall {p : α → Bool} : all l p ↔ ∀, ∀ a ∈ l, ∀, p a := by
  induction' l with a l ih
  · exact iff_of_true rfl (forall_mem_nil _)
    
  simp only [← all_cons, ← band_coe_iff, ← ih, ← forall_mem_cons]

theorem all_iff_forall_prop : (all l fun a => p a) ↔ ∀, ∀ a ∈ l, ∀, p a := by
  simp only [← all_iff_forall, ← Bool.of_to_bool_iff]

@[simp]
theorem any_nil (p : α → Bool) : any [] p = ff :=
  rfl

@[simp]
theorem any_cons (p : α → Bool) (a : α) (l : List α) : any (a :: l) p = (p a || any l p) :=
  rfl

theorem any_iff_exists {p : α → Bool} : any l p ↔ ∃ a ∈ l, p a := by
  induction' l with a l ih
  · exact iff_of_false Bool.not_ff (not_exists_mem_nil _)
    
  simp only [← any_cons, ← bor_coe_iff, ← ih, ← exists_mem_cons_iff]

theorem any_iff_exists_prop : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by
  simp [← any_iff_exists]

theorem any_of_mem {p : α → Bool} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
  any_iff_exists.2 ⟨_, h₁, h₂⟩

end List

