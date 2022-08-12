/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Localized

/-
Miscellaneous.
-/
variable {α β γ : Type}

namespace Omega

theorem fun_mono_2 {p : α → β → γ} {a1 a2 : α} {b1 b2 : β} : a1 = a2 → b1 = b2 → p a1 b1 = p a2 b2 := fun h1 h2 => by
  rw [h1, h2]

theorem pred_mono_2 {p : α → β → Prop} {a1 a2 : α} {b1 b2 : β} : a1 = a2 → b1 = b2 → (p a1 b1 ↔ p a2 b2) := fun h1 h2 =>
  by
  rw [h1, h2]

theorem pred_mono_2' {c : Prop → Prop → Prop} {a1 a2 b1 b2 : Prop} : (a1 ↔ a2) → (b1 ↔ b2) → (c a1 b1 ↔ c a2 b2) :=
  fun h1 h2 => by
  rw [h1, h2]

/-- Update variable assignment for a specific variable
    and leave everything else unchanged -/
def update (m : Nat) (a : α) (v : Nat → α) : Nat → α
  | n => if n = m then a else v n

-- mathport name: «expr ⟨ ↦ ⟩»
localized [Omega] notation v " ⟨" m " ↦ " a "⟩" => Omega.update m a v

theorem update_eq (m : Nat) (a : α) (v : Nat → α) : (v ⟨m ↦ a⟩) m = a := by
  simp only [← update, ← if_pos rfl]

theorem update_eq_of_ne {m : Nat} {a : α} {v : Nat → α} (k : Nat) : k ≠ m → update m a v k = v k := by
  intro h1
  unfold update
  rw [if_neg h1]

/-- Assign a new value to the zeroth variable, and push all
    other assignments up by 1 -/
def updateZero (a : α) (v : Nat → α) : Nat → α
  | 0 => a
  | k + 1 => v k

open Tactic

/-- Intro with a fresh name -/
unsafe def intro_fresh : tactic Unit := do
  let n ← mk_fresh_name
  intro n
  skip

/-- Revert an expr if it passes the given test -/
unsafe def revert_cond (t : expr → tactic Unit) (x : expr) : tactic Unit :=
  (t x >> revert x) >> skip <|> skip

/-- Revert all exprs in the context that pass the given test -/
unsafe def revert_cond_all (t : expr → tactic Unit) : tactic Unit := do
  let hs ← local_context
  mmap (revert_cond t) hs
  skip

/-- Try applying a tactic to each of the element in a list
    until success, and return the first successful result -/
unsafe def app_first {α β : Type} (t : α → tactic β) : List α → tactic β
  | [] => failed
  | a :: as => t a <|> app_first as

end Omega

