/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Logic.Function.Basic
import Mathbin.Tactic.Protected

/-!
# Types that are empty

In this file we define a typeclass `is_empty`, which expresses that a type has no elements.

## Main declaration

* `is_empty`: a typeclass that expresses that a type is empty.
-/


variable {α β γ : Sort _}

/-- `is_empty α` expresses that `α` is empty. -/
@[protect_proj]
class IsEmpty (α : Sort _) : Prop where
  False : α → False

instance : IsEmpty Empty :=
  ⟨Empty.elim⟩

instance : IsEmpty Pempty :=
  ⟨Pempty.elimₓ⟩

instance : IsEmpty False :=
  ⟨id⟩

instance : IsEmpty (Finₓ 0) :=
  ⟨fun n => Nat.not_lt_zeroₓ n.1 n.2⟩

protected theorem Function.is_empty [IsEmpty β] (f : α → β) : IsEmpty α :=
  ⟨fun x => IsEmpty.false (f x)⟩

instance {p : α → Sort _} [h : Nonempty α] [∀ x, IsEmpty (p x)] : IsEmpty (∀ x, p x) :=
  h.elim fun x => Function.is_empty <| Function.eval x

instance PProd.is_empty_left [IsEmpty α] : IsEmpty (PProd α β) :=
  Function.is_empty PProd.fst

instance PProd.is_empty_right [IsEmpty β] : IsEmpty (PProd α β) :=
  Function.is_empty PProd.snd

instance Prod.is_empty_left {α β} [IsEmpty α] : IsEmpty (α × β) :=
  Function.is_empty Prod.fst

instance Prod.is_empty_right {α β} [IsEmpty β] : IsEmpty (α × β) :=
  Function.is_empty Prod.snd

instance [IsEmpty α] [IsEmpty β] : IsEmpty (PSum α β) :=
  ⟨fun x => PSum.rec IsEmpty.false IsEmpty.false x⟩

instance {α β} [IsEmpty α] [IsEmpty β] : IsEmpty (Sum α β) :=
  ⟨fun x => Sum.rec IsEmpty.false IsEmpty.false x⟩

/-- subtypes of an empty type are empty -/
instance [IsEmpty α] (p : α → Prop) : IsEmpty (Subtype p) :=
  ⟨fun x => IsEmpty.false x.1⟩

/-- subtypes by an all-false predicate are false. -/
theorem Subtype.is_empty_of_false {p : α → Prop} (hp : ∀ a, ¬p a) : IsEmpty (Subtype p) :=
  ⟨fun x => hp _ x.2⟩

/-- subtypes by false are false. -/
instance Subtype.is_empty_false : IsEmpty { a : α // False } :=
  Subtype.is_empty_of_false fun a => id

instance Sigma.is_empty_left {α} [IsEmpty α] {E : α → Type _} : IsEmpty (Sigma E) :=
  Function.is_empty Sigma.fst

-- Test that `pi.is_empty` finds this instance.
example [h : Nonempty α] [IsEmpty β] : IsEmpty (α → β) := by
  infer_instance

/-- Eliminate out of a type that `is_empty` (without using projection notation). -/
@[elab_as_eliminator]
def isEmptyElim [IsEmpty α] {p : α → Sort _} (a : α) : p a :=
  (IsEmpty.false a).elim

theorem is_empty_iff : IsEmpty α ↔ α → False :=
  ⟨@IsEmpty.false α, IsEmpty.mk⟩

namespace IsEmpty

open Function

/-- Eliminate out of a type that `is_empty` (using projection notation). -/
protected def elim (h : IsEmpty α) {p : α → Sort _} (a : α) : p a :=
  isEmptyElim a

/-- Non-dependent version of `is_empty.elim`. Helpful if the elaborator cannot elaborate `h.elim a`
  correctly. -/
protected def elim' {β : Sort _} (h : IsEmpty α) (a : α) : β :=
  h.elim a

protected theorem prop_iff {p : Prop} : IsEmpty p ↔ ¬p :=
  is_empty_iff

variable [IsEmpty α]

@[simp]
theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ True :=
  iff_true_intro isEmptyElim

@[simp]
theorem exists_iff {p : α → Prop} : (∃ a, p a) ↔ False :=
  iff_false_intro fun ⟨x, hx⟩ => IsEmpty.false x

-- see Note [lower instance priority]
instance (priority := 100) : Subsingleton α :=
  ⟨isEmptyElim⟩

end IsEmpty

@[simp]
theorem not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α :=
  ⟨fun h => ⟨fun x => h ⟨x⟩⟩, fun h1 h2 => h2.elim h1.elim⟩

@[simp]
theorem not_is_empty_iff : ¬IsEmpty α ↔ Nonempty α :=
  not_iff_comm.mp not_nonempty_iff

@[simp]
theorem is_empty_Prop {p : Prop} : IsEmpty p ↔ ¬p := by
  simp only [not_nonempty_iff, ← nonempty_Prop]

@[simp]
theorem is_empty_pi {π : α → Sort _} : IsEmpty (∀ a, π a) ↔ ∃ a, IsEmpty (π a) := by
  simp only [not_nonempty_iff, ← Classical.nonempty_piₓ, ← not_forall]

@[simp]
theorem is_empty_sigma {α} {E : α → Type _} : IsEmpty (Sigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [not_nonempty_iff, ← nonempty_sigmaₓ, ← not_exists]

@[simp]
theorem is_empty_psigma {α} {E : α → Sort _} : IsEmpty (PSigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [not_nonempty_iff, ← nonempty_psigmaₓ, ← not_exists]

@[simp]
theorem is_empty_subtype (p : α → Prop) : IsEmpty (Subtype p) ↔ ∀ x, ¬p x := by
  simp only [not_nonempty_iff, ← nonempty_subtype, ← not_exists]

@[simp]
theorem is_empty_prod {α β : Type _} : IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [not_nonempty_iff, ← nonempty_prod, ← not_and_distrib]

@[simp]
theorem is_empty_pprod : IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [not_nonempty_iff, ← nonempty_pprod, ← not_and_distrib]

@[simp]
theorem is_empty_sum {α β} : IsEmpty (Sum α β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [not_nonempty_iff, ← nonempty_sum, ← not_or_distrib]

@[simp]
theorem is_empty_psum {α β} : IsEmpty (PSum α β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [not_nonempty_iff, ← nonempty_psum, ← not_or_distrib]

@[simp]
theorem is_empty_ulift {α} : IsEmpty (ULift α) ↔ IsEmpty α := by
  simp only [not_nonempty_iff, ← nonempty_ulift]

@[simp]
theorem is_empty_plift {α} : IsEmpty (Plift α) ↔ IsEmpty α := by
  simp only [not_nonempty_iff, ← nonempty_pliftₓ]

theorem well_founded_of_empty {α} [IsEmpty α] (r : α → α → Prop) : WellFounded r :=
  ⟨isEmptyElim⟩

variable (α)

theorem is_empty_or_nonempty : IsEmpty α ∨ Nonempty α :=
  (em <| IsEmpty α).elim Or.inl <| Or.inr ∘ not_is_empty_iff.mp

@[simp]
theorem not_is_empty_of_nonempty [h : Nonempty α] : ¬IsEmpty α :=
  not_is_empty_iff.mpr h

variable {α}

theorem Function.extend_of_empty [IsEmpty α] (f : α → β) (g : α → γ) (h : β → γ) : Function.extendₓ f g h = h :=
  funext fun x => (Function.extend_apply' _ _ _) fun ⟨a, h⟩ => isEmptyElim a

