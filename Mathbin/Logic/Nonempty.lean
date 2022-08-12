/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Logic.Basic

/-!
# Nonempty types

This file proves a few extra facts about `nonempty`, which is defined in core Lean.

## Main declarations

* `nonempty.some`: Extracts a witness of nonemptiness using choice. Takes `nonempty α` explicitly.
* `classical.arbitrary`: Extracts a witness of nonemptiness using choice. Takes `nonempty α` as an
  instance.
-/


variable {α β : Type _} {γ : α → Type _}

attribute [simp] nonempty_of_inhabited

instance (priority := 20) Zero.nonempty [Zero α] : Nonempty α :=
  ⟨0⟩

instance (priority := 20) One.nonempty [One α] : Nonempty α :=
  ⟨1⟩

theorem exists_true_iff_nonempty {α : Sort _} : (∃ a : α, True) ↔ Nonempty α :=
  Iff.intro (fun ⟨a, _⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨a, trivialₓ⟩

@[simp]
theorem nonempty_Prop {p : Prop} : Nonempty p ↔ p :=
  Iff.intro (fun ⟨h⟩ => h) fun h => ⟨h⟩

theorem not_nonempty_iff_imp_false {α : Sort _} : ¬Nonempty α ↔ α → False :=
  ⟨fun h a => h ⟨a⟩, fun h ⟨a⟩ => h a⟩

@[simp]
theorem nonempty_sigmaₓ : Nonempty (Σa : α, γ a) ↔ ∃ a : α, Nonempty (γ a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]
theorem nonempty_psigmaₓ {α} {β : α → Sort _} : Nonempty (PSigma β) ↔ ∃ a : α, Nonempty (β a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]
theorem nonempty_subtype {α} {p : α → Prop} : Nonempty (Subtype p) ↔ ∃ a : α, p a :=
  Iff.intro (fun ⟨⟨a, h⟩⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a, h⟩⟩

@[simp]
theorem nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]
theorem nonempty_pprod {α β} : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]
theorem nonempty_sum : Nonempty (Sum α β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | Sum.inl a => Or.inl ⟨a⟩
      | Sum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨Sum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨Sum.inr b⟩

@[simp]
theorem nonempty_psum {α β} : Nonempty (PSum α β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | PSum.inl a => Or.inl ⟨a⟩
      | PSum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨PSum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨PSum.inr b⟩

@[simp]
theorem nonempty_empty : ¬Nonempty Empty := fun ⟨h⟩ => h.elim

@[simp]
theorem nonempty_ulift : Nonempty (ULift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

@[simp]
theorem nonempty_pliftₓ {α} : Nonempty (Plift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

@[simp]
theorem Nonempty.forall {α} {p : Nonempty α → Prop} : (∀ h : Nonempty α, p h) ↔ ∀ a, p ⟨a⟩ :=
  Iff.intro (fun h a => h _) fun h ⟨a⟩ => h _

@[simp]
theorem Nonempty.exists {α} {p : Nonempty α → Prop} : (∃ h : Nonempty α, p h) ↔ ∃ a, p ⟨a⟩ :=
  Iff.intro (fun ⟨⟨a⟩, h⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩

theorem Classical.nonempty_piₓ {α} {β : α → Sort _} : Nonempty (∀ a : α, β a) ↔ ∀ a : α, Nonempty (β a) :=
  Iff.intro (fun ⟨f⟩ a => ⟨f a⟩) fun f => ⟨fun a => Classical.choice <| f a⟩

/-- Using `classical.choice`, lifts a (`Prop`-valued) `nonempty` instance to a (`Type`-valued)
  `inhabited` instance. `classical.inhabited_of_nonempty` already exists, in
  `core/init/classical.lean`, but the assumption is not a type class argument,
  which makes it unsuitable for some applications. -/
noncomputable def Classical.inhabitedOfNonempty' {α} [h : Nonempty α] : Inhabited α :=
  ⟨Classical.choice h⟩

/-- Using `classical.choice`, extracts a term from a `nonempty` type. -/
@[reducible]
protected noncomputable def Nonempty.some {α} (h : Nonempty α) : α :=
  Classical.choice h

/-- Using `classical.choice`, extracts a term from a `nonempty` type. -/
@[reducible]
protected noncomputable def Classical.arbitrary (α) [h : Nonempty α] : α :=
  Classical.choice h

/-- Given `f : α → β`, if `α` is nonempty then `β` is also nonempty.
  `nonempty` cannot be a `functor`, because `functor` is restricted to `Type`. -/
theorem Nonempty.map {α β} (f : α → β) : Nonempty α → Nonempty β
  | ⟨h⟩ => ⟨f h⟩

protected theorem Nonempty.map2 {α β γ : Sort _} (f : α → β → γ) : Nonempty α → Nonempty β → Nonempty γ
  | ⟨x⟩, ⟨y⟩ => ⟨f x y⟩

protected theorem Nonempty.congr {α β} (f : α → β) (g : β → α) : Nonempty α ↔ Nonempty β :=
  ⟨Nonempty.map f, Nonempty.map g⟩

theorem Nonempty.elim_to_inhabited {α : Sort _} [h : Nonempty α] {p : Prop} (f : Inhabited α → p) : p :=
  h.elim <| f ∘ Inhabited.mk

instance {α β} [h : Nonempty α] [h2 : Nonempty β] : Nonempty (α × β) :=
  h.elim fun g => h2.elim fun g2 => ⟨⟨g, g2⟩⟩

theorem subsingleton_of_not_nonempty {α : Sort _} (h : ¬Nonempty α) : Subsingleton α :=
  ⟨fun x => False.elim <| not_nonempty_iff_imp_false.mp h x⟩

theorem Function.Surjective.nonempty [h : Nonempty β] {f : α → β} (hf : Function.Surjective f) : Nonempty α :=
  let ⟨y⟩ := h
  let ⟨x, hx⟩ := hf y
  ⟨x⟩

