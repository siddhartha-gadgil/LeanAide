/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Relator for functions, pairs, sums, and lists.
-/
import Mathbin.Logic.Basic

namespace Relator

universe u₁ u₂ v₁ v₂

/- TODO(johoelzl):
 * should we introduce relators of datatypes as recursive function or as inductive
predicate? For now we stick to the recursor approach.
 * relation lift for datatypes, Π, Σ, set, and subtype types
 * proof composition and identity laws
 * implement method to derive relators from datatype
-/
section

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}

variable (R : α → β → Prop) (S : γ → δ → Prop)

def LiftFun (f : α → γ) (g : β → δ) : Prop :=
  ∀ ⦃a b⦄, R a b → S (f a) (g b)

-- mathport name: «expr ⇒ »
infixr:40 "⇒" => LiftFun

end

section

variable {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

def RightTotal : Prop :=
  ∀ b, ∃ a, R a b

def LeftTotal : Prop :=
  ∀ a, ∃ b, R a b

def BiTotal : Prop :=
  LeftTotal R ∧ RightTotal R

def LeftUnique : Prop :=
  ∀ ⦃a b c⦄, R a c → R b c → a = b

def RightUnique : Prop :=
  ∀ ⦃a b c⦄, R a b → R a c → b = c

def BiUnique : Prop :=
  LeftUnique R ∧ RightUnique R

variable {R}

theorem RightTotal.rel_forall (h : RightTotal R) : ((R⇒Implies)⇒Implies) (fun p => ∀ i, p i) fun q => ∀ i, q i :=
  fun p q Hrel H b => Exists.elim (h b) fun a Rab => Hrel Rab (H _)

theorem LeftTotal.rel_exists (h : LeftTotal R) : ((R⇒Implies)⇒Implies) (fun p => ∃ i, p i) fun q => ∃ i, q i :=
  fun p q Hrel ⟨a, pa⟩ => (h a).imp fun b Rab => Hrel Rab pa

theorem BiTotal.rel_forall (h : BiTotal R) : ((R⇒Iff)⇒Iff) (fun p => ∀ i, p i) fun q => ∀ i, q i := fun p q Hrel =>
  ⟨fun H b => Exists.elim (h.right b) fun a Rab => (Hrel Rab).mp (H _), fun H a =>
    Exists.elim (h.left a) fun b Rab => (Hrel Rab).mpr (H _)⟩

theorem BiTotal.rel_exists (h : BiTotal R) : ((R⇒Iff)⇒Iff) (fun p => ∃ i, p i) fun q => ∃ i, q i := fun p q Hrel =>
  ⟨fun ⟨a, pa⟩ => (h.left a).imp fun b Rab => (Hrel Rab).1 pa, fun ⟨b, qb⟩ =>
    (h.right b).imp fun a Rab => (Hrel Rab).2 qb⟩

theorem left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R⇒R⇒Iff) Eq eq') : LeftUnique R :=
  fun a b c (ac : R a c) (bc : R b c) => (he ac bc).mpr ((he bc bc).mp rfl)

end

theorem rel_imp : (Iff⇒Iff⇒Iff) Implies Implies := fun p q h r s l => imp_congr h l

theorem rel_not : (Iff⇒Iff) Not Not := fun p q h => not_congr h

theorem bi_total_eq {α : Type u₁} : Relator.BiTotal (@Eq α) :=
  { left := fun a => ⟨a, rfl⟩, right := fun a => ⟨a, rfl⟩ }

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

theorem LeftUnique.flip (h : LeftUnique r) : RightUnique (flip r) := fun a b c h₁ h₂ => h h₁ h₂

theorem rel_and : ((· ↔ ·)⇒(· ↔ ·)⇒(· ↔ ·)) (· ∧ ·) (· ∧ ·) := fun a b h₁ c d h₂ => and_congr h₁ h₂

theorem rel_or : ((· ↔ ·)⇒(· ↔ ·)⇒(· ↔ ·)) (· ∨ ·) (· ∨ ·) := fun a b h₁ c d h₂ => or_congr h₁ h₂

theorem rel_iff : ((· ↔ ·)⇒(· ↔ ·)⇒(· ↔ ·)) (· ↔ ·) (· ↔ ·) := fun a b h₁ c d h₂ => iff_congr h₁ h₂

theorem rel_eq {r : α → β → Prop} (hr : BiUnique r) : (r⇒r⇒(· ↔ ·)) (· = ·) (· = ·) := fun a b h₁ c d h₂ =>
  ⟨fun h => hr.right h₁ <| h.symm ▸ h₂, fun h => hr.left h₁ <| h.symm ▸ h₂⟩

end Relator

