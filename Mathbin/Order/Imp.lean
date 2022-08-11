/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
import Mathbin.Order.SymmDiff
import Mathbin.Tactic.Monotonicity.Basic

/-!
# Implication and equivalence as operations on a boolean algebra

In this file we define `lattice.imp` (notation: `a ⇒ₒ b`) and `lattice.biimp` (notation: `a ⇔ₒ b`)
to be the implication and equivalence as operations on a boolean algebra. More precisely, we put
`a ⇒ₒ b = aᶜ ⊔ b` and `a ⇔ₒ b = (a ⇒ₒ b) ⊓ (b ⇒ₒ a)`. Equivalently, `a ⇒ₒ b = (a \ b)ᶜ` and
`a ⇔ₒ b = (a ∆ b)ᶜ`. For propositions these operations are equal to the usual implication and `iff`.
-/


variable {α β : Type _}

namespace Lattice

/-- Implication as a binary operation on a boolean algebra. -/
def imp [HasCompl α] [HasSup α] (a b : α) : α :=
  aᶜ⊔b

-- mathport name: «expr ⇒ₒ »
infixl:65 " ⇒ₒ " => Lattice.imp

/-- Equivalence as a binary operation on a boolean algebra. -/
def biimp [HasCompl α] [HasSup α] [HasInf α] (a b : α) : α :=
  (a ⇒ₒ b)⊓(b ⇒ₒ a)

-- mathport name: «expr ⇔ₒ »
infixl:60 " ⇔ₒ " => Lattice.biimp

@[simp]
theorem imp_eq_arrow (p q : Prop) : p ⇒ₒ q = (p → q) :=
  propext imp_iff_not_or.symm

@[simp]
theorem biimp_eq_iff (p q : Prop) : p ⇔ₒ q = (p ↔ q) := by
  simp [← biimp, iff_def]

variable [BooleanAlgebra α] {a b c d : α}

@[simp]
theorem compl_imp (a b : α) : (a ⇒ₒ b)ᶜ = a \ b := by
  simp [← imp, ← sdiff_eq]

theorem compl_sdiff (a b : α) : (a \ b)ᶜ = a ⇒ₒ b := by
  rw [← compl_imp, compl_compl]

@[mono]
theorem imp_mono (h₁ : a ≤ b) (h₂ : c ≤ d) : b ⇒ₒ c ≤ a ⇒ₒ d :=
  sup_le_sup (compl_le_compl h₁) h₂

theorem inf_imp_eq (a b c : α) : a⊓(b ⇒ₒ c) = a ⇒ₒ b ⇒ₒ a⊓c := by
  unfold imp <;> simp [← inf_sup_left]

@[simp]
theorem imp_eq_top_iff : a ⇒ₒ b = ⊤ ↔ a ≤ b := by
  rw [← compl_sdiff, compl_eq_top, sdiff_eq_bot_iff]

@[simp]
theorem imp_eq_bot_iff : a ⇒ₒ b = ⊥ ↔ a = ⊤ ∧ b = ⊥ := by
  simp [← imp]

@[simp]
theorem imp_bot (a : α) : a ⇒ₒ ⊥ = aᶜ :=
  sup_bot_eq

@[simp]
theorem top_imp (a : α) : ⊤ ⇒ₒ a = a := by
  simp [← imp]

@[simp]
theorem bot_imp (a : α) : ⊥ ⇒ₒ a = ⊤ :=
  imp_eq_top_iff.2 bot_le

@[simp]
theorem imp_top (a : α) : a ⇒ₒ ⊤ = ⊤ :=
  imp_eq_top_iff.2 le_top

@[simp]
theorem imp_self (a : α) : a ⇒ₒ a = ⊤ :=
  compl_sup_eq_top

@[simp]
theorem compl_imp_compl (a b : α) : aᶜ ⇒ₒ bᶜ = b ⇒ₒ a := by
  simp [← imp, ← sup_comm]

theorem imp_inf_le {α : Type _} [BooleanAlgebra α] (a b : α) : (a ⇒ₒ b)⊓a ≤ b := by
  unfold imp
  rw [inf_sup_right]
  simp

theorem inf_imp_eq_imp_imp (a b c : α) : a⊓b ⇒ₒ c = a ⇒ₒ (b ⇒ₒ c) := by
  simp [← imp, ← sup_assoc]

theorem le_imp_iff : a ≤ b ⇒ₒ c ↔ a⊓b ≤ c := by
  rw [imp, sup_comm, is_compl_compl.le_sup_right_iff_inf_left_le]

theorem biimp_mp (a b : α) : a ⇔ₒ b ≤ a ⇒ₒ b :=
  inf_le_left

theorem biimp_mpr (a b : α) : a ⇔ₒ b ≤ b ⇒ₒ a :=
  inf_le_right

theorem biimp_comm (a b : α) : a ⇔ₒ b = b ⇔ₒ a := by
  unfold Lattice.biimp
  rw [inf_comm]

@[simp]
theorem biimp_eq_top_iff : a ⇔ₒ b = ⊤ ↔ a = b := by
  simp [← biimp, le_antisymm_iffₓ]

@[simp]
theorem biimp_self (a : α) : a ⇔ₒ a = ⊤ :=
  biimp_eq_top_iff.2 rfl

theorem biimp_symm : a ≤ b ⇔ₒ c ↔ a ≤ c ⇔ₒ b := by
  rw [biimp_comm]

theorem compl_symm_diff (a b : α) : (a ∆ b)ᶜ = a ⇔ₒ b := by
  simp only [← biimp, ← imp, ← symmDiff, ← sdiff_eq, ← compl_sup, ← compl_inf, ← compl_compl]

theorem compl_biimp (a b : α) : (a ⇔ₒ b)ᶜ = a ∆ b := by
  rw [← compl_symm_diff, compl_compl]

@[simp]
theorem compl_biimp_compl : aᶜ ⇔ₒ bᶜ = a ⇔ₒ b := by
  simp [← biimp, ← inf_comm]

end Lattice

