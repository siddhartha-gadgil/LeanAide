/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Yaël Dillies
-/
import Mathbin.Logic.Equiv.Basic
import Mathbin.Logic.Nontrivial
import Mathbin.Order.Basic

/-!
# Type synonyms

This file provides two type synonyms for order theory:
* `order_dual α`: Type synonym of `α` to equip it with the dual order (`a ≤ b` becomes `b ≤ a`).
* `lex α`: Type synonym of `α` to equip it with its lexicographic order. The precise meaning depends
  on the type we take the lex of. Examples include `prod`, `sigma`, `list`, `finset`.

## Notation

`αᵒᵈ` is notation for `order_dual α`.

The general rule for notation of `lex` types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`/`lex α`. Instead, explicit
coercions should be inserted:
* `order_dual`: `order_dual.to_dual : α → αᵒᵈ` and `order_dual.of_dual : αᵒᵈ → α`
* `lex`: `to_lex : α → lex α` and `of_lex : lex α → α`.

In fact, those are bundled as `equiv`s to put goals in the right syntactic form for rewriting with
the `equiv` API (`⇑to_lex a` where `⇑` is `coe_fn : (α ≃ lex α) → α → lex α`, instead of a bare
`to_lex a`).

## See also

This file is similar to `algebra.group.type_tags`.
-/


variable {α β γ : Type _}

/-! ### Order dual -/


namespace OrderDual

instance [h : Nontrivial α] : Nontrivial αᵒᵈ :=
  h

/-- `to_dual` is the identity function to the `order_dual` of a linear order.  -/
def toDual : α ≃ αᵒᵈ :=
  Equivₓ.refl _

/-- `of_dual` is the identity function from the `order_dual` of a linear order.  -/
def ofDual : αᵒᵈ ≃ α :=
  Equivₓ.refl _

@[simp]
theorem to_dual_symm_eq : (@toDual α).symm = of_dual :=
  rfl

@[simp]
theorem of_dual_symm_eq : (@ofDual α).symm = to_dual :=
  rfl

@[simp]
theorem to_dual_of_dual (a : αᵒᵈ) : toDual (ofDual a) = a :=
  rfl

@[simp]
theorem of_dual_to_dual (a : α) : ofDual (toDual a) = a :=
  rfl

@[simp]
theorem to_dual_inj {a b : α} : toDual a = toDual b ↔ a = b :=
  Iff.rfl

@[simp]
theorem of_dual_inj {a b : αᵒᵈ} : ofDual a = ofDual b ↔ a = b :=
  Iff.rfl

@[simp]
theorem to_dual_le_to_dual [LE α] {a b : α} : toDual a ≤ toDual b ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem to_dual_lt_to_dual [LT α] {a b : α} : toDual a < toDual b ↔ b < a :=
  Iff.rfl

@[simp]
theorem of_dual_le_of_dual [LE α] {a b : αᵒᵈ} : ofDual a ≤ ofDual b ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem of_dual_lt_of_dual [LT α] {a b : αᵒᵈ} : ofDual a < ofDual b ↔ b < a :=
  Iff.rfl

theorem le_to_dual [LE α] {a : αᵒᵈ} {b : α} : a ≤ toDual b ↔ b ≤ ofDual a :=
  Iff.rfl

theorem lt_to_dual [LT α] {a : αᵒᵈ} {b : α} : a < toDual b ↔ b < ofDual a :=
  Iff.rfl

theorem to_dual_le [LE α] {a : α} {b : αᵒᵈ} : toDual a ≤ b ↔ ofDual b ≤ a :=
  Iff.rfl

theorem to_dual_lt [LT α] {a : α} {b : αᵒᵈ} : toDual a < b ↔ ofDual b < a :=
  Iff.rfl

/-- Recursor for `αᵒᵈ`. -/
@[elab_as_eliminator]
protected def rec {C : αᵒᵈ → Sort _} (h₂ : ∀ a : α, C (toDual a)) : ∀ a : αᵒᵈ, C a :=
  h₂

@[simp]
protected theorem forall {p : αᵒᵈ → Prop} : (∀ a, p a) ↔ ∀ a, p (toDual a) :=
  Iff.rfl

@[simp]
protected theorem exists {p : αᵒᵈ → Prop} : (∃ a, p a) ↔ ∃ a, p (toDual a) :=
  Iff.rfl

alias to_dual_le_to_dual ↔ _ _root_.has_le.le.dual

alias to_dual_lt_to_dual ↔ _ _root_.has_lt.lt.dual

alias of_dual_le_of_dual ↔ _ _root_.has_le.le.of_dual

alias of_dual_lt_of_dual ↔ _ _root_.has_lt.lt.of_dual

end OrderDual

/-! ### Lexicographic order -/


/-- A type synonym to equip a type with its lexicographic order. -/
def Lex (α : Type _) :=
  α

/-- `to_lex` is the identity function to the `lex` of a type.  -/
@[matchPattern]
def toLex : α ≃ Lex α :=
  Equivₓ.refl _

/-- `of_lex` is the identity function from the `lex` of a type.  -/
@[matchPattern]
def ofLex : Lex α ≃ α :=
  Equivₓ.refl _

@[simp]
theorem to_lex_symm_eq : (@toLex α).symm = ofLex :=
  rfl

@[simp]
theorem of_lex_symm_eq : (@ofLex α).symm = toLex :=
  rfl

@[simp]
theorem to_lex_of_lex (a : Lex α) : toLex (ofLex a) = a :=
  rfl

@[simp]
theorem of_lex_to_lex (a : α) : ofLex (toLex a) = a :=
  rfl

@[simp]
theorem to_lex_inj {a b : α} : toLex a = toLex b ↔ a = b :=
  Iff.rfl

@[simp]
theorem of_lex_inj {a b : Lex α} : ofLex a = ofLex b ↔ a = b :=
  Iff.rfl

/-- A recursor for `lex`. Use as `induction x using lex.rec`. -/
protected def Lex.rec {β : Lex α → Sort _} (h : ∀ a, β (toLex a)) : ∀ a, β a := fun a => h (ofLex a)

