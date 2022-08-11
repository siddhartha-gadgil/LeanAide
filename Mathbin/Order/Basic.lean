/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathbin.Data.Prod.Basic
import Mathbin.Data.Subtype

/-!
# Basic definitions about `≤` and `<`

This file proves basic results about orders, provides extensive dot notation, defines useful order
classes and allows to transfer order instances.

## Type synonyms

* `order_dual α` : A type synonym reversing the meaning of all inequalities, with notation `αᵒᵈ`.
* `as_linear_order α`: A type synonym to promote `partial_order α` to `linear_order α` using
  `is_total α (≤)`.

### Transfering orders

- `order.preimage`, `preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `partial_order.lift`, `linear_order.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra class

* `has_sup`: type class for the `⊔` notation
* `has_inf`: type class for the `⊓` notation
* `densely_ordered`: An order with no gap, i.e. for any two elements `a < b` there exists `c` such
  that `a < c < b`.

## Notes

`≤` and `<` are highly favored over `≥` and `>` in mathlib. The reason is that we can formulate all
lemmas using `≤`/`<`, and `rw` has trouble unifying `≤` and `≥`. Hence choosing one direction spares
us useless duplication. This is enforced by a linter. See Note [nolint_ge] for more infos.

Dot notation is particularly useful on `≤` (`has_le.le`) and `<` (`has_lt.lt`). To that end, we
provide many aliases to dot notation-less lemmas. For example, `le_trans` is aliased with
`has_le.le.trans` and can be used to construct `hab.trans hbc : a ≤ c` when `hab : a ≤ b`,
`hbc : b ≤ c`, `lt_of_le_of_lt` is aliased as `has_le.le.trans_lt` and can be used to construct
`hab.trans hbc : a < c` when `hab : a ≤ b`, `hbc : b < c`.

## TODO

- expand module docs
- automatic construction of dual definitions / theorems

## Tags

preorder, order, partial order, poset, linear order, chain
-/


open Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

section Preorderₓ

variable [Preorderₓ α] {a b c : α}

theorem le_trans' : b ≤ c → a ≤ b → a ≤ c :=
  flip le_transₓ

theorem lt_trans' : b < c → a < b → a < c :=
  flip lt_transₓ

theorem lt_of_le_of_lt' : b ≤ c → a < b → a < c :=
  flip lt_of_lt_of_leₓ

theorem lt_of_lt_of_le' : b < c → a ≤ b → a < c :=
  flip lt_of_le_of_ltₓ

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] {a b : α}

theorem ge_antisymm : a ≤ b → b ≤ a → b = a :=
  flip le_antisymmₓ

theorem lt_of_le_of_ne' : a ≤ b → b ≠ a → a < b := fun h₁ h₂ => lt_of_le_of_neₓ h₁ h₂.symm

theorem Ne.lt_of_le : a ≠ b → a ≤ b → a < b :=
  flip lt_of_le_of_neₓ

theorem Ne.lt_of_le' : b ≠ a → a ≤ b → a < b :=
  flip lt_of_le_of_ne'

end PartialOrderₓ

attribute [simp] le_reflₓ

attribute [ext] LE

alias le_transₓ ← LE.le.trans

alias le_trans' ← LE.le.trans'

alias lt_of_le_of_ltₓ ← LE.le.trans_lt

alias lt_of_le_of_lt' ← LE.le.trans_lt'

alias le_antisymmₓ ← LE.le.antisymm

alias ge_antisymm ← LE.le.antisymm'

alias lt_of_le_of_neₓ ← LE.le.lt_of_ne

alias lt_of_le_of_ne' ← LE.le.lt_of_ne'

alias lt_of_le_not_leₓ ← LE.le.lt_of_not_le

alias lt_or_eq_of_leₓ ← LE.le.lt_or_eq

alias Decidable.lt_or_eq_of_leₓ ← LE.le.lt_or_eq_dec

alias le_of_ltₓ ← LT.lt.le

alias lt_transₓ ← LT.lt.trans

alias lt_trans' ← LT.lt.trans'

alias lt_of_lt_of_leₓ ← LT.lt.trans_le

alias lt_of_lt_of_le' ← LT.lt.trans_le'

alias ne_of_ltₓ ← LT.lt.ne

alias lt_asymmₓ ← LT.lt.asymm LT.lt.not_lt

alias le_of_eqₓ ← Eq.le

attribute [nolint decidable_classical] LE.le.lt_or_eq_dec

section

variable [Preorderₓ α] {a b c : α}

/-- A version of `le_refl` where the argument is implicit -/
theorem le_rfl : a ≤ a :=
  le_reflₓ a

@[simp]
theorem lt_self_iff_false (x : α) : x < x ↔ False :=
  ⟨lt_irreflₓ x, False.elim⟩

theorem le_of_le_of_eq (hab : a ≤ b) (hbc : b = c) : a ≤ c :=
  hab.trans hbc.le

theorem le_of_eq_of_le (hab : a = b) (hbc : b ≤ c) : a ≤ c :=
  hab.le.trans hbc

theorem lt_of_lt_of_eq (hab : a < b) (hbc : b = c) : a < c :=
  hab.trans_le hbc.le

theorem lt_of_eq_of_lt (hab : a = b) (hbc : b < c) : a < c :=
  hab.le.trans_lt hbc

theorem le_of_le_of_eq' : b ≤ c → a = b → a ≤ c :=
  flip le_of_eq_of_le

theorem le_of_eq_of_le' : b = c → a ≤ b → a ≤ c :=
  flip le_of_le_of_eq

theorem lt_of_lt_of_eq' : b < c → a = b → a < c :=
  flip lt_of_eq_of_lt

theorem lt_of_eq_of_lt' : b = c → a < b → a < c :=
  flip lt_of_lt_of_eq

alias le_of_le_of_eq ← LE.le.trans_eq

alias le_of_le_of_eq' ← LE.le.trans_eq'

alias lt_of_lt_of_eq ← LT.lt.trans_eq

alias lt_of_lt_of_eq' ← LT.lt.trans_eq'

alias le_of_eq_of_le ← Eq.trans_le

alias le_of_eq_of_le' ← Eq.trans_ge

alias lt_of_eq_of_lt ← Eq.trans_lt

alias lt_of_eq_of_lt' ← Eq.trans_gt

end

namespace Eq

variable [Preorderₓ α] {x y z : α}

/-- If `x = y` then `y ≤ x`. Note: this lemma uses `y ≤ x` instead of `x ≥ y`, because `le` is used
almost exclusively in mathlib. -/
protected theorem ge (h : x = y) : y ≤ x :=
  h.symm.le

theorem not_lt (h : x = y) : ¬x < y := fun h' => h'.Ne h

theorem not_gt (h : x = y) : ¬y < x :=
  h.symm.not_lt

end Eq

namespace LE.le

-- see Note [nolint_ge]
@[nolint ge_or_gt]
protected theorem ge [LE α] {x y : α} (h : x ≤ y) : y ≥ x :=
  h

theorem lt_iff_ne [PartialOrderₓ α] {x y : α} (h : x ≤ y) : x < y ↔ x ≠ y :=
  ⟨fun h => h.Ne, h.lt_of_ne⟩

theorem le_iff_eq [PartialOrderₓ α] {x y : α} (h : x ≤ y) : y ≤ x ↔ y = x :=
  ⟨fun h' => h'.antisymm h, Eq.le⟩

theorem lt_or_le [LinearOrderₓ α] {a b : α} (h : a ≤ b) (c : α) : a < c ∨ c ≤ b :=
  ((lt_or_geₓ a c).imp id) fun hc => le_transₓ hc h

theorem le_or_lt [LinearOrderₓ α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c < b :=
  ((le_or_gtₓ a c).imp id) fun hc => lt_of_lt_of_leₓ hc h

theorem le_or_le [LinearOrderₓ α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b :=
  (h.le_or_lt c).elim Or.inl fun h => Or.inr <| le_of_ltₓ h

end LE.le

namespace LT.lt

-- see Note [nolint_ge]
@[nolint ge_or_gt]
protected theorem gt [LT α] {x y : α} (h : x < y) : y > x :=
  h

protected theorem false [Preorderₓ α] {x : α} : x < x → False :=
  lt_irreflₓ x

theorem ne' [Preorderₓ α] {x y : α} (h : x < y) : y ≠ x :=
  h.Ne.symm

theorem lt_or_lt [LinearOrderₓ α] {x y : α} (h : x < y) (z : α) : x < z ∨ z < y :=
  (lt_or_geₓ z y).elim Or.inr fun hz => Or.inl <| h.trans_le hz

end LT.lt

-- see Note [nolint_ge]
@[nolint ge_or_gt]
protected theorem Ge.le [LE α] {x y : α} (h : x ≥ y) : y ≤ x :=
  h

-- see Note [nolint_ge]
@[nolint ge_or_gt]
protected theorem Gt.lt [LT α] {x y : α} (h : x > y) : y < x :=
  h

-- see Note [nolint_ge]
@[nolint ge_or_gt]
theorem ge_of_eq [Preorderₓ α] {a b : α} (h : a = b) : a ≥ b :=
  h.Ge

-- see Note [nolint_ge]
@[simp, nolint ge_or_gt]
theorem ge_iff_le [LE α] {a b : α} : a ≥ b ↔ b ≤ a :=
  Iff.rfl

-- see Note [nolint_ge]
@[simp, nolint ge_or_gt]
theorem gt_iff_lt [LT α] {a b : α} : a > b ↔ b < a :=
  Iff.rfl

theorem not_le_of_lt [Preorderₓ α] {a b : α} (h : a < b) : ¬b ≤ a :=
  (le_not_le_of_ltₓ h).right

alias not_le_of_lt ← LT.lt.not_le

theorem not_lt_of_le [Preorderₓ α] {a b : α} (h : a ≤ b) : ¬b < a := fun hba => hba.not_le h

alias not_lt_of_le ← LE.le.not_lt

theorem ne_of_not_le [Preorderₓ α] {a b : α} (h : ¬a ≤ b) : a ≠ b := fun hab => h (le_of_eqₓ hab)

-- See Note [decidable namespace]
protected theorem Decidable.le_iff_eq_or_lt [PartialOrderₓ α] [@DecidableRel α (· ≤ ·)] {a b : α} :
    a ≤ b ↔ a = b ∨ a < b :=
  Decidable.le_iff_lt_or_eqₓ.trans Or.comm

theorem le_iff_eq_or_lt [PartialOrderₓ α] {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
  le_iff_lt_or_eqₓ.trans Or.comm

theorem lt_iff_le_and_ne [PartialOrderₓ α] {a b : α} : a < b ↔ a ≤ b ∧ a ≠ b :=
  ⟨fun h => ⟨le_of_ltₓ h, ne_of_ltₓ h⟩, fun ⟨h1, h2⟩ => h1.lt_of_ne h2⟩

-- See Note [decidable namespace]
protected theorem Decidable.eq_iff_le_not_lt [PartialOrderₓ α] [@DecidableRel α (· ≤ ·)] {a b : α} :
    a = b ↔ a ≤ b ∧ ¬a < b :=
  ⟨fun h => ⟨h.le, h ▸ lt_irreflₓ _⟩, fun ⟨h₁, h₂⟩ =>
    h₁.antisymm <| Decidable.by_contradiction fun h₃ => h₂ (h₁.lt_of_not_le h₃)⟩

theorem eq_iff_le_not_lt [PartialOrderₓ α] {a b : α} : a = b ↔ a ≤ b ∧ ¬a < b :=
  have := Classical.dec
  Decidable.eq_iff_le_not_lt

theorem eq_or_lt_of_le [PartialOrderₓ α] {a b : α} (h : a ≤ b) : a = b ∨ a < b :=
  h.lt_or_eq.symm

theorem eq_or_gt_of_le [PartialOrderₓ α] {a b : α} (h : a ≤ b) : b = a ∨ a < b :=
  h.lt_or_eq.symm.imp Eq.symm id

alias Decidable.eq_or_lt_of_leₓ ← LE.le.eq_or_lt_dec

alias eq_or_lt_of_le ← LE.le.eq_or_lt

alias eq_or_gt_of_le ← LE.le.eq_or_gt

attribute [nolint decidable_classical] LE.le.eq_or_lt_dec

theorem eq_of_le_of_not_lt [PartialOrderₓ α] {a b : α} (hab : a ≤ b) (hba : ¬a < b) : a = b :=
  hab.eq_or_lt.resolve_right hba

theorem eq_of_ge_of_not_gt [PartialOrderₓ α] {a b : α} (hab : a ≤ b) (hba : ¬a < b) : b = a :=
  (hab.eq_or_lt.resolve_right hba).symm

alias eq_of_le_of_not_lt ← LE.le.eq_of_not_lt

alias eq_of_ge_of_not_gt ← LE.le.eq_of_not_gt

theorem Ne.le_iff_lt [PartialOrderₓ α] {a b : α} (h : a ≠ b) : a ≤ b ↔ a < b :=
  ⟨fun h' => lt_of_le_of_neₓ h' h, fun h => h.le⟩

theorem Ne.not_le_or_not_le [PartialOrderₓ α] {a b : α} (h : a ≠ b) : ¬a ≤ b ∨ ¬b ≤ a :=
  not_and_distrib.1 <| le_antisymm_iffₓ.Not.1 h

-- See Note [decidable namespace]
protected theorem Decidable.ne_iff_lt_iff_le [PartialOrderₓ α] [DecidableEq α] {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
  ⟨fun h => Decidable.byCases le_of_eqₓ (le_of_ltₓ ∘ h.mp), fun h => ⟨lt_of_le_of_neₓ h, ne_of_ltₓ⟩⟩

@[simp]
theorem ne_iff_lt_iff_le [PartialOrderₓ α] {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
  have := Classical.dec
  Decidable.ne_iff_lt_iff_le

theorem lt_of_not_le [LinearOrderₓ α] {a b : α} (h : ¬b ≤ a) : a < b :=
  ((le_totalₓ _ _).resolve_right h).lt_of_not_le h

theorem lt_iff_not_le [LinearOrderₓ α] {x y : α} : x < y ↔ ¬y ≤ x :=
  ⟨not_le_of_lt, lt_of_not_le⟩

theorem Ne.lt_or_lt [LinearOrderₓ α] {x y : α} (h : x ≠ y) : x < y ∨ y < x :=
  lt_or_gt_of_neₓ h

/-- A version of `ne_iff_lt_or_gt` with LHS and RHS reversed. -/
@[simp]
theorem lt_or_lt_iff_ne [LinearOrderₓ α] {x y : α} : x < y ∨ y < x ↔ x ≠ y :=
  ne_iff_lt_or_gtₓ.symm

theorem not_lt_iff_eq_or_lt [LinearOrderₓ α] {a b : α} : ¬a < b ↔ a = b ∨ b < a :=
  not_ltₓ.trans <| Decidable.le_iff_eq_or_lt.trans <| or_congr eq_comm Iff.rfl

theorem exists_ge_of_linear [LinearOrderₓ α] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  match le_totalₓ a b with
  | Or.inl h => ⟨_, h, le_rfl⟩
  | Or.inr h => ⟨_, le_rfl, h⟩

theorem lt_imp_lt_of_le_imp_le {β} [LinearOrderₓ α] [Preorderₓ β] {a b : α} {c d : β} (H : a ≤ b → c ≤ d) (h : d < c) :
    b < a :=
  lt_of_not_le fun h' => (H h').not_lt h

theorem le_imp_le_iff_lt_imp_lt {β} [LinearOrderₓ α] [LinearOrderₓ β] {a b : α} {c d : β} :
    a ≤ b → c ≤ d ↔ d < c → b < a :=
  ⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_ltₓ⟩

theorem lt_iff_lt_of_le_iff_le' {β} [Preorderₓ α] [Preorderₓ β] {a b : α} {c d : β} (H : a ≤ b ↔ c ≤ d)
    (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
  lt_iff_le_not_leₓ.trans <| (and_congr H' (not_congr H)).trans lt_iff_le_not_leₓ.symm

theorem lt_iff_lt_of_le_iff_le {β} [LinearOrderₓ α] [LinearOrderₓ β] {a b : α} {c d : β} (H : a ≤ b ↔ c ≤ d) :
    b < a ↔ d < c :=
  not_leₓ.symm.trans <| (not_congr H).trans <| not_leₓ

theorem le_iff_le_iff_lt_iff_lt {β} [LinearOrderₓ α] [LinearOrderₓ β] {a b : α} {c d : β} :
    (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
  ⟨lt_iff_lt_of_le_iff_le, fun H => not_ltₓ.symm.trans <| (not_congr H).trans <| not_ltₓ⟩

theorem eq_of_forall_le_iff [PartialOrderₓ α] {a b : α} (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
  ((H _).1 le_rfl).antisymm ((H _).2 le_rfl)

theorem le_of_forall_le [Preorderₓ α] {a b : α} (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b :=
  H _ le_rfl

theorem le_of_forall_le' [Preorderₓ α] {a b : α} (H : ∀ c, a ≤ c → b ≤ c) : b ≤ a :=
  H _ le_rfl

theorem le_of_forall_lt [LinearOrderₓ α] {a b : α} (H : ∀ c, c < a → c < b) : a ≤ b :=
  le_of_not_ltₓ fun h => lt_irreflₓ _ (H _ h)

theorem forall_lt_iff_le [LinearOrderₓ α] {a b : α} : (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
  ⟨le_of_forall_lt, fun h c hca => lt_of_lt_of_leₓ hca h⟩

theorem le_of_forall_lt' [LinearOrderₓ α] {a b : α} (H : ∀ c, a < c → b < c) : b ≤ a :=
  le_of_not_ltₓ fun h => lt_irreflₓ _ (H _ h)

theorem forall_lt_iff_le' [LinearOrderₓ α] {a b : α} : (∀ ⦃c⦄, a < c → b < c) ↔ b ≤ a :=
  ⟨le_of_forall_lt', fun h c hac => lt_of_le_of_ltₓ h hac⟩

theorem eq_of_forall_ge_iff [PartialOrderₓ α] {a b : α} (H : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
  ((H _).2 le_rfl).antisymm ((H _).1 le_rfl)

/-- A symmetric relation implies two values are equal, when it implies they're less-equal.  -/
theorem rel_imp_eq_of_rel_imp_le [PartialOrderₓ β] (r : α → α → Prop) [IsSymm α r] {f : α → β}
    (h : ∀ a b, r a b → f a ≤ f b) {a b : α} : r a b → f a = f b := fun hab =>
  le_antisymmₓ (h a b hab) (h b a <| symm hab)

/-- monotonicity of `≤` with respect to `→` -/
theorem le_implies_le_of_le_of_le {a b c d : α} [Preorderₓ α] (hca : c ≤ a) (hbd : b ≤ d) : a ≤ b → c ≤ d := fun hab =>
  (hca.trans hab).trans hbd

@[ext]
theorem Preorderₓ.to_has_le_injective {α : Type _} : Function.Injective (@Preorderₓ.toHasLe α) := fun A B h => by
  cases A
  cases B
  injection h with h_le
  have : A_lt = B_lt := by
    funext a b
    dsimp' [← (· ≤ ·)]  at A_lt_iff_le_not_le B_lt_iff_le_not_le h_le
    simp [← A_lt_iff_le_not_le, ← B_lt_iff_le_not_le, ← h_le]
  congr

@[ext]
theorem PartialOrderₓ.to_preorder_injective {α : Type _} : Function.Injective (@PartialOrderₓ.toPreorder α) :=
  fun A B h => by
  cases A
  cases B
  injection h
  congr

@[ext]
theorem LinearOrderₓ.to_partial_order_injective {α : Type _} : Function.Injective (@LinearOrderₓ.toPartialOrder α) := by
  intro A B h
  cases A
  cases B
  injection h
  obtain rfl : A_le = B_le := ‹_›
  obtain rfl : A_lt = B_lt := ‹_›
  obtain rfl : A_decidable_le = B_decidable_le := Subsingleton.elimₓ _ _
  obtain rfl : A_max = B_max := A_max_def.trans B_max_def.symm
  obtain rfl : A_min = B_min := A_min_def.trans B_min_def.symm
  congr

theorem Preorderₓ.ext {α} {A B : Preorderₓ α}
    (H :
      ∀ x y : α,
        (have := A
          x ≤ y) ↔
          x ≤ y) :
    A = B := by
  ext x y
  exact H x y

theorem PartialOrderₓ.ext {α} {A B : PartialOrderₓ α}
    (H :
      ∀ x y : α,
        (have := A
          x ≤ y) ↔
          x ≤ y) :
    A = B := by
  ext x y
  exact H x y

theorem LinearOrderₓ.ext {α} {A B : LinearOrderₓ α}
    (H :
      ∀ x y : α,
        (have := A
          x ≤ y) ↔
          x ≤ y) :
    A = B := by
  ext x y
  exact H x y

/-- Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `rel_embedding` (assuming `f`
is injective). -/
@[simp]
def Order.Preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) : Prop :=
  s (f x) (f y)

-- mathport name: «expr ⁻¹'o »
infixl:80 " ⁻¹'o " => Order.Preimage

/-- The preimage of a decidable order is decidable. -/
instance Order.Preimage.decidable {α β} (f : α → β) (s : β → β → Prop) [H : DecidableRel s] : DecidableRel (f ⁻¹'o s) :=
  fun x y => H _ _

/-! ### Order dual -/


/-- Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>`. `αᵒᵈ` is
notation for `order_dual α`. -/
def OrderDual (α : Type _) : Type _ :=
  α

-- mathport name: «expr ᵒᵈ»
notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

instance (α : Type _) [h : Nonempty α] : Nonempty αᵒᵈ :=
  h

instance (α : Type _) [h : Subsingleton α] : Subsingleton αᵒᵈ :=
  h

instance (α : Type _) [LE α] : LE αᵒᵈ :=
  ⟨fun x y : α => y ≤ x⟩

instance (α : Type _) [LT α] : LT αᵒᵈ :=
  ⟨fun x y : α => y < x⟩

instance (α : Type _) [Zero α] : Zero αᵒᵈ :=
  ⟨(0 : α)⟩

instance (α : Type _) [Preorderₓ α] : Preorderₓ αᵒᵈ :=
  { OrderDual.hasLe α, OrderDual.hasLt α with le_refl := le_reflₓ, le_trans := fun a b c hab hbc => hbc.trans hab,
    lt_iff_le_not_le := fun _ _ => lt_iff_le_not_leₓ }

instance (α : Type _) [PartialOrderₓ α] : PartialOrderₓ αᵒᵈ :=
  { OrderDual.preorder α with le_antisymm := fun a b hab hba => @le_antisymmₓ α _ a b hba hab }

instance (α : Type _) [LinearOrderₓ α] : LinearOrderₓ αᵒᵈ :=
  { OrderDual.partialOrder α with le_total := fun a b : α => le_totalₓ b a,
    decidableLe := (inferInstance : DecidableRel fun a b : α => b ≤ a),
    decidableLt := (inferInstance : DecidableRel fun a b : α => b < a), min := @max α _, max := @min α _,
    min_def := @LinearOrderₓ.max_def α _, max_def := @LinearOrderₓ.min_def α _ }

instance : ∀ [Inhabited α], Inhabited αᵒᵈ :=
  id

theorem preorder.dual_dual (α : Type _) [H : Preorderₓ α] : OrderDual.preorder αᵒᵈ = H :=
  Preorderₓ.ext fun _ _ => Iff.rfl

theorem partialOrder.dual_dual (α : Type _) [H : PartialOrderₓ α] : OrderDual.partialOrder αᵒᵈ = H :=
  PartialOrderₓ.ext fun _ _ => Iff.rfl

theorem linearOrder.dual_dual (α : Type _) [H : LinearOrderₓ α] : OrderDual.linearOrder αᵒᵈ = H :=
  LinearOrderₓ.ext fun _ _ => Iff.rfl

end OrderDual

/-! ### Order instances on the function space -/


instance Pi.hasLe {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] : LE (∀ i, α i) where le := fun x y => ∀ i, x i ≤ y i

theorem Pi.le_def {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] {x y : ∀ i, α i} : x ≤ y ↔ ∀ i, x i ≤ y i :=
  Iff.rfl

instance Pi.preorder {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] : Preorderₓ (∀ i, α i) :=
  { Pi.hasLe with le_refl := fun a i => le_reflₓ (a i), le_trans := fun a b c h₁ h₂ i => le_transₓ (h₁ i) (h₂ i) }

theorem Pi.lt_def {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] {x y : ∀ i, α i} :
    x < y ↔ x ≤ y ∧ ∃ i, x i < y i := by
  simp (config := { contextual := true })[← lt_iff_le_not_leₓ, ← Pi.le_def]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
theorem le_update_iff {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] [DecidableEq ι] {x y : ∀ i, α i} {i : ι}
    {a : α i} : x ≤ Function.update y i a ↔ x i ≤ a ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z => x j ≤ z

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
theorem update_le_iff {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] [DecidableEq ι] {x y : ∀ i, α i} {i : ι}
    {a : α i} : Function.update x i a ≤ y ↔ a ≤ y i ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z => z ≤ y j

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
theorem update_le_update_iff {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] [DecidableEq ι] {x y : ∀ i, α i}
    {i : ι} {a b : α i} : Function.update x i a ≤ Function.update y i b ↔ a ≤ b ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j := by
  simp (config := { contextual := true })[← update_le_iff]

instance Pi.partialOrder {ι : Type u} {α : ι → Type v} [∀ i, PartialOrderₓ (α i)] : PartialOrderₓ (∀ i, α i) :=
  { Pi.preorder with le_antisymm := fun f g h1 h2 => funext fun b => (h1 b).antisymm (h2 b) }

/-! ### `min`/`max` recursors -/


section MinMaxRec

variable [LinearOrderₓ α] {p : α → Prop} {x y : α}

theorem min_rec (hx : x ≤ y → p x) (hy : y ≤ x → p y) : p (min x y) :=
  (le_totalₓ x y).rec (fun h => (min_eq_leftₓ h).symm.subst (hx h)) fun h => (min_eq_rightₓ h).symm.subst (hy h)

theorem max_rec (hx : y ≤ x → p x) (hy : x ≤ y → p y) : p (max x y) :=
  @min_rec αᵒᵈ _ _ _ _ hx hy

theorem min_rec' (p : α → Prop) (hx : p x) (hy : p y) : p (min x y) :=
  min_rec (fun _ => hx) fun _ => hy

theorem max_rec' (p : α → Prop) (hx : p x) (hy : p y) : p (max x y) :=
  max_rec (fun _ => hx) fun _ => hy

end MinMaxRec

/-! ### `has_sup` and `has_inf` -/


-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Typeclass for the `⊔` (`\lub`) notation -/
@[«./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg»]
class HasSup (α : Type u) where
  sup : α → α → α

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Typeclass for the `⊓` (`\glb`) notation -/
@[«./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg»]
class HasInf (α : Type u) where
  inf : α → α → α

-- mathport name: «expr ⊔ »
infixl:68 "⊔" => HasSup.sup

-- mathport name: «expr ⊓ »
infixl:69 "⊓" => HasInf.inf

/-! ### Lifts of order instances -/


/-- Transfer a `preorder` on `β` to a `preorder` on `α` using a function `f : α → β`.
See note [reducible non-instances]. -/
@[reducible]
def Preorderₓ.lift {α β} [Preorderₓ β] (f : α → β) : Preorderₓ α where
  le := fun x y => f x ≤ f y
  le_refl := fun a => le_rfl
  le_trans := fun a b c => le_transₓ
  lt := fun x y => f x < f y
  lt_iff_le_not_le := fun a b => lt_iff_le_not_leₓ

/-- Transfer a `partial_order` on `β` to a `partial_order` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible]
def PartialOrderₓ.lift {α β} [PartialOrderₓ β] (f : α → β) (inj : Injective f) : PartialOrderₓ α :=
  { Preorderₓ.lift f with le_antisymm := fun a b h₁ h₂ => inj (h₁.antisymm h₂) }

/-- Transfer a `linear_order` on `β` to a `linear_order` on `α` using an injective
function `f : α → β`. This version takes `[has_sup α]` and `[has_inf α]` as arguments, then uses
them for `max` and `min` fields. See `linear_order.lift'` for a version that autogenerates `min` and
`max` fields. See note [reducible non-instances]. -/
@[reducible]
def LinearOrderₓ.lift {α β} [LinearOrderₓ β] [HasSup α] [HasInf α] (f : α → β) (inj : Injective f)
    (hsup : ∀ x y, f (x⊔y) = max (f x) (f y)) (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) : LinearOrderₓ α :=
  { PartialOrderₓ.lift f inj with le_total := fun x y => le_totalₓ (f x) (f y),
    decidableLe := fun x y => (inferInstance : Decidable (f x ≤ f y)),
    decidableLt := fun x y => (inferInstance : Decidable (f x < f y)),
    DecidableEq := fun x y => decidableOfIff (f x = f y) inj.eq_iff, min := (·⊓·), max := (·⊔·),
    min_def := by
      ext x y
      apply inj
      rw [hinf, min_def, minDefault, apply_ite f]
      rfl,
    max_def := by
      ext x y
      apply inj
      rw [hsup, max_def, maxDefault, apply_ite f]
      rfl }

/-- Transfer a `linear_order` on `β` to a `linear_order` on `α` using an injective
function `f : α → β`. This version autogenerates `min` and `max` fields. See `linear_order.lift`
for a version that takes `[has_sup α]` and `[has_inf α]`, then uses them as `max` and `min`.
See note [reducible non-instances]. -/
@[reducible]
def LinearOrderₓ.lift' {α β} [LinearOrderₓ β] (f : α → β) (inj : Injective f) : LinearOrderₓ α :=
  @LinearOrderₓ.lift α β _ ⟨fun x y => if f y ≤ f x then x else y⟩ ⟨fun x y => if f x ≤ f y then x else y⟩ f inj
    (fun x y => (apply_ite f _ _ _).trans (max_def _ _).symm) fun x y => (apply_ite f _ _ _).trans (min_def _ _).symm

/-! ### Subtype of an order -/


namespace Subtype

instance [LE α] {p : α → Prop} : LE (Subtype p) :=
  ⟨fun x y => (x : α) ≤ y⟩

instance [LT α] {p : α → Prop} : LT (Subtype p) :=
  ⟨fun x y => (x : α) < y⟩

@[simp]
theorem mk_le_mk [LE α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} : (⟨x, hx⟩ : Subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
  Iff.rfl

@[simp]
theorem mk_lt_mk [LT α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} : (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_le_coe [LE α] {p : α → Prop} {x y : Subtype p} : (x : α) ≤ y ↔ x ≤ y :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_lt_coe [LT α] {p : α → Prop} {x y : Subtype p} : (x : α) < y ↔ x < y :=
  Iff.rfl

instance [Preorderₓ α] (p : α → Prop) : Preorderₓ (Subtype p) :=
  Preorderₓ.lift (coe : Subtype p → α)

instance partialOrder [PartialOrderₓ α] (p : α → Prop) : PartialOrderₓ (Subtype p) :=
  PartialOrderₓ.lift coe Subtype.coe_injective

instance decidableLe [Preorderₓ α] [h : @DecidableRel α (· ≤ ·)] {p : α → Prop} : @DecidableRel (Subtype p) (· ≤ ·) :=
  fun a b => h a b

instance decidableLt [Preorderₓ α] [h : @DecidableRel α (· < ·)] {p : α → Prop} : @DecidableRel (Subtype p) (· < ·) :=
  fun a b => h a b

/-- A subtype of a linear order is a linear order. We explicitly give the proofs of decidable
equality and decidable order in order to ensure the decidability instances are all definitionally
equal. -/
instance [LinearOrderₓ α] (p : α → Prop) : LinearOrderₓ (Subtype p) :=
  @LinearOrderₓ.lift (Subtype p) _ _ ⟨fun x y => ⟨max x y, max_rec' _ x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' _ x.2 y.2⟩⟩ coe Subtype.coe_injective (fun _ _ => rfl) fun _ _ => rfl

end Subtype

/-!
### Pointwise order on `α × β`

The lexicographic order is defined in `data.prod.lex`, and the instances are available via the
type synonym `α ×ₗ β = α × β`.
-/


namespace Prod

instance (α : Type u) (β : Type v) [LE α] [LE β] : LE (α × β) :=
  ⟨fun p q => p.1 ≤ q.1 ∧ p.2 ≤ q.2⟩

theorem le_def [LE α] [LE β] {x y : α × β} : x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 :=
  Iff.rfl

@[simp]
theorem mk_le_mk [LE α] [LE β] {x₁ x₂ : α} {y₁ y₂ : β} : (x₁, y₁) ≤ (x₂, y₂) ↔ x₁ ≤ x₂ ∧ y₁ ≤ y₂ :=
  Iff.rfl

@[simp]
theorem swap_le_swap [LE α] [LE β] {x y : α × β} : x.swap ≤ y.swap ↔ x ≤ y :=
  and_comm _ _

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

instance (α : Type u) (β : Type v) [Preorderₓ α] [Preorderₓ β] : Preorderₓ (α × β) :=
  { Prod.hasLe α β with le_refl := fun ⟨a, b⟩ => ⟨le_reflₓ a, le_reflₓ b⟩,
    le_trans := fun ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ => ⟨le_transₓ hac hce, le_transₓ hbd hdf⟩ }

@[simp]
theorem swap_lt_swap : x.swap < y.swap ↔ x < y :=
  and_congr swap_le_swap (not_congr swap_le_swap)

theorem mk_le_mk_iff_left : (a₁, b) ≤ (a₂, b) ↔ a₁ ≤ a₂ :=
  and_iff_left le_rfl

theorem mk_le_mk_iff_right : (a, b₁) ≤ (a, b₂) ↔ b₁ ≤ b₂ :=
  and_iff_right le_rfl

theorem mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

theorem mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

theorem lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 ≤ y.2 ∨ x.1 ≤ y.1 ∧ x.2 < y.2 := by
  refine' ⟨fun h => _, _⟩
  · by_cases' h₁ : y.1 ≤ x.1
    · exact Or.inr ⟨h.1.1, h.1.2.lt_of_not_le fun h₂ => h.2 ⟨h₁, h₂⟩⟩
      
    · exact Or.inl ⟨h.1.1.lt_of_not_le h₁, h.1.2⟩
      
    
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨h₁.le, h₂⟩, fun h => h₁.not_le h.1⟩
      
    · exact ⟨⟨h₁, h₂.le⟩, fun h => h₂.not_le h.2⟩
      
    

@[simp]
theorem mk_lt_mk : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ ≤ b₂ ∨ a₁ ≤ a₂ ∧ b₁ < b₂ :=
  lt_iff

end Preorderₓ

/-- The pointwise partial order on a product.
    (The lexicographic ordering is defined in order/lexicographic.lean, and the instances are
    available via the type synonym `α ×ₗ β = α × β`.) -/
instance (α : Type u) (β : Type v) [PartialOrderₓ α] [PartialOrderₓ β] : PartialOrderₓ (α × β) :=
  { Prod.preorder α β with
    le_antisymm := fun ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ ⟨hca, hdb⟩ => Prod.extₓ (hac.antisymm hca) (hbd.antisymm hdb) }

end Prod

/-! ### Additional order classes -/


/-- An order is dense if there is an element between any pair of distinct elements. -/
class DenselyOrdered (α : Type u) [LT α] : Prop where
  dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂

theorem exists_between [LT α] [DenselyOrdered α] : ∀ {a₁ a₂ : α}, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
  DenselyOrdered.dense

instance OrderDual.densely_ordered (α : Type u) [LT α] [DenselyOrdered α] : DenselyOrdered αᵒᵈ :=
  ⟨fun a₁ a₂ ha => (@exists_between α _ _ _ _ ha).imp fun a => And.symm⟩

theorem le_of_forall_le_of_dense [LinearOrderₓ α] [DenselyOrdered α] {a₁ a₂ : α} (h : ∀ a, a₂ < a → a₁ ≤ a) : a₁ ≤ a₂ :=
  le_of_not_gtₓ fun ha =>
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irreflₓ a <| lt_of_lt_of_leₓ ‹a < a₁› (h _ ‹a₂ < a›)

theorem eq_of_le_of_forall_le_of_dense [LinearOrderₓ α] [DenselyOrdered α] {a₁ a₂ : α} (h₁ : a₂ ≤ a₁)
    (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
  le_antisymmₓ (le_of_forall_le_of_dense h₂) h₁

theorem le_of_forall_ge_of_dense [LinearOrderₓ α] [DenselyOrdered α] {a₁ a₂ : α} (h : ∀, ∀ a₃ < a₁, ∀, a₃ ≤ a₂) :
    a₁ ≤ a₂ :=
  le_of_not_gtₓ fun ha =>
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irreflₓ a <| lt_of_le_of_ltₓ (h _ ‹a < a₁›) ‹a₂ < a›

theorem eq_of_le_of_forall_ge_of_dense [LinearOrderₓ α] [DenselyOrdered α] {a₁ a₂ : α} (h₁ : a₂ ≤ a₁)
    (h₂ : ∀, ∀ a₃ < a₁, ∀, a₃ ≤ a₂) : a₁ = a₂ :=
  (le_of_forall_ge_of_dense h₂).antisymm h₁

theorem dense_or_discrete [LinearOrderₓ α] (a₁ a₂ : α) :
    (∃ a, a₁ < a ∧ a < a₂) ∨ (∀ a, a₁ < a → a₂ ≤ a) ∧ ∀, ∀ a < a₂, ∀, a ≤ a₁ :=
  or_iff_not_imp_left.2 fun h =>
    ⟨fun a ha₁ => le_of_not_gtₓ fun ha₂ => h ⟨a, ha₁, ha₂⟩, fun a ha₂ => le_of_not_gtₓ fun ha₁ => h ⟨a, ha₁, ha₂⟩⟩

variable {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Linear order from a total partial order -/


/-- Type synonym to create an instance of `linear_order` from a `partial_order` and
`is_total α (≤)` -/
def AsLinearOrder (α : Type u) :=
  α

instance {α} [Inhabited α] : Inhabited (AsLinearOrder α) :=
  ⟨(default : α)⟩

noncomputable instance AsLinearOrder.linearOrder {α} [PartialOrderₓ α] [IsTotal α (· ≤ ·)] :
    LinearOrderₓ (AsLinearOrder α) :=
  { (_ : PartialOrderₓ α) with le_total := @total_of α (· ≤ ·) _, decidableLe := Classical.decRel _ }

