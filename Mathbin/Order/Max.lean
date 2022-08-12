/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov, Yaël Dillies
-/
import Mathbin.Order.Synonym

/-!
# Minimal/maximal and bottom/top elements

This file defines predicates for elements to be minimal/maximal or bottom/top and typeclasses
saying that there are no such elements.

## Predicates

* `is_bot`: An element is *bottom* if all elements are greater than it.
* `is_top`: An element is *top* if all elements are less than it.
* `is_min`: An element is *minimal* if no element is strictly less than it.
* `is_max`: An element is *maximal* if no element is strictly greater than it.

See also `is_bot_iff_is_min` and `is_top_iff_is_max` for the equivalences in a (co)directed order.

## Typeclasses

* `no_bot_order`: An order without bottom elements.
* `no_top_order`: An order without top elements.
* `no_min_order`: An order without minimal elements.
* `no_max_order`: An order without maximal elements.
-/


open OrderDual

variable {α β : Type _}

/-- Order without bottom elements. -/
class NoBotOrder (α : Type _) [LE α] : Prop where
  exists_not_ge (a : α) : ∃ b, ¬a ≤ b

/-- Order without top elements. -/
class NoTopOrder (α : Type _) [LE α] : Prop where
  exists_not_le (a : α) : ∃ b, ¬b ≤ a

/-- Order without minimal elements. Sometimes called coinitial or dense. -/
class NoMinOrder (α : Type _) [LT α] : Prop where
  exists_lt (a : α) : ∃ b, b < a

/-- Order without maximal elements. Sometimes called cofinal. -/
class NoMaxOrder (α : Type _) [LT α] : Prop where
  exists_gt (a : α) : ∃ b, a < b

export NoBotOrder (exists_not_ge)

export NoTopOrder (exists_not_le)

export NoMinOrder (exists_lt)

export NoMaxOrder (exists_gt)

instance nonempty_lt [LT α] [NoMinOrder α] (a : α) : Nonempty { x // x < a } :=
  nonempty_subtype.2 (exists_lt a)

instance nonempty_gt [LT α] [NoMaxOrder α] (a : α) : Nonempty { x // a < x } :=
  nonempty_subtype.2 (exists_gt a)

instance OrderDual.no_bot_order (α : Type _) [LE α] [NoTopOrder α] : NoBotOrder αᵒᵈ :=
  ⟨fun a => @exists_not_le α _ _ a⟩

instance OrderDual.no_top_order (α : Type _) [LE α] [NoBotOrder α] : NoTopOrder αᵒᵈ :=
  ⟨fun a => @exists_not_ge α _ _ a⟩

instance OrderDual.no_min_order (α : Type _) [LT α] [NoMaxOrder α] : NoMinOrder αᵒᵈ :=
  ⟨fun a => @exists_gt α _ _ a⟩

instance OrderDual.no_max_order (α : Type _) [LT α] [NoMinOrder α] : NoMaxOrder αᵒᵈ :=
  ⟨fun a => @exists_lt α _ _ a⟩

-- See note [lower instance priority]
instance (priority := 100) NoMinOrder.to_no_bot_order (α : Type _) [Preorderₓ α] [NoMinOrder α] : NoBotOrder α :=
  ⟨fun a => (exists_lt a).imp fun _ => not_le_of_lt⟩

-- See note [lower instance priority]
instance (priority := 100) NoMaxOrder.to_no_top_order (α : Type _) [Preorderₓ α] [NoMaxOrder α] : NoTopOrder α :=
  ⟨fun a => (exists_gt a).imp fun _ => not_le_of_lt⟩

section LE

variable [LE α] {a b : α}

/-- `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `order_bot`, except that a preorder may have
several bottom elements. When `α` is linear, this is useful to make a case disjunction on
`no_min_order α` within a proof. -/
def IsBot (a : α) : Prop :=
  ∀ b, a ≤ b

/-- `a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `order_bot`, except that a preorder may have
several top elements. When `α` is linear, this is useful to make a case disjunction on
`no_max_order α` within a proof. -/
def IsTop (a : α) : Prop :=
  ∀ b, b ≤ a

/-- `a` is a minimal element of `α` if no element is strictly less than it. We spell it without `<`
to avoid having to convert between `≤` and `<`. Instead, `is_min_iff_forall_not_lt` does the
conversion. -/
def IsMin (a : α) : Prop :=
  ∀ ⦃b⦄, b ≤ a → a ≤ b

/-- `a` is a maximal element of `α` if no element is strictly greater than it. We spell it without
`<` to avoid having to convert between `≤` and `<`. Instead, `is_max_iff_forall_not_lt` does the
conversion. -/
def IsMax (a : α) : Prop :=
  ∀ ⦃b⦄, a ≤ b → b ≤ a

@[simp]
theorem not_is_bot [NoBotOrder α] (a : α) : ¬IsBot a := fun h =>
  let ⟨b, hb⟩ := exists_not_ge a
  hb <| h _

@[simp]
theorem not_is_top [NoTopOrder α] (a : α) : ¬IsTop a := fun h =>
  let ⟨b, hb⟩ := exists_not_le a
  hb <| h _

protected theorem IsBot.is_min (h : IsBot a) : IsMin a := fun b _ => h b

protected theorem IsTop.is_max (h : IsTop a) : IsMax a := fun b _ => h b

@[simp]
theorem is_bot_to_dual_iff : IsBot (toDual a) ↔ IsTop a :=
  Iff.rfl

@[simp]
theorem is_top_to_dual_iff : IsTop (toDual a) ↔ IsBot a :=
  Iff.rfl

@[simp]
theorem is_min_to_dual_iff : IsMin (toDual a) ↔ IsMax a :=
  Iff.rfl

@[simp]
theorem is_max_to_dual_iff : IsMax (toDual a) ↔ IsMin a :=
  Iff.rfl

@[simp]
theorem is_bot_of_dual_iff {a : αᵒᵈ} : IsBot (ofDual a) ↔ IsTop a :=
  Iff.rfl

@[simp]
theorem is_top_of_dual_iff {a : αᵒᵈ} : IsTop (ofDual a) ↔ IsBot a :=
  Iff.rfl

@[simp]
theorem is_min_of_dual_iff {a : αᵒᵈ} : IsMin (ofDual a) ↔ IsMax a :=
  Iff.rfl

@[simp]
theorem is_max_of_dual_iff {a : αᵒᵈ} : IsMax (ofDual a) ↔ IsMin a :=
  Iff.rfl

alias is_bot_to_dual_iff ↔ _ IsTop.to_dual

alias is_top_to_dual_iff ↔ _ IsBot.to_dual

alias is_min_to_dual_iff ↔ _ IsMax.to_dual

alias is_max_to_dual_iff ↔ _ IsMin.to_dual

alias is_bot_of_dual_iff ↔ _ IsTop.of_dual

alias is_top_of_dual_iff ↔ _ IsBot.of_dual

alias is_min_of_dual_iff ↔ _ IsMax.of_dual

alias is_max_of_dual_iff ↔ _ IsMin.of_dual

end LE

section Preorderₓ

variable [Preorderₓ α] {a b : α}

theorem IsBot.mono (ha : IsBot a) (h : b ≤ a) : IsBot b := fun c => h.trans <| ha _

theorem IsTop.mono (ha : IsTop a) (h : a ≤ b) : IsTop b := fun c => (ha _).trans h

theorem IsMin.mono (ha : IsMin a) (h : b ≤ a) : IsMin b := fun c hc => h.trans <| ha <| hc.trans h

theorem IsMax.mono (ha : IsMax a) (h : a ≤ b) : IsMax b := fun c hc => (ha <| h.trans hc).trans h

theorem IsMin.not_lt (h : IsMin a) : ¬b < a := fun hb => hb.not_le <| h hb.le

theorem IsMax.not_lt (h : IsMax a) : ¬a < b := fun hb => hb.not_le <| h hb.le

@[simp]
theorem not_is_min_of_lt (h : b < a) : ¬IsMin a := fun ha => ha.not_lt h

@[simp]
theorem not_is_max_of_lt (h : a < b) : ¬IsMax a := fun ha => ha.not_lt h

alias not_is_min_of_lt ← LT.lt.not_is_min

alias not_is_max_of_lt ← LT.lt.not_is_max

theorem is_min_iff_forall_not_lt : IsMin a ↔ ∀ b, ¬b < a :=
  ⟨fun h _ => h.not_lt, fun h b hba => of_not_not fun hab => h _ <| hba.lt_of_not_le hab⟩

theorem is_max_iff_forall_not_lt : IsMax a ↔ ∀ b, ¬a < b :=
  ⟨fun h _ => h.not_lt, fun h b hba => of_not_not fun hab => h _ <| hba.lt_of_not_le hab⟩

@[simp]
theorem not_is_min_iff : ¬IsMin a ↔ ∃ b, b < a := by
  simp_rw [lt_iff_le_not_leₓ, IsMin, not_forall, exists_prop]

@[simp]
theorem not_is_max_iff : ¬IsMax a ↔ ∃ b, a < b := by
  simp_rw [lt_iff_le_not_leₓ, IsMax, not_forall, exists_prop]

@[simp]
theorem not_is_min [NoMinOrder α] (a : α) : ¬IsMin a :=
  not_is_min_iff.2 <| exists_lt a

@[simp]
theorem not_is_max [NoMaxOrder α] (a : α) : ¬IsMax a :=
  not_is_max_iff.2 <| exists_gt a

namespace Subsingleton

variable [Subsingleton α]

protected theorem is_bot (a : α) : IsBot a := fun _ => (Subsingleton.elimₓ _ _).le

protected theorem is_top (a : α) : IsTop a := fun _ => (Subsingleton.elimₓ _ _).le

protected theorem is_min (a : α) : IsMin a :=
  (Subsingleton.is_bot _).IsMin

protected theorem is_max (a : α) : IsMax a :=
  (Subsingleton.is_top _).IsMax

end Subsingleton

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] {a b : α}

protected theorem IsMin.eq_of_le (ha : IsMin a) (h : b ≤ a) : b = a :=
  h.antisymm <| ha h

protected theorem IsMin.eq_of_ge (ha : IsMin a) (h : b ≤ a) : a = b :=
  h.antisymm' <| ha h

protected theorem IsMax.eq_of_le (ha : IsMax a) (h : a ≤ b) : a = b :=
  h.antisymm <| ha h

protected theorem IsMax.eq_of_ge (ha : IsMax a) (h : a ≤ b) : b = a :=
  h.antisymm' <| ha h

end PartialOrderₓ

section Prod

variable [Preorderₓ α] [Preorderₓ β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

theorem IsBot.prod_mk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b) := fun c => ⟨ha _, hb _⟩

theorem IsTop.prod_mk (ha : IsTop a) (hb : IsTop b) : IsTop (a, b) := fun c => ⟨ha _, hb _⟩

theorem IsMin.prod_mk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b) := fun c hc => ⟨ha hc.1, hb hc.2⟩

theorem IsMax.prod_mk (ha : IsMax a) (hb : IsMax b) : IsMax (a, b) := fun c hc => ⟨ha hc.1, hb hc.2⟩

theorem IsBot.fst (hx : IsBot x) : IsBot x.1 := fun c => (hx (c, x.2)).1

theorem IsBot.snd (hx : IsBot x) : IsBot x.2 := fun c => (hx (x.1, c)).2

theorem IsTop.fst (hx : IsTop x) : IsTop x.1 := fun c => (hx (c, x.2)).1

theorem IsTop.snd (hx : IsTop x) : IsTop x.2 := fun c => (hx (x.1, c)).2

theorem IsMin.fst (hx : IsMin x) : IsMin x.1 := fun c hc => (hx <| show (c, x.2) ≤ x from (and_iff_left le_rfl).2 hc).1

theorem IsMin.snd (hx : IsMin x) : IsMin x.2 := fun c hc => (hx <| show (x.1, c) ≤ x from (and_iff_right le_rfl).2 hc).2

theorem IsMax.fst (hx : IsMax x) : IsMax x.1 := fun c hc => (hx <| show x ≤ (c, x.2) from (and_iff_left le_rfl).2 hc).1

theorem IsMax.snd (hx : IsMax x) : IsMax x.2 := fun c hc => (hx <| show x ≤ (x.1, c) from (and_iff_right le_rfl).2 hc).2

theorem Prod.is_bot_iff : IsBot x ↔ IsBot x.1 ∧ IsBot x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩

theorem Prod.is_top_iff : IsTop x ↔ IsTop x.1 ∧ IsTop x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩

theorem Prod.is_min_iff : IsMin x ↔ IsMin x.1 ∧ IsMin x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩

theorem Prod.is_max_iff : IsMax x ↔ IsMax x.1 ∧ IsMax x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩

end Prod

