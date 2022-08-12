/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Robert Y. Lewis
-/
import Mathbin.Algebra.Group.Defs

/-!
# Eckmann-Hilton argument

The Eckmann-Hilton argument says that if a type carries two monoid structures that distribute
over one another, then they are equal, and in addition commutative.
The main application lies in proving that higher homotopy groups (`πₙ` for `n ≥ 2`) are commutative.

## Main declarations

* `eckmann_hilton.comm_monoid`: If a type carries a unital magma structure that distributes
  over a unital binary operation, then the magma is a commutative monoid.
* `eckmann_hilton.comm_group`: If a type carries a group structure that distributes
  over a unital binary operation, then the group is commutative.

-/


universe u

namespace EckmannHilton

variable {X : Type u}

-- mathport name: «expr < > »
local notation a "<" m ">" b => m a b

/-- `is_unital m e` expresses that `e : X` is a left and right unit
for the binary operation `m : X → X → X`. -/
structure IsUnital (m : X → X → X) (e : X) extends IsLeftId _ m e, IsRightId _ m e : Prop

@[to_additive EckmannHilton.AddZeroClass.is_unital]
theorem MulOneClass.is_unital [G : MulOneClassₓ X] : IsUnital (· * ·) (1 : X) :=
  IsUnital.mk
    (by
      infer_instance)
    (by
      infer_instance)

variable {m₁ m₂ : X → X → X} {e₁ e₂ : X}

variable (h₁ : IsUnital m₁ e₁) (h₂ : IsUnital m₂ e₂)

variable (distrib : ∀ a b c d, ((a<m₂>b)<m₁>c<m₂>d) = (a<m₁>c)<m₂>b<m₁>d)

include h₁ h₂ distrib

/-- If a type carries two unital binary operations that distribute over each other,
then they have the same unit elements.

In fact, the two operations are the same, and give a commutative monoid structure,
see `eckmann_hilton.comm_monoid`. -/
theorem one : e₁ = e₂ := by
  simpa only [← h₁.left_id, ← h₁.right_id, ← h₂.left_id, ← h₂.right_id] using distrib e₂ e₁ e₁ e₂

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are equal.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul : m₁ = m₂ := by
  funext a b
  calc m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) := by
      simp only [← one h₁ h₂ distrib, ← h₁.left_id, ← h₁.right_id, ← h₂.left_id, ← h₂.right_id]_ = m₂ a b := by
      simp only [← distrib, ← h₁.left_id, ← h₁.right_id, ← h₂.left_id, ← h₂.right_id]

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are commutative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul_comm : IsCommutative _ m₂ :=
  ⟨fun a b => by
    simpa [← mul h₁ h₂ distrib, ← h₂.left_id, ← h₂.right_id] using distrib e₂ a b e₂⟩

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are associative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul_assoc : IsAssociative _ m₂ :=
  ⟨fun a b c => by
    simpa [← mul h₁ h₂ distrib, ← h₂.left_id, ← h₂.right_id] using distrib a b e₂ c⟩

omit h₁ h₂ distrib

/-- If a type carries a unital magma structure that distributes over a unital binary
operations, then the magma structure is a commutative monoid. -/
@[to_additive
      "If a type carries a unital additive magma structure that distributes over a\nunital binary operations, then the additive magma structure is a commutative additive monoid."]
def commMonoid [h : MulOneClassₓ X] (distrib : ∀ a b c d, ((a * b)<m₁>c * d) = (a<m₁>c) * b<m₁>d) : CommMonoidₓ X :=
  { h with mul := (· * ·), one := 1, mul_comm := (mul_comm h₁ MulOneClass.is_unital distrib).comm,
    mul_assoc := (mul_assoc h₁ MulOneClass.is_unital distrib).assoc }

/-- If a type carries a group structure that distributes over a unital binary operation,
then the group is commutative. -/
@[to_additive
      "If a type carries an additive group structure that distributes\nover a unital binary operation, then the additive group is commutative."]
def commGroup [G : Groupₓ X] (distrib : ∀ a b c d, ((a * b)<m₁>c * d) = (a<m₁>c) * b<m₁>d) : CommGroupₓ X :=
  { EckmannHilton.commMonoid h₁ distrib, G with }

end EckmannHilton

