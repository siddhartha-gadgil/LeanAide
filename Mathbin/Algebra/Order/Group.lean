/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Abs
import Mathbin.Algebra.Order.Sub

/-!
# Ordered groups

This file develops the basics of ordered groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/


open Function

universe u

variable {α : Type u}

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
@[protect_proj, ancestor AddCommGroupₓ PartialOrderₓ]
class OrderedAddCommGroup (α : Type u) extends AddCommGroupₓ α, PartialOrderₓ α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

/-- An ordered commutative group is an commutative group
with a partial order in which multiplication is strictly monotone. -/
@[protect_proj, ancestor CommGroupₓ PartialOrderₓ]
class OrderedCommGroup (α : Type u) extends CommGroupₓ α, PartialOrderₓ α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b

attribute [to_additive] OrderedCommGroup

@[to_additive]
instance OrderedCommGroup.to_covariant_class_left_le (α : Type u) [OrderedCommGroup α] :
    CovariantClass α α (· * ·) (· ≤ ·) where elim := fun a b c bc => OrderedCommGroup.mul_le_mul_left b c bc a

/-- The units of an ordered commutative monoid form an ordered commutative group. -/
@[to_additive "The units of an ordered commutative additive monoid form an ordered commutative\nadditive group."]
instance Units.orderedCommGroup [OrderedCommMonoid α] : OrderedCommGroup αˣ :=
  { Units.partialOrder, Units.commGroup with
    mul_le_mul_left := fun a b h c => (mul_le_mul_left' (h : (a : α) ≤ b) _ : (c : α) * a ≤ c * b) }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCommGroup.toOrderedCancelCommMonoid (α : Type u) [s : OrderedCommGroup α] :
    OrderedCancelCommMonoid α :=
  { s with mul_left_cancel := fun a b c => (mul_right_injₓ a).mp,
    le_of_mul_le_mul_left := fun a b c => (mul_le_mul_iff_left a).mp }

@[to_additive]
instance (priority := 100) OrderedCommGroup.has_exists_mul_of_le (α : Type u) [OrderedCommGroup α] :
    HasExistsMulOfLe α :=
  ⟨fun a b hab => ⟨b * a⁻¹, (mul_inv_cancel_comm_assoc a b).symm⟩⟩

@[to_additive]
instance [h : Inv α] : Inv αᵒᵈ :=
  h

@[to_additive]
instance [h : Div α] : Div αᵒᵈ :=
  h

@[to_additive]
instance [h : HasInvolutiveInv α] : HasInvolutiveInv αᵒᵈ :=
  h

@[to_additive]
instance [h : DivInvMonoidₓ α] : DivInvMonoidₓ αᵒᵈ :=
  h

@[to_additive OrderDual.subtractionMonoid]
instance [h : DivisionMonoid α] : DivisionMonoid αᵒᵈ :=
  h

@[to_additive OrderDual.subtractionCommMonoid]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid αᵒᵈ :=
  h

@[to_additive]
instance [h : Groupₓ α] : Groupₓ αᵒᵈ :=
  h

@[to_additive]
instance [h : CommGroupₓ α] : CommGroupₓ αᵒᵈ :=
  h

instance [h : GroupWithZeroₓ α] : GroupWithZeroₓ αᵒᵈ :=
  h

instance [h : CommGroupWithZero α] : CommGroupWithZero αᵒᵈ :=
  h

@[to_additive]
instance [OrderedCommGroup α] : OrderedCommGroup αᵒᵈ :=
  { OrderDual.orderedCommMonoid, OrderDual.group with }

section Groupₓ

variable [Groupₓ α]

section TypeclassesLeftLe

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α}

/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.neg_nonpos_iff]
theorem Left.inv_le_one_iff : a⁻¹ ≤ 1 ↔ 1 ≤ a := by
  rw [← mul_le_mul_iff_left a]
  simp

/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.nonneg_neg_iff]
theorem Left.one_le_inv_iff : 1 ≤ a⁻¹ ↔ a ≤ 1 := by
  rw [← mul_le_mul_iff_left a]
  simp

@[simp, to_additive]
theorem le_inv_mul_iff_mul_le : b ≤ a⁻¹ * c ↔ a * b ≤ c := by
  rw [← mul_le_mul_iff_left a]
  simp

@[simp, to_additive]
theorem inv_mul_le_iff_le_mul : b⁻¹ * a ≤ c ↔ a ≤ b * c := by
  rw [← mul_le_mul_iff_left b, mul_inv_cancel_left]

@[to_additive neg_le_iff_add_nonneg']
theorem inv_le_iff_one_le_mul' : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
  (mul_le_mul_iff_left a).symm.trans <| by
    rw [mul_inv_selfₓ]

@[to_additive]
theorem le_inv_iff_mul_le_one_left : a ≤ b⁻¹ ↔ b * a ≤ 1 :=
  (mul_le_mul_iff_left b).symm.trans <| by
    rw [mul_inv_selfₓ]

@[to_additive]
theorem le_inv_mul_iff_le : 1 ≤ b⁻¹ * a ↔ b ≤ a := by
  rw [← mul_le_mul_iff_left b, mul_oneₓ, mul_inv_cancel_left]

@[to_additive]
theorem inv_mul_le_one_iff : a⁻¹ * b ≤ 1 ↔ b ≤ a :=
  trans inv_mul_le_iff_le_mul <| by
    rw [mul_oneₓ]

end TypeclassesLeftLe

section TypeclassesLeftLt

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] {a b c : α}

/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.neg_pos_iff]
theorem Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_left a, mul_inv_selfₓ, mul_oneₓ]

/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.neg_neg_iff]
theorem Left.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_left a, mul_inv_selfₓ, mul_oneₓ]

@[simp, to_additive]
theorem lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c := by
  rw [← mul_lt_mul_iff_left a]
  simp

@[simp, to_additive]
theorem inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c := by
  rw [← mul_lt_mul_iff_left b, mul_inv_cancel_left]

@[to_additive]
theorem inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b :=
  (mul_lt_mul_iff_left a).symm.trans <| by
    rw [mul_inv_selfₓ]

@[to_additive]
theorem lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1 :=
  (mul_lt_mul_iff_left b).symm.trans <| by
    rw [mul_inv_selfₓ]

@[to_additive]
theorem lt_inv_mul_iff_lt : 1 < b⁻¹ * a ↔ b < a := by
  rw [← mul_lt_mul_iff_left b, mul_oneₓ, mul_inv_cancel_left]

@[to_additive]
theorem inv_mul_lt_one_iff : a⁻¹ * b < 1 ↔ b < a :=
  trans inv_mul_lt_iff_lt_mul <| by
    rw [mul_oneₓ]

end TypeclassesLeftLt

section TypeclassesRightLe

variable [LE α] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}

/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.neg_nonpos_iff]
theorem Right.inv_le_one_iff : a⁻¹ ≤ 1 ↔ 1 ≤ a := by
  rw [← mul_le_mul_iff_right a]
  simp

/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.nonneg_neg_iff]
theorem Right.one_le_inv_iff : 1 ≤ a⁻¹ ↔ a ≤ 1 := by
  rw [← mul_le_mul_iff_right a]
  simp

@[to_additive neg_le_iff_add_nonneg]
theorem inv_le_iff_one_le_mul : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
  (mul_le_mul_iff_right a).symm.trans <| by
    rw [inv_mul_selfₓ]

@[to_additive]
theorem le_inv_iff_mul_le_one_right : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
  (mul_le_mul_iff_right b).symm.trans <| by
    rw [inv_mul_selfₓ]

@[simp, to_additive]
theorem mul_inv_le_iff_le_mul : a * b⁻¹ ≤ c ↔ a ≤ c * b :=
  (mul_le_mul_iff_right b).symm.trans <| by
    rw [inv_mul_cancel_right]

@[simp, to_additive]
theorem le_mul_inv_iff_mul_le : c ≤ a * b⁻¹ ↔ c * b ≤ a :=
  (mul_le_mul_iff_right b).symm.trans <| by
    rw [inv_mul_cancel_right]

@[simp, to_additive]
theorem mul_inv_le_one_iff_le : a * b⁻¹ ≤ 1 ↔ a ≤ b :=
  mul_inv_le_iff_le_mul.trans <| by
    rw [one_mulₓ]

@[to_additive]
theorem le_mul_inv_iff_le : 1 ≤ a * b⁻¹ ↔ b ≤ a := by
  rw [← mul_le_mul_iff_right b, one_mulₓ, inv_mul_cancel_right]

@[to_additive]
theorem mul_inv_le_one_iff : b * a⁻¹ ≤ 1 ↔ b ≤ a :=
  trans mul_inv_le_iff_le_mul <| by
    rw [one_mulₓ]

end TypeclassesRightLe

section TypeclassesRightLt

variable [LT α] [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α}

/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.neg_neg_iff "Uses `right` co(ntra)variant."]
theorem Right.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_right a, inv_mul_selfₓ, one_mulₓ]

/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.neg_pos_iff "Uses `right` co(ntra)variant."]
theorem Right.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_right a, inv_mul_selfₓ, one_mulₓ]

@[to_additive]
theorem inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a :=
  (mul_lt_mul_iff_right a).symm.trans <| by
    rw [inv_mul_selfₓ]

@[to_additive]
theorem lt_inv_iff_mul_lt_one : a < b⁻¹ ↔ a * b < 1 :=
  (mul_lt_mul_iff_right b).symm.trans <| by
    rw [inv_mul_selfₓ]

@[simp, to_additive]
theorem mul_inv_lt_iff_lt_mul : a * b⁻¹ < c ↔ a < c * b := by
  rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right]

@[simp, to_additive]
theorem lt_mul_inv_iff_mul_lt : c < a * b⁻¹ ↔ c * b < a :=
  (mul_lt_mul_iff_right b).symm.trans <| by
    rw [inv_mul_cancel_right]

@[simp, to_additive]
theorem inv_mul_lt_one_iff_lt : a * b⁻¹ < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right, one_mulₓ]

@[to_additive]
theorem lt_mul_inv_iff_lt : 1 < a * b⁻¹ ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mulₓ, inv_mul_cancel_right]

@[to_additive]
theorem mul_inv_lt_one_iff : b * a⁻¹ < 1 ↔ b < a :=
  trans mul_inv_lt_iff_lt_mul <| by
    rw [one_mulₓ]

end TypeclassesRightLt

section TypeclassesLeftRightLe

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}

@[simp, to_additive]
theorem inv_le_inv_iff : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [← mul_le_mul_iff_left a, ← mul_le_mul_iff_right b]
  simp

alias neg_le_neg_iff ↔ le_of_neg_le_neg _

section

variable (α)

/-- `x ↦ x⁻¹` as an order-reversing equivalence. -/
@[to_additive "`x ↦ -x` as an order-reversing equivalence.", simps]
def OrderIso.inv : α ≃o αᵒᵈ where
  toEquiv := (Equivₓ.inv α).trans OrderDual.toDual
  map_rel_iff' := fun a b => @inv_le_inv_iff α _ _ _ _ _ _

end

@[to_additive neg_le]
theorem inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
  (OrderIso.inv α).symm_apply_le

alias inv_le' ↔ inv_le_of_inv_le' _

attribute [to_additive neg_le_of_neg_le] inv_le_of_inv_le'

@[to_additive le_neg]
theorem le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
  (OrderIso.inv α).le_symm_apply

@[to_additive]
theorem mul_inv_le_inv_mul_iff : a * b⁻¹ ≤ d⁻¹ * c ↔ d * a ≤ c * b := by
  rw [← mul_le_mul_iff_left d, ← mul_le_mul_iff_right b, mul_inv_cancel_left, mul_assoc, inv_mul_cancel_right]

@[simp, to_additive]
theorem div_le_self_iff (a : α) {b : α} : a / b ≤ a ↔ 1 ≤ b := by
  simp [← div_eq_mul_inv]

@[simp, to_additive]
theorem le_div_self_iff (a : α) {b : α} : a ≤ a / b ↔ b ≤ 1 := by
  simp [← div_eq_mul_inv]

alias sub_le_self_iff ↔ _ sub_le_self

end TypeclassesLeftRightLe

section TypeclassesLeftRightLt

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α}

@[simp, to_additive]
theorem inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [← mul_lt_mul_iff_left a, ← mul_lt_mul_iff_right b]
  simp

@[to_additive neg_lt]
theorem inv_lt' : a⁻¹ < b ↔ b⁻¹ < a := by
  rw [← inv_lt_inv_iff, inv_invₓ]

@[to_additive lt_neg]
theorem lt_inv' : a < b⁻¹ ↔ b < a⁻¹ := by
  rw [← inv_lt_inv_iff, inv_invₓ]

alias lt_inv' ↔ lt_inv_of_lt_inv _

attribute [to_additive] lt_inv_of_lt_inv

alias inv_lt' ↔ inv_lt_of_inv_lt' _

attribute [to_additive neg_lt_of_neg_lt] inv_lt_of_inv_lt'

@[to_additive]
theorem mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b := by
  rw [← mul_lt_mul_iff_left d, ← mul_lt_mul_iff_right b, mul_inv_cancel_left, mul_assoc, inv_mul_cancel_right]

@[simp, to_additive]
theorem div_lt_self_iff (a : α) {b : α} : a / b < a ↔ 1 < b := by
  simp [← div_eq_mul_inv]

alias sub_lt_self_iff ↔ _ sub_lt_self

end TypeclassesLeftRightLt

section PreOrder

variable [Preorderₓ α]

section LeftLe

variable [CovariantClass α α (· * ·) (· ≤ ·)] {a : α}

@[to_additive]
theorem Left.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
  le_transₓ (Left.inv_le_one_iff.mpr h) h

alias Left.neg_le_self ← neg_le_self

@[to_additive]
theorem Left.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
  le_transₓ h (Left.one_le_inv_iff.mpr h)

end LeftLe

section LeftLt

variable [CovariantClass α α (· * ·) (· < ·)] {a : α}

@[to_additive]
theorem Left.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
  (Left.inv_lt_one_iff.mpr h).trans h

alias Left.neg_lt_self ← neg_lt_self

@[to_additive]
theorem Left.self_lt_inv (h : a < 1) : a < a⁻¹ :=
  lt_transₓ h (Left.one_lt_inv_iff.mpr h)

end LeftLt

section RightLe

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a : α}

@[to_additive]
theorem Right.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
  le_transₓ (Right.inv_le_one_iff.mpr h) h

@[to_additive]
theorem Right.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
  le_transₓ h (Right.one_le_inv_iff.mpr h)

end RightLe

section RightLt

variable [CovariantClass α α (swap (· * ·)) (· < ·)] {a : α}

@[to_additive]
theorem Right.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
  (Right.inv_lt_one_iff.mpr h).trans h

@[to_additive]
theorem Right.self_lt_inv (h : a < 1) : a < a⁻¹ :=
  lt_transₓ h (Right.one_lt_inv_iff.mpr h)

end RightLt

end PreOrder

end Groupₓ

section CommGroupₓ

variable [CommGroupₓ α]

section LE

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α}

@[to_additive]
theorem inv_mul_le_iff_le_mul' : c⁻¹ * a ≤ b ↔ a ≤ b * c := by
  rw [inv_mul_le_iff_le_mul, mul_comm]

@[simp, to_additive]
theorem mul_inv_le_iff_le_mul' : a * b⁻¹ ≤ c ↔ a ≤ b * c := by
  rw [← inv_mul_le_iff_le_mul, mul_comm]

@[to_additive add_neg_le_add_neg_iff]
theorem mul_inv_le_mul_inv_iff' : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b := by
  rw [mul_comm c, mul_inv_le_inv_mul_iff, mul_comm]

end LE

section LT

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] {a b c d : α}

@[to_additive]
theorem inv_mul_lt_iff_lt_mul' : c⁻¹ * a < b ↔ a < b * c := by
  rw [inv_mul_lt_iff_lt_mul, mul_comm]

@[simp, to_additive]
theorem mul_inv_lt_iff_le_mul' : a * b⁻¹ < c ↔ a < b * c := by
  rw [← inv_mul_lt_iff_lt_mul, mul_comm]

@[to_additive add_neg_lt_add_neg_iff]
theorem mul_inv_lt_mul_inv_iff' : a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b := by
  rw [mul_comm c, mul_inv_lt_inv_mul_iff, mul_comm]

end LT

end CommGroupₓ

alias le_inv' ↔ le_inv_of_le_inv _

attribute [to_additive] le_inv_of_le_inv

alias Left.inv_le_one_iff ↔ one_le_of_inv_le_one _

attribute [to_additive] one_le_of_inv_le_one

alias Left.one_le_inv_iff ↔ le_one_of_one_le_inv _

attribute [to_additive nonpos_of_neg_nonneg] le_one_of_one_le_inv

alias inv_lt_inv_iff ↔ lt_of_inv_lt_inv _

attribute [to_additive] lt_of_inv_lt_inv

alias Left.inv_lt_one_iff ↔ one_lt_of_inv_lt_one _

attribute [to_additive] one_lt_of_inv_lt_one

alias Left.inv_lt_one_iff ← inv_lt_one_iff_one_lt

attribute [to_additive] inv_lt_one_iff_one_lt

alias Left.inv_lt_one_iff ← inv_lt_one'

attribute [to_additive neg_lt_zero] inv_lt_one'

alias Left.one_lt_inv_iff ↔ inv_of_one_lt_inv _

attribute [to_additive neg_of_neg_pos] inv_of_one_lt_inv

alias Left.one_lt_inv_iff ↔ _ one_lt_inv_of_inv

attribute [to_additive neg_pos_of_neg] one_lt_inv_of_inv

alias le_inv_mul_iff_mul_le ↔ mul_le_of_le_inv_mul _

attribute [to_additive] mul_le_of_le_inv_mul

alias le_inv_mul_iff_mul_le ↔ _ le_inv_mul_of_mul_le

attribute [to_additive] le_inv_mul_of_mul_le

alias inv_mul_le_iff_le_mul ↔ _ inv_mul_le_of_le_mul

attribute [to_additive] inv_mul_le_iff_le_mul

alias lt_inv_mul_iff_mul_lt ↔ mul_lt_of_lt_inv_mul _

attribute [to_additive] mul_lt_of_lt_inv_mul

alias lt_inv_mul_iff_mul_lt ↔ _ lt_inv_mul_of_mul_lt

attribute [to_additive] lt_inv_mul_of_mul_lt

alias inv_mul_lt_iff_lt_mul ↔ lt_mul_of_inv_mul_lt inv_mul_lt_of_lt_mul

attribute [to_additive] lt_mul_of_inv_mul_lt

attribute [to_additive] inv_mul_lt_of_lt_mul

alias lt_mul_of_inv_mul_lt ← lt_mul_of_inv_mul_lt_left

attribute [to_additive] lt_mul_of_inv_mul_lt_left

alias Left.inv_le_one_iff ← inv_le_one'

attribute [to_additive neg_nonpos] inv_le_one'

alias Left.one_le_inv_iff ← one_le_inv'

attribute [to_additive neg_nonneg] one_le_inv'

alias Left.one_lt_inv_iff ← one_lt_inv'

attribute [to_additive neg_pos] one_lt_inv'

alias mul_lt_mul_left' ← OrderedCommGroup.mul_lt_mul_left'

attribute [to_additive OrderedAddCommGroup.add_lt_add_left] OrderedCommGroup.mul_lt_mul_left'

alias le_of_mul_le_mul_left' ← OrderedCommGroup.le_of_mul_le_mul_left

attribute [to_additive OrderedAddCommGroup.le_of_add_le_add_left] OrderedCommGroup.le_of_mul_le_mul_left

alias lt_of_mul_lt_mul_left' ← OrderedCommGroup.lt_of_mul_lt_mul_left

attribute [to_additive OrderedAddCommGroup.lt_of_add_lt_add_left] OrderedCommGroup.lt_of_mul_lt_mul_left

/-- Pullback an `ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.orderedAddCommGroup "Pullback an `ordered_add_comm_group` under an injective map."]
def Function.Injective.orderedCommGroup [OrderedCommGroup α] {β : Type _} [One β] [Mul β] [Inv β] [Div β] [Pow β ℕ]
    [Pow β ℤ] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : OrderedCommGroup β :=
  { PartialOrderₓ.lift f hf, hf.OrderedCommMonoid f one mul npow, hf.CommGroup f one mul inv div npow zpow with }

--  Most of the lemmas that are primed in this section appear in ordered_field. 
--  I (DT) did not try to minimise the assumptions.
section Groupₓ

variable [Groupₓ α] [LE α]

section Right

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}

@[simp, to_additive]
theorem div_le_div_iff_right (c : α) : a / c ≤ b / c ↔ a ≤ b := by
  simpa only [← div_eq_mul_inv] using mul_le_mul_iff_right _

@[to_additive sub_le_sub_right]
theorem div_le_div_right' (h : a ≤ b) (c : α) : a / c ≤ b / c :=
  (div_le_div_iff_right c).2 h

@[simp, to_additive sub_nonneg]
theorem one_le_div' : 1 ≤ a / b ↔ b ≤ a := by
  rw [← mul_le_mul_iff_right b, one_mulₓ, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_nonneg ↔ le_of_sub_nonneg sub_nonneg_of_le

@[simp, to_additive sub_nonpos]
theorem div_le_one' : a / b ≤ 1 ↔ a ≤ b := by
  rw [← mul_le_mul_iff_right b, one_mulₓ, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_nonpos ↔ le_of_sub_nonpos sub_nonpos_of_le

@[to_additive]
theorem le_div_iff_mul_le : a ≤ c / b ↔ a * b ≤ c := by
  rw [← mul_le_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]

alias le_sub_iff_add_le ↔ add_le_of_le_sub_right le_sub_right_of_add_le

@[to_additive]
theorem div_le_iff_le_mul : a / c ≤ b ↔ a ≤ b * c := by
  rw [← mul_le_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]

-- TODO: Should we get rid of `sub_le_iff_le_add` in favor of
-- (a renamed version of) `tsub_le_iff_right`?
-- see Note [lower instance priority]
instance (priority := 100) AddGroupₓ.toHasOrderedSub {α : Type _} [AddGroupₓ α] [LE α]
    [CovariantClass α α (swap (· + ·)) (· ≤ ·)] : HasOrderedSub α :=
  ⟨fun a b c => sub_le_iff_le_add⟩

/-- `equiv.mul_right` as an `order_iso`. See also `order_embedding.mul_right`. -/
@[to_additive "`equiv.add_right` as an `order_iso`. See also `order_embedding.add_right`.",
  simps (config := { simpRhs := true }) toEquiv apply]
def OrderIso.mulRight (a : α) : α ≃o α where
  map_rel_iff' := fun _ _ => mul_le_mul_iff_right a
  toEquiv := Equivₓ.mulRight a

@[simp, to_additive]
theorem OrderIso.mul_right_symm (a : α) : (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹ := by
  ext x
  rfl

end Right

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

/-- `equiv.mul_left` as an `order_iso`. See also `order_embedding.mul_left`. -/
@[to_additive "`equiv.add_left` as an `order_iso`. See also `order_embedding.add_left`.",
  simps (config := { simpRhs := true }) toEquiv apply]
def OrderIso.mulLeft (a : α) : α ≃o α where
  map_rel_iff' := fun _ _ => mul_le_mul_iff_left a
  toEquiv := Equivₓ.mulLeft a

@[simp, to_additive]
theorem OrderIso.mul_left_symm (a : α) : (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹ := by
  ext x
  rfl

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}

@[simp, to_additive]
theorem div_le_div_iff_left (a : α) : a / b ≤ a / c ↔ c ≤ b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_le_mul_iff_left a⁻¹, inv_mul_cancel_leftₓ, inv_mul_cancel_leftₓ,
    inv_le_inv_iff]

@[to_additive sub_le_sub_left]
theorem div_le_div_left' (h : a ≤ b) (c : α) : c / b ≤ c / a :=
  (div_le_div_iff_left c).2 h

end Left

end Groupₓ

section CommGroupₓ

variable [CommGroupₓ α]

section LE

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α}

@[to_additive sub_le_sub_iff]
theorem div_le_div_iff' : a / b ≤ c / d ↔ a * d ≤ c * b := by
  simpa only [← div_eq_mul_inv] using mul_inv_le_mul_inv_iff'

@[to_additive]
theorem le_div_iff_mul_le' : b ≤ c / a ↔ a * b ≤ c := by
  rw [le_div_iff_mul_le, mul_comm]

alias le_sub_iff_add_le' ↔ add_le_of_le_sub_left le_sub_left_of_add_le

@[to_additive]
theorem div_le_iff_le_mul' : a / b ≤ c ↔ a ≤ b * c := by
  rw [div_le_iff_le_mul, mul_comm]

alias sub_le_iff_le_add' ↔ le_add_of_sub_left_le sub_left_le_of_le_add

@[simp, to_additive]
theorem inv_le_div_iff_le_mul : b⁻¹ ≤ a / c ↔ c ≤ a * b :=
  le_div_iff_mul_le.trans inv_mul_le_iff_le_mul'

@[to_additive]
theorem inv_le_div_iff_le_mul' : a⁻¹ ≤ b / c ↔ c ≤ a * b := by
  rw [inv_le_div_iff_le_mul, mul_comm]

@[to_additive sub_le]
theorem div_le'' : a / b ≤ c ↔ a / c ≤ b :=
  div_le_iff_le_mul'.trans div_le_iff_le_mul.symm

@[to_additive le_sub]
theorem le_div'' : a ≤ b / c ↔ c ≤ b / a :=
  le_div_iff_mul_le'.trans le_div_iff_mul_le.symm

end LE

section Preorderₓ

variable [Preorderₓ α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α}

@[to_additive sub_le_sub]
theorem div_le_div'' (hab : a ≤ b) (hcd : c ≤ d) : a / d ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_le_inv_mul_iff, mul_comm]
  exact mul_le_mul' hab hcd

end Preorderₓ

end CommGroupₓ

--  Most of the lemmas that are primed in this section appear in ordered_field. 
--  I (DT) did not try to minimise the assumptions.
section Groupₓ

variable [Groupₓ α] [LT α]

section Right

variable [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α}

@[simp, to_additive]
theorem div_lt_div_iff_right (c : α) : a / c < b / c ↔ a < b := by
  simpa only [← div_eq_mul_inv] using mul_lt_mul_iff_right _

@[to_additive sub_lt_sub_right]
theorem div_lt_div_right' (h : a < b) (c : α) : a / c < b / c :=
  (div_lt_div_iff_right c).2 h

@[simp, to_additive sub_pos]
theorem one_lt_div' : 1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mulₓ, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_pos ↔ lt_of_sub_pos sub_pos_of_lt

@[simp, to_additive sub_neg]
theorem div_lt_one' : a / b < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b, one_mulₓ, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_neg ↔ lt_of_sub_neg sub_neg_of_lt

alias sub_neg ← sub_lt_zero

@[to_additive]
theorem lt_div_iff_mul_lt : a < c / b ↔ a * b < c := by
  rw [← mul_lt_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]

alias lt_sub_iff_add_lt ↔ add_lt_of_lt_sub_right lt_sub_right_of_add_lt

@[to_additive]
theorem div_lt_iff_lt_mul : a / c < b ↔ a < b * c := by
  rw [← mul_lt_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_lt_iff_lt_add ↔ lt_add_of_sub_right_lt sub_right_lt_of_lt_add

end Right

section Left

variable [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α}

@[simp, to_additive]
theorem div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_lt_mul_iff_left a⁻¹, inv_mul_cancel_leftₓ, inv_mul_cancel_leftₓ,
    inv_lt_inv_iff]

@[simp, to_additive]
theorem inv_lt_div_iff_lt_mul : a⁻¹ < b / c ↔ c < a * b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff_mul_lt, inv_mul_lt_iff_lt_mul]

@[to_additive sub_lt_sub_left]
theorem div_lt_div_left' (h : a < b) (c : α) : c / b < c / a :=
  (div_lt_div_iff_left c).2 h

end Left

end Groupₓ

section CommGroupₓ

variable [CommGroupₓ α]

section LT

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] {a b c d : α}

@[to_additive sub_lt_sub_iff]
theorem div_lt_div_iff' : a / b < c / d ↔ a * d < c * b := by
  simpa only [← div_eq_mul_inv] using mul_inv_lt_mul_inv_iff'

@[to_additive]
theorem lt_div_iff_mul_lt' : b < c / a ↔ a * b < c := by
  rw [lt_div_iff_mul_lt, mul_comm]

alias lt_sub_iff_add_lt' ↔ add_lt_of_lt_sub_left lt_sub_left_of_add_lt

@[to_additive]
theorem div_lt_iff_lt_mul' : a / b < c ↔ a < b * c := by
  rw [div_lt_iff_lt_mul, mul_comm]

alias sub_lt_iff_lt_add' ↔ lt_add_of_sub_left_lt sub_left_lt_of_lt_add

@[to_additive]
theorem inv_lt_div_iff_lt_mul' : b⁻¹ < a / c ↔ c < a * b :=
  lt_div_iff_mul_lt.trans inv_mul_lt_iff_lt_mul'

@[to_additive sub_lt]
theorem div_lt'' : a / b < c ↔ a / c < b :=
  div_lt_iff_lt_mul'.trans div_lt_iff_lt_mul.symm

@[to_additive lt_sub]
theorem lt_div'' : a < b / c ↔ c < b / a :=
  lt_div_iff_mul_lt'.trans lt_div_iff_mul_lt.symm

end LT

section Preorderₓ

variable [Preorderₓ α] [CovariantClass α α (· * ·) (· < ·)] {a b c d : α}

@[to_additive sub_lt_sub]
theorem div_lt_div'' (hab : a < b) (hcd : c < d) : a / d < b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_lt_inv_mul_iff, mul_comm]
  exact mul_lt_mul_of_lt_of_lt hab hcd

end Preorderₓ

end CommGroupₓ

section LinearOrderₓ

variable [Groupₓ α] [LinearOrderₓ α] [CovariantClass α α (· * ·) (· ≤ ·)]

section VariableNames

variable {a b c : α}

@[to_additive]
theorem le_of_forall_one_lt_lt_mul (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
  le_of_not_ltₓ fun h₁ =>
    lt_irreflₓ a
      (by
        simpa using h _ (lt_inv_mul_iff_lt.mpr h₁))

@[to_additive]
theorem le_iff_forall_one_lt_lt_mul : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
  ⟨fun h ε => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul⟩

/-  I (DT) introduced this lemma to prove (the additive version `sub_le_sub_flip` of)
`div_le_div_flip` below.  Now I wonder what is the point of either of these lemmas... -/
@[to_additive]
theorem div_le_inv_mul_iff [CovariantClass α α (swap (· * ·)) (· ≤ ·)] : a / b ≤ a⁻¹ * b ↔ a ≤ b := by
  rw [div_eq_mul_inv, mul_inv_le_inv_mul_iff]
  exact ⟨fun h => not_lt.mp fun k => not_lt.mpr h (mul_lt_mul_of_lt_of_lt k k), fun h => mul_le_mul' h h⟩

--  What is the point of this lemma?  See comment about `div_le_inv_mul_iff` above.
@[simp, to_additive]
theorem div_le_div_flip {α : Type _} [CommGroupₓ α] [LinearOrderₓ α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} :
    a / b ≤ b / a ↔ a ≤ b := by
  rw [div_eq_mul_inv b, mul_comm]
  exact div_le_inv_mul_iff

@[simp, to_additive]
theorem max_one_div_max_inv_one_eq_self (a : α) : max a 1 / max a⁻¹ 1 = a := by
  rcases le_totalₓ a 1 with (h | h) <;> simp [← h]

alias max_zero_sub_max_neg_zero_eq_self ← max_zero_sub_eq_self

end VariableNames

section DenselyOrdered

variable [DenselyOrdered α] {a b c : α}

@[to_additive]
theorem le_of_forall_one_lt_le_mul (h : ∀ ε : α, 1 < ε → a ≤ b * ε) : a ≤ b :=
  le_of_forall_le_of_dense fun c hc =>
    calc
      a ≤ b * (b⁻¹ * c) := h _ (lt_inv_mul_iff_lt.mpr hc)
      _ = c := mul_inv_cancel_left b c
      

@[to_additive]
theorem le_of_forall_lt_one_mul_le (h : ∀, ∀ ε < 1, ∀, a * ε ≤ b) : a ≤ b :=
  @le_of_forall_one_lt_le_mul αᵒᵈ _ _ _ _ _ _ h

@[to_additive]
theorem le_of_forall_one_lt_div_le (h : ∀ ε : α, 1 < ε → a / ε ≤ b) : a ≤ b :=
  le_of_forall_lt_one_mul_le fun ε ε1 => by
    simpa only [← div_eq_mul_inv, ← inv_invₓ] using h ε⁻¹ (Left.one_lt_inv_iff.2 ε1)

@[to_additive]
theorem le_iff_forall_one_lt_le_mul : a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε :=
  ⟨fun h ε ε_pos => le_mul_of_le_of_one_le h ε_pos.le, le_of_forall_one_lt_le_mul⟩

@[to_additive]
theorem le_iff_forall_lt_one_mul_le : a ≤ b ↔ ∀, ∀ ε < 1, ∀, a * ε ≤ b :=
  @le_iff_forall_one_lt_le_mul αᵒᵈ _ _ _ _ _ _

end DenselyOrdered

end LinearOrderₓ

/-!
### Linearly ordered commutative groups
-/


/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
@[protect_proj, ancestor OrderedAddCommGroup LinearOrderₓ]
class LinearOrderedAddCommGroup (α : Type u) extends OrderedAddCommGroup α, LinearOrderₓ α

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj, ancestor LinearOrderedAddCommMonoidWithTop SubNegMonoidₓ Nontrivial]
class LinearOrderedAddCommGroupWithTop (α : Type _) extends LinearOrderedAddCommMonoidWithTop α, SubNegMonoidₓ α,
  Nontrivial α where
  neg_top : -(⊤ : α) = ⊤
  add_neg_cancel : ∀ a : α, a ≠ ⊤ → a + -a = 0

/-- A linearly ordered commutative group is a
commutative group with a linear order in which
multiplication is monotone. -/
@[protect_proj, ancestor OrderedCommGroup LinearOrderₓ, to_additive]
class LinearOrderedCommGroup (α : Type u) extends OrderedCommGroup α, LinearOrderₓ α

@[to_additive]
instance [LinearOrderedCommGroup α] : LinearOrderedCommGroup αᵒᵈ :=
  { OrderDual.orderedCommGroup, OrderDual.linearOrder α with }

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {a b c : α}

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.toLinearOrderedCancelCommMonoid : LinearOrderedCancelCommMonoid α :=
  { ‹LinearOrderedCommGroup α› with le_of_mul_le_mul_left := fun x y z => le_of_mul_le_mul_left',
    mul_left_cancel := fun x y z => mul_left_cancelₓ }

/-- Pullback a `linear_ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedAddCommGroup
      "Pullback a `linear_ordered_add_comm_group` under an injective map."]
def Function.Injective.linearOrderedCommGroup {β : Type _} [One β] [Mul β] [Inv β] [Div β] [Pow β ℕ] [Pow β ℤ]
    [HasSup β] [HasInf β] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) (hsup : ∀ x y, f (x⊔y) = max (f x) (f y))
    (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) : LinearOrderedCommGroup β :=
  { LinearOrderₓ.lift f hf hsup hinf, hf.OrderedCommGroup f one mul inv div npow zpow with }

@[to_additive LinearOrderedAddCommGroup.add_lt_add_left]
theorem LinearOrderedCommGroup.mul_lt_mul_left' (a b : α) (h : a < b) (c : α) : c * a < c * b :=
  mul_lt_mul_left' h c

@[to_additive min_neg_neg]
theorem min_inv_inv' (a b : α) : min a⁻¹ b⁻¹ = (max a b)⁻¹ :=
  Eq.symm <| (@Monotone.map_max α αᵒᵈ _ _ Inv.inv a b) fun a b => inv_le_inv_iff.mpr

@[to_additive max_neg_neg]
theorem max_inv_inv' (a b : α) : max a⁻¹ b⁻¹ = (min a b)⁻¹ :=
  Eq.symm <| (@Monotone.map_min α αᵒᵈ _ _ Inv.inv a b) fun a b => inv_le_inv_iff.mpr

@[to_additive min_sub_sub_right]
theorem min_div_div_right' (a b c : α) : min (a / c) (b / c) = min a b / c := by
  simpa only [← div_eq_mul_inv] using min_mul_mul_right a b c⁻¹

@[to_additive max_sub_sub_right]
theorem max_div_div_right' (a b c : α) : max (a / c) (b / c) = max a b / c := by
  simpa only [← div_eq_mul_inv] using max_mul_mul_right a b c⁻¹

@[to_additive min_sub_sub_left]
theorem min_div_div_left' (a b c : α) : min (a / b) (a / c) = a / max b c := by
  simp only [← div_eq_mul_inv, ← min_mul_mul_left, ← min_inv_inv']

@[to_additive max_sub_sub_left]
theorem max_div_div_left' (a b c : α) : max (a / b) (a / c) = a / min b c := by
  simp only [← div_eq_mul_inv, ← max_mul_mul_left, ← max_inv_inv']

@[to_additive eq_zero_of_neg_eq]
theorem eq_one_of_inv_eq' (h : a⁻¹ = a) : a = 1 :=
  match lt_trichotomyₓ a 1 with
  | Or.inl h₁ =>
    have : 1 < a := h ▸ one_lt_inv_of_inv h₁
    absurd h₁ this.asymm
  | Or.inr (Or.inl h₁) => h₁
  | Or.inr (Or.inr h₁) =>
    have : a < 1 := h ▸ inv_lt_one'.mpr h₁
    absurd h₁ this.asymm

@[to_additive exists_zero_lt]
theorem exists_one_lt' [Nontrivial α] : ∃ a : α, 1 < a := by
  obtain ⟨y, hy⟩ := Decidable.exists_ne (1 : α)
  cases hy.lt_or_lt
  · exact ⟨y⁻¹, one_lt_inv'.mpr h⟩
    
  · exact ⟨y, h⟩
    

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_no_max_order [Nontrivial α] : NoMaxOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a * y, lt_mul_of_one_lt_right' a hy⟩⟩

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_no_min_order [Nontrivial α] : NoMinOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a / y, (div_lt_self_iff a).mpr hy⟩⟩

end LinearOrderedCommGroup

section CovariantAddLe

section Neg

/-- `abs a` is the absolute value of `a`. -/
-- see Note [lower instance priority]
@[to_additive "`abs a` is the absolute value of `a`"]
instance (priority := 100) Inv.toHasAbs [Inv α] [HasSup α] : HasAbs α :=
  ⟨fun a => a⊔a⁻¹⟩

@[to_additive]
theorem abs_eq_sup_inv [Inv α] [HasSup α] (a : α) : abs a = a⊔a⁻¹ :=
  rfl

variable [Neg α] [LinearOrderₓ α] {a b : α}

theorem abs_eq_max_neg : abs a = max a (-a) :=
  rfl

theorem abs_choice (x : α) : abs x = x ∨ abs x = -x :=
  max_choice _ _

theorem abs_le' : abs a ≤ b ↔ a ≤ b ∧ -a ≤ b :=
  max_le_iff

theorem le_abs : a ≤ abs b ↔ a ≤ b ∨ a ≤ -b :=
  le_max_iff

theorem le_abs_self (a : α) : a ≤ abs a :=
  le_max_leftₓ _ _

theorem neg_le_abs_self (a : α) : -a ≤ abs a :=
  le_max_rightₓ _ _

theorem lt_abs : a < abs b ↔ a < b ∨ a < -b :=
  lt_max_iff

theorem abs_le_abs (h₀ : a ≤ b) (h₁ : -a ≤ b) : abs a ≤ abs b :=
  (abs_le'.2 ⟨h₀, h₁⟩).trans (le_abs_self b)

theorem abs_by_cases (P : α → Prop) {a : α} (h1 : P a) (h2 : P (-a)) : P (abs a) :=
  sup_ind _ _ h1 h2

end Neg

section AddGroupₓ

variable [AddGroupₓ α] [LinearOrderₓ α]

@[simp]
theorem abs_neg (a : α) : abs (-a) = abs a := by
  rw [abs_eq_max_neg, max_commₓ, neg_negₓ, abs_eq_max_neg]

theorem eq_or_eq_neg_of_abs_eq {a b : α} (h : abs a = b) : a = b ∨ a = -b := by
  simpa only [h, ← eq_comm, ← eq_neg_iff_eq_neg] using abs_choice a

theorem abs_eq_abs {a b : α} : abs a = abs b ↔ a = b ∨ a = -b := by
  refine' ⟨fun h => _, fun h => _⟩
  · obtain rfl | rfl := eq_or_eq_neg_of_abs_eq h <;>
      simpa only [← neg_eq_iff_neg_eq, ← neg_inj, ← Or.comm, ← @eq_comm _ (-b)] using abs_choice b
    
  · cases h <;> simp only [← h, ← abs_neg]
    

theorem abs_sub_comm (a b : α) : abs (a - b) = abs (b - a) :=
  calc
    abs (a - b) = abs (-(b - a)) := congr_arg _ (neg_sub b a).symm
    _ = abs (b - a) := abs_neg (b - a)
    

variable [CovariantClass α α (· + ·) (· ≤ ·)] {a b c : α}

theorem abs_of_nonneg (h : 0 ≤ a) : abs a = a :=
  max_eq_leftₓ <| (neg_nonpos.2 h).trans h

theorem abs_of_pos (h : 0 < a) : abs a = a :=
  abs_of_nonneg h.le

theorem abs_of_nonpos (h : a ≤ 0) : abs a = -a :=
  max_eq_rightₓ <| h.trans (neg_nonneg.2 h)

theorem abs_of_neg (h : a < 0) : abs a = -a :=
  abs_of_nonpos h.le

@[simp]
theorem abs_zero : abs 0 = (0 : α) :=
  abs_of_nonneg le_rfl

@[simp]
theorem abs_pos : 0 < abs a ↔ a ≠ 0 := by
  rcases lt_trichotomyₓ a 0 with (ha | rfl | ha)
  · simp [← abs_of_neg ha, ← neg_pos, ← ha.ne, ← ha]
    
  · simp
    
  · simp [← abs_of_pos ha, ← ha, ← ha.ne.symm]
    

theorem abs_pos_of_pos (h : 0 < a) : 0 < abs a :=
  abs_pos.2 h.Ne.symm

theorem abs_pos_of_neg (h : a < 0) : 0 < abs a :=
  abs_pos.2 h.Ne

theorem neg_abs_le_self (a : α) : -abs a ≤ a := by
  cases' le_totalₓ 0 a with h h
  · calc -abs a = -a := congr_arg Neg.neg (abs_of_nonneg h)_ ≤ 0 := neg_nonpos.mpr h _ ≤ a := h
    
  · calc -abs a = - -a := congr_arg Neg.neg (abs_of_nonpos h)_ ≤ a := (neg_negₓ a).le
    

theorem add_abs_nonneg (a : α) : 0 ≤ a + abs a := by
  rw [← add_right_negₓ a]
  apply add_le_add_left
  exact neg_le_abs_self a

theorem neg_abs_le_neg (a : α) : -abs a ≤ -a := by
  simpa using neg_abs_le_self (-a)

@[simp]
theorem abs_nonneg (a : α) : 0 ≤ abs a :=
  (le_totalₓ 0 a).elim (fun h => h.trans (le_abs_self a)) fun h => (neg_nonneg.2 h).trans <| neg_le_abs_self a

@[simp]
theorem abs_abs (a : α) : abs (abs a) = abs a :=
  abs_of_nonneg <| abs_nonneg a

@[simp]
theorem abs_eq_zero : abs a = 0 ↔ a = 0 :=
  Decidable.not_iff_not.1 <| ne_comm.trans <| (abs_nonneg a).lt_iff_ne.symm.trans abs_pos

@[simp]
theorem abs_nonpos_iff {a : α} : abs a ≤ 0 ↔ a = 0 :=
  (abs_nonneg a).le_iff_eq.trans abs_eq_zero

variable [CovariantClass α α (swap (· + ·)) (· ≤ ·)]

theorem abs_lt : abs a < b ↔ -b < a ∧ a < b :=
  max_lt_iff.trans <|
    And.comm.trans <| by
      rw [neg_lt]

theorem neg_lt_of_abs_lt (h : abs a < b) : -b < a :=
  (abs_lt.mp h).1

theorem lt_of_abs_lt (h : abs a < b) : a < b :=
  (abs_lt.mp h).2

theorem max_sub_min_eq_abs' (a b : α) : max a b - min a b = abs (a - b) := by
  cases' le_totalₓ a b with ab ba
  · rw [max_eq_rightₓ ab, min_eq_leftₓ ab, abs_of_nonpos, neg_sub]
    rwa [sub_nonpos]
    
  · rw [max_eq_leftₓ ba, min_eq_rightₓ ba, abs_of_nonneg]
    rwa [sub_nonneg]
    

theorem max_sub_min_eq_abs (a b : α) : max a b - min a b = abs (b - a) := by
  rw [abs_sub_comm]
  exact max_sub_min_eq_abs' _ _

end AddGroupₓ

end CovariantAddLe

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {a b c d : α}

theorem abs_le : abs a ≤ b ↔ -b ≤ a ∧ a ≤ b := by
  rw [abs_le', And.comm, neg_le]

theorem le_abs' : a ≤ abs b ↔ b ≤ -a ∨ a ≤ b := by
  rw [le_abs, Or.comm, le_neg]

theorem neg_le_of_abs_le (h : abs a ≤ b) : -b ≤ a :=
  (abs_le.mp h).1

theorem le_of_abs_le (h : abs a ≤ b) : a ≤ b :=
  (abs_le.mp h).2

@[to_additive]
theorem apply_abs_le_mul_of_one_le' {β : Type _} [MulOneClassₓ β] [Preorderₓ β] [CovariantClass β β (· * ·) (· ≤ ·)]
    [CovariantClass β β (swap (· * ·)) (· ≤ ·)] {f : α → β} {a : α} (h₁ : 1 ≤ f a) (h₂ : 1 ≤ f (-a)) :
    f (abs a) ≤ f a * f (-a) :=
  (le_totalₓ a 0).byCases (fun ha => (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁) fun ha =>
    (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂

@[to_additive]
theorem apply_abs_le_mul_of_one_le {β : Type _} [MulOneClassₓ β] [Preorderₓ β] [CovariantClass β β (· * ·) (· ≤ ·)]
    [CovariantClass β β (swap (· * ·)) (· ≤ ·)] {f : α → β} (h : ∀ x, 1 ≤ f x) (a : α) : f (abs a) ≤ f a * f (-a) :=
  apply_abs_le_mul_of_one_le' (h _) (h _)

/-- The **triangle inequality** in `linear_ordered_add_comm_group`s.
-/
theorem abs_add (a b : α) : abs (a + b) ≤ abs a + abs b :=
  abs_le.2
    ⟨(neg_add (abs a) (abs b)).symm ▸ add_le_add (neg_le.2 <| neg_le_abs_self _) (neg_le.2 <| neg_le_abs_self _),
      add_le_add (le_abs_self _) (le_abs_self _)⟩

theorem abs_add' (a b : α) : abs a ≤ abs b + abs (b + a) := by
  simpa using abs_add (-b) (b + a)

theorem abs_sub (a b : α) : abs (a - b) ≤ abs a + abs b := by
  rw [sub_eq_add_neg, ← abs_neg b]
  exact abs_add a _

theorem abs_sub_le_iff : abs (a - b) ≤ c ↔ a - b ≤ c ∧ b - a ≤ c := by
  rw [abs_le, neg_le_sub_iff_le_add, sub_le_iff_le_add', and_comm, sub_le_iff_le_add']

theorem abs_sub_lt_iff : abs (a - b) < c ↔ a - b < c ∧ b - a < c := by
  rw [abs_lt, neg_lt_sub_iff_lt_add', sub_lt_iff_lt_add', and_comm, sub_lt_iff_lt_add']

theorem sub_le_of_abs_sub_le_left (h : abs (a - b) ≤ c) : b - c ≤ a :=
  sub_le.1 <| (abs_sub_le_iff.1 h).2

theorem sub_le_of_abs_sub_le_right (h : abs (a - b) ≤ c) : a - c ≤ b :=
  sub_le_of_abs_sub_le_left (abs_sub_comm a b ▸ h)

theorem sub_lt_of_abs_sub_lt_left (h : abs (a - b) < c) : b - c < a :=
  sub_lt.1 <| (abs_sub_lt_iff.1 h).2

theorem sub_lt_of_abs_sub_lt_right (h : abs (a - b) < c) : a - c < b :=
  sub_lt_of_abs_sub_lt_left (abs_sub_comm a b ▸ h)

theorem abs_sub_abs_le_abs_sub (a b : α) : abs a - abs b ≤ abs (a - b) :=
  sub_le_iff_le_add.2 <|
    calc
      abs a = abs (a - b + b) := by
        rw [sub_add_cancel]
      _ ≤ abs (a - b) + abs b := abs_add _ _
      

theorem abs_abs_sub_abs_le_abs_sub (a b : α) : abs (abs a - abs b) ≤ abs (a - b) :=
  abs_sub_le_iff.2
    ⟨abs_sub_abs_le_abs_sub _ _, by
      rw [abs_sub_comm] <;> apply abs_sub_abs_le_abs_sub⟩

theorem abs_eq (hb : 0 ≤ b) : abs a = b ↔ a = b ∨ a = -b := by
  refine' ⟨eq_or_eq_neg_of_abs_eq, _⟩
  rintro (rfl | rfl) <;> simp only [← abs_neg, ← abs_of_nonneg hb]

theorem abs_le_max_abs_abs (hab : a ≤ b) (hbc : b ≤ c) : abs b ≤ max (abs a) (abs c) :=
  abs_le'.2
    ⟨by
      simp [← hbc.trans (le_abs_self c)], by
      simp [← (neg_le_neg_iff.mpr hab).trans (neg_le_abs_self a)]⟩

theorem eq_of_abs_sub_eq_zero {a b : α} (h : abs (a - b) = 0) : a = b :=
  sub_eq_zero.1 <| abs_eq_zero.1 h

theorem abs_sub_le (a b c : α) : abs (a - c) ≤ abs (a - b) + abs (b - c) :=
  calc
    abs (a - c) = abs (a - b + (b - c)) := by
      rw [sub_add_sub_cancel]
    _ ≤ abs (a - b) + abs (b - c) := abs_add _ _
    

theorem abs_add_three (a b c : α) : abs (a + b + c) ≤ abs a + abs b + abs c :=
  (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)

theorem dist_bdd_within_interval {a b lb ub : α} (hal : lb ≤ a) (hau : a ≤ ub) (hbl : lb ≤ b) (hbu : b ≤ ub) :
    abs (a - b) ≤ ub - lb :=
  abs_sub_le_iff.2 ⟨sub_le_sub hau hbl, sub_le_sub hbu hal⟩

theorem eq_of_abs_sub_nonpos (h : abs (a - b) ≤ 0) : a = b :=
  eq_of_abs_sub_eq_zero (le_antisymmₓ h (abs_nonneg (a - b)))

theorem max_sub_max_le_max (a b c d : α) : max a b - max c d ≤ max (a - c) (b - d) := by
  simp only [← sub_le_iff_le_add, ← max_le_iff]
  constructor
  calc a = a - c + c := (sub_add_cancel a c).symm _ ≤ max (a - c) (b - d) + max c d :=
      add_le_add (le_max_leftₓ _ _) (le_max_leftₓ _ _)
  calc b = b - d + d := (sub_add_cancel b d).symm _ ≤ max (a - c) (b - d) + max c d :=
      add_le_add (le_max_rightₓ _ _) (le_max_rightₓ _ _)

theorem abs_max_sub_max_le_max (a b c d : α) : abs (max a b - max c d) ≤ max (abs (a - c)) (abs (b - d)) := by
  refine' abs_sub_le_iff.2 ⟨_, _⟩
  · exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
    
  · rw [abs_sub_comm a c, abs_sub_comm b d]
    exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
    

theorem abs_min_sub_min_le_max (a b c d : α) : abs (min a b - min c d) ≤ max (abs (a - c)) (abs (b - d)) := by
  simpa only [← max_neg_neg, ← neg_sub_neg, ← abs_sub_comm] using abs_max_sub_max_le_max (-a) (-b) (-c) (-d)

theorem abs_max_sub_max_le_abs (a b c : α) : abs (max a c - max b c) ≤ abs (a - b) := by
  simpa only [← sub_self, ← abs_zero, ← max_eq_leftₓ (abs_nonneg _)] using abs_max_sub_max_le_max a c b c

instance WithTop.linearOrderedAddCommGroupWithTop : LinearOrderedAddCommGroupWithTop (WithTop α) :=
  { WithTop.linearOrderedAddCommMonoidWithTop, Option.nontrivial with neg := Option.map fun a : α => -a,
    neg_top := @Option.map_none _ _ fun a : α => -a,
    add_neg_cancel := by
      rintro (a | a) ha
      · exact (ha rfl).elim
        
      · exact with_top.coe_add.symm.trans (WithTop.coe_eq_coe.2 (add_neg_selfₓ a))
         }

@[simp, norm_cast]
theorem WithTop.coe_neg (a : α) : ((-a : α) : WithTop α) = -a :=
  rfl

end LinearOrderedAddCommGroup

namespace AddCommGroupₓ

/-- A collection of elements in an `add_comm_group` designated as "non-negative".
This is useful for constructing an `ordered_add_commm_group`
by choosing a positive cone in an exisiting `add_comm_group`. -/
@[nolint has_inhabited_instance]
structure PositiveCone (α : Type _) [AddCommGroupₓ α] where
  Nonneg : α → Prop
  Pos : α → Prop := fun a => nonneg a ∧ ¬nonneg (-a)
  pos_iff : ∀ a, Pos a ↔ nonneg a ∧ ¬nonneg (-a) := by
    run_tac
      order_laws_tac
  zero_nonneg : nonneg 0
  add_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b)
  nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0

/-- A positive cone in an `add_comm_group` induces a linear order if
for every `a`, either `a` or `-a` is non-negative. -/
@[nolint has_inhabited_instance]
structure TotalPositiveCone (α : Type _) [AddCommGroupₓ α] extends PositiveCone α where
  nonnegDecidable : DecidablePred nonneg
  nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a)

/-- Forget that a `total_positive_cone` is total. -/
add_decl_doc total_positive_cone.to_positive_cone

end AddCommGroupₓ

namespace OrderedAddCommGroup

open AddCommGroupₓ

/-- Construct an `ordered_add_comm_group` by
designating a positive cone in an existing `add_comm_group`. -/
def mkOfPositiveCone {α : Type _} [AddCommGroupₓ α] (C : PositiveCone α) : OrderedAddCommGroup α :=
  { ‹AddCommGroupₓ α› with le := fun a b => C.Nonneg (b - a), lt := fun a b => C.Pos (b - a),
    lt_iff_le_not_le := fun a b => by
      simp <;> rw [C.pos_iff] <;> simp ,
    le_refl := fun a => by
      simp [← C.zero_nonneg],
    le_trans := fun a b c nab nbc => by
      simp [-sub_eq_add_neg] <;> rw [← sub_add_sub_cancel] <;> exact C.add_nonneg nbc nab,
    le_antisymm := fun a b nab nba =>
      eq_of_sub_eq_zero <|
        C.nonneg_antisymm nba
          (by
            rw [neg_sub] <;> exact nab),
    add_le_add_left := fun a b nab c => by
      simpa [← (· ≤ ·), ← Preorderₓ.Le] using nab }

end OrderedAddCommGroup

namespace LinearOrderedAddCommGroup

open AddCommGroupₓ

/-- Construct a `linear_ordered_add_comm_group` by
designating a positive cone in an existing `add_comm_group`
such that for every `a`, either `a` or `-a` is non-negative. -/
def mkOfPositiveCone {α : Type _} [AddCommGroupₓ α] (C : TotalPositiveCone α) : LinearOrderedAddCommGroup α :=
  { OrderedAddCommGroup.mkOfPositiveCone C.toPositiveCone with
    le_total := fun a b => by
      convert C.nonneg_total (b - a)
      change C.nonneg _ = _
      congr
      simp ,
    decidableLe := fun a b => C.nonnegDecidable _ }

end LinearOrderedAddCommGroup

namespace Prod

variable {G H : Type _}

@[to_additive]
instance [OrderedCommGroup G] [OrderedCommGroup H] : OrderedCommGroup (G × H) :=
  { Prod.commGroup, Prod.partialOrder G H, Prod.orderedCancelCommMonoid with }

end Prod

section TypeTags

instance [OrderedAddCommGroup α] : OrderedCommGroup (Multiplicative α) :=
  { Multiplicative.commGroup, Multiplicative.orderedCommMonoid with }

instance [OrderedCommGroup α] : OrderedAddCommGroup (Additive α) :=
  { Additive.addCommGroup, Additive.orderedAddCommMonoid with }

instance [LinearOrderedAddCommGroup α] : LinearOrderedCommGroup (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommGroup with }

instance [LinearOrderedCommGroup α] : LinearOrderedAddCommGroup (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommGroup with }

end TypeTags

section NormNumLemmas

/- The following lemmas are stated so that the `norm_num` tactic can use them with the
expected signatures.  -/
variable [OrderedCommGroup α] {a b : α}

@[to_additive neg_le_neg]
theorem inv_le_inv' : a ≤ b → b⁻¹ ≤ a⁻¹ :=
  inv_le_inv_iff.mpr

@[to_additive neg_lt_neg]
theorem inv_lt_inv' : a < b → b⁻¹ < a⁻¹ :=
  inv_lt_inv_iff.mpr

--  The additive version is also a `linarith` lemma.
@[to_additive]
theorem inv_lt_one_of_one_lt : 1 < a → a⁻¹ < 1 :=
  inv_lt_one_iff_one_lt.mpr

--  The additive version is also a `linarith` lemma.
@[to_additive]
theorem inv_le_one_of_one_le : 1 ≤ a → a⁻¹ ≤ 1 :=
  inv_le_one'.mpr

@[to_additive neg_nonneg_of_nonpos]
theorem one_le_inv_of_le_one : a ≤ 1 → 1 ≤ a⁻¹ :=
  one_le_inv'.mpr

end NormNumLemmas

section

variable {β : Type _} [Groupₓ α] [Preorderₓ α] [CovariantClass α α (· * ·) (· ≤ ·)]
  [CovariantClass α α (swap (· * ·)) (· ≤ ·)] [Preorderₓ β] {f : β → α} {s : Set β}

@[to_additive]
theorem Monotone.inv (hf : Monotone f) : Antitone fun x => (f x)⁻¹ := fun x y hxy => inv_le_inv_iff.2 (hf hxy)

@[to_additive]
theorem Antitone.inv (hf : Antitone f) : Monotone fun x => (f x)⁻¹ := fun x y hxy => inv_le_inv_iff.2 (hf hxy)

@[to_additive]
theorem MonotoneOn.inv (hf : MonotoneOn f s) : AntitoneOn (fun x => (f x)⁻¹) s := fun x hx y hy hxy =>
  inv_le_inv_iff.2 (hf hx hy hxy)

@[to_additive]
theorem AntitoneOn.inv (hf : AntitoneOn f s) : MonotoneOn (fun x => (f x)⁻¹) s := fun x hx y hy hxy =>
  inv_le_inv_iff.2 (hf hx hy hxy)

end

section

variable {β : Type _} [Groupₓ α] [Preorderₓ α] [CovariantClass α α (· * ·) (· < ·)]
  [CovariantClass α α (swap (· * ·)) (· < ·)] [Preorderₓ β] {f : β → α} {s : Set β}

@[to_additive]
theorem StrictMono.inv (hf : StrictMono f) : StrictAnti fun x => (f x)⁻¹ := fun x y hxy => inv_lt_inv_iff.2 (hf hxy)

@[to_additive]
theorem StrictAnti.inv (hf : StrictAnti f) : StrictMono fun x => (f x)⁻¹ := fun x y hxy => inv_lt_inv_iff.2 (hf hxy)

@[to_additive]
theorem StrictMonoOn.inv (hf : StrictMonoOn f s) : StrictAntiOn (fun x => (f x)⁻¹) s := fun x hx y hy hxy =>
  inv_lt_inv_iff.2 (hf hx hy hxy)

@[to_additive]
theorem StrictAntiOn.inv (hf : StrictAntiOn f s) : StrictMonoOn (fun x => (f x)⁻¹) s := fun x hx y hy hxy =>
  inv_lt_inv_iff.2 (hf hx hy hxy)

end

