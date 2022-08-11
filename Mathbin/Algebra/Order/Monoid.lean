/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Group.WithOne
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Hom.Equiv
import Mathbin.Algebra.Order.MonoidLemmas
import Mathbin.Order.MinMax
import Mathbin.Order.Hom.Basic

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/


open Function

universe u

variable {α : Type u} {β : Type _}

/-- An ordered commutative monoid is a commutative monoid
with a partial order such that `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
-/
@[protect_proj, ancestor CommMonoidₓ PartialOrderₓ]
class OrderedCommMonoid (α : Type _) extends CommMonoidₓ α, PartialOrderₓ α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone)
-/
@[protect_proj, ancestor AddCommMonoidₓ PartialOrderₓ]
class OrderedAddCommMonoid (α : Type _) extends AddCommMonoidₓ α, PartialOrderₓ α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

attribute [to_additive] OrderedCommMonoid

section OrderedInstances

@[to_additive]
instance OrderedCommMonoid.to_covariant_class_left (M : Type _) [OrderedCommMonoid M] :
    CovariantClass M M (· * ·) (· ≤ ·) where elim := fun a b c bc => OrderedCommMonoid.mul_le_mul_left _ _ bc a

/- This instance can be proven with `by apply_instance`.  However, `with_bot ℕ` does not
pick up a `covariant_class M M (function.swap (*)) (≤)` instance without it (see PR #7940). -/
@[to_additive]
instance OrderedCommMonoid.to_covariant_class_right (M : Type _) [OrderedCommMonoid M] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  covariant_swap_mul_le_of_covariant_mul_le M

/- This is not an instance, to avoid creating a loop in the type-class system: in a
`left_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (*) (≤)` implies
`covariant_class M M (*) (<)`, see `left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le`. -/
@[to_additive]
theorem Mul.to_covariant_class_left (M : Type _) [Mul M] [PartialOrderₓ M] [CovariantClass M M (· * ·) (· < ·)] :
    CovariantClass M M (· * ·) (· ≤ ·) :=
  ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩

/- This is not an instance, to avoid creating a loop in the type-class system: in a
`right_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (swap (*)) (<)`
implies `covariant_class M M (swap (*)) (≤)`, see
`right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le`. -/
@[to_additive]
theorem Mul.to_covariant_class_right (M : Type _) [Mul M] [PartialOrderₓ M]
    [CovariantClass M M (swap (· * ·)) (· < ·)] : CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩

end OrderedInstances

/-- An `ordered_comm_monoid` with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_monoid`. -/
class HasExistsMulOfLe (α : Type u) [Mul α] [LE α] : Prop where
  exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a * c

/-- An `ordered_add_comm_monoid` with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_add_monoid`. -/
class HasExistsAddOfLe (α : Type u) [Add α] [LE α] : Prop where
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a + c

attribute [to_additive] HasExistsMulOfLe

export HasExistsMulOfLe (exists_mul_of_le)

export HasExistsAddOfLe (exists_add_of_le)

/-- A linearly ordered additive commutative monoid. -/
@[protect_proj, ancestor LinearOrderₓ OrderedAddCommMonoid]
class LinearOrderedAddCommMonoid (α : Type _) extends LinearOrderₓ α, OrderedAddCommMonoid α

/-- A linearly ordered commutative monoid. -/
@[protect_proj, ancestor LinearOrderₓ OrderedCommMonoid, to_additive]
class LinearOrderedCommMonoid (α : Type _) extends LinearOrderₓ α, OrderedCommMonoid α

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class ZeroLeOneClass (α : Type _) [Zero α] [One α] [LE α] where
  zero_le_one : (0 : α) ≤ 1

@[simp]
theorem zero_le_one [Zero α] [One α] [LE α] [ZeroLeOneClass α] : (0 : α) ≤ 1 :=
  ZeroLeOneClass.zero_le_one

-- `zero_le_one` with an explicit type argument.
theorem zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLeOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one

theorem zero_le_two [Preorderₓ α] [One α] [AddZeroClassₓ α] [ZeroLeOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 2 :=
  add_nonneg zero_le_one zero_le_one

theorem zero_le_three [Preorderₓ α] [One α] [AddZeroClassₓ α] [ZeroLeOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 3 :=
  add_nonneg zero_le_two zero_le_one

theorem zero_le_four [Preorderₓ α] [One α] [AddZeroClassₓ α] [ZeroLeOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 4 :=
  add_nonneg zero_le_two zero_le_two

theorem one_le_two [LE α] [One α] [AddZeroClassₓ α] [ZeroLeOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (1 : α) ≤ 2 :=
  calc
    1 = 1 + 0 := (add_zeroₓ 1).symm
    _ ≤ 1 + 1 := add_le_add_left zero_le_one _
    

theorem one_le_two' [LE α] [One α] [AddZeroClassₓ α] [ZeroLeOneClass α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    (1 : α) ≤ 2 :=
  calc
    1 = 0 + 1 := (zero_addₓ 1).symm
    _ ≤ 1 + 1 := add_le_add_right zero_le_one _
    

/-- A linearly ordered commutative monoid with a zero element. -/
class LinearOrderedCommMonoidWithZero (α : Type _) extends LinearOrderedCommMonoid α, CommMonoidWithZero α where
  zero_le_one : (0 : α) ≤ 1

instance (priority := 100) LinearOrderedCommMonoidWithZero.zeroLeOneClass [h : LinearOrderedCommMonoidWithZero α] :
    ZeroLeOneClass α :=
  { h with }

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj, ancestor LinearOrderedAddCommMonoid HasTop]
class LinearOrderedAddCommMonoidWithTop (α : Type _) extends LinearOrderedAddCommMonoid α, HasTop α where
  le_top : ∀ x : α, x ≤ ⊤
  top_add' : ∀ x : α, ⊤ + x = ⊤

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedAddCommMonoidWithTop.toOrderTop (α : Type u)
    [h : LinearOrderedAddCommMonoidWithTop α] : OrderTop α :=
  { h with }

section LinearOrderedAddCommMonoidWithTop

variable [LinearOrderedAddCommMonoidWithTop α] {a b : α}

@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  trans (add_commₓ _ _) (top_add _)

end LinearOrderedAddCommMonoidWithTop

/-- Pullback an `ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.orderedAddCommMonoid "Pullback an `ordered_add_comm_monoid` under an injective map."]
def Function.Injective.orderedCommMonoid [OrderedCommMonoid α] {β : Type _} [One β] [Mul β] [Pow β ℕ] (f : β → α)
    (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : OrderedCommMonoid β :=
  { PartialOrderₓ.lift f hf, hf.CommMonoid f one mul npow with
    mul_le_mul_left := fun a b ab c =>
      show f (c * a) ≤ f (c * b) by
        rw [mul, mul]
        apply mul_le_mul_left'
        exact ab }

/-- Pullback a `linear_ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedAddCommMonoid
      "Pullback an `ordered_add_comm_monoid` under an injective map."]
def Function.Injective.linearOrderedCommMonoid [LinearOrderedCommMonoid α] {β : Type _} [One β] [Mul β] [Pow β ℕ]
    [HasSup β] [HasInf β] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (hsup : ∀ x y, f (x⊔y) = max (f x) (f y))
    (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) : LinearOrderedCommMonoid β :=
  { hf.OrderedCommMonoid f one mul npow, LinearOrderₓ.lift f hf hsup hinf with }

theorem bit0_pos [OrderedAddCommMonoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
  add_pos' h h

namespace Units

@[to_additive]
instance [Monoidₓ α] [Preorderₓ α] : Preorderₓ αˣ :=
  Preorderₓ.lift (coe : αˣ → α)

@[simp, norm_cast, to_additive]
theorem coe_le_coe [Monoidₓ α] [Preorderₓ α] {a b : αˣ} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl

@[simp, norm_cast, to_additive]
theorem coe_lt_coe [Monoidₓ α] [Preorderₓ α] {a b : αˣ} : (a : α) < b ↔ a < b :=
  Iff.rfl

@[to_additive]
instance [Monoidₓ α] [PartialOrderₓ α] : PartialOrderₓ αˣ :=
  PartialOrderₓ.lift coe Units.ext

@[to_additive]
instance [Monoidₓ α] [LinearOrderₓ α] : LinearOrderₓ αˣ :=
  LinearOrderₓ.lift' coe Units.ext

/-- `coe : αˣ → α` as an order embedding. -/
@[to_additive "`coe : add_units α → α` as an order embedding.", simps (config := { fullyApplied := false })]
def orderEmbeddingCoe [Monoidₓ α] [LinearOrderₓ α] : αˣ ↪o α :=
  ⟨⟨coe, ext⟩, fun _ _ => Iff.rfl⟩

@[simp, norm_cast, to_additive]
theorem max_coe [Monoidₓ α] [LinearOrderₓ α] {a b : αˣ} : (↑(max a b) : α) = max a b :=
  Monotone.map_max orderEmbeddingCoe.Monotone

@[simp, norm_cast, to_additive]
theorem min_coe [Monoidₓ α] [LinearOrderₓ α] {a b : αˣ} : (↑(min a b) : α) = min a b :=
  Monotone.map_min orderEmbeddingCoe.Monotone

end Units

namespace WithZero

attribute [local semireducible] WithZero

instance [Preorderₓ α] : Preorderₓ (WithZero α) :=
  WithBot.preorder

instance [PartialOrderₓ α] : PartialOrderₓ (WithZero α) :=
  WithBot.partialOrder

instance [Preorderₓ α] : OrderBot (WithZero α) :=
  WithBot.orderBot

theorem zero_le [Preorderₓ α] (a : WithZero α) : 0 ≤ a :=
  bot_le

theorem zero_lt_coe [Preorderₓ α] (a : α) : (0 : WithZero α) < a :=
  WithBot.bot_lt_coe a

theorem zero_eq_bot [Preorderₓ α] : (0 : WithZero α) = ⊥ :=
  rfl

@[simp, norm_cast]
theorem coe_lt_coe [Preorderₓ α] {a b : α} : (a : WithZero α) < b ↔ a < b :=
  WithBot.coe_lt_coe

@[simp, norm_cast]
theorem coe_le_coe [Preorderₓ α] {a b : α} : (a : WithZero α) ≤ b ↔ a ≤ b :=
  WithBot.coe_le_coe

instance [Lattice α] : Lattice (WithZero α) :=
  WithBot.lattice

instance [LinearOrderₓ α] : LinearOrderₓ (WithZero α) :=
  WithBot.linearOrder

instance covariant_class_mul_le {α : Type u} [Mul α] [Preorderₓ α] [CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass (WithZero α) (WithZero α) (· * ·) (· ≤ ·) := by
  refine' ⟨fun a b c hbc => _⟩
  induction a using WithZero.recZeroCoe
  · exact zero_le _
    
  induction b using WithZero.recZeroCoe
  · exact zero_le _
    
  rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  rw [← coe_mul, ← coe_mul, coe_le_coe]
  exact mul_le_mul_left' hbc' a

instance contravariant_class_mul_lt {α : Type u} [Mul α] [PartialOrderₓ α] [ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass (WithZero α) (WithZero α) (· * ·) (· < ·) := by
  refine' ⟨fun a b c h => _⟩
  have := ((zero_le _).trans_lt h).ne'
  lift a to α using left_ne_zero_of_mul this
  lift c to α using right_ne_zero_of_mul this
  induction b using WithZero.recZeroCoe
  exacts[zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]

@[simp]
theorem le_max_iff [LinearOrderₓ α] {a b c : α} : (a : WithZero α) ≤ max b c ↔ a ≤ max b c := by
  simp only [← WithZero.coe_le_coe, ← le_max_iff]

@[simp]
theorem min_le_iff [LinearOrderₓ α] {a b c : α} : min (a : WithZero α) b ≤ c ↔ min a b ≤ c := by
  simp only [← WithZero.coe_le_coe, ← min_le_iff]

instance [OrderedCommMonoid α] : OrderedCommMonoid (WithZero α) :=
  { WithZero.commMonoidWithZero, WithZero.partialOrder with mul_le_mul_left := fun _ _ => mul_le_mul_left' }

protected theorem covariant_class_add_le [AddZeroClassₓ α] [Preorderₓ α] [CovariantClass α α (· + ·) (· ≤ ·)]
    (h : ∀ a : α, 0 ≤ a) : CovariantClass (WithZero α) (WithZero α) (· + ·) (· ≤ ·) := by
  refine' ⟨fun a b c hbc => _⟩
  induction a using WithZero.recZeroCoe
  · rwa [zero_addₓ, zero_addₓ]
    
  induction b using WithZero.recZeroCoe
  · rw [add_zeroₓ]
    induction c using WithZero.recZeroCoe
    · rw [add_zeroₓ]
      exact le_rfl
      
    · rw [← coe_add, coe_le_coe]
      exact le_add_of_nonneg_right (h _)
      
    
  · rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    rw [← coe_add, ← coe_add, coe_le_coe]
    exact add_le_add_left hbc' a
    

/-- If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
See note [reducible non-instances].
-/
/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/
@[reducible]
protected def orderedAddCommMonoid [OrderedAddCommMonoid α] (zero_le : ∀ a : α, 0 ≤ a) :
    OrderedAddCommMonoid (WithZero α) :=
  { WithZero.partialOrder, WithZero.addCommMonoid with
    add_le_add_left := @add_le_add_left _ _ _ (WithZero.covariant_class_add_le zero_le).. }

end WithZero

/-- A canonically ordered additive monoid is an ordered commutative additive monoid
  in which the ordering coincides with the subtractibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other nontrivial `ordered_add_comm_group`s. -/
@[protect_proj, ancestor OrderedAddCommMonoid HasBot]
class CanonicallyOrderedAddMonoid (α : Type _) extends OrderedAddCommMonoid α, HasBot α where
  bot_le : ∀ x : α, ⊥ ≤ x
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c, b = a + c
  le_self_add : ∀ a b : α, a ≤ a + b

-- see Note [lower instance priority]
instance (priority := 100) CanonicallyOrderedAddMonoid.toOrderBot (α : Type u) [h : CanonicallyOrderedAddMonoid α] :
    OrderBot α :=
  { h with }

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Examples seem rare; it seems more likely that the `order_dual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1).
-/
@[protect_proj, ancestor OrderedCommMonoid HasBot, to_additive]
class CanonicallyOrderedMonoid (α : Type _) extends OrderedCommMonoid α, HasBot α where
  bot_le : ∀ x : α, ⊥ ≤ x
  exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c, b = a * c
  le_self_mul : ∀ a b : α, a ≤ a * b

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CanonicallyOrderedMonoid.toOrderBot (α : Type u) [h : CanonicallyOrderedMonoid α] :
    OrderBot α :=
  { h with }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CanonicallyOrderedMonoid.has_exists_mul_of_le (α : Type u) [h : CanonicallyOrderedMonoid α] :
    HasExistsMulOfLe α :=
  { h with }

section CanonicallyOrderedMonoid

variable [CanonicallyOrderedMonoid α] {a b c d : α}

@[to_additive]
theorem le_self_mul : a ≤ a * c :=
  CanonicallyOrderedMonoid.le_self_mul _ _

@[to_additive]
theorem le_mul_self : a ≤ b * a := by
  rw [mul_comm]
  exact le_self_mul

@[to_additive]
theorem self_le_mul_right (a b : α) : a ≤ a * b :=
  le_self_mul

@[to_additive]
theorem self_le_mul_left (a b : α) : a ≤ b * a :=
  le_mul_self

@[to_additive]
theorem le_of_mul_le_left : a * b ≤ c → a ≤ c :=
  le_self_mul.trans

@[to_additive]
theorem le_of_mul_le_right : a * b ≤ c → b ≤ c :=
  le_mul_self.trans

@[to_additive]
theorem le_iff_exists_mul : a ≤ b ↔ ∃ c, b = a * c :=
  ⟨exists_mul_of_le, by
    rintro ⟨c, rfl⟩
    exact le_self_mul⟩

@[to_additive]
theorem le_iff_exists_mul' : a ≤ b ↔ ∃ c, b = c * a := by
  simpa only [← mul_comm _ a] using le_iff_exists_mul

@[simp, to_additive zero_le]
theorem one_le (a : α) : 1 ≤ a :=
  le_iff_exists_mul.mpr ⟨a, (one_mulₓ _).symm⟩

@[to_additive]
theorem bot_eq_one : (⊥ : α) = 1 :=
  le_antisymmₓ bot_le (one_le ⊥)

@[simp, to_additive]
theorem mul_eq_one_iff : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  mul_eq_one_iff' (one_le _) (one_le _)

@[simp, to_additive]
theorem le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
  (one_le a).le_iff_eq

@[to_additive]
theorem one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
  (one_le a).lt_iff_ne.trans ne_comm

@[to_additive]
theorem eq_one_or_one_lt : a = 1 ∨ 1 < a :=
  (one_le a).eq_or_lt.imp_left Eq.symm

@[simp, to_additive add_pos_iff]
theorem one_lt_mul_iff : 1 < a * b ↔ 1 < a ∨ 1 < b := by
  simp only [← one_lt_iff_ne_one, ← Ne.def, ← mul_eq_one_iff, ← not_and_distrib]

@[to_additive]
theorem exists_one_lt_mul_of_lt (h : a < b) : ∃ (c : _)(hc : 1 < c), a * c = b := by
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le
  refine' ⟨c, one_lt_iff_ne_one.2 _, hc.symm⟩
  rintro rfl
  simpa [← hc, ← lt_irreflₓ] using h

@[to_additive]
theorem le_mul_left (h : a ≤ c) : a ≤ b * c :=
  calc
    a = 1 * a := by
      simp
    _ ≤ b * c := mul_le_mul' (one_le _) h
    

@[to_additive]
theorem le_mul_right (h : a ≤ b) : a ≤ b * c :=
  calc
    a = a * 1 := by
      simp
    _ ≤ b * c := mul_le_mul' h (one_le _)
    

@[to_additive]
theorem lt_iff_exists_mul [CovariantClass α α (· * ·) (· < ·)] : a < b ↔ ∃ c > 1, b = a * c := by
  simp_rw [lt_iff_le_and_ne, and_comm, le_iff_exists_mul, ← exists_and_distrib_left, exists_prop]
  apply exists_congr
  intro c
  rw [And.congr_left_iff, gt_iff_lt]
  rintro rfl
  constructor
  · rw [one_lt_iff_ne_one]
    apply mt
    rintro rfl
    rw [mul_oneₓ]
    
  · rw [← (self_le_mul_right a c).lt_iff_ne]
    apply lt_mul_of_one_lt_right'
    

instance WithZero.has_exists_add_of_le {α} [Add α] [Preorderₓ α] [HasExistsAddOfLe α] : HasExistsAddOfLe (WithZero α) :=
  ⟨fun a b => by
    apply WithZero.cases_on a
    · exact fun _ => ⟨b, (zero_addₓ b).symm⟩
      
    apply WithZero.cases_on b
    · exact fun b' h => (WithBot.not_coe_le_bot _ h).elim
      
    rintro a' b' h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩⟩

/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
-- This instance looks absurd: a monoid already has a zero
instance WithZero.canonicallyOrderedAddMonoid {α : Type u} [CanonicallyOrderedAddMonoid α] :
    CanonicallyOrderedAddMonoid (WithZero α) :=
  { WithZero.orderBot, WithZero.orderedAddCommMonoid zero_le, WithZero.has_exists_add_of_le with
    le_self_add := fun a b => by
      apply WithZero.cases_on a
      · exact bot_le
        
      apply WithZero.cases_on b
      · exact fun b' => le_rfl
        
      · exact fun a' b' => WithZero.coe_le_coe.2 le_self_add
         }

end CanonicallyOrderedMonoid

theorem pos_of_gt {M : Type _} [CanonicallyOrderedAddMonoid M] {n m : M} (h : n < m) : 0 < m :=
  lt_of_le_of_ltₓ (zero_le _) h

/-- A canonically linear-ordered additive monoid is a canonically ordered additive monoid
    whose ordering is a linear order. -/
@[protect_proj, ancestor CanonicallyOrderedAddMonoid LinearOrderₓ]
class CanonicallyLinearOrderedAddMonoid (α : Type _) extends CanonicallyOrderedAddMonoid α, LinearOrderₓ α

/-- A canonically linear-ordered monoid is a canonically ordered monoid
    whose ordering is a linear order. -/
@[protect_proj, ancestor CanonicallyOrderedMonoid LinearOrderₓ, to_additive]
class CanonicallyLinearOrderedMonoid (α : Type _) extends CanonicallyOrderedMonoid α, LinearOrderₓ α

section CanonicallyLinearOrderedMonoid

variable [CanonicallyLinearOrderedMonoid α]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CanonicallyLinearOrderedMonoid.semilatticeSup : SemilatticeSup α :=
  { LinearOrderₓ.toLattice with }

instance WithZero.canonicallyLinearOrderedAddMonoid (α : Type _) [CanonicallyLinearOrderedAddMonoid α] :
    CanonicallyLinearOrderedAddMonoid (WithZero α) :=
  { WithZero.canonicallyOrderedAddMonoid, WithZero.linearOrder with }

@[to_additive]
theorem min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c) := by
  cases' le_totalₓ a b with hb hb
  · simp [← hb, ← le_mul_right]
    
  · cases' le_totalₓ a c with hc hc
    · simp [← hc, ← le_mul_left]
      
    · simp [← hb, ← hc]
      
    

@[to_additive]
theorem min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c := by
  simpa [← min_commₓ _ c] using min_mul_distrib c a b

@[simp, to_additive]
theorem one_min (a : α) : min 1 a = 1 :=
  min_eq_leftₓ (one_le a)

@[simp, to_additive]
theorem min_one (a : α) : min a 1 = 1 :=
  min_eq_rightₓ (one_le a)

/-- In a linearly ordered monoid, we are happy for `bot_eq_one` to be a `@[simp]` lemma. -/
@[simp, to_additive "In a linearly ordered monoid, we are happy for `bot_eq_zero` to be a `@[simp]` lemma"]
theorem bot_eq_one' : (⊥ : α) = 1 :=
  bot_eq_one

end CanonicallyLinearOrderedMonoid

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor AddCancelCommMonoid PartialOrderₓ]
class OrderedCancelAddCommMonoid (α : Type u) extends AddCancelCommMonoid α, PartialOrderₓ α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor CancelCommMonoid PartialOrderₓ, to_additive]
class OrderedCancelCommMonoid (α : Type u) extends CancelCommMonoid α, PartialOrderₓ α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] {a b c d : α}

@[to_additive]
theorem OrderedCancelCommMonoid.lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c := fun a b c h =>
  lt_of_le_not_leₓ (OrderedCancelCommMonoid.le_of_mul_le_mul_left a b c h.le) <|
    mt (fun h => OrderedCancelCommMonoid.mul_le_mul_left _ _ h _) (not_le_of_gtₓ h)

@[to_additive]
instance OrderedCancelCommMonoid.to_contravariant_class_left (M : Type _) [OrderedCancelCommMonoid M] :
    ContravariantClass M M (· * ·)
      (· < ·) where elim := fun a b c => OrderedCancelCommMonoid.lt_of_mul_lt_mul_left _ _ _

/- This instance can be proven with `by apply_instance`.  However, by analogy with the
instance `ordered_cancel_comm_monoid.to_covariant_class_right` above, I imagine that without
this instance, some Type would not have a `contravariant_class M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance OrderedCancelCommMonoid.to_contravariant_class_right (M : Type _) [OrderedCancelCommMonoid M] :
    ContravariantClass M M (swap (· * ·)) (· < ·) :=
  contravariant_swap_mul_lt_of_contravariant_mul_lt M

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toOrderedCommMonoid : OrderedCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with }

/-- Pullback an `ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.orderedCancelAddCommMonoid
      "Pullback an `ordered_cancel_add_comm_monoid` under an injective map."]
def Function.Injective.orderedCancelCommMonoid {β : Type _} [One β] [Mul β] [Pow β ℕ] (f : β → α)
    (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : OrderedCancelCommMonoid β :=
  { hf.LeftCancelSemigroup f mul, hf.OrderedCommMonoid f one mul npow with
    le_of_mul_le_mul_left := fun a b c (bc : f (a * b) ≤ f (a * c)) =>
      (mul_le_mul_iff_left (f a)).mp
        (by
          rwa [← mul, ← mul]) }

end OrderedCancelCommMonoid

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/


@[to_additive]
theorem fn_min_mul_fn_max {β} [LinearOrderₓ α] [CommSemigroupₓ β] (f : α → β) (n m : α) :
    f (min n m) * f (max n m) = f n * f m := by
  cases' le_totalₓ n m with h h <;> simp [← h, ← mul_comm]

@[to_additive]
theorem min_mul_max [LinearOrderₓ α] [CommSemigroupₓ α] (n m : α) : min n m * max n m = n * m :=
  fn_min_mul_fn_max id n m

/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor OrderedCancelAddCommMonoid LinearOrderedAddCommMonoid]
class LinearOrderedCancelAddCommMonoid (α : Type u) extends OrderedCancelAddCommMonoid α, LinearOrderedAddCommMonoid α

/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor OrderedCancelCommMonoid LinearOrderedCommMonoid, to_additive]
class LinearOrderedCancelCommMonoid (α : Type u) extends OrderedCancelCommMonoid α, LinearOrderedCommMonoid α

section CovariantClassMulLe

variable [LinearOrderₓ α]

section Mul

variable [Mul α]

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

@[to_additive]
theorem min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
  (monotone_id.const_mul' a).map_min.symm

@[to_additive]
theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
  (monotone_id.const_mul' a).map_max.symm

@[to_additive]
theorem lt_or_lt_of_mul_lt_mul [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b m n : α} (h : m * n < a * b) :
    m < a ∨ n < b := by
  contrapose! h
  exact mul_le_mul' h.1 h.2

@[to_additive]
theorem mul_lt_mul_iff_of_le_of_le [CovariantClass α α (Function.swap (· * ·)) (· < ·)]
    [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b c d : α} (ac : a ≤ c)
    (bd : b ≤ d) : a * b < c * d ↔ a < c ∨ b < d := by
  refine' ⟨lt_or_lt_of_mul_lt_mul, fun h => _⟩
  cases' h with ha hb
  · exact mul_lt_mul_of_lt_of_le ha bd
    
  · exact mul_lt_mul_of_le_of_lt ac hb
    

end Left

section Right

variable [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

@[to_additive]
theorem min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
  (monotone_id.mul_const' c).map_min.symm

@[to_additive]
theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
  (monotone_id.mul_const' c).map_max.symm

end Right

end Mul

variable [MulOneClassₓ α]

@[to_additive]
theorem min_le_mul_of_one_le_right [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (hb : 1 ≤ b) : min a b ≤ a * b :=
  min_le_iff.2 <| Or.inl <| le_mul_of_one_le_right' hb

@[to_additive]
theorem min_le_mul_of_one_le_left [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) :
    min a b ≤ a * b :=
  min_le_iff.2 <| Or.inr <| le_mul_of_one_le_left' ha

@[to_additive]
theorem max_le_mul_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]
    {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : max a b ≤ a * b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

end CovariantClassMulLe

section LinearOrderedCancelCommMonoid

variable [LinearOrderedCancelCommMonoid α]

/-- Pullback a `linear_ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedCancelAddCommMonoid
      "Pullback a `linear_ordered_cancel_add_comm_monoid` under an injective map."]
def Function.Injective.linearOrderedCancelCommMonoid {β : Type _} [One β] [Mul β] [Pow β ℕ] [HasSup β] [HasInf β]
    (f : β → α) (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (hsup : ∀ x y, f (x⊔y) = max (f x) (f y))
    (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) : LinearOrderedCancelCommMonoid β :=
  { hf.LinearOrderedCommMonoid f one mul npow hsup hinf, hf.OrderedCancelCommMonoid f one mul npow with }

end LinearOrderedCancelCommMonoid

/-! ### Order dual -/


namespace OrderDual

@[to_additive]
instance [h : Mul α] : Mul αᵒᵈ :=
  h

@[to_additive]
instance [h : One α] : One αᵒᵈ :=
  h

@[to_additive]
instance [h : Semigroupₓ α] : Semigroupₓ αᵒᵈ :=
  h

@[to_additive]
instance [h : CommSemigroupₓ α] : CommSemigroupₓ αᵒᵈ :=
  h

@[to_additive]
instance [h : MulOneClassₓ α] : MulOneClassₓ αᵒᵈ :=
  h

@[to_additive]
instance [h : Monoidₓ α] : Monoidₓ αᵒᵈ :=
  h

@[to_additive]
instance [h : CommMonoidₓ α] : CommMonoidₓ αᵒᵈ :=
  h

@[to_additive]
instance [h : LeftCancelMonoid α] : LeftCancelMonoid αᵒᵈ :=
  h

@[to_additive]
instance [h : RightCancelMonoid α] : RightCancelMonoid αᵒᵈ :=
  h

@[to_additive]
instance [h : CancelMonoid α] : CancelMonoid αᵒᵈ :=
  h

@[to_additive]
instance [h : CancelCommMonoid α] : CancelCommMonoid αᵒᵈ :=
  h

instance [h : MulZeroClassₓ α] : MulZeroClassₓ αᵒᵈ :=
  h

instance [h : MulZeroOneClassₓ α] : MulZeroOneClassₓ αᵒᵈ :=
  h

instance [h : MonoidWithZeroₓ α] : MonoidWithZeroₓ αᵒᵈ :=
  h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ :=
  h

instance [h : CancelCommMonoidWithZero α] : CancelCommMonoidWithZero αᵒᵈ :=
  h

@[to_additive]
instance contravariant_class_mul_le [LE α] [Mul α] [c : ContravariantClass α α (· * ·) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariant_class_mul_le [LE α] [Mul α] [c : CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance contravariant_class_swap_mul_le [LE α] [Mul α] [c : ContravariantClass α α (swap (· * ·)) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariant_class_swap_mul_le [LE α] [Mul α] [c : CovariantClass α α (swap (· * ·)) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance contravariant_class_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariant_class_mul_lt [LT α] [Mul α] [c : CovariantClass α α (· * ·) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance contravariant_class_swap_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (swap (· * ·)) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariant_class_swap_mul_lt [LT α] [Mul α] [c : CovariantClass α α (swap (· * ·)) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance [OrderedCommMonoid α] : OrderedCommMonoid αᵒᵈ :=
  { OrderDual.partialOrder α, OrderDual.commMonoid with mul_le_mul_left := fun a b h c => mul_le_mul_left' h c }

@[to_additive OrderedCancelAddCommMonoid.to_contravariant_class]
instance OrderedCancelCommMonoid.to_contravariant_class [OrderedCancelCommMonoid α] :
    ContravariantClass αᵒᵈ αᵒᵈ Mul.mul
      LE.le where elim := fun a b c => OrderedCancelCommMonoid.le_of_mul_le_mul_left a c b

@[to_additive]
instance [OrderedCancelCommMonoid α] : OrderedCancelCommMonoid αᵒᵈ :=
  { OrderDual.orderedCommMonoid, OrderDual.cancelCommMonoid with
    le_of_mul_le_mul_left := fun a b c : α => le_of_mul_le_mul_left' }

@[to_additive]
instance [LinearOrderedCancelCommMonoid α] : LinearOrderedCancelCommMonoid αᵒᵈ :=
  { OrderDual.linearOrder α, OrderDual.orderedCancelCommMonoid with }

@[to_additive]
instance [LinearOrderedCommMonoid α] : LinearOrderedCommMonoid αᵒᵈ :=
  { OrderDual.linearOrder α, OrderDual.orderedCommMonoid with }

end OrderDual

namespace Prod

variable {M N : Type _}

@[to_additive]
instance [OrderedCommMonoid α] [OrderedCommMonoid β] : OrderedCommMonoid (α × β) :=
  { Prod.commMonoid, Prod.partialOrder _ _ with
    mul_le_mul_left := fun a b h c => ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩ }

@[to_additive]
instance [OrderedCancelCommMonoid M] [OrderedCancelCommMonoid N] : OrderedCancelCommMonoid (M × N) :=
  { Prod.cancelCommMonoid, Prod.orderedCommMonoid with
    le_of_mul_le_mul_left := fun a b c h => ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

@[to_additive]
instance [LE α] [LE β] [Mul α] [Mul β] [HasExistsMulOfLe α] [HasExistsMulOfLe β] : HasExistsMulOfLe (α × β) :=
  ⟨fun a b h =>
    let ⟨c, hc⟩ := exists_mul_of_le h.1
    let ⟨d, hd⟩ := exists_mul_of_le h.2
    ⟨(c, d), extₓ hc hd⟩⟩

@[to_additive]
instance [CanonicallyOrderedMonoid α] [CanonicallyOrderedMonoid β] : CanonicallyOrderedMonoid (α × β) :=
  { Prod.orderedCommMonoid, Prod.orderBot _ _, Prod.has_exists_mul_of_le with
    le_self_mul := fun a b => ⟨le_self_mul, le_self_mul⟩ }

end Prod

/-! ### `with_bot`/`with_top`-/


namespace WithTop

section One

variable [One α]

@[to_additive]
instance : One (WithTop α) :=
  ⟨(1 : α)⟩

@[simp, norm_cast, to_additive]
theorem coe_one : ((1 : α) : WithTop α) = 1 :=
  rfl

@[simp, norm_cast, to_additive]
theorem coe_eq_one {a : α} : (a : WithTop α) = 1 ↔ a = 1 :=
  coe_eq_coe

@[simp, to_additive]
protected theorem map_one {β} (f : α → β) : (1 : WithTop α).map f = (f 1 : WithTop β) :=
  rfl

@[simp, norm_cast, to_additive]
theorem one_eq_coe {a : α} : 1 = (a : WithTop α) ↔ a = 1 :=
  trans eq_comm coe_eq_one

@[simp, to_additive]
theorem top_ne_one : ⊤ ≠ (1 : WithTop α) :=
  fun.

@[simp, to_additive]
theorem one_ne_top : (1 : WithTop α) ≠ ⊤ :=
  fun.

instance [Zero α] [LE α] [ZeroLeOneClass α] : ZeroLeOneClass (WithTop α) :=
  ⟨some_le_some.2 zero_le_one⟩

end One

section Add

variable [Add α] {a b c d : WithTop α} {x y : α}

instance : Add (WithTop α) :=
  ⟨fun o₁ o₂ => o₁.bind fun a => o₂.map <| (· + ·) a⟩

@[norm_cast]
theorem coe_add : ((x + y : α) : WithTop α) = x + y :=
  rfl

@[norm_cast]
theorem coe_bit0 : ((bit0 x : α) : WithTop α) = bit0 x :=
  rfl

@[norm_cast]
theorem coe_bit1 [One α] {a : α} : ((bit1 a : α) : WithTop α) = bit1 a :=
  rfl

@[simp]
theorem top_add (a : WithTop α) : ⊤ + a = ⊤ :=
  rfl

@[simp]
theorem add_top (a : WithTop α) : a + ⊤ = ⊤ := by
  cases a <;> rfl

@[simp]
theorem add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  cases a <;> cases b <;> simp [← none_eq_top, ← some_eq_coe, WithTop.coe_add, WithZero.coe_add]

theorem add_ne_top : a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ :=
  add_eq_top.Not.trans not_or_distrib

theorem add_lt_top [PartialOrderₓ α] {a b : WithTop α} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by
  simp_rw [lt_top_iff_ne_top, add_ne_top]

theorem add_eq_coe : ∀ {a b : WithTop α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | none, b, c => by
    simp [← none_eq_top]
  | some a, none, c => by
    simp [← none_eq_top]
  | some a, some b, c => by
    simp only [← some_eq_coe, coe_add, ← coe_eq_coe, ← exists_and_distrib_left, ← exists_eq_left]

@[simp]
theorem add_coe_eq_top_iff {x : WithTop α} {y : α} : x + y = ⊤ ↔ x = ⊤ := by
  induction x using WithTop.recTopCoe <;> simp [coe_add, -WithZero.coe_add]

@[simp]
theorem coe_add_eq_top_iff {y : WithTop α} : ↑x + y = ⊤ ↔ y = ⊤ := by
  induction y using WithTop.recTopCoe <;> simp [coe_add, -WithZero.coe_add]

instance covariant_class_add_le [LE α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    CovariantClass (WithTop α) (WithTop α) (· + ·) (· ≤ ·) :=
  ⟨fun a b c h => by
    cases a <;>
      cases c <;>
        try
          exact le_top
    rcases le_coe_iff.1 h with ⟨b, rfl, h'⟩
    exact coe_le_coe.2 (add_le_add_left (coe_le_coe.1 h) _)⟩

instance covariant_class_swap_add_le [LE α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    CovariantClass (WithTop α) (WithTop α) (swap (· + ·)) (· ≤ ·) :=
  ⟨fun a b c h => by
    cases a <;>
      cases c <;>
        try
          exact le_top
    rcases le_coe_iff.1 h with ⟨b, rfl, h'⟩
    exact coe_le_coe.2 (add_le_add_right (coe_le_coe.1 h) _)⟩

instance contravariant_class_add_lt [LT α] [ContravariantClass α α (· + ·) (· < ·)] :
    ContravariantClass (WithTop α) (WithTop α) (· + ·) (· < ·) :=
  ⟨fun a b c h => by
    induction a using WithTop.recTopCoe
    · exact (not_none_lt _ h).elim
      
    induction b using WithTop.recTopCoe
    · exact (not_none_lt _ h).elim
      
    induction c using WithTop.recTopCoe
    · exact coe_lt_top _
      
    · exact coe_lt_coe.2 (lt_of_add_lt_add_left <| coe_lt_coe.1 h)
      ⟩

instance contravariant_class_swap_add_lt [LT α] [ContravariantClass α α (swap (· + ·)) (· < ·)] :
    ContravariantClass (WithTop α) (WithTop α) (swap (· + ·)) (· < ·) :=
  ⟨fun a b c h => by
    cases a <;>
      cases b <;>
        try
          exact (not_none_lt _ h).elim
    cases c
    · exact coe_lt_top _
      
    · exact coe_lt_coe.2 (lt_of_add_lt_add_right <| coe_lt_coe.1 h)
      ⟩

protected theorem le_of_add_le_add_left [LE α] [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊤)
    (h : a + b ≤ a + c) : b ≤ c := by
  lift a to α using ha
  induction c using WithTop.recTopCoe
  · exact le_top
    
  induction b using WithTop.recTopCoe
  · exact (not_top_le_coe _ h).elim
    
  simp only [coe_add, ← coe_le_coe] at h⊢
  exact le_of_add_le_add_left h

protected theorem le_of_add_le_add_right [LE α] [ContravariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊤)
    (h : b + a ≤ c + a) : b ≤ c := by
  lift a to α using ha
  cases c
  · exact le_top
    
  cases b
  · exact (not_top_le_coe _ h).elim
    
  · exact coe_le_coe.2 (le_of_add_le_add_right <| coe_le_coe.1 h)
    

protected theorem add_lt_add_left [LT α] [CovariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊤) (h : b < c) :
    a + b < a + c := by
  lift a to α using ha
  rcases lt_iff_exists_coe.1 h with ⟨b, rfl, h'⟩
  cases c
  · exact coe_lt_top _
    
  · exact coe_lt_coe.2 (add_lt_add_left (coe_lt_coe.1 h) _)
    

protected theorem add_lt_add_right [LT α] [CovariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊤) (h : b < c) :
    b + a < c + a := by
  lift a to α using ha
  rcases lt_iff_exists_coe.1 h with ⟨b, rfl, h'⟩
  cases c
  · exact coe_lt_top _
    
  · exact coe_lt_coe.2 (add_lt_add_right (coe_lt_coe.1 h) _)
    

protected theorem add_le_add_iff_left [LE α] [CovariantClass α α (· + ·) (· ≤ ·)]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊤) : a + b ≤ a + c ↔ b ≤ c :=
  ⟨WithTop.le_of_add_le_add_left ha, fun h => add_le_add_left h a⟩

protected theorem add_le_add_iff_right [LE α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊤) : b + a ≤ c + a ↔ b ≤ c :=
  ⟨WithTop.le_of_add_le_add_right ha, fun h => add_le_add_right h a⟩

protected theorem add_lt_add_iff_left [LT α] [CovariantClass α α (· + ·) (· < ·)]
    [ContravariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊤) : a + b < a + c ↔ b < c :=
  ⟨lt_of_add_lt_add_left, WithTop.add_lt_add_left ha⟩

protected theorem add_lt_add_iff_right [LT α] [CovariantClass α α (swap (· + ·)) (· < ·)]
    [ContravariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊤) : b + a < c + a ↔ b < c :=
  ⟨lt_of_add_lt_add_right, WithTop.add_lt_add_right ha⟩

protected theorem add_lt_add_of_le_of_lt [Preorderₓ α] [CovariantClass α α (· + ·) (· < ·)]
    [CovariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊤) (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
  (WithTop.add_lt_add_left ha hcd).trans_le <| add_le_add_right hab _

protected theorem add_lt_add_of_lt_of_le [Preorderₓ α] [CovariantClass α α (· + ·) (· ≤ ·)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] (hc : c ≠ ⊤) (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
  (WithTop.add_lt_add_right hc hab).trans_le <| add_le_add_left hcd _

end Add

instance [AddSemigroupₓ α] : AddSemigroupₓ (WithTop α) :=
  { WithTop.hasAdd with
    add_assoc := by
      repeat'
          refine' WithTop.recTopCoe _ _ <;>
            try
              intro <;>
        simp [WithTop.coe_add, ← add_assocₓ] }

instance [AddCommSemigroupₓ α] : AddCommSemigroupₓ (WithTop α) :=
  { WithTop.addSemigroup with
    add_comm := by
      repeat'
          refine' WithTop.recTopCoe _ _ <;>
            try
              intro <;>
        simp [WithTop.coe_add, ← add_commₓ] }

instance [AddZeroClassₓ α] : AddZeroClassₓ (WithTop α) :=
  { WithTop.hasZero, WithTop.hasAdd with
    zero_add := by
      refine' WithTop.recTopCoe _ _
      · simp
        
      · intro
        rw [← WithTop.coe_zero, ← WithTop.coe_add, zero_addₓ]
        ,
    add_zero := by
      refine' WithTop.recTopCoe _ _
      · simp
        
      · intro
        rw [← WithTop.coe_zero, ← WithTop.coe_add, add_zeroₓ]
         }

instance [AddMonoidₓ α] : AddMonoidₓ (WithTop α) :=
  { WithTop.addZeroClass, WithTop.hasZero, WithTop.addSemigroup with }

instance [AddCommMonoidₓ α] : AddCommMonoidₓ (WithTop α) :=
  { WithTop.addMonoid, WithTop.addCommSemigroup with }

instance [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithTop α) :=
  { WithTop.partialOrder, WithTop.addCommMonoid with
    add_le_add_left := by
      rintro a b h (_ | c)
      · simp [← none_eq_top]
        
      rcases b with (_ | b)
      · simp [← none_eq_top]
        
      rcases le_coe_iff.1 h with ⟨a, rfl, h⟩
      simp only [← some_eq_coe, coe_add, ← coe_le_coe] at h⊢
      exact add_le_add_left h c }

instance [LinearOrderedAddCommMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) :=
  { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid, Option.nontrivial with
    top_add' := WithTop.top_add }

instance [LE α] [Add α] [HasExistsAddOfLe α] : HasExistsAddOfLe (WithTop α) :=
  ⟨fun a b =>
    match a, b with
    | ⊤, ⊤ => by
      simp
    | (a : α), ⊤ => fun _ => ⟨⊤, rfl⟩
    | (a : α), (b : α) => fun h => by
      obtain ⟨c, rfl⟩ := exists_add_of_le (WithTop.coe_le_coe.1 h)
      exact ⟨c, rfl⟩
    | ⊤, (b : α) => fun h => (not_top_le_coe _ h).elim⟩

instance [CanonicallyOrderedAddMonoid α] : CanonicallyOrderedAddMonoid (WithTop α) :=
  { WithTop.orderBot, WithTop.orderedAddCommMonoid, WithTop.has_exists_add_of_le with
    le_self_add := fun a b =>
      match a, b with
      | ⊤, ⊤ => le_rfl
      | (a : α), ⊤ => le_top
      | (a : α), (b : α) => WithTop.coe_le_coe.2 le_self_add
      | ⊤, (b : α) => le_rfl }

instance [CanonicallyLinearOrderedAddMonoid α] : CanonicallyLinearOrderedAddMonoid (WithTop α) :=
  { WithTop.canonicallyOrderedAddMonoid, WithTop.linearOrder with }

/-- Coercion from `α` to `with_top α` as an `add_monoid_hom`. -/
def coeAddHom [AddMonoidₓ α] : α →+ WithTop α :=
  ⟨coe, rfl, fun _ _ => rfl⟩

@[simp]
theorem coe_coe_add_hom [AddMonoidₓ α] : ⇑(coeAddHom : α →+ WithTop α) = coe :=
  rfl

@[simp]
theorem zero_lt_top [OrderedAddCommMonoid α] : (0 : WithTop α) < ⊤ :=
  coe_lt_top 0

@[simp, norm_cast]
theorem zero_lt_coe [OrderedAddCommMonoid α] (a : α) : (0 : WithTop α) < a ↔ 0 < a :=
  coe_lt_coe

/-- A version of `with_top.map` for `one_hom`s. -/
@[to_additive "A version of `with_top.map` for `zero_hom`s", simps (config := { fullyApplied := false })]
protected def _root_.one_hom.with_top_map {M N : Type _} [One M] [One N] (f : OneHom M N) :
    OneHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_one' := by
    rw [WithTop.map_one, map_one, coe_one]

/-- A version of `with_top.map` for `add_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def _root_.add_hom.with_top_map {M N : Type _} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_add' := fun x y =>
    match x, y with
    | ⊤, y => by
      rw [top_add, map_top, top_add]
    | x, ⊤ => by
      rw [add_top, map_top, add_top]
    | (x : M), (y : M) => by
      simp only [coe_add, ← map_coe, ← map_add]

/-- A version of `with_top.map` for `add_monoid_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def _root_.add_monoid_hom.with_top_map {M N : Type _} [AddZeroClassₓ M] [AddZeroClassₓ N] (f : M →+ N) :
    WithTop M →+ WithTop N :=
  { f.toZeroHom.with_top_map, f.toAddHom.with_top_map with toFun := WithTop.map f }

end WithTop

namespace WithBot

@[to_additive]
instance [One α] : One (WithBot α) :=
  WithTop.hasOne

instance [Add α] : Add (WithBot α) :=
  WithTop.hasAdd

instance [AddSemigroupₓ α] : AddSemigroupₓ (WithBot α) :=
  WithTop.addSemigroup

instance [AddCommSemigroupₓ α] : AddCommSemigroupₓ (WithBot α) :=
  WithTop.addCommSemigroup

instance [AddZeroClassₓ α] : AddZeroClassₓ (WithBot α) :=
  WithTop.addZeroClass

instance [AddMonoidₓ α] : AddMonoidₓ (WithBot α) :=
  WithTop.addMonoid

instance [AddCommMonoidₓ α] : AddCommMonoidₓ (WithBot α) :=
  WithTop.addCommMonoid

instance [Zero α] [One α] [LE α] [ZeroLeOneClass α] : ZeroLeOneClass (WithBot α) :=
  ⟨some_le_some.2 zero_le_one⟩

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
@[to_additive]
theorem coe_one [One α] : ((1 : α) : WithBot α) = 1 :=
  rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
@[to_additive]
theorem coe_eq_one [One α] {a : α} : (a : WithBot α) = 1 ↔ a = 1 :=
  WithTop.coe_eq_one

@[to_additive]
protected theorem map_one {β} [One α] (f : α → β) : (1 : WithBot α).map f = (f 1 : WithBot β) :=
  rfl

section Add

variable [Add α] {a b c d : WithBot α} {x y : α}

-- `norm_cast` proves those lemmas, because `with_top`/`with_bot` are reducible
theorem coe_add (a b : α) : ((a + b : α) : WithBot α) = a + b :=
  rfl

theorem coe_bit0 : ((bit0 x : α) : WithBot α) = bit0 x :=
  rfl

theorem coe_bit1 [One α] {a : α} : ((bit1 a : α) : WithBot α) = bit1 a :=
  rfl

@[simp]
theorem bot_add (a : WithBot α) : ⊥ + a = ⊥ :=
  rfl

@[simp]
theorem add_bot (a : WithBot α) : a + ⊥ = ⊥ := by
  cases a <;> rfl

@[simp]
theorem add_eq_bot : a + b = ⊥ ↔ a = ⊥ ∨ b = ⊥ :=
  WithTop.add_eq_top

theorem add_ne_bot : a + b ≠ ⊥ ↔ a ≠ ⊥ ∧ b ≠ ⊥ :=
  WithTop.add_ne_top

theorem bot_lt_add [PartialOrderₓ α] {a b : WithBot α} : ⊥ < a + b ↔ ⊥ < a ∧ ⊥ < b :=
  @WithTop.add_lt_top αᵒᵈ _ _ _ _

theorem add_eq_coe : a + b = x ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = x :=
  WithTop.add_eq_coe

@[simp]
theorem add_coe_eq_bot_iff : a + y = ⊥ ↔ a = ⊥ :=
  WithTop.add_coe_eq_top_iff

@[simp]
theorem coe_add_eq_bot_iff : ↑x + b = ⊥ ↔ b = ⊥ :=
  WithTop.coe_add_eq_top_iff

variable [Preorderₓ α]

instance covariant_class_add_le [CovariantClass α α (· + ·) (· ≤ ·)] :
    CovariantClass (WithBot α) (WithBot α) (· + ·) (· ≤ ·) :=
  @OrderDual.covariant_class_add_le (WithTop αᵒᵈ) _ _ _

instance covariant_class_swap_add_le [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    CovariantClass (WithBot α) (WithBot α) (swap (· + ·)) (· ≤ ·) :=
  @OrderDual.covariant_class_swap_add_le (WithTop αᵒᵈ) _ _ _

instance contravariant_class_add_lt [ContravariantClass α α (· + ·) (· < ·)] :
    ContravariantClass (WithBot α) (WithBot α) (· + ·) (· < ·) :=
  @OrderDual.contravariant_class_add_lt (WithTop αᵒᵈ) _ _ _

instance contravariant_class_swap_add_lt [ContravariantClass α α (swap (· + ·)) (· < ·)] :
    ContravariantClass (WithBot α) (WithBot α) (swap (· + ·)) (· < ·) :=
  @OrderDual.contravariant_class_swap_add_lt (WithTop αᵒᵈ) _ _ _

protected theorem le_of_add_le_add_left [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊥) (h : a + b ≤ a + c) :
    b ≤ c :=
  @WithTop.le_of_add_le_add_left αᵒᵈ _ _ _ _ _ _ ha h

protected theorem le_of_add_le_add_right [ContravariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊥)
    (h : b + a ≤ c + a) : b ≤ c :=
  @WithTop.le_of_add_le_add_right αᵒᵈ _ _ _ _ _ _ ha h

protected theorem add_lt_add_left [CovariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊥) (h : b < c) : a + b < a + c :=
  @WithTop.add_lt_add_left αᵒᵈ _ _ _ _ _ _ ha h

protected theorem add_lt_add_right [CovariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊥) (h : b < c) :
    b + a < c + a :=
  @WithTop.add_lt_add_right αᵒᵈ _ _ _ _ _ _ ha h

protected theorem add_le_add_iff_left [CovariantClass α α (· + ·) (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)]
    (ha : a ≠ ⊥) : a + b ≤ a + c ↔ b ≤ c :=
  ⟨WithBot.le_of_add_le_add_left ha, fun h => add_le_add_left h a⟩

protected theorem add_le_add_iff_right [CovariantClass α α (swap (· + ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊥) : b + a ≤ c + a ↔ b ≤ c :=
  ⟨WithBot.le_of_add_le_add_right ha, fun h => add_le_add_right h a⟩

protected theorem add_lt_add_iff_left [CovariantClass α α (· + ·) (· < ·)] [ContravariantClass α α (· + ·) (· < ·)]
    (ha : a ≠ ⊥) : a + b < a + c ↔ b < c :=
  ⟨lt_of_add_lt_add_left, WithBot.add_lt_add_left ha⟩

protected theorem add_lt_add_iff_right [CovariantClass α α (swap (· + ·)) (· < ·)]
    [ContravariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊥) : b + a < c + a ↔ b < c :=
  ⟨lt_of_add_lt_add_right, WithBot.add_lt_add_right ha⟩

protected theorem add_lt_add_of_le_of_lt [CovariantClass α α (· + ·) (· < ·)]
    [CovariantClass α α (swap (· + ·)) (· ≤ ·)] (hb : b ≠ ⊥) (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
  @WithTop.add_lt_add_of_le_of_lt αᵒᵈ _ _ _ _ _ _ _ _ hb hab hcd

protected theorem add_lt_add_of_lt_of_le [CovariantClass α α (· + ·) (· ≤ ·)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] (hd : d ≠ ⊥) (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
  @WithTop.add_lt_add_of_lt_of_le αᵒᵈ _ _ _ _ _ _ _ _ hd hab hcd

end Add

instance [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithBot α) :=
  { WithBot.partialOrder, WithBot.addCommMonoid with add_le_add_left := fun a b h c => add_le_add_left h c }

instance [LinearOrderedAddCommMonoid α] : LinearOrderedAddCommMonoid (WithBot α) :=
  { WithBot.linearOrder, WithBot.orderedAddCommMonoid with }

end WithBot

/-! ### `additive`/`multiplicative` -/


section TypeTags

instance : ∀ [LE α], LE (Multiplicative α) :=
  id

instance : ∀ [LE α], LE (Additive α) :=
  id

instance : ∀ [LT α], LT (Multiplicative α) :=
  id

instance : ∀ [LT α], LT (Additive α) :=
  id

instance : ∀ [Preorderₓ α], Preorderₓ (Multiplicative α) :=
  id

instance : ∀ [Preorderₓ α], Preorderₓ (Additive α) :=
  id

instance : ∀ [PartialOrderₓ α], PartialOrderₓ (Multiplicative α) :=
  id

instance : ∀ [PartialOrderₓ α], PartialOrderₓ (Additive α) :=
  id

instance : ∀ [LinearOrderₓ α], LinearOrderₓ (Multiplicative α) :=
  id

instance : ∀ [LinearOrderₓ α], LinearOrderₓ (Additive α) :=
  id

instance [LE α] : ∀ [OrderBot α], OrderBot (Multiplicative α) :=
  id

instance [LE α] : ∀ [OrderBot α], OrderBot (Additive α) :=
  id

instance [LE α] : ∀ [OrderTop α], OrderTop (Multiplicative α) :=
  id

instance [LE α] : ∀ [OrderTop α], OrderTop (Additive α) :=
  id

instance [LE α] : ∀ [BoundedOrder α], BoundedOrder (Multiplicative α) :=
  id

instance [LE α] : ∀ [BoundedOrder α], BoundedOrder (Additive α) :=
  id

instance [OrderedAddCommMonoid α] : OrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.partialOrder, Multiplicative.commMonoid with
    mul_le_mul_left := @OrderedAddCommMonoid.add_le_add_left α _ }

instance [OrderedCommMonoid α] : OrderedAddCommMonoid (Additive α) :=
  { Additive.partialOrder, Additive.addCommMonoid with add_le_add_left := @OrderedCommMonoid.mul_le_mul_left α _ }

instance [OrderedCancelAddCommMonoid α] : OrderedCancelCommMonoid (Multiplicative α) :=
  { Multiplicative.leftCancelSemigroup, Multiplicative.orderedCommMonoid with
    le_of_mul_le_mul_left := @OrderedCancelAddCommMonoid.le_of_add_le_add_left α _ }

instance [OrderedCancelCommMonoid α] : OrderedCancelAddCommMonoid (Additive α) :=
  { Additive.addLeftCancelSemigroup, Additive.orderedAddCommMonoid with
    le_of_add_le_add_left := @OrderedCancelCommMonoid.le_of_mul_le_mul_left α _ }

instance [LinearOrderedAddCommMonoid α] : LinearOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommMonoid with }

instance [LinearOrderedCommMonoid α] : LinearOrderedAddCommMonoid (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommMonoid with }

instance [Add α] [LE α] [HasExistsAddOfLe α] : HasExistsMulOfLe (Multiplicative α) :=
  ⟨@exists_add_of_le α _ _ _⟩

instance [Mul α] [LE α] [HasExistsMulOfLe α] : HasExistsAddOfLe (Additive α) :=
  ⟨@exists_mul_of_le α _ _ _⟩

instance [CanonicallyOrderedAddMonoid α] : CanonicallyOrderedMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid, Multiplicative.orderBot, Multiplicative.has_exists_mul_of_le with
    le_self_mul := @le_self_add α _ }

instance [CanonicallyOrderedMonoid α] : CanonicallyOrderedAddMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid, Additive.orderBot, Additive.has_exists_add_of_le with
    le_self_add := @le_self_mul α _ }

instance [CanonicallyLinearOrderedAddMonoid α] : CanonicallyLinearOrderedMonoid (Multiplicative α) :=
  { Multiplicative.canonicallyOrderedMonoid, Multiplicative.linearOrder with }

instance [CanonicallyLinearOrderedMonoid α] : CanonicallyLinearOrderedAddMonoid (Additive α) :=
  { Additive.canonicallyOrderedAddMonoid, Additive.linearOrder with }

namespace Additive

variable [Preorderₓ α]

@[simp]
theorem of_mul_le {a b : α} : ofMul a ≤ ofMul b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem of_mul_lt {a b : α} : ofMul a < ofMul b ↔ a < b :=
  Iff.rfl

@[simp]
theorem to_mul_le {a b : Additive α} : toMul a ≤ toMul b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem to_mul_lt {a b : Additive α} : toMul a < toMul b ↔ a < b :=
  Iff.rfl

end Additive

namespace Multiplicative

variable [Preorderₓ α]

@[simp]
theorem of_add_le {a b : α} : ofAdd a ≤ ofAdd b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem of_add_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b :=
  Iff.rfl

@[simp]
theorem to_add_le {a b : Multiplicative α} : toAdd a ≤ toAdd b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem to_add_lt {a b : Multiplicative α} : toAdd a < toAdd b ↔ a < b :=
  Iff.rfl

end Multiplicative

end TypeTags

namespace WithZero

attribute [local semireducible] WithZero

variable [Add α]

/-- Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative. -/
def toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α) :=
  MulEquiv.refl _

@[simp]
theorem to_mul_bot_zero : toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥ :=
  rfl

@[simp]
theorem to_mul_bot_coe (x : Multiplicative α) : toMulBot ↑x = Multiplicative.ofAdd (x.toAdd : WithBot α) :=
  rfl

@[simp]
theorem to_mul_bot_symm_bot : toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0 :=
  rfl

@[simp]
theorem to_mul_bot_coe_of_add (x : α) : toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x :=
  rfl

variable [Preorderₓ α] (a b : WithZero (Multiplicative α))

theorem to_mul_bot_strict_mono : StrictMono (@toMulBot α _) := fun x y => id

@[simp]
theorem to_mul_bot_le : toMulBot a ≤ toMulBot b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem to_mul_bot_lt : toMulBot a < toMulBot b ↔ a < b :=
  Iff.rfl

end WithZero

/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `order_iso.mul_left` when working in an ordered group. -/
@[to_additive
      "The order embedding sending `b` to `a + b`, for some fixed `a`.\n  See also `order_iso.add_left` when working in an additive ordered group.",
  simps]
def OrderEmbedding.mulLeft {α : Type _} [Mul α] [LinearOrderₓ α] [CovariantClass α α (· * ·) (· < ·)] (m : α) :
    α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) fun a b w => mul_lt_mul_left' w m

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `order_iso.mul_right` when working in an ordered group. -/
@[to_additive
      "The order embedding sending `b` to `b + a`, for some fixed `a`.\n  See also `order_iso.add_right` when working in an additive ordered group.",
  simps]
def OrderEmbedding.mulRight {α : Type _} [Mul α] [LinearOrderₓ α] [CovariantClass α α (swap (· * ·)) (· < ·)] (m : α) :
    α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) fun a b w => mul_lt_mul_right' w m

