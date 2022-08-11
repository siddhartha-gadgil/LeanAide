/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.Group.InjSurj
import Mathbin.Algebra.GroupWithZero.Defs
import Mathbin.Algebra.Hom.Units
import Mathbin.Logic.Nontrivial
import Mathbin.GroupTheory.GroupAction.Units

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `group_with_zero` and `comm_group_with_zero`.
To reduce import dependencies, the type-classes themselves are in
`algebra.group_with_zero.defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/


open Classical

open Function

variable {M₀ G₀ M₀' G₀' : Type _}

section

section MulZeroClassₓ

variable [MulZeroClassₓ M₀] {a b : M₀}

/-- Pullback a `mul_zero_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0)
    (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroClassₓ M₀' where
  mul := (· * ·)
  zero := 0
  zero_mul := fun a =>
    hf <| by
      simp only [← mul, ← zero, ← zero_mul]
  mul_zero := fun a =>
    hf <| by
      simp only [← mul, ← zero, ← mul_zero]

/-- Pushforward a `mul_zero_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0)
    (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroClassₓ M₀' where
  mul := (· * ·)
  zero := 0
  mul_zero :=
    hf.forall.2 fun x => by
      simp only [zero, mul, ← mul_zero]
  zero_mul :=
    hf.forall.2 fun x => by
      simp only [zero, mul, ← zero_mul]

theorem mul_eq_zero_of_left (h : a = 0) (b : M₀) : a * b = 0 :=
  h.symm ▸ zero_mul b

theorem mul_eq_zero_of_right (a : M₀) (h : b = 0) : a * b = 0 :=
  h.symm ▸ mul_zero a

theorem left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 :=
  mt fun h => mul_eq_zero_of_left h b

theorem right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 :=
  mt (mul_eq_zero_of_right a)

theorem ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

theorem mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) : a * b = 0 :=
  if ha : a = 0 then by
    rw [ha, zero_mul]
  else by
    rw [h ha, mul_zero]

/-- To match `one_mul_eq_id`. -/
theorem zero_mul_eq_const : (· * ·) (0 : M₀) = Function.const _ 0 :=
  funext zero_mul

/-- To match `mul_one_eq_id`. -/
theorem mul_zero_eq_const : (· * (0 : M₀)) = Function.const _ 0 :=
  funext mul_zero

end MulZeroClassₓ

/-- Pushforward a `no_zero_divisors` instance along an injective function. -/
protected theorem Function.Injective.no_zero_divisors [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀'] [NoZeroDivisors M₀']
    (f : M₀ → M₀') (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) : NoZeroDivisors M₀ :=
  { eq_zero_or_eq_zero_of_mul_eq_zero := fun x y H =>
      have : f x * f y = 0 := by
        rw [← mul, H, zero]
      (eq_zero_or_eq_zero_of_mul_eq_zero this).imp
        (fun H =>
          hf <| by
            rwa [zero])
        fun H =>
        hf <| by
          rwa [zero] }

theorem eq_zero_of_mul_self_eq_zero [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a : M₀} (h : a * a = 0) : a = 0 :=
  (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id

section

variable [MulZeroClassₓ M₀] [NoZeroDivisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero, fun o => o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by
  rw [eq_comm, mul_eq_zero]

/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  (not_congr mul_eq_zero).trans not_or_distrib

@[field_simps]
theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  mul_ne_zero_iff.2 ⟨ha, hb⟩

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
  mul_eq_zero.trans <| (or_comm _ _).trans mul_eq_zero.symm

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 :=
  not_congr mul_eq_zero_comm

theorem mul_self_eq_zero : a * a = 0 ↔ a = 0 := by
  simp

theorem zero_eq_mul_self : 0 = a * a ↔ a = 0 := by
  simp

theorem mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 :=
  not_congr mul_self_eq_zero

theorem zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 :=
  not_congr zero_eq_mul_self

end

end

section

variable [MulZeroOneClassₓ M₀]

/-- Pullback a `mul_zero_one_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀' → M₀) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroOneClassₓ M₀' :=
  { hf.MulZeroClass f zero mul, hf.MulOneClass f one mul with }

/-- Pushforward a `mul_zero_one_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀ → M₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroOneClassₓ M₀' :=
  { hf.MulZeroClass f zero mul, hf.MulOneClass f one mul with }

/-- In a monoid with zero, if zero equals one, then zero is the only element. -/
theorem eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 := by
  rw [← mul_oneₓ a, ← h, mul_zero]

/-- In a monoid with zero, if zero equals one, then zero is the unique element.

Somewhat arbitrarily, we define the default element to be `0`.
All other elements will be provably equal to it, but not necessarily definitionally equal. -/
def uniqueOfZeroEqOne (h : (0 : M₀) = 1) : Unique M₀ where
  default := 0
  uniq := eq_zero_of_zero_eq_one h

/-- In a monoid with zero, zero equals one if and only if all elements of that semiring
are equal. -/
theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ Subsingleton M₀ :=
  ⟨fun h => @Unique.subsingleton _ (uniqueOfZeroEqOne h), fun h => @Subsingleton.elimₓ _ h _ _⟩

alias subsingleton_iff_zero_eq_one ↔ subsingleton_of_zero_eq_one _

theorem eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b :=
  @Subsingleton.elimₓ _ (subsingleton_of_zero_eq_one h) a b

/-- In a monoid with zero, either zero and one are nonequal, or zero is the only element. -/
theorem zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ ∀ a : M₀, a = 0 :=
  not_or_of_imp eq_zero_of_zero_eq_one

end

section

variable [MulZeroOneClassₓ M₀] [Nontrivial M₀] {a b : M₀}

/-- In a nontrivial monoid with zero, zero and one are different. -/
@[simp]
theorem zero_ne_one : 0 ≠ (1 : M₀) := by
  intro h
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩
  apply hx
  calc x = 1 * x := by
      rw [one_mulₓ]_ = 0 := by
      rw [← h, zero_mul]_ = 1 * y := by
      rw [← h, zero_mul]_ = y := by
      rw [one_mulₓ]

@[simp]
theorem one_ne_zero : (1 : M₀) ≠ 0 :=
  zero_ne_one.symm

theorem ne_zero_of_eq_one {a : M₀} (h : a = 1) : a ≠ 0 :=
  calc
    a = 1 := h
    _ ≠ 0 := one_ne_zero
    

theorem left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 :=
  left_ne_zero_of_mul <| ne_zero_of_eq_one h

theorem right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 :=
  right_ne_zero_of_mul <| ne_zero_of_eq_one h

/-- Pullback a `nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
protected theorem pullback_nonzero [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' :=
  ⟨⟨0, 1,
      mt (congr_arg f) <| by
        rw [zero, one]
        exact zero_ne_one⟩⟩

end

section SemigroupWithZeroₓ

/-- Pullback a `semigroup_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semigroupWithZero [Zero M₀'] [Mul M₀'] [SemigroupWithZeroₓ M₀] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) : SemigroupWithZeroₓ M₀' :=
  { hf.MulZeroClass f zero mul, ‹Zero M₀'›, hf.Semigroup f mul with }

/-- Pushforward a `semigroup_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.semigroupWithZero [SemigroupWithZeroₓ M₀] [Zero M₀'] [Mul M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) : SemigroupWithZeroₓ M₀' :=
  { hf.MulZeroClass f zero mul, ‹Zero M₀'›, hf.Semigroup f mul with }

end SemigroupWithZeroₓ

section MonoidWithZeroₓ

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [MonoidWithZeroₓ M₀]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : MonoidWithZeroₓ M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with }

/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [MonoidWithZeroₓ M₀]
    (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : MonoidWithZeroₓ M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with }

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [CommMonoidWithZero M₀]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CommMonoidWithZero M₀' :=
  { hf.CommMonoid f one mul npow, hf.MulZeroClass f zero mul with }

/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [CommMonoidWithZero M₀]
    (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CommMonoidWithZero M₀' :=
  { hf.CommMonoid f one mul npow, hf.MulZeroClass f zero mul with }

variable [MonoidWithZeroₓ M₀]

namespace Units

/-- An element of the unit group of a nonzero monoid with zero represented as an element
    of the monoid is nonzero. -/
@[simp]
theorem ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) ≠ 0 :=
  left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `units.ne_zero` in the next two lemmas because we don't assume
-- `nonzero M₀`.
@[simp]
theorem mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
  ⟨fun h => by
    simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩

@[simp]
theorem mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
  ⟨fun h => by
    simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right u⟩

end Units

namespace IsUnit

theorem ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a ≠ 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.ne_zero

theorem mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.mul_right_eq_zero

theorem mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0 :=
  let ⟨u, hu⟩ := hb
  hu ▸ u.mul_left_eq_zero

end IsUnit

@[simp]
theorem is_unit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1 :=
  ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by
    rwa [zero_mul] at a0, fun h => @is_unit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

@[simp]
theorem not_is_unit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀) :=
  mt is_unit_zero_iff.1 zero_ne_one

namespace Ring

open Classical

/-- Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather
than partially) defined inverse function for some purposes, including for calculus.

Note that while this is in the `ring` namespace for brevity, it requires the weaker assumption
`monoid_with_zero M₀` instead of `ring M₀`. -/
noncomputable def inverse : M₀ → M₀ := fun x => if h : IsUnit x then ((h.Unit⁻¹ : M₀ˣ) : M₀) else 0

/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
@[simp]
theorem inverse_unit (u : M₀ˣ) : inverse (u : M₀) = (u⁻¹ : M₀ˣ) := by
  simp only [← Units.is_unit, ← inverse, ← dif_pos]
  exact Units.inv_unique rfl

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp]
theorem inverse_non_unit (x : M₀) (h : ¬IsUnit x) : inverse x = 0 :=
  dif_neg h

theorem mul_inverse_cancel (x : M₀) (h : IsUnit x) : x * inverse x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.mul_inv]

theorem inverse_mul_cancel (x : M₀) (h : IsUnit x) : inverse x * x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.inv_mul]

theorem mul_inverse_cancel_right (x y : M₀) (h : IsUnit x) : y * x * inverse x = y := by
  rw [mul_assoc, mul_inverse_cancel x h, mul_oneₓ]

theorem inverse_mul_cancel_right (x y : M₀) (h : IsUnit x) : y * inverse x * x = y := by
  rw [mul_assoc, inverse_mul_cancel x h, mul_oneₓ]

theorem mul_inverse_cancel_left (x y : M₀) (h : IsUnit x) : x * (inverse x * y) = y := by
  rw [← mul_assoc, mul_inverse_cancel x h, one_mulₓ]

theorem inverse_mul_cancel_left (x y : M₀) (h : IsUnit x) : inverse x * (x * y) = y := by
  rw [← mul_assoc, inverse_mul_cancel x h, one_mulₓ]

variable (M₀)

@[simp]
theorem inverse_one : inverse (1 : M₀) = 1 :=
  inverse_unit 1

@[simp]
theorem inverse_zero : inverse (0 : M₀) = 0 := by
  nontriviality
  exact inverse_non_unit _ not_is_unit_zero

variable {M₀}

theorem mul_inverse_rev' {a b : M₀} (h : Commute a b) : inverse (a * b) = inverse b * inverse a := by
  by_cases' hab : IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.is_unit_mul_iff.mp hab
    rw [← Units.coe_mul, inverse_unit, inverse_unit, inverse_unit, ← Units.coe_mul, mul_inv_rev]
    
  obtain ha | hb := not_and_distrib.mp (mt h.is_unit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
    
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]
    

theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) : Ring.inverse (a * b) = inverse b * inverse a :=
  mul_inverse_rev' (Commute.all _ _)

end Ring

theorem IsUnit.ring_inverse {a : M₀} : IsUnit a → IsUnit (Ring.inverse a)
  | ⟨u, hu⟩ => hu ▸ ⟨u⁻¹, (Ring.inverse_unit u).symm⟩

@[simp]
theorem is_unit_ring_inverse {a : M₀} : IsUnit (Ring.inverse a) ↔ IsUnit a :=
  ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert h
      
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_is_unit_zero
      ,
    IsUnit.ring_inverse⟩

theorem Commute.ring_inverse_ring_inverse {a b : M₀} (h : Commute a b) : Commute (Ring.inverse a) (Ring.inverse b) :=
  (Ring.mul_inverse_rev' h.symm).symm.trans <| (congr_arg _ h.symm.Eq).trans <| Ring.mul_inverse_rev' h

variable (M₀)

end MonoidWithZeroₓ

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

-- see Note [lower instance priority]
instance (priority := 10) CancelMonoidWithZero.to_no_zero_divisors : NoZeroDivisors M₀ :=
  ⟨fun a b ab0 => by
    by_cases' a = 0
    · left
      exact h
      
    right
    apply CancelMonoidWithZero.mul_left_cancel_of_ne_zero h
    rw [ab0, mul_zero]⟩

theorem mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b :=
  (mul_left_injective₀ hc).eq_iff

theorem mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  (mul_right_injective₀ ha).eq_iff

@[simp]
theorem mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 := by
  by_cases' hc : c = 0 <;> [simp [← hc], simp [← mul_left_inj', ← hc]]

@[simp]
theorem mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 := by
  by_cases' ha : a = 0 <;> [simp [← ha], simp [← mul_right_inj', ← ha]]

theorem mul_right_eq_self₀ : a * b = a ↔ b = 1 ∨ a = 0 :=
  calc
    a * b = a ↔ a * b = a * 1 := by
      rw [mul_oneₓ]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff
    

theorem mul_left_eq_self₀ : a * b = b ↔ a = 1 ∨ b = 0 :=
  calc
    a * b = b ↔ a * b = 1 * b := by
      rw [one_mulₓ]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff
    

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.cancelMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CancelMonoidWithZero M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with
    mul_left_cancel_of_ne_zero := fun x y z hx H =>
      hf <|
        mul_left_cancel₀ ((hf.ne_iff' zero).2 hx) <| by
          erw [← mul, ← mul, H] <;> rfl,
    mul_right_cancel_of_ne_zero := fun x y z hx H =>
      hf <|
        mul_right_cancel₀ ((hf.ne_iff' zero).2 hx) <| by
          erw [← mul, ← mul, H] <;> rfl }

/-- An element of a `cancel_monoid_with_zero` fixed by right multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_right (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  Classical.by_contradiction fun ha => h₁ <| mul_left_cancel₀ ha <| h₂.symm ▸ (mul_oneₓ a).symm

/-- An element of a `cancel_monoid_with_zero` fixed by left multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_left (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  Classical.by_contradiction fun ha => h₁ <| mul_right_cancel₀ ha <| h₂.symm ▸ (one_mulₓ a).symm

end CancelMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero M₀] {a b c : M₀}

/-- Pullback a `cancel_comm_monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.cancelCommMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CancelCommMonoidWithZero M₀' :=
  { hf.CommMonoidWithZero f zero one mul npow, hf.CancelMonoidWithZero f zero one mul npow with }

end CancelCommMonoidWithZero

section GroupWithZeroₓ

variable [GroupWithZeroₓ G₀] {a b c g h x : G₀}

/-- Pullback a `group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZeroₓ G₀' :=
  { hf.MonoidWithZero f zero one mul npow, hf.DivInvMonoid f one mul inv div npow zpow, pullback_nonzero f zero one with
    inv_zero :=
      hf <| by
        erw [inv, zero, inv_zero],
    mul_inv_cancel := fun x hx =>
      hf <| by
        erw [one, mul, inv, mul_inv_cancel ((hf.ne_iff' zero).2 hx)] }

/-- Pushforward a `group_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZeroₓ G₀' :=
  { hf.MonoidWithZero f zero one mul npow, hf.DivInvMonoid f one mul inv div npow zpow with
    inv_zero := by
      erw [← zero, ← inv, inv_zero],
    mul_inv_cancel :=
      hf.forall.2 fun x hx => by
        erw [← inv, ← mul, mul_inv_cancel (mt (congr_arg f) <| trans_rel_left Ne hx zero.symm)] <;> exact one,
    exists_pair_ne := ⟨0, 1, h01⟩ }

@[simp]
theorem mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by
      simp [← h]
    

@[simp]
theorem mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by
      simp [← h]
    

theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
  simpa [← a_eq_0] using mul_inv_cancel h

@[simp]
theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by
      simp [← inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by
      simp [← h]
    _ = 1 := by
      simp [← inv_ne_zero h]
    

theorem GroupWithZeroₓ.mul_left_injective (h : x ≠ 0) : Function.Injective fun y => x * y := fun y y' w => by
  simpa only [mul_assoc, ← inv_mul_cancel h, ← one_mulₓ] using congr_arg (fun y => x⁻¹ * y) w

theorem GroupWithZeroₓ.mul_right_injective (h : x ≠ 0) : Function.Injective fun y => y * x := fun y y' w => by
  simpa only [← mul_assoc, ← mul_inv_cancel h, ← mul_oneₓ] using congr_arg (fun y => y * x⁻¹) w

@[simp]
theorem inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b⁻¹ * b = a :=
  calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by
      simp [← h]
    

@[simp]
theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by
      simp [← h]
    

private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_oneₓ]

-- See note [lower instance priority]
instance (priority := 100) GroupWithZeroₓ.toDivisionMonoid : DivisionMonoid G₀ :=
  { ‹GroupWithZeroₓ G₀› with inv := Inv.inv,
    inv_inv := fun a => by
      by_cases' h : a = 0
      · simp [← h]
        
      · exact left_inv_eq_right_invₓ (inv_mul_cancel <| inv_ne_zero h) (inv_mul_cancel h)
        ,
    mul_inv_rev := fun a b => by
      by_cases' ha : a = 0
      · simp [← ha]
        
      by_cases' hb : b = 0
      · simp [← hb]
        
      refine' inv_eq_of_mul _
      simp [← mul_assoc, ← ha, ← hb],
    inv_eq_of_mul := fun a b => inv_eq_of_mul }

end GroupWithZeroₓ

namespace Units

variable [GroupWithZeroₓ G₀]

variable {a b : G₀}

/-- Embed a non-zero element of a `group_with_zero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : G₀) (ha : a ≠ 0) : G₀ˣ :=
  ⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩

@[simp]
theorem mk0_one (h := one_ne_zero) : mk0 (1 : G₀) h = 1 := by
  ext
  rfl

@[simp]
theorem coe_mk0 {a : G₀} (h : a ≠ 0) : (mk0 a h : G₀) = a :=
  rfl

@[simp]
theorem mk0_coe (u : G₀ˣ) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
  Units.ext rfl

@[simp]
theorem mul_inv' (u : G₀ˣ) : (u : G₀) * u⁻¹ = 1 :=
  mul_inv_cancel u.ne_zero

@[simp]
theorem inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 :=
  inv_mul_cancel u.ne_zero

@[simp]
theorem mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) : Units.mk0 a ha = Units.mk0 b hb ↔ a = b :=
  ⟨fun h => by
    injection h, fun h => Units.ext h⟩

/-- In a group with zero, an existential over a unit can be rewritten in terms of `units.mk0`. -/
theorem exists0 {p : G₀ˣ → Prop} : (∃ g : G₀ˣ, p g) ↔ ∃ (g : G₀)(hg : g ≠ 0), p (Units.mk0 g hg) :=
  ⟨fun ⟨g, pg⟩ => ⟨g, g.ne_zero, (g.mk0_coe g.ne_zero).symm ▸ pg⟩, fun ⟨g, hg, pg⟩ => ⟨Units.mk0 g hg, pg⟩⟩

/-- An alternative version of `units.exists0`. This one is useful if Lean cannot
figure out `p` when using `units.exists0` from right to left. -/
theorem exists0' {p : ∀ g : G₀, g ≠ 0 → Prop} : (∃ (g : G₀)(hg : g ≠ 0), p g hg) ↔ ∃ g : G₀ˣ, p g g.ne_zero :=
  Iff.trans
    (by
      simp_rw [coe_mk0])
    exists0.symm

@[simp]
theorem exists_iff_ne_zero {x : G₀} : (∃ u : G₀ˣ, ↑u = x) ↔ x ≠ 0 := by
  simp [← exists0]

theorem _root_.group_with_zero.eq_zero_or_unit (a : G₀) : a = 0 ∨ ∃ u : G₀ˣ, a = u := by
  by_cases' h : a = 0
  · left
    exact h
    
  · right
    simpa only [← eq_comm] using units.exists_iff_ne_zero.mpr h
    

@[simp]
theorem smul_mk0 {α : Type _} [HasSmul G₀ α] {g : G₀} (hg : g ≠ 0) (a : α) : mk0 g hg • a = g • a :=
  rfl

end Units

section GroupWithZeroₓ

variable [GroupWithZeroₓ G₀] {a b c : G₀}

theorem IsUnit.mk0 (x : G₀) (hx : x ≠ 0) : IsUnit x :=
  (Units.mk0 x hx).IsUnit

theorem is_unit_iff_ne_zero : IsUnit a ↔ a ≠ 0 :=
  Units.exists_iff_ne_zero

alias is_unit_iff_ne_zero ↔ _ Ne.is_unit

attribute [protected] Ne.is_unit

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZeroₓ.no_zero_divisors : NoZeroDivisors G₀ :=
  { (‹_› : GroupWithZeroₓ G₀) with
    eq_zero_or_eq_zero_of_mul_eq_zero := fun a b h => by
      contrapose! h
      exact (Units.mk0 a h.1 * Units.mk0 b h.2).ne_zero }

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZeroₓ.cancelMonoidWithZero : CancelMonoidWithZero G₀ :=
  { (‹_› : GroupWithZeroₓ G₀) with
    mul_left_cancel_of_ne_zero := fun x y z hx h => by
      rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z],
    mul_right_cancel_of_ne_zero := fun x y z hy h => by
      rw [← mul_inv_cancel_right₀ hy x, h, mul_inv_cancel_right₀ hy z] }

-- Can't be put next to the other `mk0` lemmas because it depends on the
-- `no_zero_divisors` instance, which depends on `mk0`.
@[simp]
theorem Units.mk0_mul (x y : G₀) (hxy) :
    Units.mk0 (x * y) hxy = Units.mk0 x (mul_ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2 := by
  ext
  rfl

@[simp]
theorem div_self (h : a ≠ 0) : a / a = 1 :=
  h.IsUnit.div_self

theorem eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
  hc.IsUnit.eq_mul_inv_iff_mul_eq

theorem eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
  hb.IsUnit.eq_inv_mul_iff_mul_eq

theorem inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
  ha.IsUnit.inv_mul_eq_iff_eq_mul

theorem mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
  hb.IsUnit.mul_inv_eq_iff_eq_mul

theorem mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b :=
  hb.IsUnit.mul_inv_eq_one

theorem inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b :=
  ha.IsUnit.inv_mul_eq_one

theorem mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ :=
  hb.IsUnit.mul_eq_one_iff_eq_inv

theorem mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b :=
  ha.IsUnit.mul_eq_one_iff_inv_eq

@[simp]
theorem div_mul_cancel (a : G₀) (h : b ≠ 0) : a / b * b = a :=
  h.IsUnit.div_mul_cancel _

@[simp]
theorem mul_div_cancel (a : G₀) (h : b ≠ 0) : a * b / b = a :=
  h.IsUnit.mul_div_cancel _

theorem mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 :=
  h.IsUnit.mul_one_div_cancel

theorem one_div_mul_cancel (h : a ≠ 0) : 1 / a * a = 1 :=
  h.IsUnit.one_div_mul_cancel

theorem div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b :=
  hc.IsUnit.div_left_inj

@[field_simps]
theorem div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
  hb.IsUnit.div_eq_iff

@[field_simps]
theorem eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a :=
  hb.IsUnit.eq_div_iff

theorem div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
  hb.IsUnit.div_eq_iff.trans eq_comm

theorem eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b :=
  hc.IsUnit.eq_div_iff

theorem div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c :=
  hb.IsUnit.div_eq_of_eq_mul

theorem eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c :=
  hc.IsUnit.eq_div_of_mul_eq

theorem div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b :=
  hb.IsUnit.div_eq_one_iff_eq

theorem div_mul_left (hb : b ≠ 0) : b / (a * b) = 1 / a :=
  hb.IsUnit.div_mul_left

theorem mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : a * c / (b * c) = a / b :=
  hc.IsUnit.mul_div_mul_right _ _

theorem mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) :=
  (hb.IsUnit.mul_mul_div _).symm

theorem div_div_div_cancel_right (a : G₀) (hc : c ≠ 0) : a / c / (b / c) = a / b := by
  rw [div_div_eq_mul_div, div_mul_cancel _ hc]

theorem div_mul_div_cancel (a : G₀) (hc : c ≠ 0) : a / c * (c / b) = a / b := by
  rw [← mul_div_assoc, div_mul_cancel _ hc]

@[simp]
theorem zero_div (a : G₀) : 0 / a = 0 := by
  rw [div_eq_mul_inv, zero_mul]

@[simp]
theorem div_zero (a : G₀) : a / 0 = 0 := by
  rw [div_eq_mul_inv, inv_zero, mul_zero]

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a := by
  by_cases' h : a = 0
  · rw [h, inv_zero, mul_zero]
    
  · rw [mul_assoc, mul_inv_cancel h, mul_oneₓ]
    

/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_inv_mul_self (a : G₀) : a * a⁻¹ * a = a := by
  by_cases' h : a = 0
  · rw [h, inv_zero, mul_zero]
    
  · rw [mul_inv_cancel h, one_mulₓ]
    

/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp]
theorem inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a := by
  by_cases' h : a = 0
  · rw [h, inv_zero, mul_zero]
    
  · rw [inv_mul_cancel h, one_mulₓ]
    

/-- Multiplying `a` by itself and then dividing by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem mul_self_div_self (a : G₀) : a * a / a = a := by
  rw [div_eq_mul_inv, mul_self_mul_inv a]

/-- Dividing `a` by itself and then multiplying by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem div_self_mul_self (a : G₀) : a / a * a = a := by
  rw [div_eq_mul_inv, mul_inv_mul_self a]

theorem div_mul_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a / b * b = a :=
  Classical.by_cases
    (fun hb : b = 0 => by
      simp [*])
    (div_mul_cancel a)

theorem mul_div_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a * b / b = a :=
  Classical.by_cases
    (fun hb : b = 0 => by
      simp [*])
    (mul_div_cancel a)

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_commₓ

@[simp]
theorem div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ :=
  calc
    a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ := by
      simp [← mul_inv_rev]
    _ = a⁻¹ := inv_mul_mul_self _
    

theorem one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 := by
  simpa only [← one_div] using inv_ne_zero h

@[simp]
theorem inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 := by
  rw [inv_eq_iff_inv_eq, inv_zero, eq_comm]

@[simp]
theorem zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a :=
  eq_comm.trans <| inv_eq_zero.trans eq_comm

@[simp]
theorem divp_mk0 (a : G₀) {b : G₀} (hb : b ≠ 0) : a /ₚ Units.mk0 b hb = a / b :=
  divp_eq_div _ _

theorem div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by
  rw [div_eq_mul_inv]
  exact mul_ne_zero ha (inv_ne_zero hb)

@[simp]
theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0 := by
  simp [← div_eq_mul_inv]

theorem div_ne_zero_iff : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  (not_congr div_eq_zero_iff).trans not_or_distrib

theorem Ring.inverse_eq_inv (a : G₀) : Ring.inverse a = a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
    
  · exact Ring.inverse_unit (Units.mk0 a ha)
    

@[simp]
theorem Ring.inverse_eq_inv' : (Ring.inverse : G₀ → G₀) = Inv.inv :=
  funext Ring.inverse_eq_inv

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp]
theorem div_div_self (a : G₀) : a / (a / a) = a := by
  rw [div_div_eq_mul_div]
  exact mul_self_div_self a

theorem ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 := fun ha : a = 0 => by
  rw [ha, div_zero] at h
  contradiction

theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
  Classical.by_cases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim

end GroupWithZeroₓ

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

-- see Note [lower instance priority]
instance (priority := 10) CommGroupWithZero.cancelCommMonoidWithZero : CancelCommMonoidWithZero G₀ :=
  { GroupWithZeroₓ.cancelMonoidWithZero, CommGroupWithZero.toCommMonoidWithZero G₀ with }

-- See note [lower instance priority]
instance (priority := 100) CommGroupWithZero.toDivisionCommMonoid : DivisionCommMonoid G₀ :=
  { ‹CommGroupWithZero G₀›, GroupWithZeroₓ.toDivisionMonoid with }

/-- Pullback a `comm_group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.GroupWithZero f zero one mul inv div npow zpow, hf.CommSemigroup f mul with }

/-- Pushforward a `comm_group_with_zero` class along a surjective function. -/
protected def Function.Surjective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.GroupWithZero h01 f zero one mul inv div npow zpow, hf.CommSemigroup f mul with }

theorem div_mul_right (b : G₀) (ha : a ≠ 0) : a / (a * b) = 1 / b :=
  ha.IsUnit.div_mul_right _

theorem mul_div_cancel_left_of_imp {a b : G₀} (h : a = 0 → b = 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_of_imp h]

theorem mul_div_cancel_left (b : G₀) (ha : a ≠ 0) : a * b / a = b :=
  ha.IsUnit.mul_div_cancel_left _

theorem mul_div_cancel_of_imp' {a b : G₀} (h : b = 0 → a = 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel_of_imp h]

theorem mul_div_cancel' (a : G₀) (hb : b ≠ 0) : b * (a / b) = a :=
  hb.IsUnit.mul_div_cancel' _

theorem mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b :=
  hc.IsUnit.mul_div_mul_left _ _

theorem mul_eq_mul_of_div_eq_div (a : G₀) {b : G₀} (c : G₀) {d : G₀} (hb : b ≠ 0) (hd : d ≠ 0) (h : a / b = c / d) :
    a * d = c * b := by
  rw [← mul_oneₓ a, ← div_self hb, ← mul_comm_div, h, div_mul_eq_mul_div, div_mul_cancel _ hd]

@[field_simps]
theorem div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
  hb.IsUnit.div_eq_div_iff hd.IsUnit

theorem div_div_cancel' (ha : a ≠ 0) : a / (a / b) = b :=
  ha.IsUnit.div_div_cancel

theorem div_helper (b : G₀) (h : a ≠ 0) : 1 / (a * b) * a = 1 / b := by
  rw [div_mul_eq_mul_div, one_mulₓ, div_mul_right _ h]

end CommGroupWithZero

namespace SemiconjBy

@[simp]
theorem zero_right [MulZeroClassₓ G₀] (a : G₀) : SemiconjBy a 0 0 := by
  simp only [← SemiconjBy, ← mul_zero, ← zero_mul]

@[simp]
theorem zero_left [MulZeroClassₓ G₀] (x y : G₀) : SemiconjBy 0 x y := by
  simp only [← SemiconjBy, ← mul_zero, ← zero_mul]

variable [GroupWithZeroₓ G₀] {a x y x' y' : G₀}

@[simp]
theorem inv_symm_left_iff₀ : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x :=
  Classical.by_cases
    (fun ha : a = 0 => by
      simp only [← ha, ← inv_zero, ← SemiconjBy.zero_left])
    fun ha => @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _

theorem inv_symm_left₀ (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x :=
  SemiconjBy.inv_symm_left_iff₀.2 h

theorem inv_right₀ (h : SemiconjBy a x y) : SemiconjBy a x⁻¹ y⁻¹ := by
  by_cases' ha : a = 0
  · simp only [← ha, ← zero_left]
    
  by_cases' hx : x = 0
  · subst x
    simp only [← SemiconjBy, ← mul_zero, ← @eq_comm _ _ (y * a), ← mul_eq_zero] at h
    simp [← h.resolve_right ha]
    
  · have := mul_ne_zero ha hx
    rw [h.eq, mul_ne_zero_iff] at this
    exact @units_inv_right _ _ _ (Units.mk0 x hx) (Units.mk0 y this.1) h
    

@[simp]
theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  ⟨fun h => inv_invₓ x ▸ inv_invₓ y ▸ h.inv_right₀, inv_right₀⟩

theorem div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') : SemiconjBy a (x / x') (y / y') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h.mul_right h'.inv_right₀

end SemiconjBy

namespace Commute

@[simp]
theorem zero_right [MulZeroClassₓ G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a

@[simp]
theorem zero_left [MulZeroClassₓ G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a

variable [GroupWithZeroₓ G₀] {a b c : G₀}

@[simp]
theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff₀

theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b :=
  inv_left_iff₀.2 h

@[simp]
theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff₀

theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ :=
  inv_right_iff₀.2 h

@[simp]
theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  hab.div_right hac

@[simp]
theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by
  rw [div_eq_mul_inv]
  exact hac.mul_left hbc.inv_left₀

end Commute

namespace MonoidWithZeroHom

variable [GroupWithZeroₓ G₀] [GroupWithZeroₓ G₀'] [MonoidWithZeroₓ M₀] [Nontrivial M₀]

section MonoidWithZeroₓ

variable (f : G₀ →*₀ M₀) {a : G₀}

theorem map_ne_zero : f a ≠ 0 ↔ a ≠ 0 :=
  ⟨fun hfa ha => hfa <| ha.symm ▸ f.map_zero, fun ha => ((IsUnit.mk0 a ha).map f.toMonoidHom).ne_zero⟩

@[simp]
theorem map_eq_zero : f a = 0 ↔ a = 0 :=
  not_iff_not.1 f.map_ne_zero

end MonoidWithZeroₓ

section GroupWithZeroₓ

variable (f : G₀ →*₀ G₀') (a b : G₀)

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
@[simp]
theorem map_inv : f a⁻¹ = (f a)⁻¹ := by
  by_cases' h : a = 0
  · simp [← h]
    
  apply eq_inv_of_mul_eq_one_left
  rw [← f.map_mul, inv_mul_cancel h, f.map_one]

@[simp]
theorem map_div : f (a / b) = f a / f b := by
  simpa only [← div_eq_mul_inv] using (f.map_mul _ _).trans <| _root_.congr_arg _ <| f.map_inv b

end GroupWithZeroₓ

end MonoidWithZeroHom

/-- We define the inverse as a `monoid_with_zero_hom` by extending the inverse map by zero
on non-units. -/
noncomputable def MonoidWithZeroₓ.inverse {M : Type _} [CommMonoidWithZero M] : M →*₀ M where
  toFun := Ring.inverse
  map_zero' := Ring.inverse_zero _
  map_one' := Ring.inverse_one _
  map_mul' := fun x y => (Ring.mul_inverse_rev x y).trans (mul_comm _ _)

@[simp]
theorem MonoidWithZeroₓ.coe_inverse {M : Type _} [CommMonoidWithZero M] :
    (MonoidWithZeroₓ.inverse : M → M) = Ring.inverse :=
  rfl

@[simp]
theorem MonoidWithZeroₓ.inverse_apply {M : Type _} [CommMonoidWithZero M] (a : M) :
    MonoidWithZeroₓ.inverse a = Ring.inverse a :=
  rfl

/-- Inversion on a commutative group with zero, considered as a monoid with zero homomorphism. -/
def invMonoidWithZeroHom {G₀ : Type _} [CommGroupWithZero G₀] : G₀ →*₀ G₀ :=
  { invMonoidHom with map_zero' := inv_zero }

@[simp]
theorem MonoidHom.map_units_inv {M G₀ : Type _} [Monoidₓ M] [GroupWithZeroₓ G₀] (f : M →* G₀) (u : Mˣ) :
    f ↑u⁻¹ = (f u)⁻¹ := by
  rw [← Units.coe_map, ← Units.coe_map, ← Units.coe_inv, MonoidHom.map_inv]

@[simp]
theorem MonoidWithZeroHom.map_units_inv {M G₀ : Type _} [MonoidWithZeroₓ M] [GroupWithZeroₓ G₀] (f : M →*₀ G₀)
    (u : Mˣ) : f ↑u⁻¹ = (f u)⁻¹ :=
  f.toMonoidHom.map_units_inv u

section NoncomputableDefs

variable {M : Type _} [Nontrivial M]

/-- Constructs a `group_with_zero` structure on a `monoid_with_zero`
  consisting only of units and 0. -/
noncomputable def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZeroₓ M] (h : ∀ a : M, IsUnit a ∨ a = 0) :
    GroupWithZeroₓ M :=
  { hM with inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).Unit⁻¹, inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).Unit⁻¹) = 1
      rw [dif_neg h0, Units.mul_inv_eq_iff_eq_mul, one_mulₓ, IsUnit.unit_spec],
    exists_pair_ne := Nontrivial.exists_pair_ne }

/-- Constructs a `comm_group_with_zero` structure on a `comm_monoid_with_zero`
  consisting only of units and 0. -/
noncomputable def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M] (h : ∀ a : M, IsUnit a ∨ a = 0) :
    CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }

end NoncomputableDefs

