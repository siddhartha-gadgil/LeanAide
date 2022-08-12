/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathbin.Algebra.Divisibility
import Mathbin.Algebra.Regular.Basic
import Mathbin.Data.Int.Cast.Defs
import Mathbin.Data.Pi.Algebra

/-!
# Semirings and rings

This file defines semirings, rings and domains. This is analogous to `algebra.group.defs` and
`algebra.group.basic`, the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

## Main definitions

* `distrib`: Typeclass for distributivity of multiplication over addition.
* `has_distrib_neg`: Typeclass for commutativity of negation and multiplication. This is useful when
  dealing with multiplicative submonoids which are closed under negation without being closed under
  addition, for example `units`.
* `(non_unital_)(non_assoc_)(semi)ring`: Typeclasses for possibly non-unital or non-associative
  rings and semirings. Some combinations are not defined yet because they haven't found use.

## Tags

`semiring`, `comm_semiring`, `ring`, `comm_ring`, `domain`, `is_domain`, `nonzero`, `units`
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

/-!
### `distrib` class
-/


/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
@[protect_proj, ancestor Mul Add]
class Distribₓ (R : Type _) extends Mul R, Add R where
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/-- A typeclass stating that multiplication is left distributive over addition. -/
@[protect_proj]
class LeftDistribClass (R : Type _) [Mul R] [Add R] where
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c

/-- A typeclass stating that multiplication is right distributive over addition. -/
@[protect_proj]
class RightDistribClass (R : Type _) [Mul R] [Add R] where
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

-- see Note [lower instance priority]
instance (priority := 100) Distribₓ.leftDistribClass (R : Type _) [Distribₓ R] : LeftDistribClass R :=
  ⟨Distribₓ.left_distrib⟩

-- see Note [lower instance priority]
instance (priority := 100) Distribₓ.rightDistribClass (R : Type _) [Distribₓ R] : RightDistribClass R :=
  ⟨Distribₓ.right_distrib⟩

theorem left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) : a * (b + c) = a * b + a * c :=
  LeftDistribClass.left_distrib a b c

alias left_distrib ← mul_addₓ

theorem right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) : (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c

alias right_distrib ← add_mulₓ

theorem distrib_three_right [Mul R] [Add R] [RightDistribClass R] (a b c d : R) :
    (a + b + c) * d = a * d + b * d + c * d := by
  simp [← right_distrib]

/-- Pullback a `distrib` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.distrib {S} [Mul R] [Add R] [Distribₓ S] (f : R → S) (hf : Injective f)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) : Distribₓ R where
  mul := (· * ·)
  add := (· + ·)
  left_distrib := fun x y z =>
    hf <| by
      simp only [*, ← left_distrib]
  right_distrib := fun x y z =>
    hf <| by
      simp only [*, ← right_distrib]

/-- Pushforward a `distrib` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.distrib {S} [Distribₓ R] [Add S] [Mul S] (f : R → S) (hf : Surjective f)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) : Distribₓ S where
  mul := (· * ·)
  add := (· + ·)
  left_distrib :=
    hf.forall₃.2 fun x y z => by
      simp only [add, mul, ← left_distrib]
  right_distrib :=
    hf.forall₃.2 fun x y z => by
      simp only [add, mul, ← right_distrib]

/-!
### Semirings
-/


/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
@[protect_proj, ancestor AddCommMonoidₓ Distribₓ MulZeroClassₓ]
class NonUnitalNonAssocSemiringₓ (α : Type u) extends AddCommMonoidₓ α, Distribₓ α, MulZeroClassₓ α

/-- An associative but not-necessarily unital semiring. -/
@[protect_proj, ancestor NonUnitalNonAssocSemiringₓ SemigroupWithZeroₓ]
class NonUnitalSemiringₓ (α : Type u) extends NonUnitalNonAssocSemiringₓ α, SemigroupWithZeroₓ α

/-- A unital but not-necessarily-associative semiring. -/
@[protect_proj, ancestor NonUnitalNonAssocSemiringₓ MulZeroOneClassₓ]
class NonAssocSemiringₓ (α : Type u) extends NonUnitalNonAssocSemiringₓ α, MulZeroOneClassₓ α, AddCommMonoidWithOne α

/-- A semiring is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), multiplicative monoid (`monoid`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). The actual definition extends `monoid_with_zero`
instead of `monoid` and `mul_zero_class`. -/
@[protect_proj, ancestor NonUnitalSemiringₓ NonAssocSemiringₓ MonoidWithZeroₓ]
class Semiringₓ (α : Type u) extends NonUnitalSemiringₓ α, NonAssocSemiringₓ α, MonoidWithZeroₓ α

section InjectiveSurjectiveMaps

variable [Zero β] [Add β] [Mul β] [HasSmul ℕ β]

/-- Pullback a `non_unital_non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalNonAssocSemiring {α : Type u} [NonUnitalNonAssocSemiringₓ α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalNonAssocSemiringₓ β :=
  { hf.MulZeroClass f zero mul, hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalSemiring {α : Type u} [NonUnitalSemiringₓ α] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalSemiringₓ β :=
  { hf.NonUnitalNonAssocSemiring f zero add mul nsmul, hf.SemigroupWithZero f zero mul with }

/-- Pullback a `non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonAssocSemiring {α : Type u} [NonAssocSemiringₓ α] {β : Type v} [Zero β] [One β]
    [Mul β] [Add β] [HasSmul ℕ β] [HasNatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) : NonAssocSemiringₓ β :=
  { hf.AddMonoidWithOne f zero one add nsmul nat_cast, hf.NonUnitalNonAssocSemiring f zero add mul nsmul,
    hf.MulOneClass f one mul with }

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semiring {α : Type u} [Semiringₓ α] {β : Type v} [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [HasSmul ℕ β] [HasNatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semiringₓ β :=
  { hf.NonAssocSemiring f zero one add mul nsmul nat_cast, hf.MonoidWithZero f zero one mul npow,
    hf.Distrib f add mul with }

/-- Pushforward a `non_unital_non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalNonAssocSemiring {α : Type u} [NonUnitalNonAssocSemiringₓ α] (f : α → β)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalNonAssocSemiringₓ β :=
  { hf.MulZeroClass f zero mul, hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalSemiring {α : Type u} [NonUnitalSemiringₓ α] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalSemiringₓ β :=
  { hf.NonUnitalNonAssocSemiring f zero add mul nsmul, hf.SemigroupWithZero f zero mul with }

/-- Pushforward a `non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonAssocSemiring {α : Type u} [NonAssocSemiringₓ α] {β : Type v} [Zero β] [One β]
    [Add β] [Mul β] [HasSmul ℕ β] [HasNatCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) : NonAssocSemiringₓ β :=
  { hf.AddMonoidWithOne f zero one add nsmul nat_cast, hf.NonUnitalNonAssocSemiring f zero add mul nsmul,
    hf.MulOneClass f one mul with }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.semiring {α : Type u} [Semiringₓ α] {β : Type v} [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [HasSmul ℕ β] [HasNatCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semiringₓ β :=
  { hf.NonAssocSemiring f zero one add mul nsmul nat_cast, hf.MonoidWithZero f zero one mul npow,
    hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }

end InjectiveSurjectiveMaps

section HasOneHasAdd

variable [One α] [Add α]

theorem one_add_one_eq_two : 1 + 1 = (2 : α) :=
  rfl

end HasOneHasAdd

section DistribSemigroup

variable [Add α] [Semigroupₓ α]

theorem dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Dvd.elim h₁ fun d hd =>
    Dvd.elim h₂ fun e he =>
      Dvd.intro (d + e)
        (by
          simp [← left_distrib, ← hd, ← he])

end DistribSemigroup

section DistribMulOneClass

variable [Add α] [MulOneClassₓ α]

theorem add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b = a * b + b := by
  rw [add_mulₓ, one_mulₓ]

theorem mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = a * b + a := by
  rw [mul_addₓ, mul_oneₓ]

theorem one_add_mul [RightDistribClass α] (a b : α) : (1 + a) * b = b + a * b := by
  rw [add_mulₓ, one_mulₓ]

theorem mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = a + a * b := by
  rw [mul_addₓ, mul_oneₓ]

theorem two_mul [RightDistribClass α] (n : α) : 2 * n = n + n :=
  Eq.trans (right_distrib 1 1 n)
    (by
      simp )

theorem bit0_eq_two_mul [RightDistribClass α] (n : α) : bit0 n = 2 * n :=
  (two_mul _).symm

theorem mul_two [LeftDistribClass α] (n : α) : n * 2 = n + n :=
  (left_distrib n 1 1).trans
    (by
      simp )

end DistribMulOneClass

section Semiringₓ

variable [Semiringₓ α]

@[to_additive]
theorem mul_ite {α} [Mul α] (P : Prop) [Decidable P] (a b c : α) :
    (a * if P then b else c) = if P then a * b else a * c := by
  split_ifs <;> rfl

@[to_additive]
theorem ite_mul {α} [Mul α] (P : Prop) [Decidable P] (a b c : α) :
    (if P then a else b) * c = if P then a * c else b * c := by
  split_ifs <;> rfl

-- We make `mul_ite` and `ite_mul` simp lemmas,
-- but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with
-- summations of the form `∑ x in s, (f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with
-- `mul_ite` and `ite_mul`.
attribute [simp] mul_ite ite_mul

@[simp]
theorem mul_boole {α} [MulZeroOneClassₓ α] (P : Prop) [Decidable P] (a : α) :
    (a * if P then 1 else 0) = if P then a else 0 := by
  simp

@[simp]
theorem boole_mul {α} [MulZeroOneClassₓ α] (P : Prop) [Decidable P] (a : α) :
    (if P then 1 else 0) * a = if P then a else 0 := by
  simp

theorem ite_mul_zero_left {α : Type _} [MulZeroClassₓ α] (P : Prop) [Decidable P] (a b : α) :
    ite P (a * b) 0 = ite P a 0 * b := by
  by_cases' h : P <;> simp [← h]

theorem ite_mul_zero_right {α : Type _} [MulZeroClassₓ α] (P : Prop) [Decidable P] (a b : α) :
    ite P (a * b) 0 = a * ite P b 0 := by
  by_cases' h : P <;> simp [← h]

theorem ite_and_mul_zero {α : Type _} [MulZeroClassₓ α] (P Q : Prop) [Decidable P] [Decidable Q] (a b : α) :
    ite (P ∧ Q) (a * b) 0 = ite P a 0 * ite Q b 0 := by
  simp only [ite_and, ← ite_mul, ← mul_ite, ← mul_zero, ← zero_mul, ← and_comm]

end Semiringₓ

namespace AddHom

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulLeft {R : Type _} [Distribₓ R] (r : R) : AddHom R R :=
  ⟨(· * ·) r, mul_addₓ r⟩

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulRight {R : Type _} [Distribₓ R] (r : R) : AddHom R R :=
  ⟨fun a => a * r, fun _ _ => add_mulₓ _ _ r⟩

end AddHom

section AddHomClass

variable {F : Type _} [NonAssocSemiringₓ α] [NonAssocSemiringₓ β] [AddHomClass F α β]

/-- Additive homomorphisms preserve `bit0`. -/
@[simp]
theorem map_bit0 (f : F) (a : α) : (f (bit0 a) : β) = bit0 (f a) :=
  map_add _ _ _

end AddHomClass

namespace AddMonoidHom

/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulLeft {R : Type _} [NonUnitalNonAssocSemiringₓ R] (r : R) : R →+ R where
  toFun := (· * ·) r
  map_zero' := mul_zero r
  map_add' := mul_addₓ r

@[simp]
theorem coe_mul_left {R : Type _} [NonUnitalNonAssocSemiringₓ R] (r : R) : ⇑(mulLeft r) = (· * ·) r :=
  rfl

/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulRight {R : Type _} [NonUnitalNonAssocSemiringₓ R] (r : R) : R →+ R where
  toFun := fun a => a * r
  map_zero' := zero_mul r
  map_add' := fun _ _ => add_mulₓ _ _ r

@[simp]
theorem coe_mul_right {R : Type _} [NonUnitalNonAssocSemiringₓ R] (r : R) : ⇑(mulRight r) = (· * r) :=
  rfl

theorem mul_right_apply {R : Type _} [NonUnitalNonAssocSemiringₓ R] (a r : R) : mulRight r a = a * r :=
  rfl

end AddMonoidHom

@[simp]
theorem two_dvd_bit0 [Semiringₓ α] {a : α} : 2 ∣ bit0 a :=
  ⟨a, bit0_eq_two_mul _⟩

/-- A non-unital commutative semiring is a `non_unital_semiring` with commutative multiplication.
In other words, it is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), commutative semigroup (`comm_semigroup`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). -/
@[protect_proj, ancestor NonUnitalSemiringₓ CommSemigroupₓ]
class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiringₓ α, CommSemigroupₓ α

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α] [NonUnitalCommSemiring β] {a b c : α}

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalCommSemiring [Zero γ] [Add γ] [Mul γ] [HasSmul ℕ γ] (f : γ → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalCommSemiring γ :=
  { hf.NonUnitalSemiring f zero add mul nsmul, hf.CommSemigroup f mul with }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalCommSemiring [Zero γ] [Add γ] [Mul γ] [HasSmul ℕ γ] (f : α → γ)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalCommSemiring γ :=
  { hf.NonUnitalSemiring f zero add mul nsmul, hf.CommSemigroup f mul with }

theorem Dvd.Dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d ∣ a * x + b * y :=
  dvd_add (hdx.mul_left a) (hdy.mul_left b)

end NonUnitalCommSemiring

/-- A commutative semiring is a `semiring` with commutative multiplication. In other words, it is a
type with the following structures: additive commutative monoid (`add_comm_monoid`), multiplicative
commutative monoid (`comm_monoid`), distributive laws (`distrib`), and multiplication by zero law
(`mul_zero_class`). -/
@[protect_proj, ancestor Semiringₓ CommMonoidₓ]
class CommSemiringₓ (α : Type u) extends Semiringₓ α, CommMonoidₓ α

-- see Note [lower instance priority]
instance (priority := 100) CommSemiringₓ.toNonUnitalCommSemiring [CommSemiringₓ α] : NonUnitalCommSemiring α :=
  { CommSemiringₓ.toCommMonoid α, CommSemiringₓ.toSemiring α with }

-- see Note [lower instance priority]
instance (priority := 100) CommSemiringₓ.toCommMonoidWithZero [CommSemiringₓ α] : CommMonoidWithZero α :=
  { CommSemiringₓ.toCommMonoid α, CommSemiringₓ.toSemiring α with }

section CommSemiringₓ

variable [CommSemiringₓ α] [CommSemiringₓ β] {a b c : α}

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commSemiring [Zero γ] [One γ] [Add γ] [Mul γ] [HasSmul ℕ γ] [HasNatCast γ] [Pow γ ℕ]
    (f : γ → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) : CommSemiringₓ γ :=
  { hf.Semiring f zero one add mul nsmul npow nat_cast, hf.CommSemigroup f mul with }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commSemiring [Zero γ] [One γ] [Add γ] [Mul γ] [HasSmul ℕ γ] [HasNatCast γ] [Pow γ ℕ]
    (f : α → γ) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) : CommSemiringₓ γ :=
  { hf.Semiring f zero one add mul nsmul npow nat_cast, hf.CommSemigroup f mul with }

theorem add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  simp only [← two_mul, ← add_mulₓ, ← mul_addₓ, ← add_assocₓ, ← mul_comm b]

end CommSemiringₓ

section HasDistribNeg

/-- Typeclass for a negation operator that distributes across multiplication.

This is useful for dealing with submonoids of a ring that contain `-1` without having to duplicate
lemmas. -/
class HasDistribNeg (α : Type _) [Mul α] extends HasInvolutiveNeg α where
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  mul_neg : ∀ x y : α, x * -y = -(x * y)

section Mul

variable [Mul α] [HasDistribNeg α]

@[simp]
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _

@[simp]
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _

theorem neg_mul_neg (a b : α) : -a * -b = a * b := by
  simp

theorem neg_mul_eq_neg_mulₓ (a b : α) : -(a * b) = -a * b :=
  (neg_mul _ _).symm

theorem neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
  (mul_neg _ _).symm

theorem neg_mul_comm (a b : α) : -a * b = a * -b := by
  simp

/-- A type endowed with `-` and `*` has distributive negation, if it admits an injective map that
preserves `-` and `*` to a type which has distributive negation. -/
-- See note [reducible non-instances]
@[reducible]
protected def Function.Injective.hasDistribNeg [Neg β] [Mul β] (f : β → α) (hf : Injective f) (neg : ∀ a, f (-a) = -f a)
    (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.HasInvolutiveNeg _ neg, ‹Mul β› with
    neg_mul := fun x y =>
      hf <| by
        erw [neg, mul, neg, neg_mul, mul],
    mul_neg := fun x y =>
      hf <| by
        erw [neg, mul, neg, mul_neg, mul] }

/-- A type endowed with `-` and `*` has distributive negation, if it admits a surjective map that
preserves `-` and `*` from a type which has distributive negation. -/
-- See note [reducible non-instances]
@[reducible]
protected def Function.Surjective.hasDistribNeg [Neg β] [Mul β] (f : α → β) (hf : Surjective f)
    (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.HasInvolutiveNeg _ neg, ‹Mul β› with
    neg_mul :=
      hf.Forall₂.2 fun x y => by
        erw [← neg, ← mul, neg_mul, neg, mul]
        rfl,
    mul_neg :=
      hf.Forall₂.2 fun x y => by
        erw [← neg, ← mul, mul_neg, neg, mul]
        rfl }

namespace AddOpposite

instance : HasDistribNeg αᵃᵒᵖ :=
  unop_injective.HasDistribNeg _ unop_neg unop_mul

end AddOpposite

open MulOpposite

instance : HasDistribNeg αᵐᵒᵖ :=
  { MulOpposite.hasInvolutiveNeg _ with neg_mul := fun _ _ => unop_injective <| mul_neg _ _,
    mul_neg := fun _ _ => unop_injective <| neg_mul _ _ }

end Mul

section MulOneClassₓ

variable [MulOneClassₓ α] [HasDistribNeg α]

theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a := by
  simp

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
theorem mul_neg_one (a : α) : a * -1 = -a := by
  simp

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
theorem neg_one_mul (a : α) : -1 * a = -a := by
  simp

end MulOneClassₓ

section MulZeroClassₓ

variable [MulZeroClassₓ α] [HasDistribNeg α]

/-- Prefer `neg_zero` if `subtraction_monoid` is available. -/
@[simp]
theorem neg_zero' : (-0 : α) = 0 := by
  rw [← zero_mul (0 : α), ← neg_mul, mul_zero, mul_zero]

end MulZeroClassₓ

section Semigroupₓ

variable [Semigroupₓ α] [HasDistribNeg α] {a b c : α}

theorem dvd_neg_of_dvd (h : a ∣ b) : a ∣ -b :=
  let ⟨c, hc⟩ := h
  ⟨-c, by
    simp [← hc]⟩

theorem dvd_of_dvd_neg (h : a ∣ -b) : a ∣ b := by
  let t := dvd_neg_of_dvd h
  rwa [neg_negₓ] at t

/-- An element a of a semigroup with a distributive negation divides the negation of an element b
iff a divides b. -/
@[simp]
theorem dvd_neg (a b : α) : a ∣ -b ↔ a ∣ b :=
  ⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

theorem neg_dvd_of_dvd (h : a ∣ b) : -a ∣ b :=
  let ⟨c, hc⟩ := h
  ⟨-c, by
    simp [← hc]⟩

theorem dvd_of_neg_dvd (h : -a ∣ b) : a ∣ b := by
  let t := neg_dvd_of_dvd h
  rwa [neg_negₓ] at t

/-- The negation of an element a of a semigroup with a distributive negation divides
another element b iff a divides b. -/
@[simp]
theorem neg_dvd (a b : α) : -a ∣ b ↔ a ∣ b :=
  ⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩

end Semigroupₓ

section Groupₓ

variable [Groupₓ α] [HasDistribNeg α]

@[simp]
theorem inv_neg' (a : α) : (-a)⁻¹ = -a⁻¹ := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg, neg_negₓ, mul_left_invₓ]

end Groupₓ

end HasDistribNeg

/-!
### Rings
-/


/-- A not-necessarily-unital, not-necessarily-associative ring. -/
@[protect_proj, ancestor AddCommGroupₓ NonUnitalNonAssocSemiringₓ]
class NonUnitalNonAssocRing (α : Type u) extends AddCommGroupₓ α, NonUnitalNonAssocSemiringₓ α

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/-- Pullback a `non_unital_non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalNonAssocRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) :
    NonUnitalNonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul with }

/-- Pushforward a `non_unital_non_assoc_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalNonAssocRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) :
    NonUnitalNonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul with }

instance (priority := 100) NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg α where
  neg := Neg.neg
  neg_neg := neg_negₓ
  neg_mul := fun a b =>
    eq_neg_of_add_eq_zero_left <| by
      rw [← right_distrib, add_left_negₓ, zero_mul]
  mul_neg := fun a b =>
    eq_neg_of_add_eq_zero_left <| by
      rw [← left_distrib, add_left_negₓ, mul_zero]

theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := by
  simpa only [← sub_eq_add_neg, ← neg_mul_eq_mul_neg] using mul_addₓ a b (-c)

alias mul_sub_left_distrib ← mul_sub

theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simpa only [← sub_eq_add_neg, ← neg_mul_eq_neg_mulₓ] using add_mulₓ a (-b) c

alias mul_sub_right_distrib ← sub_mul

variable {a b c d e : α}

/-- An iff statement following from right distributivity in rings and the definition
  of subtraction. -/
theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e := by
      simp [← add_commₓ]
    _ ↔ a * e + c - b * e = d :=
      Iff.intro
        (fun h => by
          rw [h]
          simp )
        fun h => by
        rw [← h]
        simp
    _ ↔ (a - b) * e + c = d := by
      simp [← sub_mul, ← sub_add_eq_add_sub]
    

/-- A simplification of one side of an equation exploiting right distributivity in rings
  and the definition of subtraction. -/
theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d := fun h =>
  calc
    (a - b) * e + c = a * e + c - b * e := by
      simp [← sub_mul, ← sub_add_eq_add_sub]
    _ = d := by
      rw [h]
      simp [← @add_sub_cancel α]
    

end NonUnitalNonAssocRing

/-- An associative but not-necessarily unital ring. -/
@[protect_proj, ancestor NonUnitalNonAssocRing NonUnitalSemiringₓ]
class NonUnitalRing (α : Type _) extends NonUnitalNonAssocRing α, NonUnitalSemiringₓ α

section NonUnitalRing

variable [NonUnitalRing α]

/-- Pullback a `non_unital_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul,
    hf.Semigroup f mul with }

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul,
    hf.Semigroup f mul with }

end NonUnitalRing

/-- A unital but not-necessarily-associative ring. -/
@[protect_proj, ancestor NonUnitalNonAssocRing NonAssocSemiringₓ]
class NonAssocRing (α : Type _) extends NonUnitalNonAssocRing α, NonAssocSemiringₓ α, AddGroupWithOneₓ α

section NonAssocRing

variable [NonAssocRing α]

/-- Pullback a `non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonAssocRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] [HasNatCast β] [HasIntCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
    NonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul,
    hf.AddGroupWithOne f zero one add neg sub nsmul gsmul nat_cast int_cast, hf.MulZeroClass f zero mul,
    hf.Distrib f add mul, hf.MulOneClass f one mul with }

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonAssocRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] [HasNatCast β] [HasIntCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
    NonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul,
    hf.AddGroupWithOne f zero one add neg sub nsmul gsmul nat_cast int_cast, hf.Distrib f add mul,
    hf.MulOneClass f one mul with }

theorem sub_one_mul (a b : α) : (a - 1) * b = a * b - b := by
  rw [sub_mul, one_mulₓ]

theorem mul_sub_one (a b : α) : a * (b - 1) = a * b - a := by
  rw [mul_sub, mul_oneₓ]

theorem one_sub_mul (a b : α) : (1 - a) * b = b - a * b := by
  rw [sub_mul, one_mulₓ]

theorem mul_one_sub (a b : α) : a * (1 - b) = a - a * b := by
  rw [mul_sub, mul_oneₓ]

end NonAssocRing

/-- A ring is a type with the following structures: additive commutative group (`add_comm_group`),
multiplicative monoid (`monoid`), and distributive laws (`distrib`).  Equivalently, a ring is a
`semiring` with a negation operation making it an additive group.  -/
@[protect_proj, ancestor AddCommGroupₓ Monoidₓ Distribₓ]
class Ringₓ (α : Type u) extends AddCommGroupWithOne α, Monoidₓ α, Distribₓ α

section Ringₓ

variable [Ringₓ α] {a b c d e : α}

-- A (unital, associative) ring is a not-necessarily-unital ring 
-- see Note [lower instance priority]
instance (priority := 100) Ringₓ.toNonUnitalRing : NonUnitalRing α :=
  { ‹Ringₓ α› with
    zero_mul := fun a =>
      add_left_cancelₓ <|
        show 0 * a + 0 * a = 0 * a + 0 by
          rw [← add_mulₓ, zero_addₓ, add_zeroₓ],
    mul_zero := fun a =>
      add_left_cancelₓ <|
        show a * 0 + a * 0 = a * 0 + 0 by
          rw [← mul_addₓ, add_zeroₓ, add_zeroₓ] }

-- A (unital, associative) ring is a not-necessarily-associative ring 
-- see Note [lower instance priority]
instance (priority := 100) Ringₓ.toNonAssocRing : NonAssocRing α :=
  { ‹Ringₓ α› with
    zero_mul := fun a =>
      add_left_cancelₓ <|
        show 0 * a + 0 * a = 0 * a + 0 by
          rw [← add_mulₓ, zero_addₓ, add_zeroₓ],
    mul_zero := fun a =>
      add_left_cancelₓ <|
        show a * 0 + a * 0 = a * 0 + 0 by
          rw [← mul_addₓ, add_zeroₓ, add_zeroₓ] }

/- The instance from `ring` to `semiring` happens often in linear algebra, for which all the basic
definitions are given in terms of semirings, but many applications use rings or fields. We increase
a little bit its priority above 100 to try it quickly, but remaining below the default 1000 so that
more specific instances are tried first. -/
instance (priority := 200) Ringₓ.toSemiring : Semiringₓ α :=
  { ‹Ringₓ α›, Ringₓ.toNonUnitalRing with }

/-- Pullback a `ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.ring [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [HasNatCast β] [HasIntCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : Ringₓ β :=
  { hf.AddGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast,
    hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.Monoid f one mul npow, hf.Distrib f add mul with }

/-- Pushforward a `ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.ring [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [HasNatCast β] [HasIntCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : Ringₓ β :=
  { hf.AddGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast,
    hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.Monoid f one mul npow, hf.Distrib f add mul with }

end Ringₓ

namespace Units

variable [Ringₓ α] {a b : α}

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : Neg αˣ :=
  ⟨fun u =>
    ⟨-↑u, -↑u⁻¹, by
      simp , by
      simp ⟩⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp, norm_cast]
protected theorem coe_neg (u : αˣ) : (↑(-u) : α) = -u :=
  rfl

@[simp, norm_cast]
protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 :=
  rfl

instance : HasDistribNeg αˣ :=
  Units.ext.HasDistribNeg _ Units.coe_neg Units.coe_mul

end Units

theorem IsUnit.neg [Ringₓ α] {a : α} : IsUnit a → IsUnit (-a)
  | ⟨x, hx⟩ => hx ▸ (-x).IsUnit

theorem IsUnit.neg_iff [Ringₓ α] (a : α) : IsUnit (-a) ↔ IsUnit a :=
  ⟨fun h => neg_negₓ a ▸ h.neg, IsUnit.neg⟩

theorem IsUnit.sub_iff [Ringₓ α] {x y : α} : IsUnit (x - y) ↔ IsUnit (y - x) :=
  (IsUnit.neg_iff _).symm.trans <| neg_sub x y ▸ Iff.rfl

namespace RingHom

end RingHom

/-- A non-unital commutative ring is a `non_unital_ring` with commutative multiplication. -/
@[protect_proj, ancestor NonUnitalRing CommSemigroupₓ]
class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, CommSemigroupₓ α

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }

/-- A commutative ring is a `ring` with commutative multiplication. -/
@[protect_proj, ancestor Ringₓ CommSemigroupₓ]
class CommRingₓ (α : Type u) extends Ringₓ α, CommMonoidₓ α

-- see Note [lower instance priority]
instance (priority := 100) CommRingₓ.toCommSemiring [s : CommRingₓ α] : CommSemiringₓ α :=
  { s with mul_zero := mul_zero, zero_mul := zero_mul }

-- see Note [lower instance priority]
instance (priority := 100) CommRingₓ.toNonUnitalCommRing [s : CommRingₓ α] : NonUnitalCommRing α :=
  { s with mul_zero := mul_zero, zero_mul := zero_mul }

section NonUnitalRing

variable [NonUnitalRing α] {a b c : α}

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  rw [sub_eq_add_neg]
  exact dvd_add h₁ (dvd_neg_of_dvd h₂)

theorem dvd_add_iff_left (h : a ∣ c) : a ∣ b ↔ a ∣ b + c :=
  ⟨fun h₂ => dvd_add h₂ h, fun H => by
    have t := dvd_sub H h <;> rwa [add_sub_cancel] at t⟩

theorem dvd_add_iff_right (h : a ∣ b) : a ∣ c ↔ a ∣ b + c := by
  rw [add_commₓ] <;> exact dvd_add_iff_left h

/-- If an element a divides another element c in a commutative ring, a divides the sum of another
  element b with c iff a divides b. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  (dvd_add_iff_left h).symm

/-- If an element a divides another element b in a commutative ring, a divides the sum of b and
  another element c iff a divides c. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c :=
  (dvd_add_iff_right h).symm

theorem dvd_iff_dvd_of_dvd_sub {a b c : α} (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := by
  constructor
  · intro h'
    convert dvd_sub h' h
    exact Eq.symm (sub_sub_self b c)
    
  · intro h'
    convert dvd_add h h'
    exact eq_add_of_sub_eq rfl
    

end NonUnitalRing

section Ringₓ

variable [Ringₓ α] {a b c : α}

theorem two_dvd_bit1 : 2 ∣ bit1 a ↔ (2 : α) ∣ 1 :=
  (dvd_add_iff_right (@two_dvd_bit0 _ _ a)).symm

/-- An element a divides the sum a + b if and only if a divides b.-/
@[simp]
theorem dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
  dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b.-/
@[simp]
theorem dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
  dvd_add_left (dvd_refl a)

end Ringₓ

section NonUnitalCommRing

variable [NonUnitalCommRing α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalCommRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalCommRing β :=
  { hf.NonUnitalRing f zero add mul neg sub nsmul zsmul, hf.CommSemigroup f mul with }

/-- Pushforward a `non_unital_comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalCommRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalCommRing β :=
  { hf.NonUnitalRing f zero add mul neg sub nsmul zsmul, hf.CommSemigroup f mul with }

attribute [local simp] add_assocₓ add_commₓ add_left_commₓ mul_comm

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
theorem Vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
    ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c := by
  have : c = x * (b - x) :=
    (eq_neg_of_add_eq_zero_right h).trans
      (by
        simp [← mul_sub, ← mul_comm])
  refine'
    ⟨b - x, _, by
      simp , by
      rw [this]⟩
  rw [this, sub_add, ← sub_mul, sub_self]

theorem dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) : k ∣ a * x - b * y := by
  convert dvd_add (hxy.mul_left a) (hab.mul_right y)
  rw [mul_sub_left_distrib, mul_sub_right_distrib]
  simp only [← sub_eq_add_neg, ← add_assocₓ, ← neg_add_cancel_leftₓ]

end NonUnitalCommRing

section CommRingₓ

variable [CommRingₓ α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [HasNatCast β] [HasIntCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : CommRingₓ β :=
  { hf.Ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast, hf.CommSemigroup f mul with }

/-- Pushforward a `comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [HasNatCast β] [HasIntCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : CommRingₓ β :=
  { hf.Ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast, hf.CommSemigroup f mul with }

end CommRingₓ

theorem succ_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 ≠ a := fun h =>
  one_ne_zero
    ((add_right_injₓ a).mp
      (by
        simp [← h]))

theorem pred_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 ≠ a := fun h =>
  one_ne_zero
    (neg_injective
      ((add_right_injₓ a).mp
        (by
          simpa [← sub_eq_add_neg] using h)))

/-- Left `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
theorem is_left_regular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α) (h : ∀ x : α, k * x = 0 → x = 0) :
    IsLeftRegular k := by
  refine' fun x y (h' : k * x = k * y) => sub_eq_zero.mp (h _ _)
  rw [mul_sub, sub_eq_zero, h']

/-- Right `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
theorem is_right_regular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α) (h : ∀ x : α, x * k = 0 → x = 0) :
    IsRightRegular k := by
  refine' fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ _)
  rw [sub_mul, sub_eq_zero, h']

theorem is_regular_of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k ≠ 0) : IsRegular k :=
  ⟨is_left_regular_of_non_zero_divisor k fun x h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk,
    is_right_regular_of_non_zero_divisor k fun x h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk⟩

theorem is_regular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} :
    IsRegular k ↔ k ≠ 0 :=
  ⟨fun h => by
    rintro rfl
    exact not_not.mpr h.left not_is_left_regular_zero, is_regular_of_ne_zero'⟩

/-- A ring with no zero divisors is a `cancel_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelMonoidWithZero [Ringₓ α] [NoZeroDivisors α] : CancelMonoidWithZero α :=
  { (by
      infer_instance : MonoidWithZeroₓ α) with
    mul_left_cancel_of_ne_zero := fun a b c ha => @IsRegular.left _ _ _ (is_regular_of_ne_zero' ha) _ _,
    mul_right_cancel_of_ne_zero := fun a b c hb => @IsRegular.right _ _ _ (is_regular_of_ne_zero' hb) _ _ }

/-- A commutative ring with no zero divisors is a `cancel_comm_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelCommMonoidWithZero [CommRingₓ α] [NoZeroDivisors α] : CancelCommMonoidWithZero α :=
  { NoZeroDivisors.toCancelMonoidWithZero,
    (by
      infer_instance : CommMonoidWithZero α) with }

/-- A domain is a nontrivial ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`.

  This is implemented as a mixin for `ring α`.
  To obtain an integral domain use `[comm_ring α] [is_domain α]`. -/
@[protect_proj]
class IsDomain (α : Type u) [Ringₓ α] extends NoZeroDivisors α, Nontrivial α : Prop

section IsDomain

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelMonoidWithZero [Ringₓ α] [IsDomain α] : CancelMonoidWithZero α :=
  NoZeroDivisors.toCancelMonoidWithZero

variable [CommRingₓ α] [IsDomain α]

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelCommMonoidWithZero : CancelCommMonoidWithZero α :=
  NoZeroDivisors.toCancelCommMonoidWithZero

end IsDomain

namespace SemiconjBy

@[simp]
theorem add_right [Distribₓ R] {a x y x' y' : R} (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x + x') (y + y') := by
  simp only [← SemiconjBy, ← left_distrib, ← right_distrib, ← h.eq, ← h'.eq]

@[simp]
theorem add_left [Distribₓ R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) : SemiconjBy (a + b) x y :=
  by
  simp only [← SemiconjBy, ← left_distrib, ← right_distrib, ← ha.eq, ← hb.eq]

section

variable [Mul R] [HasDistribNeg R] {a x y : R}

theorem neg_right (h : SemiconjBy a x y) : SemiconjBy a (-x) (-y) := by
  simp only [← SemiconjBy, ← h.eq, ← neg_mul, ← mul_neg]

@[simp]
theorem neg_right_iff : SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y :=
  ⟨fun h => neg_negₓ x ▸ neg_negₓ y ▸ h.neg_right, SemiconjBy.neg_right⟩

theorem neg_left (h : SemiconjBy a x y) : SemiconjBy (-a) x y := by
  simp only [← SemiconjBy, ← h.eq, ← neg_mul, ← mul_neg]

@[simp]
theorem neg_left_iff : SemiconjBy (-a) x y ↔ SemiconjBy a x y :=
  ⟨fun h => neg_negₓ a ▸ h.neg_left, SemiconjBy.neg_left⟩

end

section

variable [MulOneClassₓ R] [HasDistribNeg R] {a x y : R}

@[simp]
theorem neg_one_right (a : R) : SemiconjBy a (-1) (-1) :=
  (one_right a).neg_right

@[simp]
theorem neg_one_left (x : R) : SemiconjBy (-1) x x :=
  (SemiconjBy.one_left x).neg_left

end

section

variable [NonUnitalNonAssocRing R] {a b x y x' y' : R}

@[simp]
theorem sub_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') : SemiconjBy a (x - x') (y - y') := by
  simpa only [← sub_eq_add_neg] using h.add_right h'.neg_right

@[simp]
theorem sub_left (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) : SemiconjBy (a - b) x y := by
  simpa only [← sub_eq_add_neg] using ha.add_left hb.neg_left

end

end SemiconjBy

namespace Commute

@[simp]
theorem add_right [Distribₓ R] {a b c : R} : Commute a b → Commute a c → Commute a (b + c) :=
  SemiconjBy.add_right

@[simp]
theorem add_left [Distribₓ R] {a b c : R} : Commute a c → Commute b c → Commute (a + b) c :=
  SemiconjBy.add_left

theorem bit0_right [Distribₓ R] {x y : R} (h : Commute x y) : Commute x (bit0 y) :=
  h.add_right h

theorem bit0_left [Distribₓ R] {x y : R} (h : Commute x y) : Commute (bit0 x) y :=
  h.add_left h

theorem bit1_right [NonAssocSemiringₓ R] {x y : R} (h : Commute x y) : Commute x (bit1 y) :=
  h.bit0_right.add_right (Commute.one_right x)

theorem bit1_left [NonAssocSemiringₓ R] {x y : R} (h : Commute x y) : Commute (bit1 x) y :=
  h.bit0_left.add_left (Commute.one_left y)

/-- Representation of a difference of two squares of commuting elements as a product. -/
theorem mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [add_mulₓ, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]

theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by
  rw [mul_addₓ, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]

theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R} (h : Commute a b) :
    a * a = b * b ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm, sub_eq_zero, add_eq_zero_iff_eq_neg]

section

variable [Mul R] [HasDistribNeg R] {a b : R}

theorem neg_right : Commute a b → Commute a (-b) :=
  SemiconjBy.neg_right

@[simp]
theorem neg_right_iff : Commute a (-b) ↔ Commute a b :=
  SemiconjBy.neg_right_iff

theorem neg_left : Commute a b → Commute (-a) b :=
  SemiconjBy.neg_left

@[simp]
theorem neg_left_iff : Commute (-a) b ↔ Commute a b :=
  SemiconjBy.neg_left_iff

end

section

variable [MulOneClassₓ R] [HasDistribNeg R] {a : R}

@[simp]
theorem neg_one_right (a : R) : Commute a (-1) :=
  SemiconjBy.neg_one_right a

@[simp]
theorem neg_one_left (a : R) : Commute (-1) a :=
  SemiconjBy.neg_one_left a

end

section

variable [NonUnitalNonAssocRing R] {a b c : R}

@[simp]
theorem sub_right : Commute a b → Commute a c → Commute a (b - c) :=
  SemiconjBy.sub_right

@[simp]
theorem sub_left : Commute a c → Commute b c → Commute (a - b) c :=
  SemiconjBy.sub_left

end

end Commute

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self [CommRingₓ R] (a b : R) : a * a - b * b = (a + b) * (a - b) :=
  (Commute.all a b).mul_self_sub_mul_self_eq

theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq, mul_oneₓ]

theorem mul_self_eq_mul_self_iff [CommRingₓ R] [NoZeroDivisors R] {a b : R} : a * a = b * b ↔ a = b ∨ a = -b :=
  (Commute.all a b).mul_self_eq_mul_self_iff

theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} : a * a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).mul_self_eq_mul_self_iff, mul_oneₓ]

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
theorem Units.inv_eq_self_iff [Ringₓ R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 := by
  rw [inv_eq_iff_mul_eq_one]
  simp only [← Units.ext_iff]
  push_cast
  exact mul_self_eq_one_iff

