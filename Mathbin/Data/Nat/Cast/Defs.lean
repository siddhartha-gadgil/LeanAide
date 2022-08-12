/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathbin.Algebra.Group.Basic

/-!
# Cast of natural numbers

This file defines the *canonical* homomorphism from the natural numbers into an
`add_monoid` with a one.  In additive monoids with one, there exists a unique
such homomorphism and we store it in the `nat_cast : ℕ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `add_monoid_with_one`: Type class for `nat.cast`.
* `nat.cast`: Canonical homomorphism `ℕ → R`.
-/


universe u

/-- The numeral `((0+1)+⋯)+1`. -/
protected def Nat.unaryCast {R : Type u} [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1

/-- Type class for the canonical homomorphism `ℕ → R`.
-/
@[protect_proj]
class HasNatCast (R : Type u) where
  natCast : ℕ → R

/-- An `add_monoid_with_one` is an `add_monoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`.
-/
@[protect_proj]
class AddMonoidWithOneₓ (R : Type u) extends HasNatCast R, AddMonoidₓ R, One R where
  natCast := Nat.unaryCast
  nat_cast_zero : nat_cast 0 = (0 : R) := by
    run_tac
      control_laws_tac
  nat_cast_succ : ∀ n, nat_cast (n + 1) = (nat_cast n + 1 : R) := by
    run_tac
      control_laws_tac

/-- Canonical homomorphism from `ℕ` to a additive monoid `R` with a `1`. -/
protected def Nat.castₓ {R : Type u} [HasNatCast R] : ℕ → R :=
  HasNatCast.natCast

/-- An `add_comm_monoid_with_one` is an `add_monoid_with_one` satisfying `a + b = b + a`.  -/
@[protect_proj]
class AddCommMonoidWithOne (R : Type _) extends AddMonoidWithOneₓ R, AddCommMonoidₓ R

section

variable {R : Type _} [AddMonoidWithOneₓ R]

library_note "coercion into rings"/-- Coercions such as `nat.cast_coe` that go from a concrete structure such as
`ℕ` to an arbitrary ring `R` should be set up as follows:
```lean
@[priority 900] instance : has_coe_t ℕ R := ⟨...⟩
```

It needs to be `has_coe_t` instead of `has_coe` because otherwise type-class
inference would loop when constructing the transitive coercion `ℕ → ℕ → ℕ → ...`.
The reduced priority is necessary so that it doesn't conflict with instances
such as `has_coe_t R (option R)`.

For this to work, we reduce the priority of the `coe_base` and `coe_trans`
instances because we want the instances for `has_coe_t` to be tried in the
following order:

 1. `has_coe_t` instances declared in mathlib (such as `has_coe_t R (with_top R)`, etc.)
 2. `coe_base`, which contains instances such as `has_coe (fin n) n`
 3. `nat.cast_coe : has_coe_t ℕ R` etc.
 4. `coe_trans`

If `coe_trans` is tried first, then `nat.cast_coe` doesn't get a chance to apply.
-/


attribute [instance] coeBaseₓ

attribute [instance] coeTransₓ

namespace Nat

-- see note [coercion into rings]
instance (priority := 900) castCoe {R} [HasNatCast R] : CoeTₓ ℕ R :=
  ⟨Nat.castₓ⟩

@[simp, norm_cast]
theorem cast_zeroₓ : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOneₓ.nat_cast_zero

-- Lemmas about nat.succ need to get a low priority, so that they are tried last.
-- This is because `nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[simp, norm_cast]
theorem cast_succₓ (n : ℕ) : ((succ n : ℕ) : R) = n + 1 :=
  AddMonoidWithOneₓ.nat_cast_succ _

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : R) = n + 1 :=
  cast_succₓ _

@[simp, norm_cast]
theorem cast_ite (P : Prop) [Decidable P] (m n : ℕ) : ((ite P m n : ℕ) : R) = ite P (m : R) (n : R) := by
  split_ifs <;> rfl

end Nat

end

namespace Nat

variable {R : Type _}

@[simp, norm_cast]
theorem cast_oneₓ [AddMonoidWithOneₓ R] : ((1 : ℕ) : R) = 1 := by
  rw [cast_succ, cast_zero, zero_addₓ]

@[simp, norm_cast]
theorem cast_addₓ [AddMonoidWithOneₓ R] (m n : ℕ) : ((m + n : ℕ) : R) = m + n := by
  induction n <;> simp [← add_succ, ← add_assocₓ, ← Nat.add_zero, *]

/-- Computationally friendlier cast than `nat.unary_cast`, using binary representation. -/
protected def binCast [Zero R] [One R] [Add R] (n : ℕ) : R :=
  @Nat.binaryRec (fun _ => R) 0 (fun odd k a => cond odd (a + a + 1) (a + a)) n

@[simp]
theorem bin_cast_eq [AddMonoidWithOneₓ R] (n : ℕ) : (Nat.binCast n : R) = ((n : ℕ) : R) := by
  rw [Nat.binCast]
  apply binary_rec _ _ n
  · rw [binary_rec_zero, cast_zero]
    
  · intro b k h
    rw [binary_rec_eq, h]
    · cases b <;> simp [← bit, ← bit0, ← bit1]
      
    · simp
      
    

@[simp, norm_cast]
theorem cast_bit0 [AddMonoidWithOneₓ R] (n : ℕ) : ((bit0 n : ℕ) : R) = bit0 n :=
  cast_addₓ _ _

@[simp, norm_cast]
theorem cast_bit1 [AddMonoidWithOneₓ R] (n : ℕ) : ((bit1 n : ℕ) : R) = bit1 n := by
  rw [bit1, cast_add_one, cast_bit0] <;> rfl

theorem cast_two [AddMonoidWithOneₓ R] : ((2 : ℕ) : R) = 2 := by
  rw [cast_add_one, cast_one, bit0]

attribute [simp, norm_cast] Int.nat_abs_of_nat

end Nat

/-- `add_monoid_with_one` implementation using unary recursion. -/
@[reducible]
protected def AddMonoidWithOneₓ.unary {R : Type _} [AddMonoidₓ R] [One R] : AddMonoidWithOneₓ R :=
  { ‹One R›, ‹AddMonoidₓ R› with }

/-- `add_monoid_with_one` implementation using binary recursion. -/
@[reducible]
protected def AddMonoidWithOneₓ.binary {R : Type _} [AddMonoidₓ R] [One R] : AddMonoidWithOneₓ R :=
  { ‹One R›, ‹AddMonoidₓ R› with natCast := Nat.binCast,
    nat_cast_zero := by
      simp [← Nat.binCast, ← Nat.castₓ],
    nat_cast_succ := fun n => by
      simp only [← Nat.castₓ]
      let this : AddMonoidWithOneₓ R := AddMonoidWithOneₓ.unary
      erw [Nat.bin_cast_eq, Nat.bin_cast_eq, Nat.cast_succₓ]
      rfl }

