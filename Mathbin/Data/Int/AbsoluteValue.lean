/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.GroupTheory.GroupAction.Units
import Mathbin.Data.Int.Cast
import Mathbin.Algebra.Order.AbsoluteValue

/-!
# Absolute values and the integers

This file contains some results on absolute values applied to integers.

## Main results

 * `absolute_value.map_units_int`: an absolute value sends all units of `ℤ` to `1`
-/


variable {R S : Type _} [Ringₓ R] [LinearOrderedCommRing S]

@[simp]
theorem AbsoluteValue.map_units_int (abv : AbsoluteValue ℤ S) (x : ℤˣ) : abv x = 1 := by
  rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

@[simp]
theorem AbsoluteValue.map_units_int_cast [Nontrivial R] (abv : AbsoluteValue R S) (x : ℤˣ) : abv ((x : ℤ) : R) = 1 := by
  rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

@[simp]
theorem AbsoluteValue.map_units_int_smul (abv : AbsoluteValue R S) (x : ℤˣ) (y : R) : abv (x • y) = abv y := by
  rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

