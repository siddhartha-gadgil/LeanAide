/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Algebra.Group.ToAdditive

/-!
# Instances on pempty

This file collects facts about algebraic structures on the (universe-polymorphic) empty type, e.g.
that it is a semigroup.
-/


universe u

@[to_additive]
instance semigroupPempty : Semigroupₓ Pempty.{u + 1} where
  mul := fun x y => by
    cases x
  mul_assoc := fun x y z => by
    cases x

