/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Algebra.Basic

/-!
# Additional facts about modules over algebras.
-/


namespace LinearMap

section RestrictScalars

variable (k : Type _) [CommSemiringₓ k] (A : Type _) [Semiringₓ A] [Algebra k A]

variable (M : Type _) [AddCommMonoidₓ M] [Module k M] [Module A M] [IsScalarTower k A M]

variable (N : Type _) [AddCommMonoidₓ N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- Restriction of scalars for linear maps between modules over a `k`-algebra is itself `k`-linear.
-/
@[simps]
def restrictScalarsLinearMap : (M →ₗ[A] N) →ₗ[k] M →ₗ[k] N where
  toFun := LinearMap.restrictScalars k
  map_add' := by
    tidy
  map_smul' := by
    tidy

end RestrictScalars

end LinearMap

