/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.Algebra.Category.Group.ZModuleEquivalence
import Mathbin.Algebra.Category.Module.Subobject

/-!
# The category of abelian groups is well-powered
-/


open CategoryTheory

universe u

namespace AddCommGroupₓₓ

instance well_powered_AddCommGroup : WellPowered AddCommGroupₓₓ.{u} :=
  well_powered_of_equiv (forget₂ (ModuleCat.{u} ℤ) AddCommGroupₓₓ.{u}).asEquivalence

end AddCommGroupₓₓ

