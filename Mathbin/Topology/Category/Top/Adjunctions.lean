/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro
-/
import Mathbin.Topology.Category.Top.Basic
import Mathbin.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions regarding the category of topological spaces

This file shows that the forgetful functor from topological spaces to types has a left and right
adjoint, given by `Top.discrete`, resp. `Top.trivial`, the functors which equip a type with the
discrete, resp. trivial, topology.
-/


universe u

open CategoryTheory

open Top

namespace Top

/-- Equipping a type with the discrete topology is left adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps Unit counit]
def adj₁ : discrete ⊣ forget Top.{u} :=
  Adjunction.mkOfUnitCounit { Unit := { app := fun X => id }, counit := { app := fun X => ⟨id, continuous_bot⟩ } }

/-- Equipping a type with the trivial topology is right adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps Unit counit]
def adj₂ : forget Top.{u} ⊣ trivialₓ :=
  Adjunction.mkOfUnitCounit { Unit := { app := fun X => ⟨id, continuous_top⟩ }, counit := { app := fun X => id } }

instance : IsRightAdjoint (forget Top.{u}) :=
  ⟨_, adj₁⟩

instance : IsLeftAdjoint (forget Top.{u}) :=
  ⟨_, adj₂⟩

end Top

