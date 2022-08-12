/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Creates
import Mathbin.CategoryTheory.Over
import Mathbin.CategoryTheory.IsConnected

/-!
# Connected limits in the over category

Shows that the forgetful functor `over B ⥤ C` creates connected limits, in particular `over B` has
any connected limit which `C` has.
-/


universe v u

-- morphism levels before object levels. See note [category_theory universes].
noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C]

variable {X : C}

namespace CategoryTheory.Over

namespace CreatesConnected

/-- (Impl) Given a diagram in the over category, produce a natural transformation from the
diagram legs to the specific object.
-/
def natTransInOver {B : C} (F : J ⥤ Over B) :
    F ⋙ forget B ⟶ (CategoryTheory.Functor.const J).obj B where app := fun j => (F.obj j).Hom

attribute [local tidy] tactic.case_bash

/-- (Impl) Given a cone in the base category, raise it to a cone in the over category. Note this is
where the connected assumption is used.
-/
@[simps]
def raiseCone [IsConnected J] {B : C} {F : J ⥤ Over B} (c : Cone (F ⋙ forget B)) : Cone F where
  x := Over.mk (c.π.app (Classical.arbitrary J) ≫ (F.obj (Classical.arbitrary J)).Hom)
  π := { app := fun j => Over.homMk (c.π.app j) (nat_trans_from_is_connected (c.π ≫ natTransInOver F) j _) }

theorem raised_cone_lowers_to_original [IsConnected J] {B : C} {F : J ⥤ Over B} (c : Cone (F ⋙ forget B))
    (t : IsLimit c) : (forget B).mapCone (raiseCone c) = c := by
  tidy

/-- (Impl) Show that the raised cone is a limit. -/
def raisedConeIsLimit [IsConnected J] {B : C} {F : J ⥤ Over B} {c : Cone (F ⋙ forget B)} (t : IsLimit c) :
    IsLimit (raiseCone c) where
  lift := fun s =>
    Over.homMk (t.lift ((forget B).mapCone s))
      (by
        dsimp'
        simp )
  uniq' := fun s m K => by
    ext1
    apply t.hom_ext
    intro j
    simp [K j]

end CreatesConnected

/-- The forgetful functor from the over category creates any connected limit. -/
instance forgetCreatesConnectedLimits [IsConnected J] {B : C} :
    CreatesLimitsOfShape J
      (forget
        B) where CreatesLimit := fun K =>
    createsLimitOfReflectsIso fun c t =>
      { liftedCone := CreatesConnected.raiseCone c,
        validLift := eqToIso (CreatesConnected.raised_cone_lowers_to_original c t),
        makesLimit := CreatesConnected.raisedConeIsLimit t }

/-- The over category has any connected limit which the original category has. -/
instance has_connected_limits {B : C} [IsConnected J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (Over B) where HasLimit := fun F => has_limit_of_created F (forget B)

end CategoryTheory.Over

