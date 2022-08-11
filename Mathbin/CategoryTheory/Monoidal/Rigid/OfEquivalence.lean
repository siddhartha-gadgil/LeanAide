/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Transport rigid structures over a monoidal equivalence.
-/


noncomputable section

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

variable (F : MonoidalFunctor C D)

/-- Given candidate data for an exact pairing,
which is sent by a faithful monoidal functor to an exact pairing,
the equations holds automatically. -/
def exactPairingOfFaithful [Faithful F.toFunctor] {X Y : C} (eval : Y ⊗ X ⟶ 𝟙_ C) (coeval : 𝟙_ C ⟶ X ⊗ Y)
    [ExactPairing (F.obj X) (F.obj Y)] (map_eval : F.map eval = inv (F.μ _ _) ≫ ε_ _ _ ≫ F.ε)
    (map_coeval : F.map coeval = inv F.ε ≫ η_ _ _ ≫ F.μ _ _) : ExactPairing X Y where
  evaluation := eval
  coevaluation := coeval
  evaluation_coevaluation' :=
    F.toFunctor.map_injective
      (by
        simp [← map_eval, ← map_coeval, ← monoidal_functor.map_tensor])
  coevaluation_evaluation' :=
    F.toFunctor.map_injective
      (by
        simp [← map_eval, ← map_coeval, ← monoidal_functor.map_tensor])

/-- Given a pair of objects which are sent by a fully faithful functor to a pair of objects
with an exact pairing, we get an exact pairing.
-/
def exactPairingOfFullyFaithful [Full F.toFunctor] [Faithful F.toFunctor] (X Y : C) [ExactPairing (F.obj X) (F.obj Y)] :
    ExactPairing X Y :=
  exactPairingOfFaithful F (F.toFunctor.preimage (inv (F.μ _ _) ≫ ε_ _ _ ≫ F.ε))
    (F.toFunctor.preimage (inv F.ε ≫ η_ _ _ ≫ F.μ _ _))
    (by
      simp )
    (by
      simp )

/-- Pull back a left dual along an equivalence. -/
def hasLeftDualOfEquivalence [IsEquivalence F.toFunctor] (X : C) [HasLeftDual (F.obj X)] : HasLeftDual X where
  leftDual := F.toFunctor.inv.obj (ᘁF.obj X)
  exact := by
    apply exact_pairing_of_fully_faithful F _ _
    apply exact_pairing_congr_left (F.to_functor.as_equivalence.counit_iso.app _)
    dsimp'
    infer_instance

/-- Pull back a right dual along an equivalence. -/
def hasRightDualOfEquivalence [IsEquivalence F.toFunctor] (X : C) [HasRightDual (F.obj X)] : HasRightDual X where
  rightDual := F.toFunctor.inv.obj (F.obj Xᘁ)
  exact := by
    apply exact_pairing_of_fully_faithful F _ _
    apply exact_pairing_congr_right (F.to_functor.as_equivalence.counit_iso.app _)
    dsimp'
    infer_instance

/-- Pull back a left rigid structure along an equivalence. -/
def leftRigidCategoryOfEquivalence [IsEquivalence F.toFunctor] [LeftRigidCategory D] :
    LeftRigidCategory C where leftDual := fun X => hasLeftDualOfEquivalence F X

/-- Pull back a right rigid structure along an equivalence. -/
def rightRigidCategoryOfEquivalence [IsEquivalence F.toFunctor] [RightRigidCategory D] :
    RightRigidCategory C where rightDual := fun X => hasRightDualOfEquivalence F X

/-- Pull back a rigid structure along an equivalence. -/
def rigidCategoryOfEquivalence [IsEquivalence F.toFunctor] [RigidCategory D] : RigidCategory C where
  leftDual := fun X => hasLeftDualOfEquivalence F X
  rightDual := fun X => hasRightDualOfEquivalence F X

end CategoryTheory

