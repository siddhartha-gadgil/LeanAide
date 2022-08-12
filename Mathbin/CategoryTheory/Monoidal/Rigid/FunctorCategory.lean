/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.Rigid.Basic
import Mathbin.CategoryTheory.Monoidal.FunctorCategory

/-!
# Functors from a groupoid into a right/left rigid category form a right/left rigid category.

(Using the pointwise monoidal structure on the functor category.)
-/


noncomputable section

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C D : Type _} [Groupoid C] [Category D] [MonoidalCategory D]

instance functorHasRightDual [RightRigidCategory D] (F : C ⥤ D) : HasRightDual F where
  rightDual :=
    { obj := fun X => F.obj Xᘁ, map := fun X Y f => F.map (inv f)ᘁ,
      map_comp' := fun X Y Z f g => by
        simp [← comp_right_adjoint_mate] }
  exact :=
    { evaluation :=
        { app := fun X => ε_ _ _,
          naturality' := fun X Y f => by
            dsimp'
            rw [category.comp_id, functor.map_inv, ← id_tensor_comp_tensor_id, category.assoc,
              right_adjoint_mate_comp_evaluation, ← category.assoc, ← id_tensor_comp, is_iso.hom_inv_id, tensor_id,
              category.id_comp] },
      coevaluation :=
        { app := fun X => η_ _ _,
          naturality' := fun X Y f => by
            dsimp'
            rw [functor.map_inv, category.id_comp, ← id_tensor_comp_tensor_id, ← category.assoc,
              coevaluation_comp_right_adjoint_mate, category.assoc, ← comp_tensor_id, is_iso.inv_hom_id, tensor_id,
              category.comp_id] } }

instance rightRigidFunctorCategory [RightRigidCategory D] : RightRigidCategory (C ⥤ D) where

instance functorHasLeftDual [LeftRigidCategory D] (F : C ⥤ D) : HasLeftDual F where
  leftDual :=
    { obj := fun X => ᘁF.obj X, map := fun X Y f => ᘁF.map (inv f),
      map_comp' := fun X Y Z f g => by
        simp [← comp_left_adjoint_mate] }
  exact :=
    { evaluation :=
        { app := fun X => ε_ _ _,
          naturality' := fun X Y f => by
            dsimp'
            rw [category.comp_id, functor.map_inv, ← tensor_id_comp_id_tensor, category.assoc,
              left_adjoint_mate_comp_evaluation, ← category.assoc, ← comp_tensor_id, is_iso.hom_inv_id, tensor_id,
              category.id_comp] },
      coevaluation :=
        { app := fun X => η_ _ _,
          naturality' := fun X Y f => by
            dsimp'
            rw [functor.map_inv, category.id_comp, ← tensor_id_comp_id_tensor, ← category.assoc,
              coevaluation_comp_left_adjoint_mate, category.assoc, ← id_tensor_comp, is_iso.inv_hom_id, tensor_id,
              category.comp_id] } }

instance leftRigidFunctorCategory [LeftRigidCategory D] : LeftRigidCategory (C ⥤ D) where

instance rigidFunctorCategory [RigidCategory D] : RigidCategory (C ⥤ D) where

end CategoryTheory.Monoidal

