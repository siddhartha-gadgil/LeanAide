/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.CategoryTheory.Monoidal.Category

/-!
# Preadditive monoidal categories

A monoidal category is `monoidal_preadditive` if it is preadditive and tensor product of morphisms
is linear in both factors.
-/


noncomputable section

open Classical

namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (C : Type _) [Category C] [Preadditive C] [MonoidalCategory C]

/-- A category is `monoidal_preadditive` if tensoring is additive in both factors.

Note we don't `extend preadditive C` here, as `abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
class MonoidalPreadditive where
  tensor_zero' : ∀ {W X Y Z : C} (f : W ⟶ X), f ⊗ (0 : Y ⟶ Z) = 0 := by
    run_tac
      obviously
  zero_tensor' : ∀ {W X Y Z : C} (f : Y ⟶ Z), (0 : W ⟶ X) ⊗ f = 0 := by
    run_tac
      obviously
  tensor_add' : ∀ {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z), f ⊗ (g + h) = f ⊗ g + f ⊗ h := by
    run_tac
      obviously
  add_tensor' : ∀ {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z), (f + g) ⊗ h = f ⊗ h + g ⊗ h := by
    run_tac
      obviously

restate_axiom monoidal_preadditive.tensor_zero'

restate_axiom monoidal_preadditive.zero_tensor'

restate_axiom monoidal_preadditive.tensor_add'

restate_axiom monoidal_preadditive.add_tensor'

attribute [simp] monoidal_preadditive.tensor_zero monoidal_preadditive.zero_tensor

variable [MonoidalPreadditive C]

attribute [local simp] monoidal_preadditive.tensor_add monoidal_preadditive.add_tensor

instance tensor_left_additive (X : C) : (tensorLeft X).Additive where

instance tensor_right_additive (X : C) : (tensorRight X).Additive where

instance tensoring_left_additive (X : C) : ((tensoringLeft C).obj X).Additive where

instance tensoring_right_additive (X : C) : ((tensoringRight C).obj X).Additive where

open BigOperators

theorem tensor_sum {P Q R S : C} {J : Type _} (s : Finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
    (f ⊗ ∑ j in s, g j) = ∑ j in s, f ⊗ g j := by
  rw [← tensor_id_comp_id_tensor]
  let tQ := (((tensoring_left C).obj Q).mapAddHom : (R ⟶ S) →+ _)
  change _ ≫ tQ _ = _
  rw [tQ.map_sum, preadditive.comp_sum]
  dsimp' [← tQ]
  simp only [← tensor_id_comp_id_tensor]

theorem sum_tensor {P Q R S : C} {J : Type _} (s : Finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
    (∑ j in s, g j) ⊗ f = ∑ j in s, g j ⊗ f := by
  rw [← tensor_id_comp_id_tensor]
  let tQ := (((tensoring_right C).obj P).mapAddHom : (R ⟶ S) →+ _)
  change tQ _ ≫ _ = _
  rw [tQ.map_sum, preadditive.sum_comp]
  dsimp' [← tQ]
  simp only [← tensor_id_comp_id_tensor]

variable {C}

-- In a closed monoidal category, this would hold because
-- `tensor_left X` is a left adjoint and hence preserves all colimits.
-- In any case it is true in any preadditive category.
instance (X : C) :
    PreservesFiniteBiproducts
      (tensorLeft
        X) where preserves := fun J _ =>
    { preserves := fun f =>
        { preserves := fun b i =>
            is_bilimit_of_total _
              (by
                dsimp'
                simp only [tensor_comp, ← category.comp_id, tensor_sum, tensor_id, ← is_bilimit.total i]) } }

instance (X : C) :
    PreservesFiniteBiproducts
      (tensorRight
        X) where preserves := fun J _ =>
    { preserves := fun f =>
        { preserves := fun b i =>
            is_bilimit_of_total _
              (by
                dsimp'
                simp only [tensor_comp, ← category.comp_id, sum_tensor, tensor_id, ← is_bilimit.total i]) } }

variable [HasFiniteBiproducts C]

/-- The isomorphism showing how tensor product on the left distributes over direct sums. -/
def leftDistributor {J : Type} [Fintype J] (X : C) (f : J → C) : X ⊗ ⨁ f ≅ ⨁ fun j => X ⊗ f j :=
  (tensorLeft X).mapBiproduct f

@[simp]
theorem left_distributor_hom {J : Type} [Fintype J] (X : C) (f : J → C) :
    (leftDistributor X f).Hom = ∑ j : J, (𝟙 X ⊗ biproduct.π f j) ≫ biproduct.ι _ j := by
  ext
  dsimp' [← tensor_left, ← left_distributor]
  simp [← preadditive.sum_comp, ← biproduct.ι_π, ← comp_dite]

@[simp]
theorem left_distributor_inv {J : Type} [Fintype J] (X : C) (f : J → C) :
    (leftDistributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (𝟙 X ⊗ biproduct.ι f j) := by
  ext
  dsimp' [← tensor_left, ← left_distributor]
  simp [← preadditive.comp_sum, ← biproduct.ι_π_assoc, ← dite_comp]

theorem left_distributor_assoc {J : Type} [Fintype J] (X Y : C) (f : J → C) :
    (asIso (𝟙 X) ⊗ leftDistributor Y f) ≪≫ leftDistributor X _ =
      (α_ X Y (⨁ f)).symm ≪≫ leftDistributor (X ⊗ Y) f ≪≫ biproduct.mapIso fun j => α_ X Y _ :=
  by
  ext
  simp only [← category.comp_id, ← category.assoc, ← eq_to_hom_refl, ← iso.trans_hom, ← iso.symm_hom, ← as_iso_hom, ←
    comp_zero, ← comp_dite, ← preadditive.sum_comp, ← preadditive.comp_sum, ← tensor_sum, ← id_tensor_comp, ←
    tensor_iso_hom, ← left_distributor_hom, ← biproduct.map_iso_hom, ← biproduct.ι_map, ← biproduct.ι_π, ←
    Finset.sum_dite_irrel, ← Finset.sum_dite_eq', ← Finset.sum_const_zero]
  simp only [id_tensor_comp, ← biproduct.ι_π]
  simp only [← id_tensor_comp, ← tensor_dite, ← comp_dite]
  simp only [← category.comp_id, ← comp_zero, ← monoidal_preadditive.tensor_zero, ← eq_to_hom_refl, ← tensor_id, ←
    if_true, ← dif_ctx_congr, ← Finset.sum_congr, ← Finset.mem_univ, ← Finset.sum_dite_eq']
  simp only [tensor_id, ← associator_naturality, ← iso.inv_hom_id_assoc]

/-- The isomorphism showing how tensor product on the right distributes over direct sums. -/
def rightDistributor {J : Type} [Fintype J] (X : C) (f : J → C) : (⨁ f) ⊗ X ≅ ⨁ fun j => f j ⊗ X :=
  (tensorRight X).mapBiproduct f

@[simp]
theorem right_distributor_hom {J : Type} [Fintype J] (X : C) (f : J → C) :
    (rightDistributor X f).Hom = ∑ j : J, (biproduct.π f j ⊗ 𝟙 X) ≫ biproduct.ι _ j := by
  ext
  dsimp' [← tensor_right, ← right_distributor]
  simp [← preadditive.sum_comp, ← biproduct.ι_π, ← comp_dite]

@[simp]
theorem right_distributor_inv {J : Type} [Fintype J] (X : C) (f : J → C) :
    (rightDistributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (biproduct.ι f j ⊗ 𝟙 X) := by
  ext
  dsimp' [← tensor_right, ← right_distributor]
  simp [← preadditive.comp_sum, ← biproduct.ι_π_assoc, ← dite_comp]

theorem right_distributor_assoc {J : Type} [Fintype J] (X Y : C) (f : J → C) :
    (rightDistributor X f ⊗ asIso (𝟙 Y)) ≪≫ rightDistributor Y _ =
      α_ (⨁ f) X Y ≪≫ rightDistributor (X ⊗ Y) f ≪≫ biproduct.mapIso fun j => (α_ _ X Y).symm :=
  by
  ext
  simp only [← category.comp_id, ← category.assoc, ← eq_to_hom_refl, ← iso.symm_hom, ← iso.trans_hom, ← as_iso_hom, ←
    comp_zero, ← comp_dite, ← preadditive.sum_comp, ← preadditive.comp_sum, ← sum_tensor, ← comp_tensor_id, ←
    tensor_iso_hom, ← right_distributor_hom, ← biproduct.map_iso_hom, ← biproduct.ι_map, ← biproduct.ι_π, ←
    Finset.sum_dite_irrel, ← Finset.sum_dite_eq', ← Finset.sum_const_zero, ← Finset.mem_univ, ← if_true]
  simp only [comp_tensor_id, ← biproduct.ι_π, ← dite_tensor, ← comp_dite]
  simp only [← category.comp_id, ← comp_tensor_id, ← eq_to_hom_refl, ← tensor_id, ← comp_zero, ←
    monoidal_preadditive.zero_tensor, ← if_true, ← dif_ctx_congr, ← Finset.mem_univ, ← Finset.sum_congr, ←
    Finset.sum_dite_eq']
  simp only [tensor_id, ← associator_inv_naturality, ← iso.hom_inv_id_assoc]

theorem left_distributor_right_distributor_assoc {J : Type _} [Fintype J] (X Y : C) (f : J → C) :
    (leftDistributor X f ⊗ asIso (𝟙 Y)) ≪≫ rightDistributor Y _ =
      α_ X (⨁ f) Y ≪≫
        (asIso (𝟙 X) ⊗ rightDistributor Y _) ≪≫ leftDistributor X _ ≪≫ biproduct.mapIso fun j => (α_ _ _ _).symm :=
  by
  ext
  simp only [← category.comp_id, ← category.assoc, ← eq_to_hom_refl, ← iso.symm_hom, ← iso.trans_hom, ← as_iso_hom, ←
    comp_zero, ← comp_dite, ← preadditive.sum_comp, ← preadditive.comp_sum, ← sum_tensor, ← tensor_sum, ←
    comp_tensor_id, ← tensor_iso_hom, ← left_distributor_hom, ← right_distributor_hom, ← biproduct.map_iso_hom, ←
    biproduct.ι_map, ← biproduct.ι_π, ← Finset.sum_dite_irrel, ← Finset.sum_dite_eq', ← Finset.sum_const_zero, ←
    Finset.mem_univ, ← if_true]
  simp only [comp_tensor_id, id_tensor_comp_assoc, ← category.assoc, ← biproduct.ι_π, ← comp_dite, ← dite_comp, ←
    tensor_dite, ← dite_tensor]
  simp only [← category.comp_id, ← category.id_comp, ← category.assoc, ← id_tensor_comp, ← comp_zero, ← zero_comp, ←
    monoidal_preadditive.tensor_zero, ← monoidal_preadditive.zero_tensor, ← comp_tensor_id, ← eq_to_hom_refl, ←
    tensor_id, ← if_true, ← dif_ctx_congr, ← Finset.sum_congr, ← Finset.mem_univ, ← Finset.sum_dite_eq']
  simp only [← associator_inv_naturality, ← iso.hom_inv_id_assoc]

end CategoryTheory

