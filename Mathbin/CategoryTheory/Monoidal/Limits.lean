/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.Functorial
import Mathbin.CategoryTheory.Monoidal.FunctorCategory
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# `lim : (J ⥤ C) ⥤ C` is lax monoidal when `C` is a monoidal category.

When `C` is a monoidal category, the functorial association `F ↦ limit F` is lax monoidal,
i.e. there are morphisms
* `lim_lax.ε : (𝟙_ C) → limit (𝟙_ (J ⥤ C))`
* `lim_lax.μ : limit F ⊗ limit G ⟶ limit (F ⊗ G)`
satisfying the laws of a lax monoidal functor.
-/


open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Limits

universe v u

noncomputable section

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C] [HasLimits C]

instance limitFunctorial : Functorial fun F : J ⥤ C => limit F :=
  { Limits.lim with }

@[simp]
theorem limit_functorial_map {F G : J ⥤ C} (α : F ⟶ G) : map (fun F : J ⥤ C => limit F) α = Limits.lim.map α :=
  rfl

variable [MonoidalCategory.{v} C]

@[simps]
instance limitLaxMonoidal : LaxMonoidal fun F : J ⥤ C => limit F where
  ε := limit.lift _ { x := _, π := { app := fun j => 𝟙 _ } }
  μ := fun F G =>
    limit.lift (F ⊗ G)
      { x := limit F ⊗ limit G,
        π :=
          { app := fun j => limit.π F j ⊗ limit.π G j,
            naturality' := fun j j' f => by
              dsimp'
              simp only [← category.id_comp, tensor_comp, ← limit.w] } }
  μ_natural' := fun X Y X' Y' f g => by
    ext
    dsimp'
    simp only [← limit.lift_π, ← cones.postcompose_obj_π, ← monoidal.tensor_hom_app, ← limit.lift_map, ←
      nat_trans.comp_app, ← category.assoc, tensor_comp, ← lim_map_π]
  associativity' := fun X Y Z => by
    ext
    dsimp'
    simp only [← limit.lift_π, ← cones.postcompose_obj_π, ← monoidal.associator_hom_app, ← limit.lift_map, ←
      nat_trans.comp_app, ← category.assoc]
    slice_lhs 2 2 => rw [← tensor_id_comp_id_tensor]
    slice_lhs 1 2 => rw [← comp_tensor_id, limit.lift_π]dsimp
    slice_lhs 1 2 => rw [tensor_id_comp_id_tensor]
    conv_lhs => rw [associator_naturality]
    conv_rhs => rw [← id_tensor_comp_tensor_id (limit.π (Y ⊗ Z) j)]
    slice_rhs 2 3 => rw [← id_tensor_comp, limit.lift_π]dsimp
    dsimp'
    simp
  left_unitality' := fun X => by
    ext
    dsimp'
    simp
    conv_rhs => rw [← tensor_id_comp_id_tensor (limit.π X j)]
    slice_rhs 1 2 => rw [← comp_tensor_id]erw [limit.lift_π]dsimp
    slice_rhs 2 3 => rw [left_unitor_naturality]
    simp
  right_unitality' := fun X => by
    ext
    dsimp'
    simp
    conv_rhs => rw [← id_tensor_comp_tensor_id _ (limit.π X j)]
    slice_rhs 1 2 => rw [← id_tensor_comp]erw [limit.lift_π]dsimp
    slice_rhs 2 3 => rw [right_unitor_naturality]
    simp

/-- The limit functor `F ↦ limit F` bundled as a lax monoidal functor. -/
def limLax : LaxMonoidalFunctor (J ⥤ C) C :=
  LaxMonoidalFunctor.of fun F : J ⥤ C => limit F

@[simp]
theorem lim_lax_obj (F : J ⥤ C) : limLax.obj F = limit F :=
  rfl

theorem lim_lax_obj' (F : J ⥤ C) : limLax.obj F = lim.obj F :=
  rfl

@[simp]
theorem lim_lax_map {F G : J ⥤ C} (α : F ⟶ G) : limLax.map α = lim.map α :=
  rfl

@[simp]
theorem lim_lax_ε : (@limLax J _ C _ _ _).ε = limit.lift _ { x := _, π := { app := fun j => 𝟙 _ } } :=
  rfl

@[simp]
theorem lim_lax_μ (F G : J ⥤ C) :
    (@limLax J _ C _ _ _).μ F G =
      limit.lift (F ⊗ G)
        { x := limit F ⊗ limit G,
          π :=
            { app := fun j => limit.π F j ⊗ limit.π G j,
              naturality' := fun j j' f => by
                dsimp'
                simp only [← category.id_comp, tensor_comp, ← limit.w] } } :=
  rfl

end CategoryTheory.Limits

