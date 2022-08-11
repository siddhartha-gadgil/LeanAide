/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.Coherence

/-!
# Monoidal opposites

We write `Cᵐᵒᵖ` for the monoidal opposite of a monoidal category `C`.
-/


universe v₁ v₂ u₁ u₂

variable {C : Type u₁}

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

/-- A type synonym for the monoidal opposite. Use the notation `Cᴹᵒᵖ`. -/
@[nolint has_inhabited_instance]
def MonoidalOpposite (C : Type u₁) :=
  C

namespace MonoidalOpposite

-- mathport name: «expr ᴹᵒᵖ»
notation:max C "ᴹᵒᵖ" => MonoidalOpposite C

/-- Think of an object of `C` as an object of `Cᴹᵒᵖ`. -/
@[pp_nodot]
def mop (X : C) : Cᴹᵒᵖ :=
  X

/-- Think of an object of `Cᴹᵒᵖ` as an object of `C`. -/
@[pp_nodot]
def unmop (X : Cᴹᵒᵖ) : C :=
  X

theorem op_injective : Function.Injective (mop : C → Cᴹᵒᵖ) := fun _ _ => id

theorem unop_injective : Function.Injective (unmop : Cᴹᵒᵖ → C) := fun _ _ => id

@[simp]
theorem op_inj_iff (x y : C) : mop x = mop y ↔ x = y :=
  Iff.rfl

@[simp]
theorem unop_inj_iff (x y : Cᴹᵒᵖ) : unmop x = unmop y ↔ x = y :=
  Iff.rfl

@[simp]
theorem mop_unmop (X : Cᴹᵒᵖ) : mop (unmop X) = X :=
  rfl

@[simp]
theorem unmop_mop (X : C) : unmop (mop X) = X :=
  rfl

instance monoidalOppositeCategory [I : Category.{v₁} C] : Category Cᴹᵒᵖ where
  Hom := fun X Y => unmop X ⟶ unmop Y
  id := fun X => 𝟙 (unmop X)
  comp := fun X Y Z f g => f ≫ g

end MonoidalOpposite

end CategoryTheory

open CategoryTheory

open CategoryTheory.MonoidalOpposite

variable [Category.{v₁} C]

/-- The monoidal opposite of a morphism `f : X ⟶ Y` is just `f`, thought of as `mop X ⟶ mop Y`. -/
def Quiver.Hom.mop {X Y : C} (f : X ⟶ Y) : @Quiver.Hom Cᴹᵒᵖ _ (mop X) (mop Y) :=
  f

/-- We can think of a morphism `f : mop X ⟶ mop Y` as a morphism `X ⟶ Y`. -/
def Quiver.Hom.unmop {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) : unmop X ⟶ unmop Y :=
  f

namespace CategoryTheory

theorem mop_inj {X Y : C} : Function.Injective (Quiver.Hom.mop : (X ⟶ Y) → (mop X ⟶ mop Y)) := fun _ _ H =>
  congr_arg Quiver.Hom.unmop H

theorem unmop_inj {X Y : Cᴹᵒᵖ} : Function.Injective (Quiver.Hom.unmop : (X ⟶ Y) → (unmop X ⟶ unmop Y)) := fun _ _ H =>
  congr_arg Quiver.Hom.mop H

@[simp]
theorem unmop_mop {X Y : C} {f : X ⟶ Y} : f.mop.unmop = f :=
  rfl

@[simp]
theorem mop_unmop {X Y : Cᴹᵒᵖ} {f : X ⟶ Y} : f.unmop.mop = f :=
  rfl

@[simp]
theorem mop_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).mop = f.mop ≫ g.mop :=
  rfl

@[simp]
theorem mop_id {X : C} : (𝟙 X).mop = 𝟙 (mop X) :=
  rfl

@[simp]
theorem unmop_comp {X Y Z : Cᴹᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unmop = f.unmop ≫ g.unmop :=
  rfl

@[simp]
theorem unmop_id {X : Cᴹᵒᵖ} : (𝟙 X).unmop = 𝟙 (unmop X) :=
  rfl

@[simp]
theorem unmop_id_mop {X : C} : (𝟙 (mop X)).unmop = 𝟙 X :=
  rfl

@[simp]
theorem mop_id_unmop {X : Cᴹᵒᵖ} : (𝟙 (unmop X)).mop = 𝟙 X :=
  rfl

namespace Iso

variable {X Y : C}

/-- An isomorphism in `C` gives an isomorphism in `Cᴹᵒᵖ`. -/
@[simps]
def mop (f : X ≅ Y) : mop X ≅ mop Y where
  Hom := f.Hom.mop
  inv := f.inv.mop
  hom_inv_id' := unmop_inj f.hom_inv_id
  inv_hom_id' := unmop_inj f.inv_hom_id

end Iso

variable [MonoidalCategory.{v₁} C]

open Opposite MonoidalCategory

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]
-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]
instance monoidalCategoryOp : MonoidalCategory Cᵒᵖ where
  tensorObj := fun X Y => op (unop X ⊗ unop Y)
  tensorHom := fun X₁ Y₁ X₂ Y₂ f g => (f.unop ⊗ g.unop).op
  tensorUnit := op (𝟙_ C)
  associator := fun X Y Z => (α_ (unop X) (unop Y) (unop Z)).symm.op
  leftUnitor := fun X => (λ_ (unop X)).symm.op
  rightUnitor := fun X => (ρ_ (unop X)).symm.op
  associator_naturality' := by
    intros
    apply Quiver.Hom.unop_inj
    simp
  left_unitor_naturality' := by
    intros
    apply Quiver.Hom.unop_inj
    simp
  right_unitor_naturality' := by
    intros
    apply Quiver.Hom.unop_inj
    simp
  triangle' := by
    intros
    apply Quiver.Hom.unop_inj
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]"
  pentagon' := by
    intros
    apply Quiver.Hom.unop_inj
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]"

theorem op_tensor_obj (X Y : Cᵒᵖ) : X ⊗ Y = op (unop X ⊗ unop Y) :=
  rfl

theorem op_tensor_unit : 𝟙_ Cᵒᵖ = op (𝟙_ C) :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]
-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]
instance monoidalCategoryMop : MonoidalCategory Cᴹᵒᵖ where
  tensorObj := fun X Y => mop (unmop Y ⊗ unmop X)
  tensorHom := fun X₁ Y₁ X₂ Y₂ f g => (g.unmop ⊗ f.unmop).mop
  tensorUnit := mop (𝟙_ C)
  associator := fun X Y Z => (α_ (unmop Z) (unmop Y) (unmop X)).symm.mop
  leftUnitor := fun X => (ρ_ (unmop X)).mop
  rightUnitor := fun X => (λ_ (unmop X)).mop
  associator_naturality' := by
    intros
    apply unmop_inj
    simp
  left_unitor_naturality' := by
    intros
    apply unmop_inj
    simp
  right_unitor_naturality' := by
    intros
    apply unmop_inj
    simp
  triangle' := by
    intros
    apply unmop_inj
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]"
  pentagon' := by
    intros
    apply unmop_inj
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]"

theorem mop_tensor_obj (X Y : Cᴹᵒᵖ) : X ⊗ Y = mop (unmop Y ⊗ unmop X) :=
  rfl

theorem mop_tensor_unit : 𝟙_ Cᴹᵒᵖ = mop (𝟙_ C) :=
  rfl

end CategoryTheory

