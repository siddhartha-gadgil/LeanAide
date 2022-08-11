/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.Mon_

/-!
# The category of module objects over a monoid object.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

variable {C}

/-- A module object for a monoid object, all internal to some monoidal category. -/
structure Modₓ (A : Mon_ C) where
  x : C
  act : A.x ⊗ X ⟶ X
  one_act' : (A.one ⊗ 𝟙 X) ≫ act = (λ_ X).Hom := by
    run_tac
      obviously
  assoc' : (A.mul ⊗ 𝟙 X) ≫ act = (α_ A.x A.x X).Hom ≫ (𝟙 A.x ⊗ act) ≫ act := by
    run_tac
      obviously

restate_axiom Modₓ.one_act'

restate_axiom Modₓ.assoc'

attribute [simp, reassoc] Modₓ.one_act Modₓ.assoc

namespace Modₓ

variable {A : Mon_ C} (M : Modₓ A)

theorem assoc_flip : (𝟙 A.x ⊗ M.act) ≫ M.act = (α_ A.x A.x M.x).inv ≫ (A.mul ⊗ 𝟙 M.x) ≫ M.act := by
  simp

/-- A morphism of module objects. -/
@[ext]
structure Hom (M N : Modₓ A) where
  Hom : M.x ⟶ N.x
  act_hom' : M.act ≫ hom = (𝟙 A.x ⊗ hom) ≫ N.act := by
    run_tac
      obviously

restate_axiom hom.act_hom'

attribute [simp, reassoc] hom.act_hom

/-- The identity morphism on a module object. -/
@[simps]
def id (M : Modₓ A) : Hom M M where Hom := 𝟙 M.x

instance homInhabited (M : Modₓ A) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : Modₓ A} (f : Hom M N) (g : Hom N O) : Hom M O where Hom := f.Hom ≫ g.Hom

instance : Category (Modₓ A) where
  Hom := fun M N => Hom M N
  id := id
  comp := fun M N O f g => comp f g

@[simp]
theorem id_hom' (M : Modₓ A) : (𝟙 M : Hom M M).Hom = 𝟙 M.x :=
  rfl

@[simp]
theorem comp_hom' {M N K : Modₓ A} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : Hom M K).Hom = f.Hom ≫ g.Hom :=
  rfl

variable (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : Modₓ A where
  x := A.x
  act := A.mul

instance : Inhabited (Modₓ A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
def forget : Modₓ A ⥤ C where
  obj := fun A => A.x
  map := fun A B f => f.Hom

open CategoryTheory.MonoidalCategory

/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : Mon_ C} (f : A ⟶ B) : Modₓ B ⥤ Modₓ A where
  obj := fun M =>
    { x := M.x, act := (f.Hom ⊗ 𝟙 M.x) ≫ M.act,
      one_act' := by
        slice_lhs 1 2 => rw [← comp_tensor_id]
        rw [f.one_hom, one_act],
      assoc' := by
        -- oh, for homotopy.io in a widget!
        slice_rhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
        rw [id_tensor_comp]
        slice_rhs 4 5 => rw [Modₓ.assoc_flip]
        slice_rhs 3 4 => rw [associator_inv_naturality]
        slice_rhs 2 3 => rw [← tensor_id, associator_inv_naturality]
        slice_rhs 1 3 => rw [iso.hom_inv_id_assoc]
        slice_rhs 1 2 => rw [← comp_tensor_id, tensor_id_comp_id_tensor]
        slice_rhs 1 2 => rw [← comp_tensor_id, ← f.mul_hom]
        rw [comp_tensor_id, category.assoc] }
  map := fun M N g =>
    { Hom := g.Hom,
      act_hom' := by
        dsimp'
        slice_rhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
        slice_rhs 2 3 => rw [← g.act_hom]
        rw [category.assoc] }

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.
end Modₓ

