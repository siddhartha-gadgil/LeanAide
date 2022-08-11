/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Scott Morrison, Simon Hudon
-/
import Mathbin.Algebra.Hom.Equiv
import Mathbin.CategoryTheory.Groupoid
import Mathbin.CategoryTheory.Opposites
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Endomorphisms

Definition and basic properties of endomorphisms and automorphisms of an object in a category.

For each `X : C`, we provide `End X := X ⟶ X` with a monoid structure,
and `Aut X := X ≅ X ` with a group structure.
-/


universe v v' u u'

namespace CategoryTheory

/-- Endomorphisms of an object in a category. Arguments order in multiplication agrees with
`function.comp`, not with `category.comp`. -/
def End {C : Type u} [CategoryStruct.{v} C] (X : C) :=
  X ⟶ X

namespace End

section Struct

variable {C : Type u} [CategoryStruct.{v} C] (X : C)

instance hasOne : One (End X) :=
  ⟨𝟙 X⟩

instance inhabited : Inhabited (End X) :=
  ⟨𝟙 X⟩

/-- Multiplication of endomorphisms agrees with `function.comp`, not `category_struct.comp`. -/
instance hasMul : Mul (End X) :=
  ⟨fun x y => y ≫ x⟩

variable {X}

/-- Assist the typechecker by expressing a morphism `X ⟶ X` as a term of `End X`. -/
def of (f : X ⟶ X) : End X :=
  f

/-- Assist the typechecker by expressing an endomorphism `f : End X` as a term of `X ⟶ X`. -/
def asHom (f : End X) : X ⟶ X :=
  f

@[simp]
theorem one_def : (1 : End X) = 𝟙 X :=
  rfl

@[simp]
theorem mul_def (xs ys : End X) : xs * ys = ys ≫ xs :=
  rfl

end Struct

/-- Endomorphisms of an object form a monoid -/
instance monoid {C : Type u} [Category.{v} C] {X : C} : Monoidₓ (End X) :=
  { End.hasMul X, End.hasOne X with mul_one := Category.id_comp, one_mul := Category.comp_id,
    mul_assoc := fun x y z => (Category.assoc z y x).symm }

section MulAction

variable {C : Type u} [Category.{v} C]

open Opposite

instance mulActionRight {X Y : C} : MulAction (End Y) (X ⟶ Y) where
  smul := fun r f => f ≫ r
  one_smul := Category.comp_id
  mul_smul := fun r s f => Eq.symm <| Category.assoc _ _ _

instance mulActionLeft {X : Cᵒᵖ} {Y : C} : MulAction (End X) (unop X ⟶ Y) where
  smul := fun r f => r.unop ≫ f
  one_smul := Category.id_comp
  mul_smul := fun r s f => Category.assoc _ _ _

theorem smul_right {X Y : C} {r : End Y} {f : X ⟶ Y} : r • f = f ≫ r :=
  rfl

theorem smul_left {X : Cᵒᵖ} {Y : C} {r : End X} {f : unop X ⟶ Y} : r • f = r.unop ≫ f :=
  rfl

end MulAction

/-- In a groupoid, endomorphisms form a group -/
instance group {C : Type u} [Groupoid.{v} C] (X : C) : Groupₓ (End X) :=
  { End.monoid with mul_left_inv := Groupoid.comp_inv, inv := Groupoid.inv }

end End

theorem is_unit_iff_is_iso {C : Type u} [Category.{v} C] {X : C} (f : End X) : IsUnit (f : End X) ↔ IsIso f :=
  ⟨fun h => { out := ⟨h.Unit.inv, ⟨h.Unit.inv_val, h.Unit.val_inv⟩⟩ }, fun h =>
    ⟨⟨f, inv f, by
        simp , by
        simp ⟩,
      rfl⟩⟩

variable {C : Type u} [Category.{v} C] (X : C)

/-- Automorphisms of an object in a category.

The order of arguments in multiplication agrees with
`function.comp`, not with `category.comp`.
-/
def Aut (X : C) :=
  X ≅ X

attribute [ext Aut] iso.ext

namespace Aut

instance inhabited : Inhabited (Aut X) :=
  ⟨Iso.refl X⟩

instance : Groupₓ (Aut X) := by
  refine_struct
      { one := iso.refl X, inv := iso.symm, mul := flip iso.trans, div := _,
        npow := @npowRec (Aut X) ⟨iso.refl X⟩ ⟨flip iso.trans⟩,
        zpow := @zpowRec (Aut X) ⟨iso.refl X⟩ ⟨flip iso.trans⟩ ⟨iso.symm⟩ } <;>
    intros <;>
      try
          rfl <;>
        ext <;>
          simp [← flip, ← (· * ·), ← Monoidₓ.mul, ← MulOneClassₓ.mul, ← MulOneClassₓ.one, ← One.one, ← Monoidₓ.one, ←
            Inv.inv]

theorem Aut_mul_def (f g : Aut X) : f * g = g.trans f :=
  rfl

/-- Units in the monoid of endomorphisms of an object
are (multiplicatively) equivalent to automorphisms of that object.
-/
def unitsEndEquivAut : (End X)ˣ ≃* Aut X where
  toFun := fun f => ⟨f.1, f.2, f.4, f.3⟩
  invFun := fun f => ⟨f.1, f.2, f.4, f.3⟩
  left_inv := fun ⟨f₁, f₂, f₃, f₄⟩ => rfl
  right_inv := fun ⟨f₁, f₂, f₃, f₄⟩ => rfl
  map_mul' := fun f g => by
    rcases f with ⟨⟩ <;> rcases g with ⟨⟩ <;> rfl

/-- Isomorphisms induce isomorphisms of the automorphism group -/
def autMulEquivOfIso {X Y : C} (h : X ≅ Y) : Aut X ≃* Aut Y where
  toFun := fun x => ⟨h.inv ≫ x.Hom ≫ h.Hom, h.inv ≫ x.inv ≫ h.Hom⟩
  invFun := fun y => ⟨h.Hom ≫ y.Hom ≫ h.inv, h.Hom ≫ y.inv ≫ h.inv⟩
  left_inv := by
    tidy
  right_inv := by
    tidy
  map_mul' := by
    simp [← Aut_mul_def]

end Aut

namespace Functor

variable {D : Type u'} [Category.{v'} D] (f : C ⥤ D) (X)

/-- `f.map` as a monoid hom between endomorphism monoids. -/
@[simps]
def mapEnd : End X →* End (f.obj X) where
  toFun := Functor.map f
  map_mul' := fun x y => f.map_comp y x
  map_one' := f.map_id X

/-- `f.map_iso` as a group hom between automorphism groups. -/
def mapAut : Aut X →* Aut (f.obj X) where
  toFun := f.mapIso
  map_mul' := fun x y => f.map_iso_trans y x
  map_one' := f.map_iso_refl X

end Functor

end CategoryTheory

