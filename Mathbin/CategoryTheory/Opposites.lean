/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import Mathbin.CategoryTheory.Equivalence

/-!
# Opposite categories

We provide a category instance on `Cᵒᵖ`.
The morphisms `X ⟶ Y` are defined to be the morphisms `unop Y ⟶ unop X` in `C`.

Here `Cᵒᵖ` is an irreducible typeclass synonym for `C`
(it is the same one used in the algebra library).

We also provide various mechanisms for constructing opposite morphisms, functors,
and natural transformations.

Unfortunately, because we do not have a definitional equality `op (op X) = X`,
there are quite a few variations that are needed in practice.
-/


universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
open Opposite

variable {C : Type u₁}

section Quiver

variable [Quiver.{v₁} C]

theorem Quiver.Hom.op_inj {X Y : C} : Function.Injective (Quiver.Hom.op : (X ⟶ Y) → (op Y ⟶ op X)) := fun _ _ H =>
  congr_arg Quiver.Hom.unop H

theorem Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injective (Quiver.Hom.unop : (X ⟶ Y) → (unop Y ⟶ unop X)) :=
  fun _ _ H => congr_arg Quiver.Hom.op H

@[simp]
theorem Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop = f :=
  rfl

@[simp]
theorem Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.op = f :=
  rfl

end Quiver

namespace CategoryTheory

variable [Category.{v₁} C]

/-- The opposite category.

See <https://stacks.math.columbia.edu/tag/001M>.
-/
instance Category.opposite : Category.{v₁} Cᵒᵖ where
  comp := fun _ _ _ f g => (g.unop ≫ f.unop).op
  id := fun X => (𝟙 (unop X)).op

@[simp]
theorem op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).op = g.op ≫ f.op :=
  rfl

@[simp]
theorem op_id {X : C} : (𝟙 X).op = 𝟙 (op X) :=
  rfl

@[simp]
theorem unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unop = g.unop ≫ f.unop :=
  rfl

@[simp]
theorem unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X) :=
  rfl

@[simp]
theorem unop_id_op {X : C} : (𝟙 (op X)).unop = 𝟙 X :=
  rfl

@[simp]
theorem op_id_unop {X : Cᵒᵖ} : (𝟙 (unop X)).op = 𝟙 X :=
  rfl

section

variable (C)

/-- The functor from the double-opposite of a category to the underlying category. -/
@[simps]
def opOp : Cᵒᵖᵒᵖ ⥤ C where
  obj := fun X => unop (unop X)
  map := fun X Y f => f.unop.unop

/-- The functor from a category to its double-opposite.  -/
@[simps]
def unopUnop : C ⥤ Cᵒᵖᵒᵖ where
  obj := fun X => op (op X)
  map := fun X Y f => f.op.op

/-- The double opposite category is equivalent to the original. -/
@[simps]
def opOpEquivalence : Cᵒᵖᵒᵖ ≌ C where
  Functor := opOp C
  inverse := unopUnop C
  unitIso := Iso.refl (𝟭 Cᵒᵖᵒᵖ)
  counitIso := Iso.refl (unopUnop C ⋙ opOp C)

end

/-- If `f` is an isomorphism, so is `f.op` -/
instance is_iso_op {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f.op :=
  ⟨⟨(inv f).op,
      ⟨Quiver.Hom.unop_inj
          (by
            tidy),
        Quiver.Hom.unop_inj
          (by
            tidy)⟩⟩⟩

/-- If `f.op` is an isomorphism `f` must be too.
(This cannot be an instance as it would immediately loop!)
-/
theorem is_iso_of_op {X Y : C} (f : X ⟶ Y) [IsIso f.op] : IsIso f :=
  ⟨⟨(inv f.op).unop,
      ⟨Quiver.Hom.op_inj
          (by
            simp ),
        Quiver.Hom.op_inj
          (by
            simp )⟩⟩⟩

theorem is_iso_op_iff {X Y : C} (f : X ⟶ Y) : IsIso f.op ↔ IsIso f :=
  ⟨fun hf => is_iso_of_op _, fun hf => inferInstance⟩

theorem is_iso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : IsIso f.unop ↔ IsIso f := by
  rw [← is_iso_op_iff f.unop, Quiver.Hom.op_unop]

instance is_iso_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : IsIso f.unop :=
  (is_iso_unop_iff _).2 inferInstance

@[simp]
theorem op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).op = inv f.op := by
  ext
  rw [← op_comp, is_iso.inv_hom_id, op_id]

@[simp]
theorem unop_inv {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : (inv f).unop = inv f.unop := by
  ext
  rw [← unop_comp, is_iso.inv_hom_id, unop_id]

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D]

variable {C D}

/-- The opposite of a functor, i.e. considering a functor `F : C ⥤ D` as a functor `Cᵒᵖ ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made between these.
-/
@[simps]
protected def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj := fun X => op (F.obj (unop X))
  map := fun X Y f => (F.map f.unop).op

/-- Given a functor `F : Cᵒᵖ ⥤ Dᵒᵖ` we can take the "unopposite" functor `F : C ⥤ D`.
In informal mathematics no distinction is made between these.
-/
@[simps]
protected def unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D where
  obj := fun X => unop (F.obj (op X))
  map := fun X Y f => (F.map f.op).unop

/-- The isomorphism between `F.op.unop` and `F`. -/
@[simps]
def opUnopIso (F : C ⥤ D) : F.op.unop ≅ F :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      tidy)

/-- The isomorphism between `F.unop.op` and `F`. -/
@[simps]
def unopOpIso (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op ≅ F :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      tidy)

variable (C D)

/-- Taking the opposite of a functor is functorial.
-/
@[simps]
def opHom : (C ⥤ D)ᵒᵖ ⥤ Cᵒᵖ ⥤ Dᵒᵖ where
  obj := fun F => (unop F).op
  map := fun F G α =>
    { app := fun X => (α.unop.app (unop X)).op,
      naturality' := fun X Y f => Quiver.Hom.unop_inj (α.unop.naturality f.unop).symm }

/-- Take the "unopposite" of a functor is functorial.
-/
@[simps]
def opInv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ where
  obj := fun F => op F.unop
  map := fun F G α =>
    Quiver.Hom.op
      { app := fun X => (α.app (op X)).unop, naturality' := fun X Y f => Quiver.Hom.op_inj <| (α.naturality f.op).symm }

variable {C D}

/-- Another variant of the opposite of functor, turning a functor `C ⥤ Dᵒᵖ` into a functor `Cᵒᵖ ⥤ D`.
In informal mathematics no distinction is made.
-/
@[simps]
protected def leftOp (F : C ⥤ Dᵒᵖ) : Cᵒᵖ ⥤ D where
  obj := fun X => unop (F.obj (unop X))
  map := fun X Y f => (F.map f.unop).unop

/-- Another variant of the opposite of functor, turning a functor `Cᵒᵖ ⥤ D` into a functor `C ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made.
-/
@[simps]
protected def rightOp (F : Cᵒᵖ ⥤ D) : C ⥤ Dᵒᵖ where
  obj := fun X => op (F.obj (op X))
  map := fun X Y f => (F.map f.op).op

instance {F : C ⥤ D} [Full F] : Full F.op where preimage := fun X Y f => (F.preimage f.unop).op

instance {F : C ⥤ D} [Faithful F] :
    Faithful F.op where map_injective' := fun X Y f g h =>
    Quiver.Hom.unop_inj <| by
      simpa using map_injective F (Quiver.Hom.op_inj h)

/-- If F is faithful then the right_op of F is also faithful. -/
instance right_op_faithful {F : Cᵒᵖ ⥤ D} [Faithful F] :
    Faithful
      F.rightOp where map_injective' := fun X Y f g h => Quiver.Hom.op_inj (map_injective F (Quiver.Hom.op_inj h))

/-- If F is faithful then the left_op of F is also faithful. -/
instance left_op_faithful {F : C ⥤ Dᵒᵖ} [Faithful F] :
    Faithful
      F.leftOp where map_injective' := fun X Y f g h => Quiver.Hom.unop_inj (map_injective F (Quiver.Hom.unop_inj h))

/-- The isomorphism between `F.left_op.right_op` and `F`. -/
@[simps]
def leftOpRightOpIso (F : C ⥤ Dᵒᵖ) : F.leftOp.rightOp ≅ F :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      tidy)

/-- The isomorphism between `F.right_op.left_op` and `F`. -/
@[simps]
def rightOpLeftOpIso (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp ≅ F :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      tidy)

end

end Functor

namespace NatTrans

variable {D : Type u₂} [Category.{v₂} D]

section

variable {F G : C ⥤ D}

/-- The opposite of a natural transformation. -/
@[simps]
protected def op (α : F ⟶ G) : G.op ⟶ F.op where
  app := fun X => (α.app (unop X)).op
  naturality' := fun X Y f =>
    Quiver.Hom.unop_inj
      (by
        simp )

@[simp]
theorem op_id (F : C ⥤ D) : NatTrans.op (𝟙 F) = 𝟙 F.op :=
  rfl

/-- The "unopposite" of a natural transformation. -/
@[simps]
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) : G.unop ⟶ F.unop where
  app := fun X => (α.app (op X)).unop
  naturality' := fun X Y f =>
    Quiver.Hom.op_inj
      (by
        simp )

@[simp]
theorem unop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.unop (𝟙 F) = 𝟙 F.unop :=
  rfl

/-- Given a natural transformation `α : F.op ⟶ G.op`,
we can take the "unopposite" of each component obtaining a natural transformation `G ⟶ F`.
-/
@[simps]
protected def removeOp (α : F.op ⟶ G.op) : G ⟶ F where
  app := fun X => (α.app (op X)).unop
  naturality' := fun X Y f =>
    Quiver.Hom.op_inj <| by
      simpa only [← functor.op_map] using (α.naturality f.op).symm

@[simp]
theorem remove_op_id (F : C ⥤ D) : NatTrans.removeOp (𝟙 F.op) = 𝟙 F :=
  rfl

/-- Given a natural transformation `α : F.unop ⟶ G.unop`, we can take the opposite of each
component obtaining a natural transformation `G ⟶ F`. -/
@[simps]
protected def removeUnop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F.unop ⟶ G.unop) : G ⟶ F where
  app := fun X => (α.app (unop X)).op
  naturality' := fun X Y f =>
    Quiver.Hom.unop_inj <| by
      simpa only [← functor.unop_map] using (α.naturality f.unop).symm

@[simp]
theorem remove_unop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.removeUnop (𝟙 F.unop) = 𝟙 F :=
  rfl

end

section

variable {F G H : C ⥤ Dᵒᵖ}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : C ⥤ Dᵒᵖ`,
taking `unop` of each component gives a natural transformation `G.left_op ⟶ F.left_op`.
-/
@[simps]
protected def leftOp (α : F ⟶ G) : G.leftOp ⟶ F.leftOp where
  app := fun X => (α.app (unop X)).unop
  naturality' := fun X Y f =>
    Quiver.Hom.op_inj
      (by
        simp )

@[simp]
theorem left_op_id : (𝟙 F : F ⟶ F).leftOp = 𝟙 F.leftOp :=
  rfl

@[simp]
theorem left_op_comp (α : F ⟶ G) (β : G ⟶ H) : (α ≫ β).leftOp = β.leftOp ≫ α.leftOp :=
  rfl

/-- Given a natural transformation `α : F.left_op ⟶ G.left_op`, for `F G : C ⥤ Dᵒᵖ`,
taking `op` of each component gives a natural transformation `G ⟶ F`.
-/
@[simps]
protected def removeLeftOp (α : F.leftOp ⟶ G.leftOp) : G ⟶ F where
  app := fun X => (α.app (op X)).op
  naturality' := fun X Y f =>
    Quiver.Hom.unop_inj <| by
      simpa only [← functor.left_op_map] using (α.naturality f.op).symm

@[simp]
theorem remove_left_op_id : NatTrans.removeLeftOp (𝟙 F.leftOp) = 𝟙 F :=
  rfl

end

section

variable {F G H : Cᵒᵖ ⥤ D}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : Cᵒᵖ ⥤ D`,
taking `op` of each component gives a natural transformation `G.right_op ⟶ F.right_op`.
-/
@[simps]
protected def rightOp (α : F ⟶ G) : G.rightOp ⟶ F.rightOp where
  app := fun X => (α.app _).op
  naturality' := fun X Y f =>
    Quiver.Hom.unop_inj
      (by
        simp )

@[simp]
theorem right_op_id : (𝟙 F : F ⟶ F).rightOp = 𝟙 F.rightOp :=
  rfl

@[simp]
theorem right_op_comp (α : F ⟶ G) (β : G ⟶ H) : (α ≫ β).rightOp = β.rightOp ≫ α.rightOp :=
  rfl

/-- Given a natural transformation `α : F.right_op ⟶ G.right_op`, for `F G : Cᵒᵖ ⥤ D`,
taking `unop` of each component gives a natural transformation `G ⟶ F`.
-/
@[simps]
protected def removeRightOp (α : F.rightOp ⟶ G.rightOp) : G ⟶ F where
  app := fun X => (α.app X.unop).unop
  naturality' := fun X Y f =>
    Quiver.Hom.op_inj <| by
      simpa only [← functor.right_op_map] using (α.naturality f.unop).symm

@[simp]
theorem remove_right_op_id : NatTrans.removeRightOp (𝟙 F.rightOp) = 𝟙 F :=
  rfl

end

end NatTrans

namespace Iso

variable {X Y : C}

/-- The opposite isomorphism.
-/
@[simps]
protected def op (α : X ≅ Y) : op Y ≅ op X where
  Hom := α.Hom.op
  inv := α.inv.op
  hom_inv_id' := Quiver.Hom.unop_inj α.inv_hom_id
  inv_hom_id' := Quiver.Hom.unop_inj α.hom_inv_id

/-- The isomorphism obtained from an isomorphism in the opposite category. -/
@[simps]
def unop {X Y : Cᵒᵖ} (f : X ≅ Y) : Y.unop ≅ X.unop where
  Hom := f.Hom.unop
  inv := f.inv.unop
  hom_inv_id' := by
    simp only [unop_comp, ← f.inv_hom_id, ← unop_id]
  inv_hom_id' := by
    simp only [unop_comp, ← f.hom_inv_id, ← unop_id]

@[simp]
theorem unop_op {X Y : Cᵒᵖ} (f : X ≅ Y) : f.unop.op = f := by
  ext <;> rfl

@[simp]
theorem op_unop {X Y : C} (f : X ≅ Y) : f.op.unop = f := by
  ext <;> rfl

end Iso

namespace NatIso

variable {D : Type u₂} [Category.{v₂} D]

variable {F G : C ⥤ D}

/-- The natural isomorphism between opposite functors `G.op ≅ F.op` induced by a natural
isomorphism between the original functors `F ≅ G`. -/
@[simps]
protected def op (α : F ≅ G) : G.op ≅ F.op where
  Hom := NatTrans.op α.Hom
  inv := NatTrans.op α.inv
  hom_inv_id' := by
    ext
    dsimp'
    rw [← op_comp]
    rw [α.inv_hom_id_app]
    rfl
  inv_hom_id' := by
    ext
    dsimp'
    rw [← op_comp]
    rw [α.hom_inv_id_app]
    rfl

/-- The natural isomorphism between functors `G ≅ F` induced by a natural isomorphism
between the opposite functors `F.op ≅ G.op`. -/
@[simps]
protected def removeOp (α : F.op ≅ G.op) : G ≅ F where
  Hom := NatTrans.removeOp α.Hom
  inv := NatTrans.removeOp α.inv
  hom_inv_id' := by
    ext
    dsimp'
    rw [← unop_comp]
    rw [α.inv_hom_id_app]
    rfl
  inv_hom_id' := by
    ext
    dsimp'
    rw [← unop_comp]
    rw [α.hom_inv_id_app]
    rfl

/-- The natural isomorphism between functors `G.unop ≅ F.unop` induced by a natural isomorphism
between the original functors `F ≅ G`. -/
@[simps]
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : G.unop ≅ F.unop where
  Hom := NatTrans.unop α.Hom
  inv := NatTrans.unop α.inv
  hom_inv_id' := by
    ext
    dsimp'
    rw [← unop_comp]
    rw [α.inv_hom_id_app]
    rfl
  inv_hom_id' := by
    ext
    dsimp'
    rw [← unop_comp]
    rw [α.hom_inv_id_app]
    rfl

end NatIso

namespace Equivalenceₓ

variable {D : Type u₂} [Category.{v₂} D]

/-- An equivalence between categories gives an equivalence between the opposite categories.
-/
@[simps]
def op (e : C ≌ D) : Cᵒᵖ ≌ Dᵒᵖ where
  Functor := e.Functor.op
  inverse := e.inverse.op
  unitIso := (NatIso.op e.unitIso).symm
  counitIso := (NatIso.op e.counitIso).symm
  functor_unit_iso_comp' := fun X => by
    apply Quiver.Hom.unop_inj
    dsimp'
    simp

/-- An equivalence between opposite categories gives an equivalence between the original categories.
-/
@[simps]
def unop (e : Cᵒᵖ ≌ Dᵒᵖ) : C ≌ D where
  Functor := e.Functor.unop
  inverse := e.inverse.unop
  unitIso := (NatIso.unop e.unitIso).symm
  counitIso := (NatIso.unop e.counitIso).symm
  functor_unit_iso_comp' := fun X => by
    apply Quiver.Hom.op_inj
    dsimp'
    simp

end Equivalenceₓ

/-- The equivalence between arrows of the form `A ⟶ B` and `B.unop ⟶ A.unop`. Useful for building
adjunctions.
Note that this (definitionally) gives variants
```
def op_equiv' (A : C) (B : Cᵒᵖ) : (opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
op_equiv _ _

def op_equiv'' (A : Cᵒᵖ) (B : C) : (A ⟶ opposite.op B) ≃ (B ⟶ A.unop) :=
op_equiv _ _

def op_equiv''' (A B : C) : (opposite.op A ⟶ opposite.op B) ≃ (B ⟶ A) :=
op_equiv _ _
```
-/
@[simps]
def opEquiv (A B : Cᵒᵖ) : (A ⟶ B) ≃ (B.unop ⟶ A.unop) where
  toFun := fun f => f.unop
  invFun := fun g => g.op
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance subsingleton_of_unop (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)] : Subsingleton (A ⟶ B) :=
  (opEquiv A B).Subsingleton

instance decidableEqOfUnop (A B : Cᵒᵖ) [DecidableEq (unop B ⟶ unop A)] : DecidableEq (A ⟶ B) :=
  (opEquiv A B).DecidableEq

/-- The equivalence between isomorphisms of the form `A ≅ B` and `B.unop ≅ A.unop`.

Note this is definitionally the same as the other three variants:
* `(opposite.op A ≅ B) ≃ (B.unop ≅ A)`
* `(A ≅ opposite.op B) ≃ (B ≅ A.unop)`
* `(opposite.op A ≅ opposite.op B) ≃ (B ≅ A)`
-/
@[simps]
def isoOpEquiv (A B : Cᵒᵖ) : (A ≅ B) ≃ (B.unop ≅ A.unop) where
  toFun := fun f => f.unop
  invFun := fun g => g.op
  left_inv := fun _ => by
    ext
    rfl
  right_inv := fun _ => by
    ext
    rfl

namespace Functor

variable (C)

variable (D : Type u₂) [Category.{v₂} D]

/-- The equivalence of functor categories induced by `op` and `unop`.
-/
@[simps]
def opUnopEquiv : (C ⥤ D)ᵒᵖ ≌ Cᵒᵖ ⥤ Dᵒᵖ where
  Functor := opHom _ _
  inverse := opInv _ _
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.opUnopIso.op)
      (by
        intro F G f
        dsimp' [← op_unop_iso]
        rw
          [show f = f.unop.op by
            simp ,
          ← op_comp, ← op_comp]
        congr 1
        tidy)
  counitIso :=
    NatIso.ofComponents (fun F => F.unopOpIso)
      (by
        tidy)

/-- The equivalence of functor categories induced by `left_op` and `right_op`.
-/
@[simps]
def leftOpRightOpEquiv : (Cᵒᵖ ⥤ D)ᵒᵖ ≌ C ⥤ Dᵒᵖ where
  Functor := { obj := fun F => F.unop.rightOp, map := fun F G η => η.unop.rightOp }
  inverse := { obj := fun F => op F.leftOp, map := fun F G η => η.leftOp.op }
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.rightOpLeftOpIso.op)
      (by
        intro F G η
        dsimp'
        rw
          [show η = η.unop.op by
            simp ,
          ← op_comp, ← op_comp]
        congr 1
        tidy)
  counitIso :=
    NatIso.ofComponents (fun F => F.leftOpRightOpIso)
      (by
        tidy)

end Functor

end CategoryTheory

