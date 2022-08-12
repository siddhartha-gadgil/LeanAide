/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathbin.Algebra.PemptyInstances
import Mathbin.Algebra.Hom.Equiv
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms
import Mathbin.CategoryTheory.Elementwise

/-!
# Category instances for has_mul, has_add, semigroup and add_semigroup

We introduce the bundled categories:
* `Magma`
* `AddMagma`
* `Semigroup`
* `AddSemigroup`
along with the relevant forgetful functors between them.

This closely follows `algebra.category.Mon.basic`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/


universe u v

open CategoryTheory

/-- The category of magmas and magma morphisms. -/
@[to_additive AddMagma]
def Magma : Type (u + 1) :=
  Bundled Mul

/-- The category of additive magmas and additive magma morphisms. -/
add_decl_doc AddMagma

namespace Magma

@[to_additive]
instance bundledHom : BundledHom @MulHom :=
  ⟨@MulHom.toFun, @MulHom.id, @MulHom.comp, @MulHom.coe_inj⟩

deriving instance LargeCategory, ConcreteCategory for Magma

attribute [to_additive] Magma.largeCategory Magma.concreteCategory

@[to_additive]
instance : CoeSort Magma (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `Magma` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Mul M] : Magma :=
  Bundled.of M

/-- Construct a bundled `AddMagma` from the underlying type and typeclass. -/
add_decl_doc AddMagma.of

/-- Typecheck a `mul_hom` as a morphism in `Magma`. -/
@[to_additive]
def ofHom {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f

/-- Typecheck a `add_hom` as a morphism in `AddMagma`. -/
add_decl_doc AddMagma.ofHom

@[simp, to_additive]
theorem of_hom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) (x : X) : ofHom f x = f x :=
  rfl

@[to_additive]
instance : Inhabited Magma :=
  ⟨Magma.of Pempty⟩

@[to_additive]
instance (M : Magma) : Mul M :=
  M.str

@[simp, to_additive]
theorem coe_of (R : Type u) [Mul R] : (Magma.of R : Type u) = R :=
  rfl

end Magma

/-- The category of semigroups and semigroup morphisms. -/
@[to_additive AddSemigroupₓₓ]
def Semigroupₓₓ : Type (u + 1) :=
  Bundled Semigroupₓ

/-- The category of additive semigroups and semigroup morphisms. -/
add_decl_doc AddSemigroupₓₓ

namespace Semigroupₓₓ

@[to_additive]
instance : BundledHom.ParentProjection Semigroupₓ.toHasMul :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for Semigroupₓₓ

attribute [to_additive] Semigroupₓₓ.largeCategory Semigroupₓₓ.concreteCategory

@[to_additive]
instance : CoeSort Semigroupₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `Semigroup` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Semigroupₓ M] : Semigroupₓₓ :=
  Bundled.of M

/-- Construct a bundled `AddSemigroup` from the underlying type and typeclass. -/
add_decl_doc AddSemigroupₓₓ.of

/-- Typecheck a `mul_hom` as a morphism in `Semigroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [Semigroupₓ X] [Semigroupₓ Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f

/-- Typecheck a `add_hom` as a morphism in `AddSemigroup`. -/
add_decl_doc AddSemigroupₓₓ.ofHom

@[simp, to_additive]
theorem of_hom_apply {X Y : Type u} [Semigroupₓ X] [Semigroupₓ Y] (f : X →ₙ* Y) (x : X) : ofHom f x = f x :=
  rfl

@[to_additive]
instance : Inhabited Semigroupₓₓ :=
  ⟨Semigroupₓₓ.of Pempty⟩

@[to_additive]
instance (M : Semigroupₓₓ) : Semigroupₓ M :=
  M.str

@[simp, to_additive]
theorem coe_of (R : Type u) [Semigroupₓ R] : (Semigroupₓₓ.of R : Type u) = R :=
  rfl

@[to_additive has_forget_to_AddMagma]
instance hasForgetToMagma : HasForget₂ Semigroupₓₓ Magma :=
  BundledHom.forget₂ _ _

end Semigroupₓₓ

variable {X Y : Type u}

section

variable [Mul X] [Mul Y]

/-- Build an isomorphism in the category `Magma` from a `mul_equiv` between `has_mul`s. -/
@[to_additive AddEquiv.toAddMagmaIso
      "Build an isomorphism in the category `AddMagma` from\nan `add_equiv` between `has_add`s.",
  simps]
def MulEquiv.toMagmaIso (e : X ≃* Y) : Magma.of X ≅ Magma.of Y where
  Hom := e.toMulHom
  inv := e.symm.toMulHom

end

section

variable [Semigroupₓ X] [Semigroupₓ Y]

/-- Build an isomorphism in the category `Semigroup` from a `mul_equiv` between `semigroup`s. -/
@[to_additive AddEquiv.toAddSemigroupIso
      "Build an isomorphism in the category\n`AddSemigroup` from an `add_equiv` between `add_semigroup`s.",
  simps]
def MulEquiv.toSemigroupIso (e : X ≃* Y) : Semigroupₓₓ.of X ≅ Semigroupₓₓ.of Y where
  Hom := e.toMulHom
  inv := e.symm.toMulHom

end

namespace CategoryTheory.Iso

/-- Build a `mul_equiv` from an isomorphism in the category `Magma`. -/
@[to_additive AddMagma_iso_to_add_equiv "Build an `add_equiv` from an isomorphism in the category\n`AddMagma`."]
def magmaIsoToMulEquiv {X Y : Magma} (i : X ≅ Y) : X ≃* Y where
  toFun := i.Hom
  invFun := i.inv
  left_inv := fun x => by
    simp
  right_inv := fun y => by
    simp
  map_mul' := by
    simp

/-- Build a `mul_equiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive "Build an `add_equiv` from an isomorphism in the category\n`AddSemigroup`."]
def semigroupIsoToMulEquiv {X Y : Semigroupₓₓ} (i : X ≅ Y) : X ≃* Y where
  toFun := i.Hom
  invFun := i.inv
  left_inv := fun x => by
    simp
  right_inv := fun y => by
    simp
  map_mul' := by
    simp

end CategoryTheory.Iso

/-- multiplicative equivalences between `has_mul`s are the same as (isomorphic to) isomorphisms
in `Magma` -/
@[to_additive addEquivIsoAddMagmaIso
      "additive equivalences between `has_add`s are the same\nas (isomorphic to) isomorphisms in `AddMagma`"]
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] : X ≃* Y ≅ Magma.of X ≅ Magma.of Y where
  Hom := fun e => e.toMagmaIso
  inv := fun i => i.magmaIsoToMulEquiv

/-- multiplicative equivalences between `semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive addEquivIsoAddSemigroupIso
      "additive equivalences between `add_semigroup`s are\nthe same as (isomorphic to) isomorphisms in `AddSemigroup`"]
def mulEquivIsoSemigroupIso {X Y : Type u} [Semigroupₓ X] [Semigroupₓ Y] :
    X ≃* Y ≅ Semigroupₓₓ.of X ≅ Semigroupₓₓ.of Y where
  Hom := fun e => e.toSemigroupIso
  inv := fun i => i.semigroupIsoToMulEquiv

@[to_additive]
instance Magma.forget_reflects_isos :
    ReflectsIsomorphisms (forget Magma.{u}) where reflects := fun X Y f _ => by
    skip
    let i := as_iso ((forget Magma).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Magma_iso).1⟩

@[to_additive]
instance Semigroupₓₓ.forget_reflects_isos :
    ReflectsIsomorphisms (forget Semigroupₓₓ.{u}) where reflects := fun X Y f _ => by
    skip
    let i := as_iso ((forget Semigroupₓₓ).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Semigroup_iso).1⟩

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/


example : ReflectsIsomorphisms (forget₂ Semigroupₓₓ Magma) := by
  infer_instance

