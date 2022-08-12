/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathbin.Algebra.Category.Mon.Basic
import Mathbin.Algebra.Category.Semigroup.Basic
import Mathbin.Algebra.Group.WithOne
import Mathbin.Algebra.FreeMonoid

/-!
# Adjunctions regarding the category of monoids

This file proves the adjunction between adjoining a unit to a semigroup and the forgetful functor
from monoids to semigroups.

## TODO

* free-forgetful adjunction for monoids
* adjunctions related to commutative monoids
-/


universe u

open CategoryTheory

/-- The functor of adjoining a neutral element `one` to a semigroup.
 -/
@[to_additive "The functor of adjoining a neutral element `zero` to a semigroup", simps]
def adjoinOne : Semigroupₓₓ.{u} ⥤ Mon.{u} where
  obj := fun S => Mon.of (WithOne S)
  map := fun X Y => WithOne.map
  map_id' := fun X => WithOne.map_id
  map_comp' := fun X Y Z => WithOne.map_comp

@[to_additive hasForgetToAddSemigroup]
instance hasForgetToSemigroup :
    HasForget₂ Mon
      Semigroupₓₓ where forget₂ := { obj := fun M => Semigroupₓₓ.of M, map := fun M N => MonoidHom.toMulHom }

/-- The adjoin_one-forgetful adjunction from `Semigroup` to `Mon`.-/
@[to_additive "The adjoin_one-forgetful adjunction from `AddSemigroup` to `AddMon`"]
def adjoinOneAdj : adjoinOne ⊣ forget₂ Mon.{u} Semigroupₓₓ.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun S M => WithOne.lift.symm,
      hom_equiv_naturality_left_symm' := by
        intro S T M f g
        ext
        simp only [← Equivₓ.symm_symm, ← adjoin_one_map, ← coe_comp]
        simp_rw [WithOne.map]
        apply WithOne.cases_on x
        · rfl
          
        · simp
           }

/-- The free functor `Type u ⥤ Mon` sending a type `X` to the free monoid on `X`. -/
def free : Type u ⥤ Mon.{u} where
  obj := fun α => Mon.of (FreeMonoid α)
  map := fun X Y => FreeMonoid.map
  map_id' := by
    intros
    ext1
    rfl
  map_comp' := by
    intros
    ext1
    rfl

/-- The free-forgetful adjunction for monoids. -/
def adj : free ⊣ forget Mon.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeMonoid.lift.symm,
      hom_equiv_naturality_left_symm' := fun X Y G f g => by
        ext1
        rfl }

instance : IsRightAdjoint (forget Mon.{u}) :=
  ⟨_, adj⟩

