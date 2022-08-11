/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Closed.Cartesian
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.Conj

/-!
# A cartesian closed category with zero object is trivial

A cartesian closed category with zero object is trivial: it is equivalent to the category with one
object and one morphism.

## References

* https://mathoverflow.net/a/136480

-/


universe v u

noncomputable section

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

variable [HasFiniteProducts C] [CartesianClosed C]

/-- If a cartesian closed category has an initial object which is isomorphic to the terminal object,
then each homset has exactly one element.
-/
def uniqueHomsetOfInitialIsoTerminal [HasInitial C] (i : ⊥_ C ≅ ⊤_ C) (X Y : C) : Unique (X ⟶ Y) :=
  Equivₓ.unique <|
    calc
      (X ⟶ Y) ≃ (X ⨯ ⊤_ C ⟶ Y) := Iso.homCongr (prod.rightUnitor _).symm (Iso.refl _)
      _ ≃ (X ⨯ ⊥_ C ⟶ Y) := Iso.homCongr (prod.mapIso (Iso.refl _) i.symm) (Iso.refl _)
      _ ≃ (⊥_ C ⟶ Y ^^ X) := (exp.adjunction _).homEquiv _ _
      

open ZeroObject

/-- If a cartesian closed category has a zero object, each homset has exactly one element. -/
def uniqueHomsetOfZero [HasZeroObject C] (X Y : C) : Unique (X ⟶ Y) := by
  have : has_initial C := has_zero_object.has_initial
  apply unique_homset_of_initial_iso_terminal _ X Y
  refine' ⟨default, (default : ⊤_ C ⟶ 0) ≫ default, _, _⟩ <;> simp

attribute [local instance] unique_homset_of_zero

/-- A cartesian closed category with a zero object is equivalent to the category with one object and
one morphism.
-/
def equivPunit [HasZeroObject C] : C ≌ Discrete PUnit :=
  Equivalence.mk (Functor.star C) (Functor.fromPunit 0)
    (NatIso.ofComponents (fun X => { Hom := default, inv := default }) fun X Y f => by
      decide)
    (Functor.punitExt _ _)

end CategoryTheory

