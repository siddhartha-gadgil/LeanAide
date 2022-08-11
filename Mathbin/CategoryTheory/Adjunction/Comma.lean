/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.StructuredArrow

/-!
# Properties of comma categories relating to adjunctions

This file shows that for a functor `G : D ⥤ C` the data of an initial object in each
`structured_arrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.

Specifically, `adjunction_of_structured_arrow_initials` gives the left adjoint assuming the
appropriate initial objects exist, and `mk_initial_of_left_adjoint` constructs the initial objects
provided a left adjoint.

The duals are also shown.
-/


universe v u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D] (G : D ⥤ C)

section OfInitials

variable [∀ A, HasInitial (StructuredArrow A G)]

/-- Implementation: If each structured arrow category on `G` has an initial object, an equivalence
which is helpful for constructing a left adjoint to `G`.
-/
@[simps]
def leftAdjointOfStructuredArrowInitialsAux (A : C) (B : D) : ((⊥_ StructuredArrow A G).right ⟶ B) ≃ (A ⟶ G.obj B) where
  toFun := fun g => (⊥_ StructuredArrow A G).Hom ≫ G.map g
  invFun := fun f => CommaMorphism.right (initial.to (StructuredArrow.mk f))
  left_inv := fun g => by
    let B' : structured_arrow A G := structured_arrow.mk ((⊥_ structured_arrow A G).Hom ≫ G.map g)
    let g' : ⊥_ structured_arrow A G ⟶ B' := structured_arrow.hom_mk g rfl
    have : initial.to _ = g' := by
      apply colimit.hom_ext
      rintro ⟨⟨⟩⟩
    change comma_morphism.right (initial.to B') = _
    rw [this]
    rfl
  right_inv := fun f => by
    let B' : structured_arrow A G := { right := B, Hom := f }
    apply (comma_morphism.w (initial.to B')).symm.trans (category.id_comp _)

/-- If each structured arrow category on `G` has an initial object, construct a left adjoint to `G`. It
is shown that it is a left adjoint in `adjunction_of_structured_arrow_initials`.
-/
def leftAdjointOfStructuredArrowInitials : C ⥤ D :=
  Adjunction.leftAdjointOfEquiv (leftAdjointOfStructuredArrowInitialsAux G) fun _ _ => by
    simp

/-- If each structured arrow category on `G` has an initial object, we have a constructed left adjoint
to `G`.
-/
def adjunctionOfStructuredArrowInitials : leftAdjointOfStructuredArrowInitials G ⊣ G :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- If each structured arrow category on `G` has an initial object, `G` is a right adjoint. -/
def isRightAdjointOfStructuredArrowInitials : IsRightAdjoint G where
  left := _
  adj := adjunctionOfStructuredArrowInitials G

end OfInitials

section OfTerminals

variable [∀ A, HasTerminal (CostructuredArrow G A)]

/-- Implementation: If each costructured arrow category on `G` has a terminal object, an equivalence
which is helpful for constructing a right adjoint to `G`.
-/
@[simps]
def rightAdjointOfCostructuredArrowTerminalsAux (B : D) (A : C) :
    (G.obj B ⟶ A) ≃ (B ⟶ (⊤_ CostructuredArrow G A).left) where
  toFun := fun g => CommaMorphism.left (terminal.from (CostructuredArrow.mk g))
  invFun := fun g => G.map g ≫ (⊤_ CostructuredArrow G A).Hom
  left_inv := by
    tidy
  right_inv := fun g => by
    let B' : costructured_arrow G A := costructured_arrow.mk (G.map g ≫ (⊤_ costructured_arrow G A).Hom)
    let g' : B' ⟶ ⊤_ costructured_arrow G A := costructured_arrow.hom_mk g rfl
    have : terminal.from _ = g' := by
      apply limit.hom_ext
      rintro ⟨⟨⟩⟩
    change comma_morphism.left (terminal.from B') = _
    rw [this]
    rfl

/-- If each costructured arrow category on `G` has a terminal object, construct a right adjoint to `G`.
It is shown that it is a right adjoint in `adjunction_of_structured_arrow_initials`.
-/
def rightAdjointOfCostructuredArrowTerminals : C ⥤ D :=
  Adjunction.rightAdjointOfEquiv (rightAdjointOfCostructuredArrowTerminalsAux G) fun B₁ B₂ A f g => by
    rw [← Equivₓ.eq_symm_apply]
    simp

/-- If each costructured arrow category on `G` has a terminal object, we have a constructed right
adjoint to `G`.
-/
def adjunctionOfCostructuredArrowTerminals : G ⊣ rightAdjointOfCostructuredArrowTerminals G :=
  Adjunction.adjunctionOfEquivRight _ _

/-- If each costructured arrow category on `G` has an terminal object, `G` is a left adjoint. -/
def isRightAdjointOfCostructuredArrowTerminals : IsLeftAdjoint G where
  right := rightAdjointOfCostructuredArrowTerminals G
  adj := Adjunction.adjunctionOfEquivRight _ _

end OfTerminals

section

variable {F : C ⥤ D}

attribute [local tidy] tactic.discrete_cases

/-- Given a left adjoint to `G`, we can construct an initial object in each structured arrow
category on `G`. -/
def mkInitialOfLeftAdjoint (h : F ⊣ G) (A : C) :
    IsInitial (StructuredArrow.mk (h.Unit.app A) : StructuredArrow A G) where
  desc := fun B =>
    StructuredArrow.homMk ((h.homEquiv _ _).symm B.x.Hom)
      (by
        tidy)
  uniq' := fun s m w => by
    ext
    dsimp'
    rw [Equivₓ.eq_symm_apply, adjunction.hom_equiv_unit]
    apply structured_arrow.w m

/-- Given a right adjoint to `F`, we can construct a terminal object in each costructured arrow
category on `F`. -/
def mkTerminalOfRightAdjoint (h : F ⊣ G) (A : D) :
    IsTerminal (CostructuredArrow.mk (h.counit.app A) : CostructuredArrow F A) where
  lift := fun B =>
    CostructuredArrow.homMk (h.homEquiv _ _ B.x.Hom)
      (by
        tidy)
  uniq' := fun s m w => by
    ext
    dsimp'
    rw [h.eq_hom_equiv_apply, adjunction.hom_equiv_counit]
    exact costructured_arrow.w m

end

end CategoryTheory

