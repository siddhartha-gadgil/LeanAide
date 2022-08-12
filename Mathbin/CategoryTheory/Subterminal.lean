/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.Subobject.MonoOver

/-!
# Subterminal objects

Subterminal objects are the objects which can be thought of as subobjects of the terminal object.
In fact, the definition can be constructed to not require a terminal object, by defining `A` to be
subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`.
An alternate definition is that the diagonal morphism `A ⟶ A ⨯ A` is an isomorphism.
In this file we define subterminal objects and show the equivalence of these three definitions.

We also construct the subcategory of subterminal objects.

## TODO

* Define exponential ideals, and show this subcategory is an exponential ideal.
* Use the above to show that in a locally cartesian closed category, every subobject lattice
  is cartesian closed (equivalently, a Heyting algebra).

-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits Category

variable {C : Type u₁} [Category.{v₁} C] {A : C}

/-- An object `A` is subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`. -/
def IsSubterminal (A : C) : Prop :=
  ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g

theorem IsSubterminal.def : IsSubterminal A ↔ ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g :=
  Iff.rfl

/-- If `A` is subterminal, the unique morphism from it to a terminal object is a monomorphism.
The converse of `is_subterminal_of_mono_is_terminal_from`.
-/
theorem IsSubterminal.mono_is_terminal_from (hA : IsSubterminal A) {T : C} (hT : IsTerminal T) : Mono (hT.from A) :=
  { right_cancellation := fun Z g h _ => hA _ _ }

/-- If `A` is subterminal, the unique morphism from it to the terminal object is a monomorphism.
The converse of `is_subterminal_of_mono_terminal_from`.
-/
theorem IsSubterminal.mono_terminal_from [HasTerminal C] (hA : IsSubterminal A) : Mono (terminal.from A) :=
  hA.mono_is_terminal_from terminalIsTerminal

/-- If the unique morphism from `A` to a terminal object is a monomorphism, `A` is subterminal.
The converse of `is_subterminal.mono_is_terminal_from`.
-/
theorem is_subterminal_of_mono_is_terminal_from {T : C} (hT : IsTerminal T) [Mono (hT.from A)] : IsSubterminal A :=
  fun Z f g => by
  rw [← cancel_mono (hT.from A)]
  apply hT.hom_ext

/-- If the unique morphism from `A` to the terminal object is a monomorphism, `A` is subterminal.
The converse of `is_subterminal.mono_terminal_from`.
-/
theorem is_subterminal_of_mono_terminal_from [HasTerminal C] [Mono (terminal.from A)] : IsSubterminal A := fun Z f g =>
  by
  rw [← cancel_mono (terminal.from A)]
  apply Subsingleton.elimₓ

theorem is_subterminal_of_is_terminal {T : C} (hT : IsTerminal T) : IsSubterminal T := fun Z f g => hT.hom_ext _ _

theorem is_subterminal_of_terminal [HasTerminal C] : IsSubterminal (⊤_ C) := fun Z f g => Subsingleton.elimₓ _ _

/-- If `A` is subterminal, its diagonal morphism is an isomorphism.
The converse of `is_subterminal_of_is_iso_diag`.
-/
theorem IsSubterminal.is_iso_diag (hA : IsSubterminal A) [HasBinaryProduct A A] : IsIso (diag A) :=
  ⟨⟨Limits.prod.fst,
      ⟨by
        simp , by
        rw [is_subterminal.def] at hA
        tidy⟩⟩⟩

/-- If the diagonal morphism of `A` is an isomorphism, then it is subterminal.
The converse of `is_subterminal.is_iso_diag`.
-/
theorem is_subterminal_of_is_iso_diag [HasBinaryProduct A A] [IsIso (diag A)] : IsSubterminal A := fun Z f g => by
  have : (limits.prod.fst : A ⨯ A ⟶ _) = limits.prod.snd := by
    simp [cancel_epi (diag A)]
  rw [← prod.lift_fst f g, this, prod.lift_snd]

/-- If `A` is subterminal, it is isomorphic to `A ⨯ A`. -/
@[simps]
def IsSubterminal.isoDiag (hA : IsSubterminal A) [HasBinaryProduct A A] : A ⨯ A ≅ A := by
  let this := is_subterminal.is_iso_diag hA
  apply (as_iso (diag A)).symm

variable (C)

/-- The (full sub)category of subterminal objects.
TODO: If `C` is the category of sheaves on a topological space `X`, this category is equivalent
to the lattice of open subsets of `X`. More generally, if `C` is a topos, this is the lattice of
"external truth values".
-/
def Subterminals (C : Type u₁) [Category.{v₁} C] :=
  { A : C // IsSubterminal A }deriving Category

instance [HasTerminal C] : Inhabited (Subterminals C) :=
  ⟨⟨⊤_ C, is_subterminal_of_terminal⟩⟩

/-- The inclusion of the subterminal objects into the original category. -/
@[simps]
def subterminalInclusion : Subterminals C ⥤ C :=
  fullSubcategoryInclusion _ deriving Full, Faithful

instance subterminals_thin (X Y : Subterminals C) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => Y.2 f g⟩

/-- The category of subterminal objects is equivalent to the category of monomorphisms to the terminal
object (which is in turn equivalent to the subobjects of the terminal object).
-/
@[simps]
def subterminalsEquivMonoOverTerminal [HasTerminal C] : Subterminals C ≌ MonoOver (⊤_ C) where
  Functor :=
    { obj := fun X => ⟨Over.mk (terminal.from X.1), X.2.mono_terminal_from⟩,
      map := fun X Y f =>
        MonoOver.homMk f
          (by
            ext1 ⟨⟨⟩⟩) }
  inverse :=
    { obj := fun X =>
        ⟨X.val.left, fun Z f g => by
          rw [← cancel_mono X.arrow]
          apply Subsingleton.elimₓ⟩,
      map := fun X Y f => f.1 }
  unitIso := { Hom := { app := fun X => 𝟙 _ }, inv := { app := fun X => 𝟙 _ } }
  counitIso := { Hom := { app := fun X => Over.homMk (𝟙 _) }, inv := { app := fun X => Over.homMk (𝟙 _) } }

@[simp]
theorem subterminals_to_mono_over_terminal_comp_forget [HasTerminal C] :
    (subterminalsEquivMonoOverTerminal C).Functor ⋙ MonoOver.forget _ ⋙ Over.forget _ = subterminalInclusion C :=
  rfl

@[simp]
theorem mono_over_terminal_to_subterminals_comp [HasTerminal C] :
    (subterminalsEquivMonoOverTerminal C).inverse ⋙ subterminalInclusion C = MonoOver.forget _ ⋙ Over.forget _ :=
  rfl

end CategoryTheory

