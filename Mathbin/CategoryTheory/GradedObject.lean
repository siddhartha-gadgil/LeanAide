/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Int.Basic
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.CategoryTheory.Pi.Basic
import Mathbin.CategoryTheory.Shift
import Mathbin.CategoryTheory.ConcreteCategory.Basic

/-!
# The category of graded objects

For any type `β`, a `β`-graded object over some category `C` is just
a function `β → C` into the objects of `C`.
We put the "pointwise" category structure on these, as the non-dependent specialization of
`category_theory.pi`.

We describe the `comap` functors obtained by precomposing with functions `β → γ`.

As a consequence a fixed element (e.g. `1`) in an additive group `β` provides a shift
functor on `β`-graded objects

When `C` has coproducts we construct the `total` functor `graded_object β C ⥤ C`,
show that it is faithful, and deduce that when `C` is concrete so is `graded_object β C`.
-/


open CategoryTheory.pi

open CategoryTheory.Limits

namespace CategoryTheory

universe w v u

/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`. -/
def GradedObject (β : Type w) (C : Type u) : Type max w u :=
  β → C

-- Satisfying the inhabited linter...
instance inhabitedGradedObject (β : Type w) (C : Type u) [Inhabited C] : Inhabited (GradedObject β C) :=
  ⟨fun b => Inhabited.default⟩

/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`
with a shift functor given by translation by `s`.
-/
-- `s` is here to distinguish type synonyms asking for different shifts
@[nolint unused_arguments]
abbrev GradedObjectWithShift {β : Type w} [AddCommGroupₓ β] (s : β) (C : Type u) : Type max w u :=
  GradedObject β C

namespace GradedObject

variable {C : Type u} [Category.{v} C]

instance categoryOfGradedObjects (β : Type w) : Category.{max w v} (GradedObject β C) :=
  CategoryTheory.pi fun _ => C

/-- The projection of a graded object to its `i`-th component. -/
@[simps]
def eval {β : Type w} (b : β) : GradedObject β C ⥤ C where
  obj := fun X => X b
  map := fun X Y f => f b

section

variable (C)

/-- The natural isomorphism comparing between
pulling back along two propositionally equal functions.
-/
@[simps]
def comapEq {β γ : Type w} {f g : β → γ} (h : f = g) : comap (fun _ => C) f ≅ comap (fun _ => C) g where
  hom :=
    { app := fun X b =>
        eqToHom
          (by
            dsimp' [← comap]
            subst h) }
  inv :=
    { app := fun X b =>
        eqToHom
          (by
            dsimp' [← comap]
            subst h) }

theorem comap_eq_symm {β γ : Type w} {f g : β → γ} (h : f = g) : comapEq C h.symm = (comapEq C h).symm := by
  tidy

theorem comap_eq_trans {β γ : Type w} {f g h : β → γ} (k : f = g) (l : g = h) :
    comapEq C (k.trans l) = comapEq C k ≪≫ comapEq C l := by
  ext X b
  simp

@[simp]
theorem eq_to_hom_apply {β : Type w} {X Y : ∀ b : β, C} (h : X = Y) (b : β) :
    (eqToHom h : X ⟶ Y) b =
      eqToHom
        (by
          subst h) :=
  by
  subst h
  rfl

/-- The equivalence between β-graded objects and γ-graded objects,
given an equivalence between β and γ.
-/
@[simps]
def comapEquiv {β γ : Type w} (e : β ≃ γ) : GradedObject β C ≌ GradedObject γ C where
  Functor := comap (fun _ => C) (e.symm : γ → β)
  inverse := comap (fun _ => C) (e : β → γ)
  counitIso :=
    (comapComp (fun _ => C) _ _).trans
      (comapEq C
        (by
          ext
          simp ))
  unitIso :=
    (comapEq C
          (by
            ext
            simp )).trans
      (comapComp _ _ _).symm
  functor_unit_iso_comp' := fun X => by
    ext b
    dsimp'
    simp

-- See note [dsimp, simp].
end

instance hasShift {β : Type _} [AddCommGroupₓ β] (s : β) : HasShift (GradedObjectWithShift s C) ℤ :=
  hasShiftMk _ _
    { f := fun n => (comap fun _ => C) fun b : β => b + n • s,
      ε :=
        (comapId β fun _ => C).symm ≪≫
          comapEq C
            (by
              ext
              simp ),
      μ := fun m n =>
        comapComp _ _ _ ≪≫
          comapEq C
            (by
              ext
              simp [← add_zsmul, ← add_commₓ]),
      left_unitality := by
        introv
        ext
        dsimp'
        simpa,
      right_unitality := by
        introv
        ext
        dsimp'
        simpa,
      associativity := by
        introv
        ext
        dsimp'
        simp }

@[simp]
theorem shift_functor_obj_apply {β : Type _} [AddCommGroupₓ β] (s : β) (X : β → C) (t : β) (n : ℤ) :
    (shiftFunctor (GradedObjectWithShift s C) n).obj X t = X (t + n • s) :=
  rfl

@[simp]
theorem shift_functor_map_apply {β : Type _} [AddCommGroupₓ β] (s : β) {X Y : GradedObjectWithShift s C} (f : X ⟶ Y)
    (t : β) (n : ℤ) : (shiftFunctor (GradedObjectWithShift s C) n).map f t = f (t + n • s) :=
  rfl

instance hasZeroMorphisms [HasZeroMorphisms C] (β : Type w) :
    HasZeroMorphisms.{max w v} (GradedObject β C) where HasZero := fun X Y => { zero := fun b => 0 }

@[simp]
theorem zero_apply [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) (b : β) : (0 : X ⟶ Y) b = 0 :=
  rfl

section

open ZeroObject

instance has_zero_object [HasZeroObject C] [HasZeroMorphisms C] (β : Type w) :
    HasZeroObject.{max w v} (GradedObject β C) := by
  refine' ⟨⟨fun b => 0, fun X => ⟨⟨⟨fun b => 0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨fun b => 0⟩, fun f => _⟩⟩⟩⟩ <;> ext

end

end GradedObject

namespace GradedObject

-- The universes get a little hairy here, so we restrict the universe level for the grading to 0.
-- Since we're typically interested in grading by ℤ or a finite group, this should be okay.
-- If you're grading by things in higher universes, have fun!
variable (β : Type)

variable (C : Type u) [Category.{v} C]

variable [HasCoproducts.{0} C]

section

attribute [local tidy] tactic.discrete_cases

/-- The total object of a graded object is the coproduct of the graded components.
-/
noncomputable def total : GradedObject β C ⥤ C where
  obj := fun X => ∐ fun i : β => X i
  map := fun X Y f => Limits.Sigma.map fun i => f i

end

variable [HasZeroMorphisms C]

/-- The `total` functor taking a graded object to the coproduct of its graded components is faithful.
To prove this, we need to know that the coprojections into the coproduct are monomorphisms,
which follows from the fact we have zero morphisms and decidable equality for the grading.
-/
instance :
    Faithful (total β C) where map_injective' := fun X Y f g w => by
    classical
    ext i
    replace w := sigma.ι (fun i : β => X i) i ≫= w
    erw [colimit.ι_map, colimit.ι_map] at w
    simp at *
    exact mono.right_cancellation _ _ w

end GradedObject

namespace GradedObject

noncomputable section

variable (β : Type)

variable (C : Type (u + 1)) [LargeCategory C] [ConcreteCategory C] [HasCoproducts.{0} C] [HasZeroMorphisms C]

instance : ConcreteCategory (GradedObject β C) where forget := total β C ⋙ forget C

instance : HasForget₂ (GradedObject β C) C where forget₂ := total β C

end GradedObject

end CategoryTheory

