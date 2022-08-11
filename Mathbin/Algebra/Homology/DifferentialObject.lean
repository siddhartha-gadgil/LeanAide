/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Homology.HomologicalComplex
import Mathbin.CategoryTheory.DifferentialObject

/-!
# Homological complexes are differential graded objects.

We verify that a `homological_complex` indexed by an `add_comm_group` is
essentially the same thing as a differential graded object.

This equivalence is probably not particularly useful in practice;
it's here to check that definitions match up as expected.
-/


open CategoryTheory

open CategoryTheory.Limits

open Classical

noncomputable section

namespace HomologicalComplex

variable {β : Type _} [AddCommGroupₓ β] {b : β}

variable {V : Type _} [Category V] [HasZeroMorphisms V]

/-- Since `eq_to_hom` only preserves the fact that `X.X i = X.X j` but not `i = j`, this definition
is used to aid the simplifier. -/
abbrev _root_.category_theory.differential_object.X_eq_to_hom (X : DifferentialObject (GradedObjectWithShift b V))
    {i j : β} (h : i = j) : X.x i ⟶ X.x j :=
  eqToHom (congr_arg X.x h)

@[simp]
theorem _root_.category_theory.differential_object.X_eq_to_hom_refl (X : DifferentialObject (GradedObjectWithShift b V))
    (i : β) : X.xEqToHom (refl i) = 𝟙 _ :=
  rfl

@[simp, reassoc]
theorem eq_to_hom_d (X : DifferentialObject (GradedObjectWithShift b V)) {x y : β} (h : x = y) :
    X.xEqToHom h ≫ X.d y =
      X.d x ≫
        X.xEqToHom
          (by
            cases h
            rfl) :=
  by
  cases h
  dsimp'
  simp

@[simp, reassoc]
theorem d_eq_to_hom (X : HomologicalComplex V (ComplexShape.up' b)) {x y z : β} (h : y = z) :
    X.d x y ≫ eqToHom (congr_arg X.x h) = X.d x z := by
  cases h
  simp

@[simp, reassoc]
theorem eq_to_hom_f' {X Y : DifferentialObject (GradedObjectWithShift b V)} (f : X ⟶ Y) {x y : β} (h : x = y) :
    X.xEqToHom h ≫ f.f y = f.f x ≫ Y.xEqToHom h := by
  cases h
  simp

variable (b V)

attribute [local reducible] graded_object.has_shift

/-- The functor from differential graded objects to homological complexes.
-/
@[simps]
def dgoToHomologicalComplex :
    DifferentialObject (GradedObjectWithShift b V) ⥤ HomologicalComplex V (ComplexShape.up' b) where
  obj := fun X =>
    { x := fun i => X.x i,
      d := fun i j =>
        if h : i + b = j then
          X.d i ≫
            X.xEqToHom
              (show i + (1 : ℤ) • b = j by
                simp [← h])
        else 0,
      shape' := fun i j w => by
        dsimp'  at w
        convert dif_neg w,
      d_comp_d' := fun i j k hij hjk => by
        dsimp'  at hij hjk
        substs hij hjk
        have : X.d i ≫ X.d _ = _ := (congr_fun X.d_squared i : _)
        reassoc! this
        simp [← this] }
  map := fun X Y f =>
    { f := f.f,
      comm' := fun i j h => by
        dsimp'  at h⊢
        subst h
        have : f.f i ≫ Y.d i = X.d i ≫ f.f (i + 1 • b) := (congr_fun f.comm i).symm
        reassoc! this
        simp only [← category.comp_id, ← eq_to_hom_refl, ← dif_pos rfl, ← this, ← category.assoc, ← eq_to_hom_f'] }

/-- The functor from homological complexes to differential graded objects.
-/
@[simps]
def homologicalComplexToDgo :
    HomologicalComplex V (ComplexShape.up' b) ⥤ DifferentialObject (GradedObjectWithShift b V) where
  obj := fun X =>
    { x := fun i => X.x i, d := fun i => X.d i (i + 1 • b),
      d_squared' := by
        ext i
        dsimp'
        simp }
  map := fun X Y f =>
    { f := f.f,
      comm' := by
        ext i
        dsimp'
        simp }

/-- The unit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgoEquivHomologicalComplexUnitIso :
    𝟭 (DifferentialObject (GradedObjectWithShift b V)) ≅ dgoToHomologicalComplex b V ⋙ homologicalComplexToDgo b V :=
  NatIso.ofComponents (fun X => { Hom := { f := fun i => 𝟙 (X.x i) }, inv := { f := fun i => 𝟙 (X.x i) } })
    (by
      tidy)

/-- The counit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgoEquivHomologicalComplexCounitIso :
    homologicalComplexToDgo b V ⋙ dgoToHomologicalComplex b V ≅ 𝟭 (HomologicalComplex V (ComplexShape.up' b)) :=
  NatIso.ofComponents
    (fun X =>
      { Hom :=
          { f := fun i => 𝟙 (X.x i),
            comm' := fun i j h => by
              dsimp'  at h⊢
              subst h
              delta' homological_complex_to_dgo
              simp },
        inv :=
          { f := fun i => 𝟙 (X.x i),
            comm' := fun i j h => by
              dsimp'  at h⊢
              subst h
              delta' homological_complex_to_dgo
              simp } })
    (by
      tidy)

/-- The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
@[simps]
def dgoEquivHomologicalComplex :
    DifferentialObject (GradedObjectWithShift b V) ≌ HomologicalComplex V (ComplexShape.up' b) where
  Functor := dgoToHomologicalComplex b V
  inverse := homologicalComplexToDgo b V
  unitIso := dgoEquivHomologicalComplexUnitIso b V
  counitIso := dgoEquivHomologicalComplexCounitIso b V

end HomologicalComplex

