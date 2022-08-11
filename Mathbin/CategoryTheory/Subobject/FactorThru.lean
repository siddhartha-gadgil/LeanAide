/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import Mathbin.CategoryTheory.Subobject.Basic
import Mathbin.CategoryTheory.Preadditive.Default

/-!
# Factoring through subobjects

The predicate `h : P.factors f`, for `P : subobject Y` and `f : X ⟶ Y`
asserts the existence of some `P.factor_thru f : X ⟶ (P : C)` making the obvious diagram commute.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

/-- When `f : X ⟶ Y` and `P : mono_over Y`,
`P.factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.factors f`, you can recover the morphism as `P.factor_thru f h`.
-/
def Factors {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) : Prop :=
  ∃ g : X ⟶ (P : C), g ≫ P.arrow = f

theorem factors_congr {X : C} {f g : MonoOver X} {Y : C} (h : Y ⟶ X) (e : f ≅ g) : f.Factors h ↔ g.Factors h :=
  ⟨fun ⟨u, hu⟩ =>
    ⟨u ≫ ((MonoOver.forget _).map e.Hom).left, by
      simp [← hu]⟩,
    fun ⟨u, hu⟩ =>
    ⟨u ≫ ((MonoOver.forget _).map e.inv).left, by
      simp [← hu]⟩⟩

/-- `P.factor_thru f h` provides a factorisation of `f : X ⟶ Y` through some `P : mono_over Y`,
given the evidence `h : P.factors f` that such a factorisation exists. -/
def factorThru {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) (h : Factors P f) : X ⟶ (P : C) :=
  Classical.some h

end MonoOver

namespace Subobject

/-- When `f : X ⟶ Y` and `P : subobject Y`,
`P.factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.factors f`, you can recover the morphism as `P.factor_thru f h`.
-/
def Factors {X Y : C} (P : Subobject Y) (f : X ⟶ Y) : Prop :=
  Quotientₓ.liftOn' P (fun P => P.Factors f)
    (by
      rintro P Q ⟨h⟩
      apply propext
      constructor
      · rintro ⟨i, w⟩
        exact
          ⟨i ≫ h.hom.left, by
            erw [category.assoc, over.w h.hom, w]⟩
        
      · rintro ⟨i, w⟩
        exact
          ⟨i ≫ h.inv.left, by
            erw [category.assoc, over.w h.inv, w]⟩
        )

@[simp]
theorem mk_factors_iff {X Y Z : C} (f : Y ⟶ X) [Mono f] (g : Z ⟶ X) :
    (Subobject.mk f).Factors g ↔ (MonoOver.mk' f).Factors g :=
  Iff.rfl

theorem mk_factors_self (f : X ⟶ Y) [Mono f] : (mk f).Factors f :=
  ⟨𝟙 _, by
    simp ⟩

theorem factors_iff {X Y : C} (P : Subobject Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f :=
  (Quot.induction_on P) fun a => MonoOver.factors_congr _ (representativeIso _).symm

theorem factors_self {X : C} (P : Subobject X) : P.Factors P.arrow :=
  (factors_iff _ _).mpr
    ⟨𝟙 P, by
      simp ⟩

theorem factors_comp_arrow {X Y : C} {P : Subobject Y} (f : X ⟶ P) : P.Factors (f ≫ P.arrow) :=
  (factors_iff _ _).mpr ⟨f, rfl⟩

theorem factors_of_factors_right {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z} (h : P.Factors g) :
    P.Factors (f ≫ g) := by
  revert P
  refine' Quotientₓ.ind' _
  intro P
  rintro ⟨g, rfl⟩
  exact
    ⟨f ≫ g, by
      simp ⟩

theorem factors_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} : P.Factors (0 : X ⟶ Y) :=
  (factors_iff _ _).mpr
    ⟨0, by
      simp ⟩

theorem factors_of_le {Y Z : C} {P Q : Subobject Y} (f : Z ⟶ Y) (h : P ≤ Q) : P.Factors f → Q.Factors f := by
  simp only [← factors_iff]
  exact fun ⟨u, hu⟩ =>
    ⟨u ≫ of_le _ _ h, by
      simp [hu]⟩

/-- `P.factor_thru f h` provides a factorisation of `f : X ⟶ Y` through some `P : subobject Y`,
given the evidence `h : P.factors f` that such a factorisation exists. -/
def factorThru {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : X ⟶ P :=
  Classical.some ((factors_iff _ _).mp h)

@[simp, reassoc]
theorem factor_thru_arrow {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f :=
  Classical.some_spec ((factors_iff _ _).mp h)

@[simp]
theorem factor_thru_self {X : C} (P : Subobject X) (h) : P.factorThru P.arrow h = 𝟙 P := by
  ext
  simp

@[simp]
theorem factor_thru_mk_self (f : X ⟶ Y) [Mono f] : (mk f).factorThru f (mk_factors_self f) = (underlyingIso f).inv := by
  ext
  simp

@[simp]
theorem factor_thru_comp_arrow {X Y : C} {P : Subobject Y} (f : X ⟶ P) (h) : P.factorThru (f ≫ P.arrow) h = f := by
  ext
  simp

@[simp]
theorem factor_thru_eq_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} {f : X ⟶ Y} {h : Factors P f} :
    P.factorThru f h = 0 ↔ f = 0 := by
  fconstructor
  · intro w
    replace w := w =≫ P.arrow
    simpa using w
    
  · rintro rfl
    ext
    simp
    

theorem factor_thru_right {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h : P.Factors g) :
    f ≫ P.factorThru g h = P.factorThru (f ≫ g) (factors_of_factors_right f h) := by
  apply (cancel_mono P.arrow).mp
  simp

@[simp]
theorem factor_thru_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} (h : P.Factors (0 : X ⟶ Y)) :
    P.factorThru 0 h = 0 := by
  simp

-- `h` is an explicit argument here so we can use
-- `rw factor_thru_le h`, obtaining a subgoal `P.factors f`.
-- (While the reverse direction looks plausible as a simp lemma, it seems to be unproductive.)
theorem factor_thru_of_le {Y Z : C} {P Q : Subobject Y} {f : Z ⟶ Y} (h : P ≤ Q) (w : P.Factors f) :
    Q.factorThru f (factors_of_le f h w) = P.factorThru f w ≫ ofLe P Q h := by
  ext
  simp

section Preadditive

variable [Preadditive C]

theorem factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (wf : P.Factors f) (wg : P.Factors g) :
    P.Factors (f + g) :=
  (factors_iff _ _).mpr
    ⟨P.factorThru f wf + P.factorThru g wg, by
      simp ⟩

-- This can't be a `simp` lemma as `wf` and `wg` may not exist.
-- However you can `rw` by it to assert that `f` and `g` factor through `P` separately.
theorem factor_thru_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g)) (wf : P.Factors f)
    (wg : P.Factors g) : P.factorThru (f + g) w = P.factorThru f wf + P.factorThru g wg := by
  ext
  simp

theorem factors_left_of_factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g))
    (wg : P.Factors g) : P.Factors f :=
  (factors_iff _ _).mpr
    ⟨P.factorThru (f + g) w - P.factorThru g wg, by
      simp ⟩

@[simp]
theorem factor_thru_add_sub_factor_thru_right {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g))
    (wg : P.Factors g) :
    P.factorThru (f + g) w - P.factorThru g wg = P.factorThru f (factors_left_of_factors_add f g w wg) := by
  ext
  simp

theorem factors_right_of_factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g))
    (wf : P.Factors f) : P.Factors g :=
  (factors_iff _ _).mpr
    ⟨P.factorThru (f + g) w - P.factorThru f wf, by
      simp ⟩

@[simp]
theorem factor_thru_add_sub_factor_thru_left {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g))
    (wf : P.Factors f) :
    P.factorThru (f + g) w - P.factorThru f wf = P.factorThru g (factors_right_of_factors_add f g w wf) := by
  ext
  simp

end Preadditive

end Subobject

end CategoryTheory

