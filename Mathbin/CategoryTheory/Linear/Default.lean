/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.Invertible
import Mathbin.LinearAlgebra.Basic
import Mathbin.Algebra.Algebra.Basic

/-!
# Linear categories

An `R`-linear category is a category in which `X ⟶ Y` is an `R`-module in such a way that
composition of morphisms is `R`-linear in both variables.

Note that sometimes in the literature a "linear category" is further required to be abelian.

## Implementation

Corresponding to the fact that we need to have an `add_comm_group X` structure in place
to talk about a `module R X` structure,
we need `preadditive C` as a prerequisite typeclass for `linear R C`.
This makes for longer signatures than would be ideal.

## Future work

It would be nice to have a usable framework of enriched categories in which this just became
a category enriched in `Module R`.

-/


universe w v u

open CategoryTheory.Limits

open LinearMap

namespace CategoryTheory

/-- A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that composition is
    `R`-linear in both variables. -/
class Linear (R : Type w) [Semiringₓ R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by
    run_tac
      tactic.apply_instance
  smul_comp' : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g := by
    run_tac
      obviously
  comp_smul' : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g := by
    run_tac
      obviously

attribute [instance] linear.hom_module

restate_axiom linear.smul_comp'

restate_axiom linear.comp_smul'

attribute [simp, reassoc] linear.smul_comp

attribute [reassoc, simp] linear.comp_smul

-- (the linter doesn't like `simp` on the `_assoc` lemma)
end CategoryTheory

open CategoryTheory

namespace CategoryTheory.Linear

variable {C : Type u} [Category.{v} C] [Preadditive C]

instance preadditiveNatLinear : Linear ℕ C where
  smul_comp' := fun X Y Z r f g => (Preadditive.rightComp X g).map_nsmul f r
  comp_smul' := fun X Y Z f r g => (Preadditive.leftComp Z f).map_nsmul g r

instance preadditiveIntLinear : Linear ℤ C where
  smul_comp' := fun X Y Z r f g => (Preadditive.rightComp X g).map_zsmul f r
  comp_smul' := fun X Y Z f r g => (Preadditive.leftComp Z f).map_zsmul g r

section End

variable {R : Type w}

instance [Semiringₓ R] [Linear R C] (X : C) : Module R (End X) := by
  dsimp' [← End]
  infer_instance

instance [CommSemiringₓ R] [Linear R C] (X : C) : Algebra R (End X) :=
  Algebra.ofModule (fun r f g => comp_smul _ _ _ _ _ _) fun r f g => smul_comp _ _ _ _ _ _

end End

section

variable {R : Type w} [Semiringₓ R] [Linear R C]

section InducedCategory

universe u'

variable {C} {D : Type u'} (F : D → C)

instance InducedCategory.category : Linear.{w, v} R (InducedCategory C F) where
  homModule := fun X Y => @Linear.homModule R _ C _ _ _ (F X) (F Y)
  smul_comp' := fun P Q R f f' g => smul_comp' _ _ _ _ _ _
  comp_smul' := fun P Q R f g g' => comp_smul' _ _ _ _ _ _

end InducedCategory

variable (R)

/-- Composition by a fixed left argument as an `R`-linear map. -/
@[simps]
def leftComp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →ₗ[R] X ⟶ Z where
  toFun := fun g => f ≫ g
  map_add' := by
    simp
  map_smul' := by
    simp

/-- Composition by a fixed right argument as an `R`-linear map. -/
@[simps]
def rightComp (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) →ₗ[R] X ⟶ Z where
  toFun := fun f => f ≫ g
  map_add' := by
    simp
  map_smul' := by
    simp

instance {X Y : C} (f : X ⟶ Y) [Epi f] (r : R) [Invertible r] : Epi (r • f) :=
  ⟨fun R g g' H => by
    rw [smul_comp, smul_comp, ← comp_smul, ← comp_smul, cancel_epi] at H
    simpa [← smul_smul] using congr_arg (fun f => ⅟ r • f) H⟩

instance {X Y : C} (f : X ⟶ Y) [Mono f] (r : R) [Invertible r] : Mono (r • f) :=
  ⟨fun R g g' H => by
    rw [comp_smul, comp_smul, ← smul_comp, ← smul_comp, cancel_mono] at H
    simpa [← smul_smul] using congr_arg (fun f => ⅟ r • f) H⟩

end

section

variable {S : Type w} [CommSemiringₓ S] [Linear S C]

/-- Composition as a bilinear map. -/
@[simps]
def comp (X Y Z : C) : (X ⟶ Y) →ₗ[S] (Y ⟶ Z) →ₗ[S] X ⟶ Z where
  toFun := fun f => leftComp S Z f
  map_add' := by
    intros
    ext
    simp
  map_smul' := by
    intros
    ext
    simp

end

end CategoryTheory.Linear

