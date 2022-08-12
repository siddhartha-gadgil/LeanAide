/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Over
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Products in the over category

Shows that products in the over category can be derived from wide pullbacks in the base category.
The main result is `over_product_of_wide_pullback`, which says that if `C` has `J`-indexed wide
pullbacks, then `over B` has `J`-indexed products.
-/


universe w v u

-- morphism levels before object levels. See note [category_theory universes].
open CategoryTheory CategoryTheory.Limits

variable {J : Type w}

variable {C : Type u} [Category.{v} C]

variable {X : C}

namespace CategoryTheory.Over

namespace ConstructProducts

/-- (Implementation)
Given a product diagram in `C/B`, construct the corresponding wide pullback diagram
in `C`.
-/
@[reducible]
def widePullbackDiagramOfDiagramOver (B : C) {J : Type w} (F : Discrete J ⥤ Over B) : WidePullbackShape J ⥤ C :=
  WidePullbackShape.wideCospan B (fun j => (F.obj ⟨j⟩).left) fun j => (F.obj ⟨j⟩).Hom

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivInverseObj (B : C) {J : Type w} (F : Discrete J ⥤ Over B) (c : Cone F) :
    Cone (widePullbackDiagramOfDiagramOver B F) where
  x := c.x.left
  π :=
    { app := fun X =>
        Option.casesOn X c.x.Hom fun j : J =>
          (c.π.app ⟨j⟩).left,-- `tidy` can do this using `case_bash`, but let's try to be a good `-T50000` citizen:
      naturality' := fun X Y f => by
        dsimp'
        cases X <;> cases Y <;> cases f
        · rw [category.id_comp, category.comp_id]
          
        · rw [over.w, category.id_comp]
          
        · rw [category.id_comp, category.comp_id]
           }

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivInverse (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone F ⥤ Cone (widePullbackDiagramOfDiagramOver B F) where
  obj := conesEquivInverseObj B F
  map := fun c₁ c₂ f =>
    { Hom := f.Hom.left,
      w' := fun j => by
        cases j
        · simp
          
        · dsimp'
          rw [← f.w ⟨j⟩]
          rfl
           }

attribute [local tidy] tactic.discrete_cases

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivFunctor (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ⥤ Cone F where
  obj := fun c =>
    { x := Over.mk (c.π.app none),
      π :=
        { app := fun ⟨j⟩ =>
            Over.homMk (c.π.app (some j))
              (by
                apply c.w (wide_pullback_shape.hom.term j)) } }
  map := fun c₁ c₂ f => { Hom := Over.homMk f.Hom }

attribute [local tidy] tactic.case_bash

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def conesEquivUnitIso (B : C) (F : Discrete J ⥤ Over B) :
    𝟭 (Cone (widePullbackDiagramOfDiagramOver B F)) ≅ conesEquivFunctor B F ⋙ conesEquivInverse B F :=
  NatIso.ofComponents
    (fun _ =>
      Cones.ext { Hom := 𝟙 _, inv := 𝟙 _ }
        (by
          tidy))
    (by
      tidy)

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def conesEquivCounitIso (B : C) (F : Discrete J ⥤ Over B) :
    conesEquivInverse B F ⋙ conesEquivFunctor B F ≅ 𝟭 (Cone F) :=
  NatIso.ofComponents
    (fun _ =>
      Cones.ext { Hom := Over.homMk (𝟙 _), inv := Over.homMk (𝟙 _) }
        (by
          tidy))
    (by
      tidy)

/-- (Impl) Establish an equivalence between the category of cones for `F` and for the "grown" `F`.
-/
-- TODO: Can we add `. obviously` to the second arguments of `nat_iso.of_components` and
--       `cones.ext`?
@[simps]
def conesEquiv (B : C) (F : Discrete J ⥤ Over B) : Cone (widePullbackDiagramOfDiagramOver B F) ≌ Cone F where
  Functor := conesEquivFunctor B F
  inverse := conesEquivInverse B F
  unitIso := conesEquivUnitIso B F
  counitIso := conesEquivCounitIso B F

/-- Use the above equivalence to prove we have a limit. -/
theorem has_over_limit_discrete_of_wide_pullback_limit {B : C} (F : Discrete J ⥤ Over B)
    [HasLimit (widePullbackDiagramOfDiagramOver B F)] : HasLimit F :=
  HasLimit.mk
    { Cone := _,
      IsLimit :=
        IsLimit.ofRightAdjoint (conesEquiv B F).Functor (limit.isLimit (widePullbackDiagramOfDiagramOver B F)) }

/-- Given a wide pullback in `C`, construct a product in `C/B`. -/
theorem over_product_of_wide_pullback [HasLimitsOfShape (WidePullbackShape J) C] {B : C} :
    HasLimitsOfShape (Discrete J) (Over B) :=
  { HasLimit := fun F => has_over_limit_discrete_of_wide_pullback_limit F }

/-- Given a pullback in `C`, construct a binary product in `C/B`. -/
theorem over_binary_product_of_pullback [HasPullbacks C] {B : C} : HasBinaryProducts (Over B) :=
  over_product_of_wide_pullback

/-- Given all wide pullbacks in `C`, construct products in `C/B`. -/
theorem over_products_of_wide_pullbacks [HasWidePullbacks.{w} C] {B : C} : HasProducts.{w} (Over B) := fun J =>
  over_product_of_wide_pullback

/-- Given all finite wide pullbacks in `C`, construct finite products in `C/B`. -/
theorem over_finite_products_of_finite_wide_pullbacks [HasFiniteWidePullbacks C] {B : C} : HasFiniteProducts (Over B) :=
  ⟨fun J 𝒥 => over_product_of_wide_pullback⟩

end ConstructProducts

attribute [local tidy] tactic.discrete_cases

/-- Construct terminal object in the over category. This isn't an instance as it's not typically the
way we want to define terminal objects.
(For instance, this gives a terminal object which is different from the generic one given by
`over_product_of_wide_pullback` above.)
-/
theorem over_has_terminal (B : C) : HasTerminal (Over B) :=
  { HasLimit := fun F =>
      HasLimit.mk
        { Cone := { x := Over.mk (𝟙 _), π := { app := fun p => p.as.elim } },
          IsLimit :=
            { lift := fun s => Over.homMk _, fac' := fun _ j => j.as.elim,
              uniq' := fun s m _ => by
                ext
                rw [over.hom_mk_left]
                have := m.w
                dsimp'  at this
                rwa [category.comp_id, category.comp_id] at this } } }

end CategoryTheory.Over

