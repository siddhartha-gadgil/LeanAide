/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel
-/
import Mathbin.Algebra.Category.Group.Preadditive
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.Linear.Default
import Mathbin.CategoryTheory.Elementwise
import Mathbin.LinearAlgebra.Basic
import Mathbin.CategoryTheory.Conj
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The category of `R`-modules

`Module.{v} R` is the category of bundled `R`-modules with carrier in the universe `v`. We show
that it is preadditive and show that being an isomorphism, monomorphism and epimorphism is
equivalent to being a linear equivalence, an injective linear map and a surjective linear map,
respectively.

## Implementation details

To construct an object in the category of `R`-modules from a type `M` with an instance of the
`module` typeclass, write `of R M`. There is a coercion in the other direction.

Similarly, there is a coercion from morphisms in `Module R` to linear maps.

Unfortunately, Lean is not smart enough to see that, given an object `M : Module R`, the expression
`of R M`, where we coerce `M` to the carrier type, is definitionally equal to `M` itself.
This means that to go the other direction, i.e., from linear maps/equivalences to (iso)morphisms
in the category of `R`-modules, we have to take care not to inadvertently end up with an
`of R M` where `M` is already an object. Hence, given `f : M →ₗ[R] N`,
* if `M N : Module R`, simply use `f`;
* if `M : Module R` and `N` is an unbundled `R`-module, use `↿f` or `as_hom_left f`;
* if `M` is an unbundled `R`-module and `N : Module R`, use `↾f` or `as_hom_right f`;
* if `M` and `N` are unbundled `R`-modules, use `↟f` or `as_hom f`.

Similarly, given `f : M ≃ₗ[R] N`, use `to_Module_iso`, `to_Module_iso'_left`, `to_Module_iso'_right`
or `to_Module_iso'`, respectively.

The arrow notations are localized, so you may have to `open_locale Module` to use them. Note that
the notation for `as_hom_left` clashes with the notation used to promote functions between types to
morphisms in the category `Type`, so to avoid confusion, it is probably a good idea to avoid having
the locales `Module` and `category_theory.Type` open at the same time.

If you get an error when trying to apply a theorem and the `convert` tactic produces goals of the
form `M = of R M`, then you probably used an incorrect variant of `as_hom` or `to_Module_iso`.

-/


open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe v u

variable (R : Type u) [Ringₓ R]

/-- The category of R-modules and their morphisms.

 Note that in the case of `R = ℤ`, we can not
impose here that the `ℤ`-multiplication field from the module structure is defeq to the one coming
from the `is_add_comm_group` structure (contrary to what we do for all module structures in
mathlib), which creates some difficulties down the road. -/
structure ModuleCat where
  Carrier : Type v
  [isAddCommGroup : AddCommGroupₓ carrier]
  [isModule : Module R carrier]

attribute [instance] ModuleCat.isAddCommGroup ModuleCat.isModule

namespace ModuleCat

instance : CoeSort (ModuleCat.{v} R) (Type v) :=
  ⟨ModuleCat.Carrier⟩

instance moduleCategory : Category (ModuleCat.{v} R) where
  Hom := fun M N => M →ₗ[R] N
  id := fun M => 1
  comp := fun A B C f g => g.comp f
  id_comp' := fun X Y f => LinearMap.id_comp _
  comp_id' := fun X Y f => LinearMap.comp_id _
  assoc' := fun W X Y Z f g h => LinearMap.comp_assoc _ _ _

instance moduleConcreteCategory : ConcreteCategory.{v} (ModuleCat.{v} R) where
  forget := { obj := fun R => R, map := fun R S f => (f : R → S) }
  forget_faithful := {  }

instance hasForgetToAddCommGroup :
    HasForget₂ (ModuleCat R)
      AddCommGroupₓₓ where forget₂ :=
    { obj := fun M => AddCommGroupₓₓ.of M, map := fun M₁ M₂ f => LinearMap.toAddMonoidHom f }

instance (M N : ModuleCat R) : LinearMapClass (M ⟶ N) R M N :=
  { LinearMap.semilinearMapClass with coe := fun f => f }

/-- The object in the category of R-modules associated to an R-module -/
def of (X : Type v) [AddCommGroupₓ X] [Module R X] : ModuleCat R :=
  ⟨X⟩

@[simp]
theorem forget₂_obj (X : ModuleCat R) : (forget₂ (ModuleCat R) AddCommGroupₓₓ).obj X = AddCommGroupₓₓ.of X :=
  rfl

@[simp]
theorem forget₂_obj_Module_of (X : Type v) [AddCommGroupₓ X] [Module R X] :
    (forget₂ (ModuleCat R) AddCommGroupₓₓ).obj (of R X) = AddCommGroupₓₓ.of X :=
  rfl

@[simp]
theorem forget₂_map (X Y : ModuleCat R) (f : X ⟶ Y) :
    (forget₂ (ModuleCat R) AddCommGroupₓₓ).map f = LinearMap.toAddMonoidHom f :=
  rfl

/-- Typecheck a `linear_map` as a morphism in `Module R`. -/
def ofHom {R : Type u} [Ringₓ R] {X Y : Type v} [AddCommGroupₓ X] [Module R X] [AddCommGroupₓ Y] [Module R Y]
    (f : X →ₗ[R] Y) : of R X ⟶ of R Y :=
  f

@[simp]
theorem of_hom_apply {R : Type u} [Ringₓ R] {X Y : Type v} [AddCommGroupₓ X] [Module R X] [AddCommGroupₓ Y] [Module R Y]
    (f : X →ₗ[R] Y) (x : X) : ofHom f x = f x :=
  rfl

instance : Inhabited (ModuleCat R) :=
  ⟨of R PUnit⟩

instance ofUnique {X : Type v} [AddCommGroupₓ X] [Module R X] [i : Unique X] : Unique (of R X) :=
  i

@[simp]
theorem coe_of (X : Type v) [AddCommGroupₓ X] [Module R X] : (of R X : Type v) = X :=
  rfl

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[simps]
def ofSelfIso (M : ModuleCat R) : ModuleCat.of R M ≅ M where
  Hom := 𝟙 M
  inv := 𝟙 M

theorem is_zero_of_subsingleton (M : ModuleCat R) [Subsingleton M] : IsZero M := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext
    have : x = 0 := Subsingleton.elimₓ _ _
    rw [this, map_zero, map_zero]
    
  · ext
    apply Subsingleton.elimₓ
    

instance : HasZeroObject (ModuleCat.{v} R) :=
  ⟨⟨of R PUnit, is_zero_of_subsingleton _⟩⟩

variable {R} {M N U : ModuleCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl

end ModuleCat

variable {R}

variable {X₁ X₂ : Type v}

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def ModuleCat.asHom [AddCommGroupₓ X₁] [Module R X₁] [AddCommGroupₓ X₂] [Module R X₂] :
    (X₁ →ₗ[R] X₂) → (ModuleCat.of R X₁ ⟶ ModuleCat.of R X₂) :=
  id

-- mathport name: «expr↟ »
localized [ModuleCat] notation "↟" f:1024 => ModuleCat.asHom f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def ModuleCat.asHomRight [AddCommGroupₓ X₁] [Module R X₁] {X₂ : ModuleCat.{v} R} :
    (X₁ →ₗ[R] X₂) → (ModuleCat.of R X₁ ⟶ X₂) :=
  id

-- mathport name: «expr↾ »
localized [ModuleCat] notation "↾" f:1024 => ModuleCat.asHomRight f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def ModuleCat.asHomLeft {X₁ : ModuleCat.{v} R} [AddCommGroupₓ X₂] [Module R X₂] :
    (X₁ →ₗ[R] X₂) → (X₁ ⟶ ModuleCat.of R X₂) :=
  id

-- mathport name: «expr↿ »
localized [ModuleCat] notation "↿" f:1024 => ModuleCat.asHomLeft f

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
@[simps]
def LinearEquiv.toModuleIso {g₁ : AddCommGroupₓ X₁} {g₂ : AddCommGroupₓ X₂} {m₁ : Module R X₁} {m₂ : Module R X₂}
    (e : X₁ ≃ₗ[R] X₂) : ModuleCat.of R X₁ ≅ ModuleCat.of R X₂ where
  Hom := (e : X₁ →ₗ[R] X₂)
  inv := (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id' := by
    ext
    exact e.left_inv x
  inv_hom_id' := by
    ext
    exact e.right_inv x

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s.

This version is better than `linear_equiv_to_Module_iso` when applicable, because Lean can't see
`Module.of R M` is defeq to `M` when `M : Module R`. -/
@[simps]
def LinearEquiv.toModuleIso' {M N : ModuleCat.{v} R} (i : M ≃ₗ[R] N) : M ≅ N where
  Hom := i
  inv := i.symm
  hom_inv_id' :=
    LinearMap.ext fun x => by
      simp
  inv_hom_id' :=
    LinearMap.ext fun x => by
      simp

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s.

This version is better than `linear_equiv_to_Module_iso` when applicable, because Lean can't see
`Module.of R M` is defeq to `M` when `M : Module R`. -/
@[simps]
def LinearEquiv.toModuleIso'Left {X₁ : ModuleCat.{v} R} {g₂ : AddCommGroupₓ X₂} {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) :
    X₁ ≅ ModuleCat.of R X₂ where
  Hom := (e : X₁ →ₗ[R] X₂)
  inv := (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id' :=
    LinearMap.ext fun x => by
      simp
  inv_hom_id' :=
    LinearMap.ext fun x => by
      simp

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s.

This version is better than `linear_equiv_to_Module_iso` when applicable, because Lean can't see
`Module.of R M` is defeq to `M` when `M : Module R`. -/
@[simps]
def LinearEquiv.toModuleIso'Right {g₁ : AddCommGroupₓ X₁} {m₁ : Module R X₁} {X₂ : ModuleCat.{v} R} (e : X₁ ≃ₗ[R] X₂) :
    ModuleCat.of R X₁ ≅ X₂ where
  Hom := (e : X₁ →ₗ[R] X₂)
  inv := (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id' :=
    LinearMap.ext fun x => by
      simp
  inv_hom_id' :=
    LinearMap.ext fun x => by
      simp

namespace CategoryTheory.Iso

/-- Build a `linear_equiv` from an isomorphism in the category `Module R`. -/
@[simps]
def toLinearEquiv {X Y : ModuleCat R} (i : X ≅ Y) : X ≃ₗ[R] Y where
  toFun := i.Hom
  invFun := i.inv
  left_inv := by
    tidy
  right_inv := by
    tidy
  map_add' := by
    tidy
  map_smul' := by
    tidy

end CategoryTheory.Iso

/-- linear equivalences between `module`s are the same as (isomorphic to) isomorphisms
in `Module` -/
@[simps]
def linearEquivIsoModuleIso {X Y : Type u} [AddCommGroupₓ X] [AddCommGroupₓ Y] [Module R X] [Module R Y] :
    (X ≃ₗ[R] Y) ≅ ModuleCat.of R X ≅ ModuleCat.of R Y where
  Hom := fun e => e.toModuleIso
  inv := fun i => i.toLinearEquiv

namespace ModuleCat

instance : Preadditive (ModuleCat.{v} R) where
  add_comp' := fun P Q R f f' g =>
    show (f + f') ≫ g = f ≫ g + f' ≫ g by
      ext
      simp
  comp_add' := fun P Q R f g g' =>
    show f ≫ (g + g') = f ≫ g + f ≫ g' by
      ext
      simp

instance forget₂_AddCommGroup_additive : (forget₂ (ModuleCat.{v} R) AddCommGroupₓₓ).Additive where

section

variable {S : Type u} [CommRingₓ S]

instance : Linear S (ModuleCat.{v} S) where
  homModule := fun X Y => LinearMap.module
  smul_comp' := by
    intros
    ext
    simp
  comp_smul' := by
    intros
    ext
    simp

variable {X Y X' Y' : ModuleCat.{v} S}

theorem Iso.hom_congr_eq_arrow_congr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = LinearEquiv.arrowCongr i.toLinearEquiv j.toLinearEquiv f :=
  rfl

theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) : Iso.conj i f = LinearEquiv.conj i.toLinearEquiv f :=
  rfl

end

end ModuleCat

instance (M : Type u) [AddCommGroupₓ M] [Module R M] : Coe (Submodule R M) (ModuleCat R) :=
  ⟨fun N => ModuleCat.of R N⟩

