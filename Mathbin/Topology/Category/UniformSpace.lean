/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Scott Morrison
-/
import Mathbin.CategoryTheory.Adjunction.Reflective
import Mathbin.CategoryTheory.ConcreteCategory.UnbundledHom
import Mathbin.CategoryTheory.Monad.Limits
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.Topology.Category.Top.Basic
import Mathbin.Topology.UniformSpace.Completion

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/


universe u

open CategoryTheory

/-- A (bundled) uniform space. -/
def UniformSpaceₓ : Type (u + 1) :=
  Bundled UniformSpace

namespace UniformSpaceₓ

/-- The information required to build morphisms for `UniformSpace`. -/
instance : UnbundledHom @UniformContinuous :=
  ⟨@uniform_continuous_id, @UniformContinuous.comp⟩

deriving instance LargeCategory, ConcreteCategory for UniformSpaceₓ

instance : CoeSort UniformSpaceₓ (Type _) :=
  bundled.has_coe_to_sort

instance (x : UniformSpaceₓ) : UniformSpace x :=
  x.str

/-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
def of (α : Type u) [UniformSpace α] : UniformSpaceₓ :=
  ⟨α⟩

instance : Inhabited UniformSpaceₓ :=
  ⟨UniformSpaceₓ.of Empty⟩

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] : (of X : Type u) = X :=
  rfl

instance (X Y : UniformSpaceₓ) : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ⟨CategoryTheory.Functor.map (forget UniformSpaceₓ)⟩

@[simp]
theorem coe_comp {X Y Z : UniformSpaceₓ} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  rfl

@[simp]
theorem coe_id (X : UniformSpaceₓ) : (𝟙 X : X → X) = id :=
  rfl

@[simp]
theorem coe_mk {X Y : UniformSpaceₓ} (f : X → Y) (hf : UniformContinuous f) : ((⟨f, hf⟩ : X ⟶ Y) : X → Y) = f :=
  rfl

theorem hom_ext {X Y : UniformSpaceₓ} {f g : X ⟶ Y} : (f : X → Y) = g → f = g :=
  Subtype.eq

/-- The forgetful functor from uniform spaces to topological spaces. -/
instance hasForgetToTop :
    HasForget₂ UniformSpaceₓ.{u}
      Top.{u} where forget₂ :=
    { obj := fun X => Top.of X,
      map := fun X Y f => { toFun := f, continuous_to_fun := UniformContinuous.continuous f.property } }

end UniformSpaceₓ

/-- A (bundled) complete separated uniform space. -/
structure CpltSepUniformSpace where
  α : Type u
  [isUniformSpace : UniformSpace α]
  [is_complete_space : CompleteSpace α]
  [IsSeparated : SeparatedSpace α]

namespace CpltSepUniformSpace

instance : CoeSort CpltSepUniformSpace (Type u) :=
  ⟨CpltSepUniformSpace.α⟩

attribute [instance] is_uniform_space is_complete_space IsSeparated

/-- The function forgetting that a complete separated uniform spaces is complete and separated. -/
def toUniformSpace (X : CpltSepUniformSpace) : UniformSpaceₓ :=
  UniformSpaceₓ.of X

instance complete_space (X : CpltSepUniformSpace) : CompleteSpace (toUniformSpace X).α :=
  CpltSepUniformSpace.is_complete_space X

instance separated_space (X : CpltSepUniformSpace) : SeparatedSpace (toUniformSpace X).α :=
  CpltSepUniformSpace.is_separated X

/-- Construct a bundled `UniformSpace` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [UniformSpace X] [CompleteSpace X] [SeparatedSpace X] : CpltSepUniformSpace :=
  ⟨X⟩

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] [CompleteSpace X] [SeparatedSpace X] : (of X : Type u) = X :=
  rfl

instance : Inhabited CpltSepUniformSpace := by
  have : SeparatedSpace Empty :=
    separated_iff_t2.mpr
      (by
        infer_instance)
  exact ⟨CpltSepUniformSpace.of Empty⟩

/-- The category instance on `CpltSepUniformSpace`. -/
instance category : LargeCategory CpltSepUniformSpace :=
  InducedCategory.category toUniformSpace

/-- The concrete category instance on `CpltSepUniformSpace`. -/
instance concreteCategory : ConcreteCategory CpltSepUniformSpace :=
  InducedCategory.concreteCategory toUniformSpace

instance hasForgetToUniformSpace : HasForget₂ CpltSepUniformSpace UniformSpaceₓ :=
  InducedCategory.hasForget₂ toUniformSpace

end CpltSepUniformSpace

namespace UniformSpaceₓ

open UniformSpace

open CpltSepUniformSpace

/-- The functor turning uniform spaces into complete separated uniform spaces. -/
noncomputable def completionFunctor : UniformSpaceₓ ⥤ CpltSepUniformSpace where
  obj := fun X => CpltSepUniformSpace.of (Completion X)
  map := fun X Y f => ⟨Completion.map f.1, Completion.uniform_continuous_map⟩
  map_id' := fun X => Subtype.eq Completion.map_id
  map_comp' := fun X Y Z f g => Subtype.eq (Completion.map_comp g.property f.property).symm

/-- The inclusion of a uniform space into its completion. -/
def completionHom (X : UniformSpaceₓ) :
    X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceₓ).obj (completionFunctor.obj X) where
  val := (coe : X → Completion X)
  property := Completion.uniform_continuous_coe X

@[simp]
theorem completion_hom_val (X : UniformSpaceₓ) (x) : (completionHom X) x = (x : Completion X) :=
  rfl

/-- The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`. -/
noncomputable def extensionHom {X : UniformSpaceₓ} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceₓ).obj Y) : completionFunctor.obj X ⟶ Y where
  val := Completion.extension f
  property := Completion.uniform_continuous_extension

@[simp]
theorem extension_hom_val {X : UniformSpaceₓ} {Y : CpltSepUniformSpace} (f : X ⟶ (forget₂ _ _).obj Y) (x) :
    (extensionHom f) x = Completion.extension f x :=
  rfl

@[simp]
theorem extension_comp_coe {X : UniformSpaceₓ} {Y : CpltSepUniformSpace}
    (f : toUniformSpace (CpltSepUniformSpace.of (Completion X)) ⟶ toUniformSpace Y) :
    extensionHom (completionHom X ≫ f) = f := by
  apply Subtype.eq
  funext x
  exact congr_fun (completion.extension_comp_coe f.property) x

/-- The completion functor is left adjoint to the forgetful functor. -/
noncomputable def adj : completion_functor ⊣ forget₂ CpltSepUniformSpace UniformSpaceₓ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => completionHom X ≫ f, invFun := fun f => extensionHom f,
          left_inv := fun f => by
            dsimp'
            erw [extension_comp_coe],
          right_inv := fun f => by
            apply Subtype.eq
            funext x
            cases f
            exact @completion.extension_coe _ _ _ _ _ (CpltSepUniformSpace.separated_space _) f_property _ },
      hom_equiv_naturality_left_symm' := fun X X' Y f g => by
        apply hom_ext
        funext x
        dsimp'
        erw [coe_comp, ← completion.extension_map]
        rfl
        exact g.property
        exact f.property }

noncomputable instance : IsRightAdjoint (forget₂ CpltSepUniformSpace UniformSpaceₓ) :=
  ⟨completionFunctor, adj⟩

noncomputable instance : Reflective (forget₂ CpltSepUniformSpace UniformSpaceₓ) where

open CategoryTheory.Limits

-- TODO Once someone defines `has_limits UniformSpace`, turn this into an instance.
example [HasLimits.{u} UniformSpaceₓ.{u}] : HasLimits.{u} CpltSepUniformSpace.{u} :=
  has_limits_of_reflective <| forget₂ CpltSepUniformSpace UniformSpaceₓ.{u}

end UniformSpaceₓ

