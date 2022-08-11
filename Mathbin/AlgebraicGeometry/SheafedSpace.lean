/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace.HasColimits
import Mathbin.Topology.Sheaves.Functors

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/


universe v u

open CategoryTheory

open Top

open TopologicalSpace

open Opposite

open CategoryTheory.Limits

open CategoryTheory.Category CategoryTheory.Functor

variable (C : Type u) [Category.{v} C] [HasProducts.{v} C]

attribute [local tidy] tactic.op_induction'

namespace AlgebraicGeometry

/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
structure SheafedSpace extends PresheafedSpace.{v} C where
  IsSheaf : presheaf.IsSheaf

variable {C}

namespace SheafedSpace

instance coeCarrier : Coe (SheafedSpace C) Top where coe := fun X => X.Carrier

/-- Extract the `sheaf C (X : Top)` from a `SheafedSpace C`. -/
def sheaf (X : SheafedSpace C) : Sheaf C (X : Top.{v}) :=
  ⟨X.Presheaf, X.IsSheaf⟩

@[simp]
theorem as_coe (X : SheafedSpace.{v} C) : X.Carrier = (X : Top.{v}) :=
  rfl

@[simp]
theorem mk_coe (carrier) (presheaf) (h) :
    (({ Carrier, Presheaf, IsSheaf := h } : SheafedSpace.{v} C) : Top.{v}) = carrier :=
  rfl

instance (X : SheafedSpace.{v} C) : TopologicalSpace X :=
  X.Carrier.str

/-- The trivial `unit` valued sheaf on any topological space. -/
def unit (X : Top) : SheafedSpace (discrete Unit) :=
  { @PresheafedSpace.const (discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.is_sheaf_unit _ }

instance : Inhabited (SheafedSpace (discrete Unit)) :=
  ⟨unit (Top.of Pempty)⟩

instance : Category (SheafedSpace C) :=
  show Category (InducedCategory (PresheafedSpace.{v} C) SheafedSpace.toPresheafedSpace) by
    infer_instance

/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
def forgetToPresheafedSpace : SheafedSpace.{v} C ⥤ PresheafedSpace.{v} C :=
  inducedFunctor _ deriving Full, Faithful

instance is_PresheafedSpace_iso {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) [IsIso f] : @IsIso (PresheafedSpace C) _ _ _ f :=
  SheafedSpace.forgetToPresheafedSpace.map_is_iso f

variable {C}

section

attribute [local simp] id comp

@[simp]
theorem id_base (X : SheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : Top.{v}) :=
  rfl

theorem id_c (X : SheafedSpace C) : (𝟙 X : X ⟶ X).c = eqToHom (Presheaf.Pushforward.id_eq X.Presheaf).symm :=
  rfl

@[simp]
theorem id_c_app (X : SheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).c.app U =
      eqToHom
        (by
          induction U using Opposite.rec
          cases U
          rfl) :=
  by
  induction U using Opposite.rec
  cases U
  simp only [← id_c]
  dsimp'
  simp

@[simp]
theorem comp_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl

theorem comp_c_app' {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app (op U) = β.c.app (op U) ≫ α.c.app (op ((Opens.map β.base).obj U)) :=
  rfl

theorem congr_app {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U =
      β.c.app U ≫
        X.Presheaf.map
          (eqToHom
            (by
              subst h)) :=
  PresheafedSpace.congr_app h U

variable (C)

/-- The forgetful functor from `SheafedSpace` to `Top`. -/
def forget : SheafedSpace C ⥤ Top where
  obj := fun X => (X : Top.{v})
  map := fun X Y f => f.base

end

open Top.Presheaf

/-- The restriction of a sheafed space along an open embedding into the space.
-/
def restrict {U : Top} (X : SheafedSpace C) {f : U ⟶ (X : Top.{v})} (h : OpenEmbedding f) : SheafedSpace C :=
  { X.toPresheafedSpace.restrict h with
    IsSheaf := fun ι 𝒰 =>
      ⟨IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv _ _).invFun (X.IsSheaf _).some)
          (SheafConditionEqualizerProducts.fork.isoOfOpenEmbedding h 𝒰).symm⟩ }

/-- The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` itself.
-/
def restrictTopIso (X : SheafedSpace C) : X.restrict (Opens.open_embedding ⊤) ≅ X :=
  forgetToPresheafedSpace.preimageIso X.toPresheafedSpace.restrictTopIso

/-- The global sections, notated Gamma.
-/
def Γ : (SheafedSpace C)ᵒᵖ ⥤ C :=
  forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ

theorem Γ_def : (Γ : _ ⥤ C) = forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ :=
  rfl

@[simp]
theorem Γ_obj (X : (SheafedSpace C)ᵒᵖ) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl

theorem Γ_obj_op (X : SheafedSpace C) : Γ.obj (op X) = X.Presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.c.app (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : SheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

noncomputable instance [HasLimits C] : CreatesColimits (forgetToPresheafedSpace : SheafedSpace C ⥤ _) :=
  ⟨fun J hJ =>
    ⟨fun K =>
      creates_colimit_of_fully_faithful_of_iso
        ⟨(PresheafedSpace.colimit_cocone (K ⋙ forget_to_PresheafedSpace)).x,
          limit_is_sheaf _ fun j => sheaf.pushforward_sheaf_of_sheaf _ (K.obj (unop j)).2⟩
        (colimit.iso_colimit_cocone ⟨_, PresheafedSpace.colimit_cocone_is_colimit _⟩).symm⟩⟩

instance [HasLimits C] : HasColimits (SheafedSpace C) :=
  has_colimits_of_has_colimits_creates_colimits forgetToPresheafedSpace

noncomputable instance [HasLimits C] : PreservesColimits (forget C) :=
  Limits.compPreservesColimits forgetToPresheafedSpace (PresheafedSpace.forget C)

end SheafedSpace

end AlgebraicGeometry

