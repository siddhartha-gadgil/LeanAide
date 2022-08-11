/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca
-/
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.CategoryTheory.Elementwise

/-!
# The category of seminormed groups

We define `SemiNormedGroup`, the category of seminormed groups and normed group homs between them,
as well as `SemiNormedGroup₁`, the subcategory of norm non-increasing morphisms.
-/


noncomputable section

universe u

open CategoryTheory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGroupₓ : Type (u + 1) :=
  Bundled SemiNormedGroup

namespace SemiNormedGroupₓ

instance bundledHom : BundledHom @NormedGroupHom :=
  ⟨@NormedGroupHom.toFun, @NormedGroupHom.id, @NormedGroupHom.comp, @NormedGroupHom.coe_inj⟩

deriving instance LargeCategory, ConcreteCategory for SemiNormedGroupₓ

instance : CoeSort SemiNormedGroupₓ (Type u) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `SemiNormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [SemiNormedGroup M] : SemiNormedGroupₓ :=
  Bundled.of M

instance (M : SemiNormedGroupₓ) : SemiNormedGroup M :=
  M.str

@[simp]
theorem coe_of (V : Type u) [SemiNormedGroup V] : (SemiNormedGroupₓ.of V : Type u) = V :=
  rfl

@[simp]
theorem coe_id (V : SemiNormedGroupₓ) : ⇑(𝟙 V) = id :=
  rfl

@[simp]
theorem coe_comp {M N K : SemiNormedGroupₓ} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl

instance : Inhabited SemiNormedGroupₓ :=
  ⟨of PUnit⟩

instance ofUnique (V : Type u) [SemiNormedGroup V] [i : Unique V] : Unique (SemiNormedGroupₓ.of V) :=
  i

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroupₓ where

@[simp]
theorem zero_apply {V W : SemiNormedGroupₓ} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

theorem is_zero_of_subsingleton (V : SemiNormedGroupₓ) [Subsingleton V] : Limits.IsZero V := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext
    have : x = 0 := Subsingleton.elimₓ _ _
    simp only [← this, ← map_zero]
    
  · ext
    apply Subsingleton.elimₓ
    

instance has_zero_object : Limits.HasZeroObject SemiNormedGroupₓ.{u} :=
  ⟨⟨of PUnit, is_zero_of_subsingleton _⟩⟩

theorem iso_isometry_of_norm_noninc {V W : SemiNormedGroupₓ} (i : V ≅ W) (h1 : i.hom.NormNoninc)
    (h2 : i.inv.NormNoninc) : Isometry i.hom := by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymmₓ (h1 v)
  calc ∥v∥ = ∥i.inv (i.hom v)∥ := by
      rw [iso.hom_inv_id_apply]_ ≤ ∥i.hom v∥ := h2 _

end SemiNormedGroupₓ

/-- `SemiNormedGroup₁` is a type synonym for `SemiNormedGroup`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
def SemiNormedGroup₁ : Type (u + 1) :=
  Bundled SemiNormedGroup

namespace SemiNormedGroup₁

instance : CoeSort SemiNormedGroup₁ (Type u) :=
  bundled.has_coe_to_sort

instance : LargeCategory.{u} SemiNormedGroup₁ where
  hom := fun X Y => { f : NormedGroupHom X Y // f.NormNoninc }
  id := fun X => ⟨NormedGroupHom.id X, NormedGroupHom.NormNoninc.id⟩
  comp := fun X Y Z f g => ⟨(g : NormedGroupHom Y Z).comp (f : NormedGroupHom X Y), g.2.comp f.2⟩

@[ext]
theorem hom_ext {M N : SemiNormedGroup₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) : f = g :=
  Subtype.eq (NormedGroupHom.ext (congr_fun w))

instance : ConcreteCategory.{u} SemiNormedGroup₁ where
  forget := { obj := fun X => X, map := fun X Y f => f }
  forget_faithful := {  }

/-- Construct a bundled `SemiNormedGroup₁` from the underlying type and typeclass. -/
def of (M : Type u) [SemiNormedGroup M] : SemiNormedGroup₁ :=
  Bundled.of M

instance (M : SemiNormedGroup₁) : SemiNormedGroup M :=
  M.str

/-- Promote a morphism in `SemiNormedGroup` to a morphism in `SemiNormedGroup₁`. -/
def mkHom {M N : SemiNormedGroupₓ} (f : M ⟶ N) (i : f.NormNoninc) : SemiNormedGroup₁.of M ⟶ SemiNormedGroup₁.of N :=
  ⟨f, i⟩

@[simp]
theorem mk_hom_apply {M N : SemiNormedGroupₓ} (f : M ⟶ N) (i : f.NormNoninc) (x) : mkHom f i x = f x :=
  rfl

/-- Promote an isomorphism in `SemiNormedGroup` to an isomorphism in `SemiNormedGroup₁`. -/
@[simps]
def mkIso {M N : SemiNormedGroupₓ} (f : M ≅ N) (i : f.hom.NormNoninc) (i' : f.inv.NormNoninc) :
    SemiNormedGroup₁.of M ≅ SemiNormedGroup₁.of N where
  hom := mkHom f.hom i
  inv := mkHom f.inv i'
  hom_inv_id' := by
    apply Subtype.eq
    exact f.hom_inv_id
  inv_hom_id' := by
    apply Subtype.eq
    exact f.inv_hom_id

instance : HasForget₂ SemiNormedGroup₁ SemiNormedGroupₓ where forget₂ := { obj := fun X => X, map := fun X Y f => f.1 }

@[simp]
theorem coe_of (V : Type u) [SemiNormedGroup V] : (SemiNormedGroup₁.of V : Type u) = V :=
  rfl

@[simp]
theorem coe_id (V : SemiNormedGroup₁) : ⇑(𝟙 V) = id :=
  rfl

@[simp]
theorem coe_comp {M N K : SemiNormedGroup₁} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl

-- If `coe_fn_coe_base` fires before `coe_comp`, `coe_comp'` puts us back in normal form.
@[simp]
theorem coe_comp' {M N K : SemiNormedGroup₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : NormedGroupHom M K) = (↑g : NormedGroupHom N K).comp ↑f :=
  rfl

instance : Inhabited SemiNormedGroup₁ :=
  ⟨of PUnit⟩

instance ofUnique (V : Type u) [SemiNormedGroup V] [i : Unique V] : Unique (SemiNormedGroup₁.of V) :=
  i

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroup₁ where
  HasZero := fun X Y => { zero := ⟨0, NormedGroupHom.NormNoninc.zero⟩ }
  comp_zero' := fun X Y f Z => by
    ext
    rfl
  zero_comp' := fun X Y Z f => by
    ext
    simp [← coe_fn_coe_base']

@[simp]
theorem zero_apply {V W : SemiNormedGroup₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

theorem is_zero_of_subsingleton (V : SemiNormedGroup₁) [Subsingleton V] : Limits.IsZero V := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext
    have : x = 0 := Subsingleton.elimₓ _ _
    simp only [← this, ← map_zero]
    exact map_zero f.1
    
  · ext
    apply Subsingleton.elimₓ
    

instance has_zero_object : Limits.HasZeroObject SemiNormedGroup₁.{u} :=
  ⟨⟨of PUnit, is_zero_of_subsingleton _⟩⟩

theorem iso_isometry {V W : SemiNormedGroup₁} (i : V ≅ W) : Isometry i.hom := by
  change Isometry (i.hom : V →+ W)
  refine' AddMonoidHomClass.isometry_of_norm i.hom _
  intro v
  apply le_antisymmₓ (i.hom.2 v)
  calc ∥v∥ = ∥i.inv (i.hom v)∥ := by
      rw [iso.hom_inv_id_apply]_ ≤ ∥i.hom v∥ := i.inv.2 _

end SemiNormedGroup₁

