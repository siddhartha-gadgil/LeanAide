/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.CategoryTheory.Endomorphism

/-!
# Conjugate morphisms by isomorphisms

An isomorphism `α : X ≅ Y` defines
- a monoid isomorphism `conj : End X ≃* End Y` by `α.conj f = α.inv ≫ f ≫ α.hom`;
- a group isomorphism `conj_Aut : Aut X ≃* Aut Y` by `α.conj_Aut f = α.symm ≪≫ f ≪≫ α`.

For completeness, we also define `hom_congr : (X ≅ X₁) → (Y ≅ Y₁) → (X ⟶ Y) ≃ (X₁ ⟶ Y₁)`,
cf. `equiv.arrow_congr`.
-/


universe v u

namespace CategoryTheory

namespace Iso

variable {C : Type u} [Category.{v} C]

/-- If `X` is isomorphic to `X₁` and `Y` is isomorphic to `Y₁`, then
there is a natural bijection between `X ⟶ Y` and `X₁ ⟶ Y₁`. See also `equiv.arrow_congr`. -/
def homCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) : (X ⟶ Y) ≃ (X₁ ⟶ Y₁) where
  toFun := fun f => α.inv ≫ f ≫ β.Hom
  invFun := fun f => α.Hom ≫ f ≫ β.inv
  left_inv := fun f =>
    show α.Hom ≫ (α.inv ≫ f ≫ β.Hom) ≫ β.inv = f by
      rw [category.assoc, category.assoc, β.hom_inv_id, α.hom_inv_id_assoc, category.comp_id]
  right_inv := fun f =>
    show α.inv ≫ (α.Hom ≫ f ≫ β.inv) ≫ β.Hom = f by
      rw [category.assoc, category.assoc, β.inv_hom_id, α.inv_hom_id_assoc, category.comp_id]

@[simp]
theorem hom_congr_apply {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y) : α.homCongr β f = α.inv ≫ f ≫ β.Hom :=
  rfl

theorem hom_congr_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁) (f : X ⟶ Y) (g : Y ⟶ Z) :
    α.homCongr γ (f ≫ g) = α.homCongr β f ≫ β.homCongr γ g := by
  simp

@[simp]
theorem hom_congr_refl {X Y : C} (f : X ⟶ Y) : (Iso.refl X).homCongr (Iso.refl Y) f = f := by
  simp

@[simp]
theorem hom_congr_trans {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂) (α₂ : X₂ ≅ X₃) (β₂ : Y₂ ≅ Y₃)
    (f : X₁ ⟶ Y₁) : (α₁ ≪≫ α₂).homCongr (β₁ ≪≫ β₂) f = (α₁.homCongr β₁).trans (α₂.homCongr β₂) f := by
  simp

@[simp]
theorem hom_congr_symm {X₁ Y₁ X₂ Y₂ : C} (α : X₁ ≅ X₂) (β : Y₁ ≅ Y₂) : (α.homCongr β).symm = α.symm.homCongr β.symm :=
  rfl

variable {X Y : C} (α : X ≅ Y)

/-- An isomorphism between two objects defines a monoid isomorphism between their
monoid of endomorphisms. -/
def conj : End X ≃* End Y :=
  { homCongr α α with map_mul' := fun f g => hom_congr_comp α α α g f }

theorem conj_apply (f : End X) : α.conj f = α.inv ≫ f ≫ α.Hom :=
  rfl

@[simp]
theorem conj_comp (f g : End X) : α.conj (f ≫ g) = α.conj f ≫ α.conj g :=
  α.conj.map_mul g f

@[simp]
theorem conj_id : α.conj (𝟙 X) = 𝟙 Y :=
  α.conj.map_one

@[simp]
theorem refl_conj (f : End X) : (Iso.refl X).conj f = f := by
  rw [conj_apply, iso.refl_inv, iso.refl_hom, category.id_comp, category.comp_id]

@[simp]
theorem trans_conj {Z : C} (β : Y ≅ Z) (f : End X) : (α ≪≫ β).conj f = β.conj (α.conj f) :=
  hom_congr_trans α α β β f

@[simp]
theorem symm_self_conj (f : End X) : α.symm.conj (α.conj f) = f := by
  rw [← trans_conj, α.self_symm_id, refl_conj]

@[simp]
theorem self_symm_conj (f : End Y) : α.conj (α.symm.conj f) = f :=
  α.symm.symm_self_conj f

@[simp]
theorem conj_pow (f : End X) (n : ℕ) : α.conj (f ^ n) = α.conj f ^ n :=
  α.conj.toMonoidHom.map_pow f n

/-- `conj` defines a group isomorphisms between groups of automorphisms -/
def conjAut : Aut X ≃* Aut Y :=
  (Aut.unitsEndEquivAut X).symm.trans <| (Units.mapEquiv α.conj).trans <| Aut.unitsEndEquivAut Y

theorem conj_Aut_apply (f : Aut X) : α.conjAut f = α.symm ≪≫ f ≪≫ α := by
  cases f <;> cases α <;> ext <;> rfl

@[simp]
theorem conj_Aut_hom (f : Aut X) : (α.conjAut f).Hom = α.conj f.Hom :=
  rfl

@[simp]
theorem trans_conj_Aut {Z : C} (β : Y ≅ Z) (f : Aut X) : (α ≪≫ β).conjAut f = β.conjAut (α.conjAut f) := by
  simp only [← conj_Aut_apply, ← iso.trans_symm, ← iso.trans_assoc]

@[simp]
theorem conj_Aut_mul (f g : Aut X) : α.conjAut (f * g) = α.conjAut f * α.conjAut g :=
  α.conjAut.map_mul f g

@[simp]
theorem conj_Aut_trans (f g : Aut X) : α.conjAut (f ≪≫ g) = α.conjAut f ≪≫ α.conjAut g :=
  conj_Aut_mul α g f

@[simp]
theorem conj_Aut_pow (f : Aut X) (n : ℕ) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  α.conjAut.toMonoidHom.map_pow f n

@[simp]
theorem conj_Aut_zpow (f : Aut X) (n : ℤ) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  α.conjAut.toMonoidHom.map_zpow f n

end Iso

namespace Functor

universe v₁ u₁

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D)

theorem map_hom_congr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y) :
    F.map (Iso.homCongr α β f) = Iso.homCongr (F.mapIso α) (F.mapIso β) (F.map f) := by
  simp

theorem map_conj {X Y : C} (α : X ≅ Y) (f : End X) : F.map (α.conj f) = (F.mapIso α).conj (F.map f) :=
  map_hom_congr F α α f

theorem map_conj_Aut (F : C ⥤ D) {X Y : C} (α : X ≅ Y) (f : Aut X) :
    F.mapIso (α.conjAut f) = (F.mapIso α).conjAut (F.mapIso f) := by
  ext <;> simp only [← map_iso_hom, ← iso.conj_Aut_hom, ← F.map_conj]

-- alternative proof: by simp only [iso.conj_Aut_apply, F.map_iso_trans, F.map_iso_symm]
end Functor

end CategoryTheory

