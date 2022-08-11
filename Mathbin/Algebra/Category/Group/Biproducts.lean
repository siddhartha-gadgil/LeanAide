/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Category.Group.Preadditive
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.Algebra.Category.Group.Limits

/-!
# The category of abelian groups has finite biproducts
-/


open CategoryTheory

open CategoryTheory.Limits

open BigOperators

universe w u

namespace AddCommGroupₓₓ

-- As `AddCommGroup` is preadditive, and has all limits, it automatically has biproducts.
instance : HasBinaryBiproducts AddCommGroupₓₓ :=
  has_binary_biproducts.of_has_binary_products

instance : HasFiniteBiproducts AddCommGroupₓₓ :=
  has_finite_biproducts.of_has_finite_products

/-- Construct limit data for a binary product in `AddCommGroup`, using `AddCommGroup.of (G × H)`.
-/
-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
@[simps cone_X is_limit_lift]
def binaryProductLimitCone (G H : AddCommGroupₓₓ.{u}) : Limits.LimitCone (pair G H) where
  Cone :=
    { x := AddCommGroupₓₓ.of (G × H),
      π :=
        { app := fun j =>
            Discrete.casesOn j fun j => WalkingPair.casesOn j (AddMonoidHom.fst G H) (AddMonoidHom.snd G H),
          naturality' := by
            rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  IsLimit :=
    { lift := fun s => AddMonoidHom.prod (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩),
      fac' := by
        rintro s (⟨⟩ | ⟨⟩) <;>
          · ext x
            simp
            ,
      uniq' := fun s m w => by
        ext <;> [rw [← w ⟨walking_pair.left⟩], rw [← w ⟨walking_pair.right⟩]] <;> rfl }

@[simp]
theorem binary_product_limit_cone_cone_π_app_left (G H : AddCommGroupₓₓ.{u}) :
    (binaryProductLimitCone G H).Cone.π.app ⟨WalkingPair.left⟩ = AddMonoidHom.fst G H :=
  rfl

@[simp]
theorem binary_product_limit_cone_cone_π_app_right (G H : AddCommGroupₓₓ.{u}) :
    (binaryProductLimitCone G H).Cone.π.app ⟨WalkingPair.right⟩ = AddMonoidHom.snd G H :=
  rfl

/-- We verify that the biproduct in AddCommGroup is isomorphic to
the cartesian product of the underlying types:
-/
@[simps hom_apply]
noncomputable def biprodIsoProd (G H : AddCommGroupₓₓ.{u}) : (G ⊞ H : AddCommGroupₓₓ) ≅ AddCommGroupₓₓ.of (G × H) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).IsLimit

@[simp, elementwise]
theorem biprod_iso_prod_inv_comp_fst (G H : AddCommGroupₓₓ.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.fst = AddMonoidHom.fst G H :=
  IsLimit.cone_point_unique_up_to_iso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]
theorem biprod_iso_prod_inv_comp_snd (G H : AddCommGroupₓₓ.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.snd = AddMonoidHom.snd G H :=
  IsLimit.cone_point_unique_up_to_iso_inv_comp _ _ (Discrete.mk WalkingPair.right)

namespace HasLimit

variable {J : Type w} (f : J → AddCommGroupₓₓ.{max w u})

/-- The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
@[simps]
def lift (s : Fan f) : s.x ⟶ AddCommGroupₓₓ.of (∀ j, f j) where
  toFun := fun x j => s.π.app ⟨j⟩ x
  map_zero' := by
    ext
    simp
  map_add' := fun x y => by
    ext
    simp

/-- Construct limit data for a product in `AddCommGroup`, using `AddCommGroup.of (Π j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  Cone := { x := AddCommGroupₓₓ.of (∀ j, f j), π := Discrete.natTrans fun j => Pi.evalAddMonoidHom (fun j => f j) j.as }
  IsLimit :=
    { lift := lift f,
      fac' := fun s j => by
        cases j
        ext
        simp ,
      uniq' := fun s m w => by
        ext x j
        dsimp' only [← has_limit.lift]
        simp only [← AddMonoidHom.coe_mk]
        exact congr_arg (fun g : s.X ⟶ f j => (g : s.X → f j) x) (w ⟨j⟩) }

end HasLimit

open HasLimit

variable {J : Type} [Fintype J]

/-- We verify that the biproduct we've just defined is isomorphic to the AddCommGroup structure
on the dependent function type
-/
@[simps hom_apply]
noncomputable def biproductIsoPi (f : J → AddCommGroupₓₓ.{u}) : (⨁ f : AddCommGroupₓₓ) ≅ AddCommGroupₓₓ.of (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (Biproduct.isLimit f) (productLimitCone f).IsLimit

@[simp, elementwise]
theorem biproduct_iso_pi_inv_comp_π (f : J → AddCommGroupₓₓ.{u}) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = Pi.evalAddMonoidHom (fun j => f j) j :=
  IsLimit.cone_point_unique_up_to_iso_inv_comp _ _ (Discrete.mk j)

end AddCommGroupₓₓ

