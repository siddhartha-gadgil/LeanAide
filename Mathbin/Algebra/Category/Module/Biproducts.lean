/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.Algebra.Category.Module.Limits
import Mathbin.Algebra.Homology.ShortExact.Abelian

/-!
# The category of `R`-modules has finite biproducts
-/


open CategoryTheory

open CategoryTheory.Limits

open BigOperators

universe w v u

namespace ModuleCat

variable {R : Type u} [Ringₓ R]

-- As `Module R` is preadditive, and has all limits, it automatically has biproducts.
instance : HasBinaryBiproducts (ModuleCat.{v} R) :=
  has_binary_biproducts.of_has_binary_products

instance : HasFiniteBiproducts (ModuleCat.{v} R) :=
  has_finite_biproducts.of_has_finite_products

/-- Construct limit data for a binary product in `Module R`, using `Module.of R (M × N)`.
-/
-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
@[simps cone_X is_limit_lift]
def binaryProductLimitCone (M N : ModuleCat.{v} R) : Limits.LimitCone (pair M N) where
  Cone :=
    { x := ModuleCat.of R (M × N),
      π :=
        { app := fun j => Discrete.casesOn j fun j => WalkingPair.casesOn j (LinearMap.fst R M N) (LinearMap.snd R M N),
          naturality' := by
            rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  IsLimit :=
    { lift := fun s => LinearMap.prod (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩),
      fac' := by
        rintro s (⟨⟩ | ⟨⟩) <;>
          · ext x
            simp
            ,
      uniq' := fun s m w => by
        ext <;> [rw [← w ⟨walking_pair.left⟩], rw [← w ⟨walking_pair.right⟩]] <;> rfl }

@[simp]
theorem binary_product_limit_cone_cone_π_app_left (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).Cone.π.app ⟨WalkingPair.left⟩ = LinearMap.fst R M N :=
  rfl

@[simp]
theorem binary_product_limit_cone_cone_π_app_right (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).Cone.π.app ⟨WalkingPair.right⟩ = LinearMap.snd R M N :=
  rfl

/-- We verify that the biproduct in `Module R` is isomorphic to
the cartesian product of the underlying types:
-/
@[simps hom_apply]
noncomputable def biprodIsoProd (M N : ModuleCat.{v} R) : (M ⊞ N : ModuleCat.{v} R) ≅ ModuleCat.of R (M × N) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).IsLimit

@[simp, elementwise]
theorem biprod_iso_prod_inv_comp_fst (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).inv ≫ biprod.fst = LinearMap.fst R M N :=
  IsLimit.cone_point_unique_up_to_iso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]
theorem biprod_iso_prod_inv_comp_snd (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).inv ≫ biprod.snd = LinearMap.snd R M N :=
  IsLimit.cone_point_unique_up_to_iso_inv_comp _ _ (Discrete.mk WalkingPair.right)

namespace HasLimit

variable {J : Type w} (f : J → ModuleCat.{max w v} R)

/-- The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
@[simps]
def lift (s : Fan f) : s.x ⟶ ModuleCat.of R (∀ j, f j) where
  toFun := fun x j => s.π.app ⟨j⟩ x
  map_add' := fun x y => by
    ext
    simp
  map_smul' := fun r x => by
    ext
    simp

/-- Construct limit data for a product in `Module R`, using `Module.of R (Π j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  Cone :=
    { x := ModuleCat.of R (∀ j, f j), π := Discrete.natTrans fun j => (LinearMap.proj j.as : (∀ j, f j) →ₗ[R] f j.as) }
  IsLimit :=
    { lift := lift f,
      fac' := fun s j => by
        cases j
        ext
        simp ,
      uniq' := fun s m w => by
        ext x j
        dsimp' only [← has_limit.lift]
        simp only [← LinearMap.coe_mk]
        exact congr_arg (fun g : s.X ⟶ f j => (g : s.X → f j) x) (w ⟨j⟩) }

end HasLimit

open HasLimit

variable {J : Type} (f : J → ModuleCat.{v} R)

/-- We verify that the biproduct we've just defined is isomorphic to the `Module R` structure
on the dependent function type
-/
@[simps hom_apply]
noncomputable def biproductIsoPi [Fintype J] (f : J → ModuleCat.{v} R) :
    (⨁ f : ModuleCat.{v} R) ≅ ModuleCat.of R (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (Biproduct.isLimit f) (productLimitCone f).IsLimit

@[simp, elementwise]
theorem biproduct_iso_pi_inv_comp_π [Fintype J] (f : J → ModuleCat.{v} R) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = (LinearMap.proj j : (∀ j, f j) →ₗ[R] f j) :=
  IsLimit.cone_point_unique_up_to_iso_inv_comp _ _ (Discrete.mk j)

end ModuleCat

section SplitExact

variable {R : Type u} {A M B : Type v} [Ringₓ R] [AddCommGroupₓ A] [Module R A] [AddCommGroupₓ B] [Module R B]
  [AddCommGroupₓ M] [Module R M]

variable {j : A →ₗ[R] M} {g : M →ₗ[R] B}

open ModuleCat

/-- The isomorphism `A × B ≃ₗ[R] M` coming from a right split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules.-/
noncomputable def lequivProdOfRightSplitExact {f : B →ₗ[R] M} (hj : Function.Injective j) (exac : j.range = g.ker)
    (h : g.comp f = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  (({ RightSplit := ⟨asHom f, h⟩, mono := (ModuleCat.mono_iff_injective <| asHom j).mpr hj,
                exact := (exact_iff _ _).mpr exac } :
                RightSplit _ _).Splitting.Iso.trans <|
        biprodIsoProd _ _).toLinearEquiv.symm

/-- The isomorphism `A × B ≃ₗ[R] M` coming from a left split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules.-/
noncomputable def lequivProdOfLeftSplitExact {f : M →ₗ[R] A} (hg : Function.Surjective g) (exac : j.range = g.ker)
    (h : f.comp j = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  (({ LeftSplit := ⟨asHom f, h⟩, Epi := (ModuleCat.epi_iff_surjective <| asHom g).mpr hg,
                exact := (exact_iff _ _).mpr exac } :
                LeftSplit _ _).Splitting.Iso.trans <|
        biprodIsoProd _ _).toLinearEquiv.symm

end SplitExact

