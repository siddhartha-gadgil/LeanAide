/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import Mathbin.Algebra.Category.Module.Monoidal
import Mathbin.CategoryTheory.Monoidal.Functorial
import Mathbin.CategoryTheory.Monoidal.Types
import Mathbin.LinearAlgebra.DirectSum.Finsupp
import Mathbin.CategoryTheory.Linear.LinearFunctor

/-!
The functor of forming finitely supported functions on a type with values in a `[ring R]`
is the left adjoint of
the forgetful functor from `R`-modules to types.
-/


noncomputable section

open CategoryTheory

namespace ModuleCat

universe u

open Classical

variable (R : Type u)

section

variable [Ringₓ R]

/-- The free functor `Type u ⥤ Module R` sending a type `X` to the
free `R`-module with generators `x : X`, implemented as the type `X →₀ R`.
-/
@[simps]
def free : Type u ⥤ ModuleCat R where
  obj := fun X => ModuleCat.of R (X →₀ R)
  map := fun X Y f => Finsupp.lmapDomain _ _ f
  map_id' := by
    intros
    exact Finsupp.lmap_domain_id _ _
  map_comp' := by
    intros
    exact Finsupp.lmap_domain_comp _ _ _ _

/-- The free-forgetful adjunction for R-modules.
-/
def adj : free R ⊣ forget (ModuleCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X M => (Finsupp.lift M R X).toEquiv.symm,
      hom_equiv_naturality_left_symm' := fun _ _ M f g =>
        Finsupp.lhom_ext' fun x =>
          LinearMap.ext_ring (Finsupp.sum_map_domain_index_add_monoid_hom fun y => (smulAddHom R M).flip (g y)).symm }

instance : IsRightAdjoint (forget (ModuleCat.{u} R)) :=
  ⟨_, adj R⟩

end

namespace Free

variable [CommRingₓ R]

attribute [local ext] TensorProduct.ext

/-- (Implementation detail) The unitor for `free R`. -/
def ε : 𝟙_ (ModuleCat.{u} R) ⟶ (free R).obj (𝟙_ (Type u)) :=
  Finsupp.lsingle PUnit.unit

@[simp]
theorem ε_apply (r : R) : ε R r = Finsupp.single PUnit.unit r :=
  rfl

/-- (Implementation detail) The tensorator for `free R`. -/
def μ (α β : Type u) : (free R).obj α ⊗ (free R).obj β ≅ (free R).obj (α ⊗ β) :=
  (finsuppTensorFinsupp' R α β).toModuleIso

theorem μ_natural {X Y X' Y' : Type u} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (free R).map f ⊗ (free R).map g ≫ (μ R Y Y').Hom = (μ R X X').Hom ≫ (free R).map (f ⊗ g) := by
  intros
  ext x x' ⟨y, y'⟩
  dsimp' [← μ]
  simp_rw [Finsupp.map_domain_single, finsupp_tensor_finsupp'_single_tmul_single, mul_oneₓ, Finsupp.map_domain_single,
    CategoryTheory.tensor_apply]

theorem left_unitality (X : Type u) :
    (λ_ ((free R).obj X)).Hom = ε R ⊗ 𝟙 ((free R).obj X) ≫ (μ R (𝟙_ (Type u)) X).Hom ≫ map (free R).obj (λ_ X).Hom := by
  intros
  ext
  dsimp' [← ε, ← μ]
  simp_rw [finsupp_tensor_finsupp'_single_tmul_single, ModuleCat.monoidalCategory.left_unitor_hom_apply,
    Finsupp.smul_single', mul_oneₓ, Finsupp.map_domain_single, CategoryTheory.left_unitor_hom_apply]

theorem right_unitality (X : Type u) :
    (ρ_ ((free R).obj X)).Hom = 𝟙 ((free R).obj X) ⊗ ε R ≫ (μ R X (𝟙_ (Type u))).Hom ≫ map (free R).obj (ρ_ X).Hom := by
  intros
  ext
  dsimp' [← ε, ← μ]
  simp_rw [finsupp_tensor_finsupp'_single_tmul_single, ModuleCat.monoidalCategory.right_unitor_hom_apply,
    Finsupp.smul_single', mul_oneₓ, Finsupp.map_domain_single, CategoryTheory.right_unitor_hom_apply]

theorem associativity (X Y Z : Type u) :
    (μ R X Y).Hom ⊗ 𝟙 ((free R).obj Z) ≫ (μ R (X ⊗ Y) Z).Hom ≫ map (free R).obj (α_ X Y Z).Hom =
      (α_ ((free R).obj X) ((free R).obj Y) ((free R).obj Z)).Hom ≫
        𝟙 ((free R).obj X) ⊗ (μ R Y Z).Hom ≫ (μ R X (Y ⊗ Z)).Hom :=
  by
  intros
  ext
  dsimp' [← μ]
  simp_rw [finsupp_tensor_finsupp'_single_tmul_single, Finsupp.map_domain_single, mul_oneₓ,
    CategoryTheory.associator_hom_apply]

/-- The free R-module functor is lax monoidal. -/
-- In fact, it's strong monoidal, but we don't yet have a typeclass for that.
@[simps]
instance : LaxMonoidal.{u} (free R).obj where
  -- Send `R` to `punit →₀ R`
  ε := ε R
  -- Send `(α →₀ R) ⊗ (β →₀ R)` to `α × β →₀ R`
  μ := fun X Y => (μ R X Y).Hom
  μ_natural' := fun X Y X' Y' f g => μ_natural R f g
  left_unitality' := left_unitality R
  right_unitality' := right_unitality R
  associativity' := associativity R

instance : IsIso (LaxMonoidal.ε (free R).obj) :=
  ⟨⟨Finsupp.lapply PUnit.unit,
      ⟨by
        ext
        simp , by
        ext ⟨⟩ ⟨⟩
        simp ⟩⟩⟩

end Free

variable [CommRingₓ R]

/-- The free functor `Type u ⥤ Module R`, as a monoidal functor. -/
def monoidalFree : MonoidalFunctor (Type u) (ModuleCat.{u} R) :=
  { LaxMonoidalFunctor.of (free R).obj with
    ε_is_iso := by
      dsimp'
      infer_instance,
    μ_is_iso := fun X Y => by
      dsimp'
      infer_instance }

example (X Y : Type u) : (free R).obj (X × Y) ≅ (free R).obj X ⊗ (free R).obj Y :=
  ((monoidalFree R).μIso X Y).symm

end ModuleCat

namespace CategoryTheory

universe v u

/-- `Free R C` is a type synonym for `C`, which, given `[comm_ring R]` and `[category C]`,
we will equip with a category structure where the morphisms are formal `R`-linear combinations
of the morphisms in `C`.
-/
@[nolint unused_arguments has_inhabited_instance]
def Free (R : Type _) (C : Type u) :=
  C

/-- Consider an object of `C` as an object of the `R`-linear completion.

It may be preferable to use `(Free.embedding R C).obj X` instead;
this functor can also be used to lift morphisms.
-/
def Free.of (R : Type _) {C : Type u} (X : C) : Free R C :=
  X

variable (R : Type _) [CommRingₓ R] (C : Type u) [Category.{v} C]

open Finsupp

-- Conceptually, it would be nice to construct this via "transport of enrichment",
-- using the fact that `Module.free R : Type ⥤ Module R` and `Module.forget` are both lax monoidal.
-- This still seems difficult, so we just do it by hand.
instance categoryFree : Category (Free R C) where
  Hom := fun X Y : C => (X ⟶ Y) →₀ R
  id := fun X : C => Finsupp.single (𝟙 X) 1
  comp := fun (X Y Z : C) f g => f.Sum fun f' s => g.Sum fun g' t => Finsupp.single (f' ≫ g') (s * t)
  assoc' := fun W X Y Z f g h => by
    dsimp'
    -- This imitates the proof of associativity for `monoid_algebra`.
    simp only [← sum_sum_index, ← sum_single_index, ← single_zero, ← single_add, ← eq_self_iff_true, ← forall_true_iff,
      ← forall_3_true_iff, ← add_mulₓ, ← mul_addₓ, ← category.assoc, ← mul_assoc, ← zero_mul, ← mul_zero, ← sum_zero, ←
      sum_add]

namespace Free

section

attribute [local reducible] CategoryTheory.categoryFree

instance : Preadditive (Free R C) where
  homGroup := fun X Y => Finsupp.addCommGroup
  add_comp' := fun X Y Z f f' g => by
    dsimp'
    rw [Finsupp.sum_add_index] <;>
      · simp [← add_mulₓ]
        
  comp_add' := fun X Y Z f g g' => by
    dsimp'
    rw [← Finsupp.sum_add]
    congr
    ext r h
    rw [Finsupp.sum_add_index] <;>
      · simp [← mul_addₓ]
        

instance : Linear R (Free R C) where
  homModule := fun X Y => Finsupp.module (X ⟶ Y) R
  smul_comp' := fun X Y Z r f g => by
    dsimp'
    rw [Finsupp.sum_smul_index] <;> simp [← Finsupp.smul_sum, ← mul_assoc]
  comp_smul' := fun X Y Z f r g => by
    dsimp'
    simp_rw [Finsupp.smul_sum]
    congr
    ext h s
    rw [Finsupp.sum_smul_index] <;> simp [← Finsupp.smul_sum, ← mul_left_commₓ]

theorem single_comp_single {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : R) :
    (single f r ≫ single g s : Free.of R X ⟶ Free.of R Z) = single (f ≫ g) (r * s) := by
  dsimp'
  simp

end

attribute [local simp] single_comp_single

/-- A category embeds into its `R`-linear completion.
-/
@[simps]
def embedding : C ⥤ Free R C where
  obj := fun X => X
  map := fun X Y f => Finsupp.single f 1
  map_id' := fun X => rfl
  map_comp' := fun X Y Z f g => by
    simp

variable (R) {C} {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]

open Preadditive Linear

/-- A functor to an `R`-linear category lifts to a functor from its `R`-linear completion.
-/
@[simps]
def lift (F : C ⥤ D) : Free R C ⥤ D where
  obj := fun X => F.obj X
  map := fun X Y f => f.Sum fun f' r => r • F.map f'
  map_id' := by
    dsimp' [← CategoryTheory.categoryFree]
    simp
  map_comp' := fun X Y Z f g => by
    apply Finsupp.induction_linear f
    · simp
      
    · intro f₁ f₂ w₁ w₂
      rw [add_comp]
      rw [Finsupp.sum_add_index, Finsupp.sum_add_index]
      · simp [← w₁, ← w₂, ← add_comp]
        
      · simp
        
      · intros
        simp only [← add_smul]
        
      · simp
        
      · intros
        simp only [← add_smul]
        
      
    · intro f' r
      apply Finsupp.induction_linear g
      · simp
        
      · intro f₁ f₂ w₁ w₂
        rw [comp_add]
        rw [Finsupp.sum_add_index, Finsupp.sum_add_index]
        · simp [← w₁, ← w₂, ← add_comp]
          
        · simp
          
        · intros
          simp only [← add_smul]
          
        · simp
          
        · intros
          simp only [← add_smul]
          
        
      · intro g' s
        erw [single_comp_single]
        simp [← mul_comm r s, ← mul_smul]
        
      

@[simp]
theorem lift_map_single (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R) : (lift R F).map (single f r) = r • F.map f := by
  simp

instance lift_additive (F : C ⥤ D) :
    (lift R F).Additive where map_add' := fun X Y f g => by
    dsimp'
    rw [Finsupp.sum_add_index] <;> simp [← add_smul]

instance lift_linear (F : C ⥤ D) :
    (lift R F).Linear R where map_smul' := fun X Y f r => by
    dsimp'
    rw [Finsupp.sum_smul_index] <;> simp [← Finsupp.smul_sum, ← mul_smul]

/-- The embedding into the `R`-linear completion, followed by the lift,
is isomorphic to the original functor.
-/
def embeddingLiftIso (F : C ⥤ D) : embedding R C ⋙ lift R F ≅ F :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      tidy)

/-- Two `R`-linear functors out of the `R`-linear completion are isomorphic iff their
compositions with the embedding functor are isomorphic.
-/
@[ext]
def ext {F G : Free R C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    (α : embedding R C ⋙ F ≅ embedding R C ⋙ G) : F ≅ G :=
  NatIso.ofComponents (fun X => α.app X)
    (by
      intro X Y f
      apply Finsupp.induction_linear f
      · simp
        
      · intro f₁ f₂ w₁ w₂
        simp only [← F.map_add, ← G.map_add, ← add_comp, ← comp_add, ← w₁, ← w₂]
        
      · intro f' r
        rw [iso.app_hom, iso.app_hom, ← smul_single_one, F.map_smul, G.map_smul, smul_comp, comp_smul]
        change r • (embedding R C ⋙ F).map f' ≫ _ = r • _ ≫ (embedding R C ⋙ G).map f'
        rw [α.hom.naturality f']
        infer_instance
        -- Why are these not picked up automatically when we rewrite?
        infer_instance
        )

/-- `Free.lift` is unique amongst `R`-linear functors `Free R C ⥤ D`
which compose with `embedding ℤ C` to give the original functor.
-/
def liftUnique (F : C ⥤ D) (L : Free R C ⥤ D) [L.Additive] [L.Linear R] (α : embedding R C ⋙ L ≅ F) : L ≅ lift R F :=
  ext R (α.trans (embeddingLiftIso R F).symm)

end Free

end CategoryTheory

