/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.BigOperators.Pi
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.Data.Matrix.Dmatrix
import Mathbin.Data.Matrix.Basic
import Mathbin.CategoryTheory.Fintype
import Mathbin.CategoryTheory.Preadditive.SingleObj
import Mathbin.Algebra.Opposites

/-!
# Matrices over a category.

When `C` is a preadditive category, `Mat_ C` is the preadditive category
whose objects are finite tuples of objects in `C`, and
whose morphisms are matrices of morphisms from `C`.

There is a functor `Mat_.embedding : C ⥤ Mat_ C` sending morphisms to one-by-one matrices.

`Mat_ C` has finite biproducts.

## The additive envelope

We show that this construction is the "additive envelope" of `C`,
in the sense that any additive functor `F : C ⥤ D` to a category `D` with biproducts
lifts to a functor `Mat_.lift F : Mat_ C ⥤ D`,
Moreover, this functor is unique (up to natural isomorphisms) amongst functors `L : Mat_ C ⥤ D`
such that `embedding C ⋙ L ≅ F`.
(As we don't have 2-category theory, we can't explicitly state that `Mat_ C` is
the initial object in the 2-category of categories under `C` which have biproducts.)

As a consequence, when `C` already has finite biproducts we have `Mat_ C ≌ C`.

## Future work

We should provide a more convenient `Mat R`, when `R` is a ring,
as a category with objects `n : FinType`,
and whose morphisms are matrices with components in `R`.

Ideally this would conveniently interact with both `Mat_` and `matrix`.

-/


open CategoryTheory CategoryTheory.Preadditive

open BigOperators Classical

noncomputable section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]

/-- An object in `Mat_ C` is a finite tuple of objects in `C`.
-/
structure Mat_ where
  ι : Type
  [f : Fintype ι]
  x : ι → C

attribute [instance] Mat_.F

namespace Mat_

variable {C}

/-- A morphism in `Mat_ C` is a dependently typed matrix of morphisms. -/
@[nolint has_inhabited_instance]
def Hom (M N : Mat_ C) : Type v₁ :=
  Dmatrix M.ι N.ι fun i j => M.x i ⟶ N.x j

namespace Hom

/-- The identity matrix consists of identity morphisms on the diagonal, and zeros elsewhere. -/
def id (M : Mat_ C) : Hom M M := fun i j => if h : i = j then eqToHom (congr_arg M.x h) else 0

/-- Composition of matrices using matrix multiplication. -/
def comp {M N K : Mat_ C} (f : Hom M N) (g : Hom N K) : Hom M K := fun i k => ∑ j : N.ι, f i j ≫ g j k

end Hom

section

attribute [local simp] hom.id hom.comp

instance : Category.{v₁} (Mat_ C) where
  hom := Hom
  id := Hom.id
  comp := fun M N K f g => f.comp g
  id_comp' := fun M N f => by
    simp [← dite_comp]
  comp_id' := fun M N f => by
    simp [← comp_dite]
  assoc' := fun M N K L f g h => by
    ext i k
    simp_rw [hom.comp, sum_comp, comp_sum, category.assoc]
    rw [Finset.sum_comm]

theorem id_def (M : Mat_ C) : (𝟙 M : Hom M M) = fun i j => if h : i = j then eqToHom (congr_arg M.x h) else 0 :=
  rfl

theorem id_apply (M : Mat_ C) (i j : M.ι) : (𝟙 M : Hom M M) i j = if h : i = j then eqToHom (congr_arg M.x h) else 0 :=
  rfl

@[simp]
theorem id_apply_self (M : Mat_ C) (i : M.ι) : (𝟙 M : Hom M M) i i = 𝟙 _ := by
  simp [← id_apply]

@[simp]
theorem id_apply_of_ne (M : Mat_ C) (i j : M.ι) (h : i ≠ j) : (𝟙 M : Hom M M) i j = 0 := by
  simp [← id_apply, ← h]

theorem comp_def {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) : f ≫ g = fun i k => ∑ j : N.ι, f i j ≫ g j k :=
  rfl

@[simp]
theorem comp_apply {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) : (f ≫ g) i k = ∑ j : N.ι, f i j ≫ g j k :=
  rfl

instance (M N : Mat_ C) : Inhabited (M ⟶ N) :=
  ⟨fun i j => (0 : M.x i ⟶ N.x j)⟩

end

instance : Preadditive (Mat_ C) where
  homGroup := fun M N => by
    change AddCommGroupₓ (Dmatrix M.ι N.ι _)
    infer_instance
  add_comp' := fun M N K f f' g => by
    ext
    simp [← Finset.sum_add_distrib]
  comp_add' := fun M N K f g g' => by
    ext
    simp [← Finset.sum_add_distrib]

@[simp]
theorem add_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
  rfl

open CategoryTheory.Limits

/-- We now prove that `Mat_ C` has finite biproducts.

Be warned, however, that `Mat_ C` is not necessarily Krull-Schmidt,
and so the internal indexing of a biproduct may have nothing to do with the external indexing,
even though the construction we give uses a sigma type.
See however `iso_biproduct_embedding`.
-/
instance has_finite_biproducts :
    HasFiniteBiproducts
      (Mat_
        C) where HasBiproductsOfShape := fun J 𝒟 =>
    { HasBiproduct := fun f =>
        has_biproduct_of_total
          { x := ⟨Σj : J, (f j).ι, fun p => (f p.1).x p.2⟩,
            π := fun j x y => by
              dsimp'  at x⊢
              refine' if h : x.1 = j then _ else 0
              refine' if h' : @Eq.ndrec J x.1 (fun j => (f j).ι) x.2 _ h = y then _ else 0
              apply eq_to_hom
              substs h h',-- Notice we were careful not to use `subst` until we had a goal in `Prop`.
            ι := fun j x y => by
              dsimp'  at y⊢
              refine' if h : y.1 = j then _ else 0
              refine' if h' : @Eq.ndrec J y.1 (fun j => (f j).ι) y.2 _ h = x then _ else 0
              apply eq_to_hom
              substs h h',
            ι_π := fun j j' => by
              ext x y
              dsimp'
              simp_rw [dite_comp, comp_dite]
              simp only [← if_t_t, ← dite_eq_ite, ← dif_ctx_congr, ← limits.comp_zero, ← limits.zero_comp, ←
                eq_to_hom_trans, ← Finset.sum_congr]
              erw [Finset.sum_sigma]
              dsimp'
              simp only [← if_congr, ← if_true, ← dif_ctx_congr, ← Finset.sum_dite_irrel, ← Finset.mem_univ, ←
                Finset.sum_const_zero, ← Finset.sum_congr, ← Finset.sum_dite_eq']
              split_ifs with h h'
              · substs h h'
                simp only [← CategoryTheory.eq_to_hom_refl, ← CategoryTheory.Mat_.id_apply_self]
                
              · subst h
                simp only [← id_apply_of_ne _ _ _ h', ← CategoryTheory.eq_to_hom_refl]
                
              · rfl
                 }
          (by
            dsimp'
            funext i₁
            dsimp'  at i₁⊢
            rcases i₁ with ⟨j₁, i₁⟩
            -- I'm not sure why we can't just `simp` by `finset.sum_apply`: something doesn't quite match
            convert Finset.sum_apply _ _ _ using 1
            · rfl
              
            · apply heq_of_eq
              symm
              funext i₂
              rcases i₂ with ⟨j₂, i₂⟩
              simp only [← comp_apply, ← dite_comp, ← comp_dite, ← if_t_t, ← dite_eq_ite, ← if_congr, ← if_true, ←
                dif_ctx_congr, ← Finset.sum_dite_irrel, ← Finset.sum_dite_eq, ← Finset.mem_univ, ←
                Finset.sum_const_zero, ← Finset.sum_congr, ← Finset.sum_dite_eq, ← Finset.sum_apply, ← limits.comp_zero,
                ← limits.zero_comp, ← eq_to_hom_trans, ← Mat_.id_apply]
              by_cases' h : j₁ = j₂
              · subst h
                simp
                
              · simp [← h]
                
              ) }

end Mat_

namespace Functor

variable {C} {D : Type _} [Category.{v₁} D] [Preadditive D]

attribute [local simp] Mat_.id_apply eq_to_hom_map

/-- A functor induces a functor of matrix categories.
-/
@[simps]
def mapMat_ (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ Mat_ D where
  obj := fun M => ⟨M.ι, fun i => F.obj (M.x i)⟩
  map := fun M N f i j => F.map (f i j)
  map_comp' := fun M N K f g => by
    ext i k
    simp

/-- The identity functor induces the identity functor on matrix categories.
-/
@[simps]
def mapMatId : (𝟭 C).mapMat_ ≅ 𝟭 (Mat_ C) :=
  NatIso.ofComponents
    (fun M =>
      eqToIso
        (by
          cases M
          rfl))
    fun M N f => by
    ext i j
    cases M
    cases N
    simp [← comp_dite, ← dite_comp]

/-- Composite functors induce composite functors on matrix categories.
-/
@[simps]
def mapMatComp {E : Type _} [Category.{v₁} E] [Preadditive E] (F : C ⥤ D) [Functor.Additive F] (G : D ⥤ E)
    [Functor.Additive G] : (F ⋙ G).mapMat_ ≅ F.mapMat_ ⋙ G.mapMat_ :=
  NatIso.ofComponents
    (fun M =>
      eqToIso
        (by
          cases M
          rfl))
    fun M N f => by
    ext i j
    cases M
    cases N
    simp [← comp_dite, ← dite_comp]

end Functor

namespace Mat_

variable (C)

/-- The embedding of `C` into `Mat_ C` as one-by-one matrices.
(We index the summands by `punit`.) -/
@[simps]
def embedding : C ⥤ Mat_ C where
  obj := fun X => ⟨PUnit, fun _ => X⟩
  map := fun X Y f => fun _ _ => f
  map_id' := fun X => by
    ext ⟨⟩ ⟨⟩
    simp
  map_comp' := fun X Y Z f g => by
    ext ⟨⟩ ⟨⟩
    simp

namespace Embedding

instance : Faithful (embedding C) where map_injective' := fun X Y f g h => congr_fun (congr_fun h PUnit.unit) PUnit.unit

instance : Full (embedding C) where Preimage := fun X Y f => f PUnit.unit PUnit.unit

instance : Functor.Additive (embedding C) where

end Embedding

instance [Inhabited C] : Inhabited (Mat_ C) :=
  ⟨(embedding C).obj default⟩

open CategoryTheory.Limits

variable {C}

/-- Every object in `Mat_ C` is isomorphic to the biproduct of its summands.
-/
@[simps]
def isoBiproductEmbedding (M : Mat_ C) : M ≅ ⨁ fun i => (embedding C).obj (M.x i) where
  hom := biproduct.lift fun i j k => if h : j = i then eqToHom (congr_arg M.x h) else 0
  inv := biproduct.desc fun i j k => if h : i = k then eqToHom (congr_arg M.x h) else 0
  hom_inv_id' := by
    simp only [← biproduct.lift_desc]
    funext i
    dsimp'
    convert Finset.sum_apply _ _ _
    · dsimp'
      rfl
      
    · apply heq_of_eq
      symm
      funext j
      simp only [← Finset.sum_apply]
      dsimp'
      simp [← dite_comp, ← comp_dite, ← Mat_.id_apply]
      
  inv_hom_id' := by
    apply biproduct.hom_ext
    intro i
    apply biproduct.hom_ext'
    intro j
    simp only [← category.id_comp, ← category.assoc, ← biproduct.lift_π, ← biproduct.ι_desc_assoc, ← biproduct.ι_π]
    ext ⟨⟩ ⟨⟩
    simp [← dite_comp, ← comp_dite]
    split_ifs
    · subst h
      simp
      
    · simp [← h]
      

variable {D : Type u₁} [Category.{v₁} D] [Preadditive D]

/-- Every `M` is a direct sum of objects from `C`, and `F` preserves biproducts. -/
@[simps]
def additiveObjIsoBiproduct (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) :
    F.obj M ≅ ⨁ fun i => F.obj ((embedding C).obj (M.x i)) :=
  F.mapIso (isoBiproductEmbedding M) ≪≫ F.mapBiproduct _

variable [HasFiniteBiproducts D]

@[reassoc]
theorem additive_obj_iso_biproduct_naturality (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C} (f : M ⟶ N) :
    F.map f ≫ (additiveObjIsoBiproduct F N).hom =
      (additiveObjIsoBiproduct F M).hom ≫ biproduct.matrix fun i j => F.map ((embedding C).map (f i j)) :=
  by
  -- This is disappointingly tedious.
  ext
  simp only [← additive_obj_iso_biproduct_hom, ← category.assoc, ← biproduct.lift_π, ← functor.map_bicone_π, ←
    biproduct.bicone_π, ← biproduct.lift_matrix]
  dsimp' [← embedding]
  simp only [F.map_comp, ← biproduct.lift_π, ← biproduct.matrix_π, ← category.assoc]
  simp only [F.map_comp, F.map_sum, ← biproduct.lift_desc, ← biproduct.lift_π_assoc, ← comp_sum]
  simp only [← comp_def, ← comp_dite, ← comp_zero, ← Finset.sum_dite_eq', ← Finset.mem_univ, ← if_true]
  dsimp'
  simp only [← Finset.sum_singleton, ← dite_comp, ← zero_comp]
  congr
  symm
  convert Finset.sum_fn _ _
  -- It's hard to use this as a simp lemma!
  simp only [← Finset.sum_fn, ← Finset.sum_dite_eq]
  ext
  simp

@[reassoc]
theorem additive_obj_iso_biproduct_naturality' (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C} (f : M ⟶ N) :
    (additiveObjIsoBiproduct F M).inv ≫ F.map f =
      biproduct.matrix (fun i j => F.map ((embedding C).map (f i j)) : _) ≫ (additiveObjIsoBiproduct F N).inv :=
  by
  rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, additive_obj_iso_biproduct_naturality]

/-- Any additive functor `C ⥤ D` to a category `D` with finite biproducts extends to
a functor `Mat_ C ⥤ D`. -/
@[simps]
def lift (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ D where
  obj := fun X => ⨁ fun i => F.obj (X.x i)
  map := fun X Y f => biproduct.matrix fun i j => F.map (f i j)
  map_id' := fun X => by
    ext i j
    by_cases' h : i = j
    · subst h
      simp
      
    · simp [← h, ← Mat_.id_apply]
      
  map_comp' := fun X Y Z f g => by
    ext i j
    simp

instance lift_additive (F : C ⥤ D) [Functor.Additive F] : Functor.Additive (lift F) where

/-- An additive functor `C ⥤ D` factors through its lift to `Mat_ C ⥤ D`. -/
@[simps]
def embeddingLiftIso (F : C ⥤ D) [Functor.Additive F] : embedding C ⋙ lift F ≅ F :=
  NatIso.ofComponents
    (fun X => { hom := biproduct.desc fun P => 𝟙 (F.obj X), inv := biproduct.lift fun P => 𝟙 (F.obj X) }) fun X Y f =>
    by
    dsimp'
    ext
    simp only [← category.id_comp, ← biproduct.ι_desc_assoc]
    erw [biproduct.ι_matrix_assoc]
    -- Not sure why this doesn't fire via `simp`.
    simp

/-- `Mat_.lift F` is the unique additive functor `L : Mat_ C ⥤ D` such that `F ≅ embedding C ⋙ L`.
-/
def liftUnique (F : C ⥤ D) [Functor.Additive F] (L : Mat_ C ⥤ D) [Functor.Additive L] (α : embedding C ⋙ L ≅ F) :
    L ≅ lift F :=
  NatIso.ofComponents
    (fun M =>
      additiveObjIsoBiproduct L M ≪≫
        (biproduct.mapIso fun i => α.app (M.x i)) ≪≫
          (biproduct.mapIso fun i => (embeddingLiftIso F).symm.app (M.x i)) ≪≫
            (additiveObjIsoBiproduct (lift F) M).symm)
    fun M N f => by
    dsimp' only [← iso.trans_hom, ← iso.symm_hom, ← biproduct.map_iso_hom]
    simp only [← additive_obj_iso_biproduct_naturality_assoc]
    simp only [← biproduct.matrix_map_assoc, ← category.assoc]
    simp only [← additive_obj_iso_biproduct_naturality']
    simp only [← biproduct.map_matrix_assoc, ← category.assoc]
    congr
    ext j k ⟨⟩
    dsimp'
    simp
    exact α.hom.naturality (f j k)

/-- Two additive functors `Mat_ C ⥤ D` are naturally isomorphic if
their precompositions with `embedding C` are naturally isomorphic as functors `C ⥤ D`. -/
-- TODO is there some uniqueness statement for the natural isomorphism in `lift_unique`?
@[ext]
def ext {F G : Mat_ C ⥤ D} [Functor.Additive F] [Functor.Additive G] (α : embedding C ⋙ F ≅ embedding C ⋙ G) : F ≅ G :=
  liftUnique (embedding C ⋙ G) _ α ≪≫ (liftUnique _ _ (Iso.refl _)).symm

/-- Natural isomorphism needed in the construction of `equivalence_self_of_has_finite_biproducts`.
-/
def equivalenceSelfOfHasFiniteBiproductsAux [HasFiniteBiproducts C] :
    embedding C ⋙ 𝟭 (Mat_ C) ≅ embedding C ⋙ lift (𝟭 C) ⋙ embedding C :=
  Functor.rightUnitor _ ≪≫
    (Functor.leftUnitor _).symm ≪≫ isoWhiskerRight (embeddingLiftIso _).symm _ ≪≫ Functor.associator _ _ _

/-- A preadditive category that already has finite biproducts is equivalent to its additive envelope.

Note that we only prove this for a large category;
otherwise there are universe issues that I haven't attempted to sort out.
-/
def equivalenceSelfOfHasFiniteBiproducts (C : Type (u₁ + 1)) [LargeCategory C] [Preadditive C] [HasFiniteBiproducts C] :
    Mat_ C ≌ C :=
  Equivalence.mk
    (-- I suspect this is already an adjoint equivalence, but it seems painful to verify.
      lift
      (𝟭 C))
    (embedding C) (ext equivalenceSelfOfHasFiniteBiproductsAux) (embeddingLiftIso (𝟭 C))

@[simp]
theorem equivalence_self_of_has_finite_biproducts_functor {C : Type (u₁ + 1)} [LargeCategory C] [Preadditive C]
    [HasFiniteBiproducts C] : (equivalenceSelfOfHasFiniteBiproducts C).Functor = lift (𝟭 C) :=
  rfl

@[simp]
theorem equivalence_self_of_has_finite_biproducts_inverse {C : Type (u₁ + 1)} [LargeCategory C] [Preadditive C]
    [HasFiniteBiproducts C] : (equivalenceSelfOfHasFiniteBiproducts C).inverse = embedding C :=
  rfl

end Mat_

universe u

/-- A type synonym for `Fintype`, which we will equip with a category structure
where the morphisms are matrices with components in `R`. -/
@[nolint unused_arguments]
def Mat (R : Type u) :=
  Fintypeₓ.{u}deriving Inhabited

instance (R : Type u) : CoeSort (Mat R) (Type u) :=
  bundled.has_coe_to_sort

open Classical Matrix

instance (R : Type u) [Semiringₓ R] : Category (Mat R) where
  hom := fun X Y => Matrix X Y R
  id := fun X => 1
  comp := fun X Y Z f g => f ⬝ g
  assoc' := by
    intros
    simp [← Matrix.mul_assoc]

namespace Mat

section

variable (R : Type u) [Semiringₓ R]

theorem id_def (M : Mat R) : 𝟙 M = fun i j => if h : i = j then 1 else 0 :=
  rfl

theorem id_apply (M : Mat R) (i j : M) : (𝟙 M : Matrix M M R) i j = if h : i = j then 1 else 0 :=
  rfl

@[simp]
theorem id_apply_self (M : Mat R) (i : M) : (𝟙 M : Matrix M M R) i i = 1 := by
  simp [← id_apply]

@[simp]
theorem id_apply_of_ne (M : Mat R) (i j : M) (h : i ≠ j) : (𝟙 M : Matrix M M R) i j = 0 := by
  simp [← id_apply, ← h]

theorem comp_def {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) : f ≫ g = fun i k => ∑ j : N, f i j * g j k :=
  rfl

@[simp]
theorem comp_apply {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) (i k) : (f ≫ g) i k = ∑ j : N, f i j * g j k :=
  rfl

instance (M N : Mat R) : Inhabited (M ⟶ N) :=
  ⟨fun (i : M) (j : N) => (0 : R)⟩

end

variable (R : Type) [Ringₓ R]

open Opposite

/-- Auxiliary definition for `category_theory.Mat.equivalence_single_obj`. -/
@[simps]
def equivalenceSingleObjInverse : Mat_ (SingleObj Rᵐᵒᵖ) ⥤ Mat R where
  obj := fun X => Fintypeₓ.of X.ι
  map := fun X Y f i j => MulOpposite.unop (f i j)
  map_id' := fun X => by
    ext i j
    simp [← id_def, ← Mat_.id_def]
    split_ifs <;> rfl

instance :
    Faithful (equivalenceSingleObjInverse R) where map_injective' := fun X Y f g w => by
    ext i j
    apply_fun MulOpposite.unop using MulOpposite.unop_injective
    exact congr_fun (congr_fun w i) j

instance : Full (equivalenceSingleObjInverse R) where Preimage := fun X Y f i j => MulOpposite.op (f i j)

instance :
    EssSurj
      (equivalenceSingleObjInverse
        R) where mem_ess_image := fun X =>
    ⟨{ ι := X, x := fun _ => PUnit.unit },
      ⟨eqToIso
          (by
            dsimp'
            cases X
            congr)⟩⟩

/-- The categorical equivalence between the category of matrices over a ring,
and the category of matrices over that ring considered as a single-object category. -/
def equivalenceSingleObj : Mat R ≌ Mat_ (SingleObj Rᵐᵒᵖ) := by
  have := equivalence.of_fully_faithfully_ess_surj (equivalence_single_obj_inverse R)
  exact (equivalence_single_obj_inverse R).asEquivalence.symm

instance : Preadditive (Mat R) where
  add_comp' := by
    intros
    ext
    simp [← add_mulₓ, ← Finset.sum_add_distrib]
  comp_add' := by
    intros
    ext
    simp [← mul_addₓ, ← Finset.sum_add_distrib]

-- TODO show `Mat R` has biproducts, and that `biprod.map` "is" forming a block diagonal matrix.
end Mat

end CategoryTheory

