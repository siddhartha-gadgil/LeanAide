/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.CategoryTheory.Elementwise
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Category instance for topological spaces

We introduce the bundled category `Top` of topological spaces together with the functors `discrete`
and `trivial` from the category of types to `Top` which equip a type with the corresponding
discrete, resp. trivial, topology. For a proof that these functors are left, resp. right adjoint
to the forgetful functor, see `topology.category.Top.adjunctions`.
-/


open CategoryTheory

open TopologicalSpace

universe u

/-- The category of topological spaces and continuous maps. -/
def Top : Type (u + 1) :=
  Bundled TopologicalSpace

namespace Top

instance bundledHom : BundledHom @ContinuousMap :=
  ⟨@ContinuousMap.toFun, @ContinuousMap.id, @ContinuousMap.comp, @ContinuousMap.coe_injective⟩

deriving instance LargeCategory, ConcreteCategory for Top

instance : CoeSort Top (Type _) :=
  bundled.has_coe_to_sort

instance topologicalSpaceUnbundled (x : Top) : TopologicalSpace x :=
  x.str

@[simp]
theorem id_app (X : Top.{u}) (x : X) : (𝟙 X : X → X) x = x :=
  rfl

@[simp]
theorem comp_app {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X → Z) x = g (f x) :=
  rfl

/-- Construct a bundled `Top` from the underlying type and the typeclass. -/
def of (X : Type u) [TopologicalSpace X] : Top :=
  ⟨X⟩

instance (X : Top) : TopologicalSpace X :=
  X.str

@[simp]
theorem coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X :=
  rfl

instance : Inhabited Top :=
  ⟨Top.of Empty⟩

/-- The discrete topology on any type. -/
def discrete : Type u ⥤ Top.{u} where
  obj := fun X => ⟨X, ⊥⟩
  map := fun X Y f => { toFun := f, continuous_to_fun := continuous_bot }

/-- The trivial topology on any type. -/
def trivial : Type u ⥤ Top.{u} where
  obj := fun X => ⟨X, ⊤⟩
  map := fun X Y f => { toFun := f, continuous_to_fun := continuous_top }

/-- Any homeomorphisms induces an isomorphism in `Top`. -/
@[simps]
def isoOfHomeo {X Y : Top.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  Hom := ⟨f⟩
  inv := ⟨f.symm⟩

/-- Any isomorphism in `Top` induces a homeomorphism. -/
@[simps]
def homeoOfIso {X Y : Top.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.Hom
  invFun := f.inv
  left_inv := fun x => by
    simp
  right_inv := fun x => by
    simp
  continuous_to_fun := f.Hom.Continuous
  continuous_inv_fun := f.inv.Continuous

@[simp]
theorem of_iso_of_homeo {X Y : Top.{u}} (f : X ≃ₜ Y) : homeoOfIso (isoOfHomeo f) = f := by
  ext
  rfl

@[simp]
theorem of_homeo_of_iso {X Y : Top.{u}} (f : X ≅ Y) : isoOfHomeo (homeoOfIso f) = f := by
  ext
  rfl

@[simp]
theorem open_embedding_iff_comp_is_iso {X Y Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    OpenEmbedding (f ≫ g) ↔ OpenEmbedding f :=
  (Top.homeoOfIso (asIso g)).OpenEmbedding.of_comp_iff f

@[simp]
theorem open_embedding_iff_is_iso_comp {X Y Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    OpenEmbedding (f ≫ g) ↔ OpenEmbedding g := by
  constructor
  · intro h
    convert h.comp (Top.homeoOfIso (as_iso f).symm).OpenEmbedding
    exact congr_arg _ (is_iso.inv_hom_id_assoc f g).symm
    
  · exact fun h => h.comp (Top.homeoOfIso (as_iso f)).OpenEmbedding
    

end Top

