/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Homology.ImageToKernel
import Mathbin.Algebra.Homology.HomologicalComplex
import Mathbin.CategoryTheory.GradedObject

/-!
# The homology of a complex

Given `C : homological_complex V c`, we have `C.cycles i` and `C.boundaries i`,
both defined as subobjects of `C.X i`.

We show these are functorial with respect to chain maps,
as `C.cycles_map f i` and `C.boundaries_map f i`.

As a consequence we construct `homology_functor i : homological_complex V c ⥤ V`,
computing the `i`-th homology.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

open Classical ZeroObject

noncomputable section

namespace HomologicalComplex

variable [HasZeroObject V]

section Cycles

variable [HasKernels V]

/-- The cycles at index `i`, as a subobject. -/
abbrev cycles (i : ι) : Subobject (C.x i) :=
  kernelSubobject (C.dFrom i)

theorem cycles_eq_kernel_subobject {i j : ι} (r : c.Rel i j) : C.cycles i = kernelSubobject (C.d i j) :=
  C.kernel_from_eq_kernel r

/-- The underlying object of `C.cycles i` is isomorphic to `kernel (C.d i j)`,
for any `j` such that `rel i j`.
-/
def cyclesIsoKernel {i j : ι} (r : c.Rel i j) : (C.cycles i : V) ≅ kernel (C.d i j) :=
  Subobject.isoOfEq _ _ (C.cycles_eq_kernel_subobject r) ≪≫ kernelSubobjectIso (C.d i j)

theorem cycles_eq_top {i} (h : c.next i = none) : C.cycles i = ⊤ := by
  rw [eq_top_iff]
  apply le_kernel_subobject
  rw [C.d_from_eq_zero h, comp_zero]

end Cycles

section Boundaries

variable [HasImages V]

/-- The boundaries at index `i`, as a subobject. -/
abbrev boundaries (C : HomologicalComplex V c) (j : ι) : Subobject (C.x j) :=
  imageSubobject (C.dTo j)

theorem boundaries_eq_image_subobject [HasEqualizers V] {i j : ι} (r : c.Rel i j) :
    C.boundaries j = imageSubobject (C.d i j) :=
  C.image_to_eq_image r

/-- The underlying object of `C.boundaries j` is isomorphic to `image (C.d i j)`,
for any `i` such that `rel i j`.
-/
def boundariesIsoImage [HasEqualizers V] {i j : ι} (r : c.Rel i j) : (C.boundaries j : V) ≅ image (C.d i j) :=
  Subobject.isoOfEq _ _ (C.boundaries_eq_image_subobject r) ≪≫ imageSubobjectIso (C.d i j)

theorem boundaries_eq_bot {j} (h : c.prev j = none) : C.boundaries j = ⊥ := by
  rw [eq_bot_iff]
  refine' image_subobject_le _ 0 _
  rw [C.d_to_eq_zero h, zero_comp]

end Boundaries

section

variable [HasKernels V] [HasImages V]

theorem boundaries_le_cycles (C : HomologicalComplex V c) (i : ι) : C.boundaries i ≤ C.cycles i :=
  image_le_kernel _ _ (C.d_to_comp_d_from i)

/-- The canonical map from `boundaries i` to `cycles i`.
-/
abbrev boundariesToCycles (C : HomologicalComplex V c) (i : ι) : (C.boundaries i : V) ⟶ (C.cycles i : V) :=
  imageToKernel _ _ (C.d_to_comp_d_from i)

/-- Prefer `boundaries_to_cycles`. -/
@[simp]
theorem image_to_kernel_as_boundaries_to_cycles (C : HomologicalComplex V c) (i : ι) (h) :
    (C.boundaries i).ofLe (C.cycles i) h = C.boundariesToCycles i :=
  rfl

variable [HasCokernels V]

/-- The homology of a complex at index `i`.
-/
abbrev homology (C : HomologicalComplex V c) (i : ι) : V :=
  homology (C.dTo i) (C.dFrom i) (C.d_to_comp_d_from i)

end

end HomologicalComplex

open HomologicalComplex

/-! Computing the cycles is functorial. -/


section

variable [HasZeroObject V] [HasKernels V]

variable {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂)

/-- The morphism between cycles induced by a chain map.
-/
abbrev cyclesMap (f : C₁ ⟶ C₂) (i : ι) : (C₁.cycles i : V) ⟶ (C₂.cycles i : V) :=
  Subobject.factorThru _ ((C₁.cycles i).arrow ≫ f.f i)
    (kernel_subobject_factors _ _
      (by
        simp ))

@[simp, reassoc, elementwise]
theorem cycles_map_arrow (f : C₁ ⟶ C₂) (i : ι) : cyclesMap f i ≫ (C₂.cycles i).arrow = (C₁.cycles i).arrow ≫ f.f i := by
  simp

@[simp]
theorem cycles_map_id (i : ι) : cyclesMap (𝟙 C₁) i = 𝟙 _ := by
  dunfold cyclesMap
  simp

@[simp]
theorem cycles_map_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : cyclesMap (f ≫ g) i = cyclesMap f i ≫ cyclesMap g i := by
  dunfold cyclesMap
  simp [← subobject.factor_thru_right]

variable (V c)

/-- Cycles as a functor. -/
@[simps]
def cyclesFunctor (i : ι) : HomologicalComplex V c ⥤ V where
  obj := fun C => C.cycles i
  map := fun C₁ C₂ f => cyclesMap f i

end

/-! Computing the boundaries is functorial. -/


section

variable [HasZeroObject V] [HasImages V] [HasImageMaps V]

variable {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂)

/-- The morphism between boundaries induced by a chain map.
-/
abbrev boundariesMap (f : C₁ ⟶ C₂) (i : ι) : (C₁.boundaries i : V) ⟶ (C₂.boundaries i : V) :=
  imageSubobjectMap (f.sqTo i)

variable (V c)

/-- Boundaries as a functor. -/
@[simps]
def boundariesFunctor (i : ι) : HomologicalComplex V c ⥤ V where
  obj := fun C => C.boundaries i
  map := fun C₁ C₂ f => imageSubobjectMap (f.sqTo i)

end

section

/-! The `boundaries_to_cycles` morphisms are natural. -/


variable [HasZeroObject V] [HasEqualizers V] [HasImages V] [HasImageMaps V]

variable {C₁ C₂ : HomologicalComplex V c} (f : C₁ ⟶ C₂)

@[simp, reassoc]
theorem boundaries_to_cycles_naturality (i : ι) :
    boundariesMap f i ≫ C₂.boundariesToCycles i = C₁.boundariesToCycles i ≫ cyclesMap f i := by
  ext
  simp

variable (V c)

/-- The natural transformation from the boundaries functor to the cycles functor. -/
@[simps]
def boundariesToCyclesNatTrans (i : ι) : boundariesFunctor V c i ⟶ cyclesFunctor V c i where
  app := fun C => C.boundariesToCycles i
  naturality' := fun C₁ C₂ f => boundaries_to_cycles_naturality f i

/-- The `i`-th homology, as a functor to `V`. -/
@[simps]
def homologyFunctor [HasCokernels V] (i : ι) : HomologicalComplex V c ⥤ V where
  -- It would be nice if we could just write
  -- `cokernel (boundaries_to_cycles_nat_trans V c i)`
  -- here, but universe implementation details get in the way...
  obj := fun C => C.homology i
  map := fun C₁ C₂ f => homology.map _ _ (f.sqTo i) (f.sqFrom i) rfl
  map_id' := by
    intros
    ext1
    simp only [← homology.π_map, ← kernel_subobject_map_id, ← hom.sq_from_id, ← category.id_comp, ← category.comp_id]
  map_comp' := by
    intros
    ext1
    simp only [← hom.sq_from_comp, ← kernel_subobject_map_comp, ← homology.π_map_assoc, ← homology.π_map, ←
      category.assoc]

/-- The homology functor from `ι`-indexed complexes to `ι`-graded objects in `V`. -/
@[simps]
def gradedHomologyFunctor [HasCokernels V] : HomologicalComplex V c ⥤ GradedObject ι V where
  obj := fun C i => C.homology i
  map := fun C C' f i => (homologyFunctor V c i).map f
  map_id' := by
    intros
    ext
    simp only [← pi.id_apply, ← homology.π_map, ← homology_functor_map, ← kernel_subobject_map_id, ← hom.sq_from_id, ←
      category.id_comp, ← category.comp_id]
  map_comp' := by
    intros
    ext
    simp only [← hom.sq_from_comp, ← kernel_subobject_map_comp, ← homology.π_map_assoc, ← pi.comp_apply, ←
      homology.π_map, ← homology_functor_map, ← category.assoc]

end

