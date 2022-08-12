/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Preserving (co)kernels

Constructions to relate the notions of preserving (co)kernels and reflecting (co)kernels
to concrete (co)forks.

In particular, we show that `kernel_comparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,0`, as well as the dual result.
-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

namespace CategoryTheory.Limits

section Kernels

variable {X Y Z : C} {f : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = 0)

/-- The map of a kernel fork is a limit iff
the kernel fork consisting of the mapped morphisms is a limit.
This essentially lets us commute `kernel_fork.of_ι` with `functor.map_cone`.

This is a variant of `is_limit_map_cone_fork_equiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isLimitMapConeForkEquiv' :
    IsLimit (G.mapCone (KernelFork.ofι h w)) ≃
      IsLimit
        (KernelFork.ofι (G.map h)
          (by
            simp only [G.map_comp, ← w, ← functor.map_zero]) :
          Fork (G.map f) 0) :=
  by
  refine' (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _)
  refine' parallel_pair.ext (iso.refl _) (iso.refl _) _ _ <;> simp
  refine' fork.ext (iso.refl _) _
  simp [← fork.ι]

/-- The property of preserving kernels expressed in terms of kernel forks.

This is a variant of `is_limit_fork_map_of_is_limit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isLimitForkMapOfIsLimit' [PreservesLimit (parallelPair f 0) G] (l : IsLimit (KernelFork.ofι h w)) :
    IsLimit
      (KernelFork.ofι (G.map h)
        (by
          simp only [G.map_comp, ← w, ← functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitMapConeForkEquiv' G w (PreservesLimit.preserves l)

variable (f) [HasKernel f]

/-- If `G` preserves kernels and `C` has them, then the fork constructed of the mapped morphisms of
a kernel fork is a limit.
-/
def isLimitOfHasKernelOfPreservesLimit [PreservesLimit (parallelPair f 0) G] :
    IsLimit
      (Fork.ofι (G.map (kernel.ι f))
        (by
          simp only [G.map_comp, ← equalizer.condition, ← comp_zero, ← functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitForkMapOfIsLimit' G (kernel.condition f) (kernelIsKernel f)

instance [PreservesLimit (parallelPair f 0) G] :
    HasKernel (G.map f) where exists_limit := ⟨⟨_, isLimitOfHasKernelOfPreservesLimit G f⟩⟩

variable [HasKernel (G.map f)]

/-- If the kernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
kernel of `f`.
-/
def PreservesKernel.ofIsoComparison [i : IsIso (kernelComparison f G)] : PreservesLimit (parallelPair f 0) G := by
  apply preserves_limit_of_preserves_limit_cone (kernel_is_kernel f)
  apply (is_limit_map_cone_fork_equiv' G (kernel.condition f)).symm _
  apply is_limit.of_point_iso (limit.is_limit (parallel_pair (G.map f) 0))
  apply i

variable [PreservesLimit (parallelPair f 0) G]

/-- If `G` preserves the kernel of `f`, then the kernel comparison map for `G` at `f` is
an isomorphism.
-/
def PreservesKernel.iso : G.obj (kernel f) ≅ kernel (G.map f) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasKernelOfPreservesLimit G f) (limit.isLimit _)

@[simp]
theorem PreservesKernel.iso_hom : (PreservesKernel.iso G f).Hom = kernelComparison f G :=
  rfl

instance : IsIso (kernelComparison f G) := by
  rw [← preserves_kernel.iso_hom]
  infer_instance

end Kernels

section Cokernels

variable {X Y Z : C} {f : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = 0)

/-- The map of a cokernel cofork is a colimit iff
the cokernel cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `cokernel_cofork.of_π` with `functor.map_cocone`.

This is a variant of `is_colimit_map_cocone_cofork_equiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isColimitMapCoconeCoforkEquiv' :
    IsColimit (G.mapCocone (CokernelCofork.ofπ h w)) ≃
      IsColimit
        (CokernelCofork.ofπ (G.map h)
          (by
            simp only [G.map_comp, ← w, ← functor.map_zero]) :
          Cofork (G.map f) 0) :=
  by
  refine' (is_colimit.precompose_hom_equiv _ _).symm.trans (is_colimit.equiv_iso_colimit _)
  refine' parallel_pair.ext (iso.refl _) (iso.refl _) _ _ <;> simp
  refine' cofork.ext (iso.refl _) _
  simp only [← cofork.π, ← iso.refl_hom, ← id_comp, ← cocones.precompose_obj_ι, ← nat_trans.comp_app, ←
    parallel_pair.ext_hom_app, ← functor.map_cocone_ι_app, ← cofork.of_π_ι_app]
  apply category.comp_id

/-- The property of preserving cokernels expressed in terms of cokernel coforks.

This is a variant of `is_colimit_cofork_map_of_is_colimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isColimitCoforkMapOfIsColimit' [PreservesColimit (parallelPair f 0) G] (l : IsColimit (CokernelCofork.ofπ h w)) :
    IsColimit
      (CokernelCofork.ofπ (G.map h)
        (by
          simp only [G.map_comp, ← w, ← functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitMapCoconeCoforkEquiv' G w (PreservesColimit.preserves l)

variable (f) [HasCokernel f]

/-- If `G` preserves cokernels and `C` has them, then the cofork constructed of the mapped morphisms of
a cokernel cofork is a colimit.
-/
def isColimitOfHasCokernelOfPreservesColimit [PreservesColimit (parallelPair f 0) G] :
    IsColimit
      (Cofork.ofπ (G.map (cokernel.π f))
        (by
          simp only [G.map_comp, ← coequalizer.condition, ← zero_comp, ← functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitCoforkMapOfIsColimit' G (cokernel.condition f) (cokernelIsCokernel f)

instance [PreservesColimit (parallelPair f 0) G] :
    HasCokernel (G.map f) where exists_colimit := ⟨⟨_, isColimitOfHasCokernelOfPreservesColimit G f⟩⟩

variable [HasCokernel (G.map f)]

/-- If the cokernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
cokernel of `f`.
-/
def PreservesCokernel.ofIsoComparison [i : IsIso (cokernelComparison f G)] : PreservesColimit (parallelPair f 0) G := by
  apply preserves_colimit_of_preserves_colimit_cocone (cokernel_is_cokernel f)
  apply (is_colimit_map_cocone_cofork_equiv' G (cokernel.condition f)).symm _
  apply is_colimit.of_point_iso (colimit.is_colimit (parallel_pair (G.map f) 0))
  apply i

variable [PreservesColimit (parallelPair f 0) G]

/-- If `G` preserves the cokernel of `f`, then the cokernel comparison map for `G` at `f` is
an isomorphism.
-/
def PreservesCokernel.iso : G.obj (cokernel f) ≅ cokernel (G.map f) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCokernelOfPreservesColimit G f) (colimit.isColimit _)

@[simp]
theorem PreservesCokernel.iso_inv : (PreservesCokernel.iso G f).inv = cokernelComparison f G :=
  rfl

instance : IsIso (cokernelComparison f G) := by
  rw [← preserves_cokernel.iso_inv]
  infer_instance

end Cokernels

end CategoryTheory.Limits

