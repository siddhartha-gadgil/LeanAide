/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.SplitCoequalizer
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving (co)equalizers

Constructions to relate the notions of preserving (co)equalizers and reflecting (co)equalizers
to concrete (co)forks.

In particular, we show that `equalizer_comparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,g`, as well as the dual result.
-/


noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section Equalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g)

/-- The map of a fork is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `fork.of_ι` with `functor.map_cone`.
-/
def isLimitMapConeForkEquiv :
    IsLimit (G.mapCone (Fork.ofι h w)) ≃
      IsLimit
        (Fork.ofι (G.map h)
          (by
            simp only [G.map_comp, ← w]) :
          Fork (G.map f) (G.map g)) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoParallelPair _) _).symm.trans
    (IsLimit.equivIsoLimit
      (Fork.ext (Iso.refl _)
        (by
          simp [← fork.ι])))

/-- The property of preserving equalizers expressed in terms of forks. -/
def isLimitForkMapOfIsLimit [PreservesLimit (parallelPair f g) G] (l : IsLimit (Fork.ofι h w)) :
    IsLimit
      (Fork.ofι (G.map h)
        (by
          simp only [G.map_comp, ← w]) :
        Fork (G.map f) (G.map g)) :=
  isLimitMapConeForkEquiv G w (PreservesLimit.preserves l)

/-- The property of reflecting equalizers expressed in terms of forks. -/
def isLimitOfIsLimitForkMap [ReflectsLimit (parallelPair f g) G]
    (l :
      IsLimit
        (Fork.ofι (G.map h)
          (by
            simp only [G.map_comp, ← w]) :
          Fork (G.map f) (G.map g))) :
    IsLimit (Fork.ofι h w) :=
  ReflectsLimit.reflects ((isLimitMapConeForkEquiv G w).symm l)

variable (f g) [HasEqualizer f g]

/-- If `G` preserves equalizers and `C` has them, then the fork constructed of the mapped morphisms of
a fork is a limit.
-/
def isLimitOfHasEqualizerOfPreservesLimit [PreservesLimit (parallelPair f g) G] :
    IsLimit
      (Fork.ofι (G.map (equalizer.ι f g))
        (by
          simp only [G.map_comp, ← equalizer.condition])) :=
  isLimitForkMapOfIsLimit G _ (equalizerIsEqualizer f g)

variable [HasEqualizer (G.map f) (G.map g)]

/-- If the equalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
equalizer of `(f,g)`.
-/
def PreservesEqualizer.ofIsoComparison [i : IsIso (equalizerComparison f g G)] : PreservesLimit (parallelPair f g) G :=
  by
  apply preserves_limit_of_preserves_limit_cone (equalizer_is_equalizer f g)
  apply (is_limit_map_cone_fork_equiv _ _).symm _
  apply is_limit.of_point_iso (limit.is_limit (parallel_pair (G.map f) (G.map g)))
  apply i

variable [PreservesLimit (parallelPair f g) G]

/-- If `G` preserves the equalizer of `(f,g)`, then the equalizer comparison map for `G` at `(f,g)` is
an isomorphism.
-/
def PreservesEqualizer.iso : G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasEqualizerOfPreservesLimit G f g) (limit.isLimit _)

@[simp]
theorem PreservesEqualizer.iso_hom : (PreservesEqualizer.iso G f g).Hom = equalizerComparison f g G :=
  rfl

instance : IsIso (equalizerComparison f g G) := by
  rw [← preserves_equalizer.iso_hom]
  infer_instance

end Equalizers

section Coequalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h)

/-- The map of a cofork is a colimit iff the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `cofork.of_π` with `functor.map_cocone`.
-/
def isColimitMapCoconeCoforkEquiv :
    IsColimit (G.mapCocone (Cofork.ofπ h w)) ≃
      IsColimit
        (Cofork.ofπ (G.map h)
          (by
            simp only [G.map_comp, ← w]) :
          Cofork (G.map f) (G.map g)) :=
  (IsColimit.precomposeInvEquiv (diagramIsoParallelPair _) _).symm.trans <|
    is_colimit.equiv_iso_colimit <|
      Cofork.ext (Iso.refl _) <| by
        dsimp' only [← cofork.π, ← cofork.of_π_ι_app]
        dsimp'
        rw [category.comp_id, category.id_comp]

/-- The property of preserving coequalizers expressed in terms of coforks. -/
def isColimitCoforkMapOfIsColimit [PreservesColimit (parallelPair f g) G] (l : IsColimit (Cofork.ofπ h w)) :
    IsColimit
      (Cofork.ofπ (G.map h)
        (by
          simp only [G.map_comp, ← w]) :
        Cofork (G.map f) (G.map g)) :=
  isColimitMapCoconeCoforkEquiv G w (PreservesColimit.preserves l)

/-- The property of reflecting coequalizers expressed in terms of coforks. -/
def isColimitOfIsColimitCoforkMap [ReflectsColimit (parallelPair f g) G]
    (l :
      IsColimit
        (Cofork.ofπ (G.map h)
          (by
            simp only [G.map_comp, ← w]) :
          Cofork (G.map f) (G.map g))) :
    IsColimit (Cofork.ofπ h w) :=
  ReflectsColimit.reflects ((isColimitMapCoconeCoforkEquiv G w).symm l)

variable (f g) [HasCoequalizer f g]

/-- If `G` preserves coequalizers and `C` has them, then the cofork constructed of the mapped morphisms
of a cofork is a colimit.
-/
def isColimitOfHasCoequalizerOfPreservesColimit [PreservesColimit (parallelPair f g) G] :
    IsColimit (Cofork.ofπ (G.map (coequalizer.π f g)) _) :=
  isColimitCoforkMapOfIsColimit G _ (coequalizerIsCoequalizer f g)

variable [HasCoequalizer (G.map f) (G.map g)]

/-- If the coequalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
coequalizer of `(f,g)`.
-/
def ofIsoComparison [i : IsIso (coequalizerComparison f g G)] : PreservesColimit (parallelPair f g) G := by
  apply preserves_colimit_of_preserves_colimit_cocone (coequalizer_is_coequalizer f g)
  apply (is_colimit_map_cocone_cofork_equiv _ _).symm _
  apply is_colimit.of_point_iso (colimit.is_colimit (parallel_pair (G.map f) (G.map g)))
  apply i

variable [PreservesColimit (parallelPair f g) G]

/-- If `G` preserves the coequalizer of `(f,g)`, then the coequalizer comparison map for `G` at `(f,g)`
is an isomorphism.
-/
def PreservesCoequalizer.iso : coequalizer (G.map f) (G.map g) ≅ G.obj (coequalizer f g) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitOfHasCoequalizerOfPreservesColimit G f g)

@[simp]
theorem PreservesCoequalizer.iso_hom : (PreservesCoequalizer.iso G f g).Hom = coequalizerComparison f g G :=
  rfl

instance : IsIso (coequalizerComparison f g G) := by
  rw [← preserves_coequalizer.iso_hom]
  infer_instance

/-- Any functor preserves coequalizers of split pairs. -/
instance (priority := 1) preservesSplitCoequalizers (f g : X ⟶ Y) [HasSplitCoequalizer f g] :
    PreservesColimit (parallelPair f g) G := by
  apply preserves_colimit_of_preserves_colimit_cocone (has_split_coequalizer.is_split_coequalizer f g).isCoequalizer
  apply
    (is_colimit_map_cocone_cofork_equiv G _).symm ((has_split_coequalizer.is_split_coequalizer f g).map G).isCoequalizer

end Coequalizers

end CategoryTheory.Limits

