/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving terminal object

Constructions to relate the notions of preserving terminal objects and reflecting terminal objects
to concrete objects.

In particular, we show that `terminal_comparison G` is an isomorphism iff `G` preserves terminal
objects.
-/


universe w v v₁ v₂ u u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable (X : C)

section Terminal

/-- The map of an empty cone is a limit iff the mapped object is terminal.
-/
def isLimitMapConeEmptyConeEquiv : IsLimit (G.mapCone (asEmptyCone X)) ≃ IsTerminal (G.obj X) :=
  isLimitEmptyConeEquiv D _ _ (eqToIso rfl)

/-- The property of preserving terminal objects expressed in terms of `is_terminal`. -/
def IsTerminal.isTerminalObj [PreservesLimit (Functor.empty.{0} C) G] (l : IsTerminal X) : IsTerminal (G.obj X) :=
  isLimitMapConeEmptyConeEquiv G X (PreservesLimit.preserves l)

/-- The property of reflecting terminal objects expressed in terms of `is_terminal`. -/
def IsTerminal.isTerminalOfObj [ReflectsLimit (Functor.empty.{0} C) G] (l : IsTerminal (G.obj X)) : IsTerminal X :=
  ReflectsLimit.reflects ((isLimitMapConeEmptyConeEquiv G X).symm l)

/-- Preserving the terminal object implies preserving all limits of the empty diagram. -/
def preservesLimitsOfShapePemptyOfPreservesTerminal [PreservesLimit (Functor.empty.{0} C) G] :
    PreservesLimitsOfShape (Discrete Pempty)
      G where PreservesLimit := fun K => preservesLimitOfIsoDiagram G (Functor.emptyExt (Functor.empty.{0} C) _)

variable [HasTerminal C]

/-- If `G` preserves the terminal object and `C` has a terminal object, then the image of the terminal
object is terminal.
-/
def isLimitOfHasTerminalOfPreservesLimit [PreservesLimit (Functor.empty.{0} C) G] : IsTerminal (G.obj (⊤_ C)) :=
  terminalIsTerminal.isTerminalObj G (⊤_ C)

/-- If `C` has a terminal object and `G` preserves terminal objects, then `D` has a terminal object
also.
Note this property is somewhat unique to (co)limits of the empty diagram: for general `J`, if `C`
has limits of shape `J` and `G` preserves them, then `D` does not necessarily have limits of shape
`J`.
-/
theorem has_terminal_of_has_terminal_of_preserves_limit [PreservesLimit (Functor.empty.{0} C) G] : HasTerminal D :=
  ⟨fun F => by
    have := has_limit.mk ⟨_, is_limit_of_has_terminal_of_preserves_limit G⟩
    apply has_limit_of_iso F.unique_from_empty.symm⟩

variable [HasTerminal D]

/-- If the terminal comparison map for `G` is an isomorphism, then `G` preserves terminal objects.
-/
def PreservesTerminal.ofIsoComparison [i : IsIso (terminalComparison G)] : PreservesLimit (Functor.empty C) G := by
  apply preserves_limit_of_preserves_limit_cone terminal_is_terminal
  apply (is_limit_map_cone_empty_cone_equiv _ _).symm _
  apply is_limit.of_point_iso (limit.is_limit (Functor.empty.{0} D))
  apply i

/-- If there is any isomorphism `G.obj ⊤ ⟶ ⊤`, then `G` preserves terminal objects. -/
def preservesTerminalOfIsIso (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f] : PreservesLimit (Functor.empty C) G := by
  rw [Subsingleton.elimₓ f (terminal_comparison G)] at i
  exact preserves_terminal.of_iso_comparison G

/-- If there is any isomorphism `G.obj ⊤ ≅ ⊤`, then `G` preserves terminal objects. -/
def preservesTerminalOfIso (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty C) G :=
  preservesTerminalOfIsIso G f.Hom

variable [PreservesLimit (Functor.empty.{0} C) G]

/-- If `G` preserves terminal objects, then the terminal comparison map for `G` is an isomorphism.
-/
def PreservesTerminal.iso : G.obj (⊤_ C) ≅ ⊤_ D :=
  (isLimitOfHasTerminalOfPreservesLimit G).conePointUniqueUpToIso (limit.isLimit _)

@[simp]
theorem PreservesTerminal.iso_hom : (PreservesTerminal.iso G).Hom = terminalComparison G :=
  rfl

instance : IsIso (terminalComparison G) := by
  rw [← preserves_terminal.iso_hom]
  infer_instance

end Terminal

section Initial

/-- The map of an empty cocone is a colimit iff the mapped object is initial.
-/
def isColimitMapCoconeEmptyCoconeEquiv : IsColimit (G.mapCocone (asEmptyCocone.{v₁} X)) ≃ IsInitial (G.obj X) :=
  isColimitEmptyCoconeEquiv D _ _ (eqToIso rfl)

/-- The property of preserving initial objects expressed in terms of `is_initial`. -/
def IsInitial.isInitialObj [PreservesColimit (Functor.empty.{0} C) G] (l : IsInitial X) : IsInitial (G.obj X) :=
  isColimitMapCoconeEmptyCoconeEquiv G X (PreservesColimit.preserves l)

/-- The property of reflecting initial objects expressed in terms of `is_initial`. -/
def IsInitial.isInitialOfObj [ReflectsColimit (Functor.empty.{0} C) G] (l : IsInitial (G.obj X)) : IsInitial X :=
  ReflectsColimit.reflects ((isColimitMapCoconeEmptyCoconeEquiv G X).symm l)

/-- Preserving the initial object implies preserving all colimits of the empty diagram. -/
def preservesColimitsOfShapePemptyOfPreservesInitial [PreservesColimit (Functor.empty.{0} C) G] :
    PreservesColimitsOfShape (Discrete Pempty)
      G where PreservesColimit := fun K => preservesColimitOfIsoDiagram G (Functor.emptyExt (Functor.empty.{0} C) _)

variable [HasInitial C]

/-- If `G` preserves the initial object and `C` has a initial object, then the image of the initial
object is initial.
-/
def isColimitOfHasInitialOfPreservesColimit [PreservesColimit (Functor.empty.{0} C) G] : IsInitial (G.obj (⊥_ C)) :=
  initialIsInitial.isInitialObj G (⊥_ C)

/-- If `C` has a initial object and `G` preserves initial objects, then `D` has a initial object
also.
Note this property is somewhat unique to colimits of the empty diagram: for general `J`, if `C`
has colimits of shape `J` and `G` preserves them, then `D` does not necessarily have colimits of
shape `J`.
-/
theorem has_initial_of_has_initial_of_preserves_colimit [PreservesColimit (Functor.empty.{0} C) G] : HasInitial D :=
  ⟨fun F => by
    have := has_colimit.mk ⟨_, is_colimit_of_has_initial_of_preserves_colimit G⟩
    apply has_colimit_of_iso F.unique_from_empty⟩

variable [HasInitial D]

/-- If the initial comparison map for `G` is an isomorphism, then `G` preserves initial objects.
-/
def PreservesInitial.ofIsoComparison [i : IsIso (initialComparison G)] : PreservesColimit (Functor.empty C) G := by
  apply preserves_colimit_of_preserves_colimit_cocone initial_is_initial
  apply (is_colimit_map_cocone_empty_cocone_equiv _ _).symm _
  apply is_colimit.of_point_iso (colimit.is_colimit (Functor.empty.{0} D))
  apply i

/-- If there is any isomorphism `⊥ ⟶ G.obj ⊥`, then `G` preserves initial objects. -/
def preservesInitialOfIsIso (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : IsIso f] : PreservesColimit (Functor.empty C) G := by
  rw [Subsingleton.elimₓ f (initial_comparison G)] at i
  exact preserves_initial.of_iso_comparison G

/-- If there is any isomorphism `⊥ ≅ G.obj ⊥ `, then `G` preserves initial objects. -/
def preservesInitialOfIso (f : ⊥_ D ≅ G.obj (⊥_ C)) : PreservesColimit (Functor.empty C) G :=
  preservesInitialOfIsIso G f.Hom

variable [PreservesColimit (Functor.empty.{0} C) G]

/-- If `G` preserves initial objects, then the initial comparison map for `G` is an isomorphism. -/
def PreservesInitial.iso : G.obj (⊥_ C) ≅ ⊥_ D :=
  (isColimitOfHasInitialOfPreservesColimit G).coconePointUniqueUpToIso (colimit.isColimit _)

@[simp]
theorem PreservesInitial.iso_hom : (PreservesInitial.iso G).inv = initialComparison G :=
  rfl

instance : IsIso (initialComparison G) := by
  rw [← preserves_initial.iso_hom]
  infer_instance

end Initial

end CategoryTheory.Limits

