/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathbin.Algebra.Category.Module.EpiMono
import Mathbin.Algebra.Module.Projective
import Mathbin.CategoryTheory.Preadditive.Projective
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!
# The category of `R`-modules has enough projectives.
-/


universe v u

open CategoryTheory

open CategoryTheory.Limits

open LinearMap

open ModuleCat

/-- The categorical notion of projective object agrees with the explicit module-theoretic notion. -/
theorem IsProjective.iff_projective {R : Type u} [Ringₓ R] {P : Type max u v} [AddCommGroupₓ P] [Module R P] :
    Module.Projective R P ↔ Projective (ModuleCat.of R P) := by
  refine' ⟨fun h => _, fun h => _⟩
  · let this : Module.Projective R ↥(ModuleCat.of R P) := h
    exact ⟨fun E X f e epi => Module.projective_lifting_property _ _ ((ModuleCat.epi_iff_surjective _).mp epi)⟩
    
  · refine' Module.projective_of_lifting_property _
    intro E X mE mX sE sX f g s
    have : epi (↟f) := (ModuleCat.epi_iff_surjective (↟f)).mpr s
    let this : projective (ModuleCat.of R P) := h
    exact ⟨projective.factor_thru (↟g) (↟f), projective.factor_thru_comp (↟g) (↟f)⟩
    

namespace ModuleCat

variable {R : Type u} [Ringₓ R] {M : ModuleCat.{max u v} R}

/-- Modules that have a basis are projective. -/
-- We transport the corresponding result from `module.projective`.
theorem projective_of_free {ι : Type _} (b : Basis ι R M) : Projective M :=
  Projective.of_iso (ModuleCat.ofSelfIso _) (IsProjective.iff_projective.mp (Module.projective_of_basis b))

/-- The category of modules has enough projectives, since every module is a quotient of a free
    module. -/
instance Module_enough_projectives :
    EnoughProjectives
      (ModuleCat.{max u v}
        R) where presentation := fun M =>
    ⟨{ P := ModuleCat.of R (M →₀ R), Projective := projective_of_free Finsupp.basisSingleOne,
        f := Finsupp.basisSingleOne.constr ℕ id,
        Epi :=
          (epi_iff_range_eq_top _).mpr
            (range_eq_top.2 fun m =>
              ⟨Finsupp.single m (1 : R), by
                simp [← Basis.constr]⟩) }⟩

end ModuleCat

