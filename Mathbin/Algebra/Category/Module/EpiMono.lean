/-
Copyright (c) 2021 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.LinearAlgebra.Quotient
import Mathbin.CategoryTheory.EpiMono
import Mathbin.Algebra.Category.Module.Basic

/-!
# Monomorphisms in `Module R`

This file shows that an `R`-linear map is a monomorphism in the category of `R`-modules
if and only if it is injective, and similarly an epimorphism if and only if it is surjective.
-/


universe v u

open CategoryTheory

open ModuleCat

open ModuleCat

namespace ModuleCat

variable {R : Type u} [Ringₓ R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroupₓ M] [Module R M]

theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  LinearMap.ker_eq_bot_of_cancel fun u v => (@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1

theorem range_eq_top_of_epi [Epi f] : f.range = ⊤ :=
  LinearMap.range_eq_top_of_cancel fun u v => (@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1

theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun hf => ker_eq_bot_of_mono _, fun hf => ConcreteCategory.mono_of_injective _ <| LinearMap.ker_eq_bot.1 hf⟩

theorem mono_iff_injective : Mono f ↔ Function.Injective f := by
  rw [mono_iff_ker_eq_bot, LinearMap.ker_eq_bot]

theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  ⟨fun hf => range_eq_top_of_epi _, fun hf => ConcreteCategory.epi_of_surjective _ <| LinearMap.range_eq_top.1 hf⟩

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, LinearMap.range_eq_top]

/-- If the zero morphism is an epi then the codomain is trivial. -/
def uniqueOfEpiZero (X) [h : Epi (0 : X ⟶ of R M)] : Unique M :=
  uniqueOfSurjectiveZero X ((ModuleCat.epi_iff_surjective _).mp h)

instance mono_as_hom'_subtype (U : Submodule R X) : Mono (↾U.Subtype) :=
  (mono_iff_ker_eq_bot _).mpr (Submodule.ker_subtype U)

instance epi_as_hom''_mkq (U : Submodule R X) : Epi (↿U.mkq) :=
  (epi_iff_range_eq_top _).mpr <| Submodule.range_mkq _

end ModuleCat

