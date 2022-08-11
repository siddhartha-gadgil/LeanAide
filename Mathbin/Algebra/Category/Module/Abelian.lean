/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.LinearAlgebra.Isomorphisms
import Mathbin.Algebra.Category.Module.Kernels
import Mathbin.Algebra.Category.Module.Limits
import Mathbin.CategoryTheory.Abelian.Exact

/-!
# The category of left R-modules is abelian.

Additionally, two linear maps are exact in the categorical sense iff `range f = ker g`.
-/


open CategoryTheory

open CategoryTheory.Limits

noncomputable section

universe w v u

namespace ModuleCat

variable {R : Type u} [Ringₓ R] {M N : ModuleCat.{v} R} (f : M ⟶ N)

/-- In the category of modules, every monomorphism is normal. -/
def normalMono (hf : Mono f) : NormalMono f where
  z := of R (N ⧸ f.range)
  g := f.range.mkq
  w := LinearMap.range_mkq_comp _
  IsLimit :=/- The following [invalid Lean code](https://github.com/leanprover-community/lean/issues/341)
                might help you understand what's going on here:
                ```
                calc
                M   ≃ₗ[R] f.ker.quotient  : (submodule.quot_equiv_of_eq_bot _ (ker_eq_bot_of_mono _)).symm
                ... ≃ₗ[R] f.range         : linear_map.quot_ker_equiv_range f
                ... ≃ₗ[R] r.range.mkq.ker : linear_equiv.of_eq _ _ (submodule.ker_mkq _).symm
                ```
              -/
        IsKernel.isoKernel
        _ _ (kernelIsLimit _)
        (LinearEquiv.toModuleIso'
          ((Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm ≪≫ₗ
            (LinearMap.quotKerEquivRange f ≪≫ₗ LinearEquiv.ofEq _ _ (Submodule.ker_mkq _).symm))) <|
      by
      ext
      rfl

/-- In the category of modules, every epimorphism is normal. -/
def normalEpi (hf : Epi f) : NormalEpi f where
  w := of R f.ker
  g := f.ker.Subtype
  w := LinearMap.comp_ker_subtype _
  IsColimit :=/- The following invalid Lean code might help you understand what's going on here:
                ```
                calc f.ker.subtype.range.quotient
                    ≃ₗ[R] f.ker.quotient : submodule.quot_equiv_of_eq _ _ (submodule.range_subtype _)
                ... ≃ₗ[R] f.range        : linear_map.quot_ker_equiv_range f
                ... ≃ₗ[R] N              : linear_equiv.of_top _ (range_eq_top_of_epi _)
                ```
              -/
        IsCokernel.cokernelIso
        _ _ (cokernelIsColimit _)
        (LinearEquiv.toModuleIso'
          (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ LinearMap.quotKerEquivRange f ≪≫ₗ
            LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <|
      by
      ext
      rfl

/-- The category of R-modules is abelian. -/
instance : Abelian (ModuleCat R) where
  HasFiniteProducts := ⟨fun J _ => Limits.has_limits_of_shape_of_has_limits⟩
  HasKernels := Limits.has_kernels_of_has_equalizers (ModuleCat R)
  HasCokernels := has_cokernels_Module
  normalMonoOfMono := fun X Y => normalMono
  normalEpiOfEpi := fun X Y => normalEpi

section ReflectsLimits

/- We need to put this in this weird spot because we need to know that the category of modules
    is balanced. -/
instance forgetReflectsLimitsOfSize : ReflectsLimitsOfSize.{v, v} (forget (ModuleCat.{max v w} R)) :=
  reflects_limits_of_reflects_isomorphisms

instance forget₂ReflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget₂ (ModuleCat.{max v w} R) AddCommGroupₓₓ.{max v w}) :=
  reflects_limits_of_reflects_isomorphisms

instance forgetReflectsLimits : ReflectsLimits (forget (ModuleCat.{v} R)) :=
  ModuleCat.forgetReflectsLimitsOfSize.{v, v}

instance forget₂ReflectsLimits : ReflectsLimits (forget₂ (ModuleCat.{v} R) AddCommGroupₓₓ.{v}) :=
  ModuleCat.forget₂ReflectsLimitsOfSize.{v, v}

end ReflectsLimits

variable {O : ModuleCat.{v} R} (g : N ⟶ O)

open LinearMap

attribute [local instance] preadditive.has_equalizers_of_has_kernels

theorem exact_iff : Exact f g ↔ f.range = g.ker := by
  rw [abelian.exact_iff' f g (kernel_is_limit _) (cokernel_is_colimit _)]
  exact
    ⟨fun h => le_antisymmₓ (range_le_ker_iff.2 h.1) (ker_le_range_iff.2 h.2), fun h =>
      ⟨range_le_ker_iff.1 <| le_of_eqₓ h, ker_le_range_iff.1 <| le_of_eqₓ h.symm⟩⟩

end ModuleCat

