/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.Algebra.Category.Module.EpiMono
import Mathbin.CategoryTheory.Limits.ConcreteCategory

/-!
# The concrete (co)kernels in the category of modules are (co)kernels in the categorical sense.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ringₓ R]

section

variable {M N : ModuleCat.{v} R} (f : M ⟶ N)

/-- The kernel cone induced by the concrete kernel. -/
def kernelCone : KernelFork f :=
  KernelFork.ofι (asHom f.ker.Subtype) <| by
    tidy

/-- The kernel of a linear map is a kernel in the categorical sense. -/
def kernelIsLimit : IsLimit (kernelCone f) :=
  Fork.IsLimit.mk _
    (fun s =>
      LinearMap.codRestrict f.ker (Fork.ι s) fun c =>
        LinearMap.mem_ker.2 <| by
          rw [← @Function.comp_applyₓ _ _ _ f (fork.ι s) c, ← coe_comp, fork.condition,
            has_zero_morphisms.comp_zero (fork.ι s) N]
          rfl)
    (fun s => LinearMap.subtype_comp_cod_restrict _ _ _) fun s m h =>
    LinearMap.ext fun x =>
      Subtype.ext_iff_val.2
        (by
          simpa [h] )

/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (asHom f.range.mkq) <| LinearMap.range_mkq_comp _

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  Cofork.IsColimit.mk _
    (fun s => f.range.liftq (Cofork.π s) <| LinearMap.range_le_ker_iff.2 <| CokernelCofork.condition s)
    (fun s => f.range.liftq_mkq (Cofork.π s) _) fun s m h => by
    have : epi (as_hom f.range.mkq) := (epi_iff_range_eq_top _).mpr (Submodule.range_mkq _)
    apply (cancel_epi (as_hom f.range.mkq)).1
    convert h
    exact Submodule.liftq_mkq _ _ _

end

/-- The category of R-modules has kernels, given by the inclusion of the kernel submodule. -/
theorem has_kernels_Module : HasKernels (ModuleCat R) :=
  ⟨fun X Y f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/-- The category or R-modules has cokernels, given by the projection onto the quotient. -/
theorem has_cokernels_Module : HasCokernels (ModuleCat R) :=
  ⟨fun X Y f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

open ModuleCat

attribute [local instance] has_kernels_Module

attribute [local instance] has_cokernels_Module

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

/-- The categorical kernel of a morphism in `Module`
agrees with the usual module-theoretical kernel.
-/
noncomputable def kernelIsoKer {G H : ModuleCat.{v} R} (f : G ⟶ H) : kernel f ≅ ModuleCat.of R f.ker :=
  limit.isoLimitCone ⟨_, kernelIsLimit f⟩

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
@[simp, elementwise]
theorem kernel_iso_ker_inv_kernel_ι : (kernelIsoKer f).inv ≫ kernel.ι f = f.ker.Subtype :=
  limit.iso_limit_cone_inv_π _ _

@[simp, elementwise]
theorem kernel_iso_ker_hom_ker_subtype : (kernelIsoKer f).hom ≫ f.ker.Subtype = kernel.ι f :=
  IsLimit.cone_point_unique_up_to_iso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero

/-- The categorical cokernel of a morphism in `Module`
agrees with the usual module-theoretical quotient.
-/
noncomputable def cokernelIsoRangeQuotient {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    cokernel f ≅ ModuleCat.of R (H ⧸ f.range) :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩

-- We now show this isomorphism commutes with the projection of target to the cokernel.
@[simp, elementwise]
theorem cokernel_π_cokernel_iso_range_quotient_hom : cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = f.range.mkq := by
  convert colimit.iso_colimit_cocone_ι_hom _ _ <;> rfl

@[simp, elementwise]
theorem range_mkq_cokernel_iso_range_quotient_inv : ↿f.range.mkq ≫ (cokernelIsoRangeQuotient f).inv = cokernel.π f := by
  convert colimit.iso_colimit_cocone_ι_inv ⟨_, cokernel_is_colimit f⟩ _ <;> rfl

theorem cokernel_π_ext {M N : ModuleCat.{u} R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m) :
    cokernel.π f x = cokernel.π f y := by
  subst w
  simp

end ModuleCat

