/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.Algebra.Category.Module.EpiMono
import Mathbin.Algebra.Category.Module.Kernels
import Mathbin.CategoryTheory.Subobject.WellPowered
import Mathbin.CategoryTheory.Subobject.Limits
import Mathbin.CategoryTheory.Limits.ConcreteCategory

/-!
# Subobjects in the category of `R`-modules

We construct an explicit order isomorphism between the categorical subobjects of an `R`-module `M`
and its submodules. This immediately implies that the category of `R`-modules is well-powered.

-/


open CategoryTheory

open CategoryTheory.Subobject

open CategoryTheory.Limits

open ModuleCat

universe v u

namespace ModuleCat

variable {R : Type u} [Ringₓ R] (M : ModuleCat.{v} R)

/-- The categorical subobjects of a module `M` are in one-to-one correspondence with its
    submodules.-/
noncomputable def subobjectModule : Subobject M ≃o Submodule R M :=
  OrderIso.symm
    { invFun := fun S => S.arrow.range, toFun := fun N => Subobject.mk (↾N.Subtype),
      right_inv := fun S =>
        Eq.symm
          (by
            fapply eq_mk_of_comm
            · apply LinearEquiv.toModuleIso'Left
              apply LinearEquiv.ofBijective (LinearMap.codRestrict S.arrow.range S.arrow _)
              · simpa only [LinearMap.ker_eq_bot, ← LinearMap.ker_cod_restrict] using ker_eq_bot_of_mono _
                
              · rw [← LinearMap.range_eq_top, LinearMap.range_cod_restrict, Submodule.comap_subtype_self]
                
              · exact LinearMap.mem_range_self _
                
              
            · apply LinearMap.ext
              intro x
              rfl
              ),
      left_inv := fun N => by
        convert congr_arg LinearMap.range (underlying_iso_arrow (↾N.subtype)) using 1
        · have : (underlying_iso (↾N.subtype)).inv = (underlying_iso (↾N.subtype)).symm.toLinearEquiv := by
            apply LinearMap.ext
            intro x
            rfl
          rw [this, comp_def, LinearEquiv.range_comp]
          
        · exact (Submodule.range_subtype _).symm
          ,
      map_rel_iff' := fun S T => by
        refine'
          ⟨fun h => _, fun h =>
            mk_le_mk_of_comm (↟(Submodule.ofLe h))
              (by
                ext
                rfl)⟩
        convert LinearMap.range_comp_le_range (of_mk_le_mk _ _ h) (↾T.subtype)
        · simpa only [comp_def, ← of_mk_le_mk_comp] using (Submodule.range_subtype _).symm
          
        · exact (Submodule.range_subtype _).symm
           }

instance well_powered_Module : WellPowered (ModuleCat.{v} R) :=
  ⟨fun M => ⟨⟨_, ⟨(subobjectModule M).toEquiv⟩⟩⟩⟩

attribute [local instance] has_kernels_Module

/-- Bundle an element `m : M` such that `f m = 0` as a term of `kernel_subobject f`. -/
noncomputable def toKernelSubobject {M N : ModuleCat R} {f : M ⟶ N} : LinearMap.ker f →ₗ[R] kernelSubobject f :=
  (kernelSubobjectIso f ≪≫ ModuleCat.kernelIsoKer f).inv

@[simp]
theorem to_kernel_subobject_arrow {M N : ModuleCat R} {f : M ⟶ N} (x : LinearMap.ker f) :
    (kernelSubobject f).arrow (toKernelSubobject x) = x.1 := by
  simp [← to_kernel_subobject]

/-- An extensionality lemma showing that two elements of a cokernel by an image
are equal if they differ by an element of the image.

The application is for homology:
two elements in homology are equal if they differ by a boundary.
-/
@[ext]
theorem cokernel_π_image_subobject_ext {L M N : ModuleCat.{v} R} (f : L ⟶ M) [HasImage f]
    (g : (imageSubobject f : ModuleCat.{v} R) ⟶ N) [HasCokernel g] {x y : N} (l : L)
    (w : x = y + g (factorThruImageSubobject f l)) : cokernel.π g x = cokernel.π g y := by
  subst w
  simp

end ModuleCat

