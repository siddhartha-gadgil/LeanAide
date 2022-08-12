/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Adam Topaz, Johan Commelin, Jakob von Raumer
-/
import Mathbin.CategoryTheory.Abelian.Opposite
import Mathbin.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.Algebra.Homology.Exact
import Mathbin.Tactic.Tfae

/-!
# Exact sequences in abelian categories

In an abelian category, we get several interesting results related to exactness which are not
true in more general settings.

## Main results
* `(f, g)` is exact if and only if `f ≫ g = 0` and `kernel.ι g ≫ cokernel.π f = 0`. This
  characterisation tends to be less cumbersome to work with than the original definition involving
  the comparison map `image f ⟶ kernel g`.
* If `(f, g)` is exact, then `image.ι f` has the universal property of the kernel of `g`.
* `f` is a monomorphism iff `kernel.ι f = 0` iff `exact 0 f`, and `f` is an epimorphism iff
  `cokernel.π = 0` iff `exact f 0`.
* A faithful functor between abelian categories that preserves zero morphisms reflects exact
  sequences.
* `X ⟶ Y ⟶ Z ⟶ 0` is exact if and only if the second map is a cokernel of the first, and
  `0 ⟶ X ⟶ Y ⟶ Z` is exact if and only if the first map is a kernel of the second.
* An exact functor preserves exactness, more specifically, if `F` preserves finite colimits and
  limits, then `exact f g` implies `exact (F.map f) (F.map g)`
-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Preadditive

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

namespace CategoryTheory

namespace Abelian

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

attribute [local instance] has_equalizers_of_has_kernels

/-- In an abelian category, a pair of morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` is exact
iff `image_subobject f = kernel_subobject g`.
-/
theorem exact_iff_image_eq_kernel : Exact f g ↔ imageSubobject f = kernelSubobject g := by
  constructor
  · intro h
    fapply subobject.eq_of_comm
    · suffices is_iso (imageToKernel _ _ h.w) by
        exact as_iso (imageToKernel _ _ h.w)
      exact is_iso_of_mono_of_epi _
      
    · simp
      
    
  · apply exact_of_image_eq_kernel
    

theorem exact_iff : Exact f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0 := by
  constructor
  · intro h
    exact ⟨h.1, kernel_comp_cokernel f g h⟩
    
  · refine' fun h => ⟨h.1, _⟩
    suffices hl : is_limit (kernel_fork.of_ι (image_subobject f).arrow (image_subobject_arrow_comp_eq_zero h.1))
    · have :
        imageToKernel f g h.1 =
          (is_limit.cone_point_unique_up_to_iso hl (limit.is_limit _)).Hom ≫ (kernel_subobject_iso _).inv :=
        by
        ext
        simp
      rw [this]
      infer_instance
      
    refine' kernel_fork.is_limit.of_ι _ _ _ _ _
    · refine' fun W u hu => kernel.lift (cokernel.π f) u _ ≫ (image_iso_image f).Hom ≫ (image_subobject_iso _).inv
      rw [← kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero]
      
    · tidy
      
    · intros
      rw [← cancel_mono (image_subobject f).arrow, w]
      simp
      
    

theorem exact_iff' {cg : KernelFork g} (hg : IsLimit cg) {cf : CokernelCofork f} (hf : IsColimit cf) :
    Exact f g ↔ f ≫ g = 0 ∧ cg.ι ≫ cf.π = 0 := by
  constructor
  · intro h
    exact ⟨h.1, fork_ι_comp_cofork_π f g h cg cf⟩
    
  · rw [exact_iff]
    refine' fun h => ⟨h.1, _⟩
    apply zero_of_epi_comp (is_limit.cone_point_unique_up_to_iso hg (limit.is_limit _)).Hom
    apply zero_of_comp_mono (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) hf).Hom
    simp [← h.2]
    

theorem exact_tfae :
    Tfae [Exact f g, f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0, imageSubobject f = kernelSubobject g] := by
  tfae_have 1 ↔ 2
  · apply exact_iff
    
  tfae_have 1 ↔ 3
  · apply exact_iff_image_eq_kernel
    
  tfae_finish

theorem IsEquivalence.exact_iff {D : Type u₁} [Category.{v₁} D] [Abelian D] (F : C ⥤ D) [IsEquivalence F] :
    Exact (F.map f) (F.map g) ↔ Exact f g := by
  simp only [← exact_iff, F.map_eq_zero_iff, ← F.map_comp, ← category.assoc, kernel_comparison_comp_ι g F,
    π_comp_cokernel_comparison f F]
  rw [is_iso.comp_left_eq_zero (kernel_comparison g F), ← category.assoc,
    is_iso.comp_right_eq_zero _ (cokernel_comparison f F)]

/-- The dual result is true even in non-abelian categories, see
    `category_theory.exact_epi_comp_iff`. -/
theorem exact_epi_comp_iff {W : C} (h : W ⟶ X) [Epi h] : Exact (h ≫ f) g ↔ Exact f g := by
  refine' ⟨fun hfg => _, fun h => exact_epi_comp h⟩
  let hc :=
    is_cokernel_of_comp _ _ (colimit.is_colimit (parallel_pair (h ≫ f) 0))
      (by
        rw [← cancel_epi h, ← category.assoc, cokernel_cofork.condition, comp_zero])
      rfl
  refine' (exact_iff' _ _ (limit.is_limit _) hc).2 ⟨_, ((exact_iff _ _).1 hfg).2⟩
  exact
    zero_of_epi_comp h
      (by
        rw [← hfg.1, category.assoc])

/-- If `(f, g)` is exact, then `images.image.ι f` is a kernel of `g`. -/
def isLimitImage (h : Exact f g) :
    IsLimit (KernelFork.ofι (Abelian.image.ι f) (image_ι_comp_eq_zero h.1) : KernelFork g) := by
  rw [exact_iff] at h
  refine' kernel_fork.is_limit.of_ι _ _ _ _ _
  · refine' fun W u hu => kernel.lift (cokernel.π f) u _
    rw [← kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero]
    
  tidy

/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
def isLimitImage' (h : Exact f g) : IsLimit (KernelFork.ofι (Limits.image.ι f) (Limits.image_ι_comp_eq_zero h.1)) :=
  IsKernel.isoKernel _ _ (isLimitImage f g h) (imageIsoImage f).symm <| IsImage.lift_fac _ _

/-- If `(f, g)` is exact, then `coimages.coimage.π g` is a cokernel of `f`. -/
def isColimitCoimage (h : Exact f g) :
    IsColimit (CokernelCofork.ofπ (Abelian.coimage.π g) (Abelian.comp_coimage_π_eq_zero h.1) : CokernelCofork f) := by
  rw [exact_iff] at h
  refine' cokernel_cofork.is_colimit.of_π _ _ _ _ _
  · refine' fun W u hu => cokernel.desc (kernel.ι g) u _
    rw [← cokernel.π_desc f u hu, ← category.assoc, h.2, has_zero_morphisms.zero_comp]
    
  tidy

/-- If `(f, g)` is exact, then `factor_thru_image g` is a cokernel of `f`. -/
def isColimitImage (h : Exact f g) :
    IsColimit (CokernelCofork.ofπ (Limits.factorThruImage g) (comp_factor_thru_image_eq_zero h.1)) :=
  IsCokernel.cokernelIso _ _ (isColimitCoimage f g h) (coimageIsoImage' g) <|
    (cancel_mono (Limits.image.ι g)).1 <| by
      simp

theorem exact_cokernel : Exact f (cokernel.π f) := by
  rw [exact_iff]
  tidy

instance (h : Exact f g) : Mono (cokernel.desc f g h.w) :=
  suffices h :
    cokernel.desc f g h.w =
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitImage f g h)).Hom ≫ Limits.image.ι g
    from by
    rw [h]
    apply mono_comp
  (cancel_epi (cokernel.π f)).1 <| by
    simp

/-- If `ex : exact f g` and `epi g`, then `cokernel.desc _ _ ex.w` is an isomorphism. -/
instance (ex : Exact f g) [Epi g] : IsIso (cokernel.desc f g ex.w) :=
  is_iso_of_mono_of_epi (Limits.cokernel.desc f g ex.w)

@[simp, reassoc]
theorem Cokernel.Desc.inv [Epi g] (ex : Exact f g) : g ≫ inv (cokernel.desc _ _ ex.w) = cokernel.π _ := by
  simp

instance (ex : Exact f g) [Mono f] : IsIso (kernel.lift g f ex.w) :=
  is_iso_of_mono_of_epi (Limits.kernel.lift g f ex.w)

@[simp, reassoc]
theorem Kernel.Lift.inv [Mono f] (ex : Exact f g) : inv (kernel.lift _ _ ex.w) ≫ f = kernel.ι g := by
  simp

/-- If `X ⟶ Y ⟶ Z ⟶ 0` is exact, then the second map is a cokernel of the first. -/
def isColimitOfExactOfEpi [Epi g] (h : Exact f g) : IsColimit (CokernelCofork.ofπ _ h.w) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) <|
    Cocones.ext
      ⟨cokernel.desc _ _ h.w, epiDesc g (cokernel.π f) ((exact_iff _ _).1 h).2,
        (cancel_epi (cokernel.π f)).1
          (by
            tidy),
        (cancel_epi g).1
          (by
            tidy)⟩
      fun j => by
      cases j <;> simp

/-- If `0 ⟶ X ⟶ Y ⟶ Z` is exact, then the first map is a kernel of the second. -/
def isLimitOfExactOfMono [Mono f] (h : Exact f g) : IsLimit (KernelFork.ofι _ h.w) :=
  IsLimit.ofIsoLimit (limit.isLimit _) <|
    Cones.ext
      ⟨monoLift f (kernel.ι g) ((exact_iff _ _).1 h).2, kernel.lift _ _ h.w,
        (cancel_mono (kernel.ι g)).1
          (by
            tidy),
        (cancel_mono f).1
          (by
            tidy)⟩
      fun j => by
      cases j <;> simp

theorem exact_of_is_cokernel (w : f ≫ g = 0) (h : IsColimit (CokernelCofork.ofπ _ w)) : Exact f g := by
  refine' (exact_iff _ _).2 ⟨w, _⟩
  have := h.fac (cokernel_cofork.of_π _ (cokernel.condition f)) walking_parallel_pair.one
  simp only [← cofork.of_π_ι_app] at this
  rw [← this, ← category.assoc, kernel.condition, zero_comp]

theorem exact_of_is_kernel (w : f ≫ g = 0) (h : IsLimit (KernelFork.ofι _ w)) : Exact f g := by
  refine' (exact_iff _ _).2 ⟨w, _⟩
  have := h.fac (kernel_fork.of_ι _ (kernel.condition g)) walking_parallel_pair.zero
  simp only [← fork.of_ι_π_app] at this
  rw [← this, category.assoc, cokernel.condition, comp_zero]

section

variable (Z)

theorem tfae_mono : Tfae [Mono f, kernel.ι f = 0, Exact (0 : Z ⟶ X) f] := by
  tfae_have 3 → 2
  · exact kernel_ι_eq_zero_of_exact_zero_left Z
    
  tfae_have 1 → 3
  · intros
    exact exact_zero_left_of_mono Z
    
  tfae_have 2 → 1
  · exact mono_of_kernel_ι_eq_zero _
    
  tfae_finish

-- Note we've already proved `mono_iff_exact_zero_left : mono f ↔ exact (0 : Z ⟶ X) f`
-- in any preadditive category with kernels and images.
theorem mono_iff_kernel_ι_eq_zero : Mono f ↔ kernel.ι f = 0 :=
  (tfae_mono X f).out 0 1

theorem tfae_epi : Tfae [Epi f, cokernel.π f = 0, Exact f (0 : Y ⟶ Z)] := by
  tfae_have 3 → 2
  · rw [exact_iff]
    rintro ⟨-, h⟩
    exact zero_of_epi_comp _ h
    
  tfae_have 1 → 3
  · rw [exact_iff]
    intro
    exact
      ⟨by
        simp , by
        simp [← cokernel.π_of_epi]⟩
    
  tfae_have 2 → 1
  · exact epi_of_cokernel_π_eq_zero _
    
  tfae_finish

-- Note we've already proved `epi_iff_exact_zero_right : epi f ↔ exact f (0 : Y ⟶ Z)`
-- in any preadditive category with equalizers and images.
theorem epi_iff_cokernel_π_eq_zero : Epi f ↔ cokernel.π f = 0 :=
  (tfae_epi X f).out 0 1

end

section Opposite

theorem Exact.op (h : Exact f g) : Exact g.op f.op := by
  rw [exact_iff]
  refine'
    ⟨by
      simp [op_comp, ← h.w], Quiver.Hom.unop_inj _⟩
  simp only [← unop_comp, ← cokernel.π_op, ← eq_to_hom_refl, ← kernel.ι_op, ← category.id_comp, ← category.assoc, ←
    kernel_comp_cokernel_assoc _ _ h, ← zero_comp, ← comp_zero, ← unop_zero]

theorem Exact.op_iff : Exact g.op f.op ↔ Exact f g :=
  ⟨fun e => by
    rw [← is_equivalence.exact_iff _ _ (op_op_equivalence C).inverse]
    exact exact.op _ _ e, Exact.op _ _⟩

theorem Exact.unop {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (f : Y ⟶ Z) (h : Exact g f) : Exact f.unop g.unop := by
  rw [← f.op_unop, ← g.op_unop] at h
  rwa [← exact.op_iff]

theorem Exact.unop_iff {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (f : Y ⟶ Z) : Exact f.unop g.unop ↔ Exact g f :=
  ⟨fun e => by
    rwa [← f.op_unop, ← g.op_unop, ← exact.op_iff] at e, fun e => @Exact.unop _ _ g f e⟩

end Opposite

end Abelian

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

instance (priority := 100) reflectsExactSequencesOfPreservesZeroMorphismsOfFaithful [Faithful F] :
    ReflectsExactSequences F where reflects := fun X Y Z f g hfg => by
    rw [abelian.exact_iff, ← F.map_comp, F.map_eq_zero_iff] at hfg
    refine' (abelian.exact_iff _ _).2 ⟨hfg.1, F.zero_of_map_zero _ _⟩
    obtain ⟨k, hk⟩ :=
      kernel.lift' (F.map g) (F.map (kernel.ι g))
        (by
          simp only [F.map_comp, ← kernel.condition, ← CategoryTheory.Functor.map_zero])
    obtain ⟨l, hl⟩ :=
      cokernel.desc' (F.map f) (F.map (cokernel.π f))
        (by
          simp only [F.map_comp, ← cokernel.condition, ← CategoryTheory.Functor.map_zero])
    rw [F.map_comp, ← hk, ← hl, category.assoc, reassoc_of hfg.2, zero_comp, comp_zero]

end

end Functor

namespace Functor

open Limits Abelian

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]

variable [HasZeroObject A] [HasZeroMorphisms A] [HasImages A] [HasEqualizers A]

variable [has_cokernels A] [Abelian B]

variable (L : A ⥤ B) [PreservesFiniteLimits L] [PreservesFiniteColimits L]

theorem map_exact {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (e1 : Exact f g) : Exact (L.map f) (L.map g) := by
  let hcoker := is_colimit_of_has_cokernel_of_preserves_colimit L f
  let hker := is_limit_of_has_kernel_of_preserves_limit L g
  refine'
    (exact_iff' _ _ hker hcoker).2
      ⟨by
        simp [L.map_comp, ← e1.1], _⟩
  rw [fork.ι_of_ι, cofork.π_of_π, ← L.map_comp, kernel_comp_cokernel _ _ e1, L.map_zero]

end Functor

end CategoryTheory

