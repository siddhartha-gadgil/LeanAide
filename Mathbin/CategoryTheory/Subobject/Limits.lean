/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import Mathbin.CategoryTheory.Subobject.Lattice

/-!
# Specific subobjects

We define `equalizer_subobject`, `kernel_subobject` and `image_subobject`, which are the subobjects
represented by the equalizer, kernel and image of (a pair of) morphism(s) and provide conditions
for `P.factors f`, where `P` is one of these special subobjects.

TODO: Add conditions for when `P` is a pullback subobject.
TODO: an iff characterisation of `(image_subobject f).factors h`

-/


universe v u

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace CategoryTheory

namespace Limits

section Equalizer

variable (f g : X ⟶ Y) [HasEqualizer f g]

/-- The equalizer of morphisms `f g : X ⟶ Y` as a `subobject X`. -/
abbrev equalizerSubobject : Subobject X :=
  Subobject.mk (equalizer.ι f g)

/-- The underlying object of `equalizer_subobject f g` is (up to isomorphism!)
the same as the chosen object `equalizer f g`. -/
def equalizerSubobjectIso : (equalizerSubobject f g : C) ≅ equalizer f g :=
  Subobject.underlyingIso (equalizer.ι f g)

@[simp, reassoc]
theorem equalizer_subobject_arrow :
    (equalizerSubobjectIso f g).Hom ≫ equalizer.ι f g = (equalizerSubobject f g).arrow := by
  simp [← equalizer_subobject_iso]

@[simp, reassoc]
theorem equalizer_subobject_arrow' :
    (equalizerSubobjectIso f g).inv ≫ (equalizerSubobject f g).arrow = equalizer.ι f g := by
  simp [← equalizer_subobject_iso]

@[reassoc]
theorem equalizer_subobject_arrow_comp : (equalizerSubobject f g).arrow ≫ f = (equalizerSubobject f g).arrow ≫ g := by
  rw [← equalizer_subobject_arrow, category.assoc, category.assoc, equalizer.condition]

theorem equalizer_subobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) : (equalizerSubobject f g).Factors h :=
  ⟨equalizer.lift h w, by
    simp ⟩

theorem equalizer_subobject_factors_iff {W : C} (h : W ⟶ X) : (equalizerSubobject f g).Factors h ↔ h ≫ f = h ≫ g :=
  ⟨fun w => by
    rw [← subobject.factor_thru_arrow _ _ w, category.assoc, equalizer_subobject_arrow_comp, category.assoc],
    equalizer_subobject_factors f g h⟩

end Equalizer

section Kernel

variable [HasZeroMorphisms C] (f : X ⟶ Y) [HasKernel f]

/-- The kernel of a morphism `f : X ⟶ Y` as a `subobject X`. -/
abbrev kernelSubobject : Subobject X :=
  Subobject.mk (kernel.ι f)

/-- The underlying object of `kernel_subobject f` is (up to isomorphism!)
the same as the chosen object `kernel f`. -/
def kernelSubobjectIso : (kernelSubobject f : C) ≅ kernel f :=
  Subobject.underlyingIso (kernel.ι f)

@[simp, reassoc, elementwise]
theorem kernel_subobject_arrow : (kernelSubobjectIso f).Hom ≫ kernel.ι f = (kernelSubobject f).arrow := by
  simp [← kernel_subobject_iso]

@[simp, reassoc, elementwise]
theorem kernel_subobject_arrow' : (kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f := by
  simp [← kernel_subobject_iso]

@[simp, reassoc, elementwise]
theorem kernel_subobject_arrow_comp : (kernelSubobject f).arrow ≫ f = 0 := by
  rw [← kernel_subobject_arrow]
  simp only [← category.assoc, ← kernel.condition, ← comp_zero]

theorem kernel_subobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = 0) : (kernelSubobject f).Factors h :=
  ⟨kernel.lift _ h w, by
    simp ⟩

theorem kernel_subobject_factors_iff {W : C} (h : W ⟶ X) : (kernelSubobject f).Factors h ↔ h ≫ f = 0 :=
  ⟨fun w => by
    rw [← subobject.factor_thru_arrow _ _ w, category.assoc, kernel_subobject_arrow_comp, comp_zero],
    kernel_subobject_factors f h⟩

/-- A factorisation of `h : W ⟶ X` through `kernel_subobject f`, assuming `h ≫ f = 0`. -/
def factorThruKernelSubobject {W : C} (h : W ⟶ X) (w : h ≫ f = 0) : W ⟶ kernelSubobject f :=
  (kernelSubobject f).factorThru h (kernel_subobject_factors f h w)

@[simp]
theorem factor_thru_kernel_subobject_comp_arrow {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    factorThruKernelSubobject f h w ≫ (kernelSubobject f).arrow = h := by
  dsimp' [← factor_thru_kernel_subobject]
  simp

@[simp]
theorem factor_thru_kernel_subobject_comp_kernel_subobject_iso {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    factorThruKernelSubobject f h w ≫ (kernelSubobjectIso f).Hom = kernel.lift f h w :=
  (cancel_mono (kernel.ι f)).1 <| by
    simp

section

variable {f} {X' Y' : C} {f' : X' ⟶ Y'} [HasKernel f']

/-- A commuting square induces a morphism between the kernel subobjects. -/
def kernelSubobjectMap (sq : Arrow.mk f ⟶ Arrow.mk f') : (kernelSubobject f : C) ⟶ (kernelSubobject f' : C) :=
  Subobject.factorThru _ ((kernelSubobject f).arrow ≫ sq.left)
    (kernel_subobject_factors _ _
      (by
        simp [← sq.w]))

@[simp, reassoc, elementwise]
theorem kernel_subobject_map_arrow (sq : Arrow.mk f ⟶ Arrow.mk f') :
    kernelSubobjectMap sq ≫ (kernelSubobject f').arrow = (kernelSubobject f).arrow ≫ sq.left := by
  simp [← kernel_subobject_map]

@[simp]
theorem kernel_subobject_map_id : kernelSubobjectMap (𝟙 (Arrow.mk f)) = 𝟙 _ := by
  ext
  simp
  dsimp'
  simp

-- See library note [dsimp, simp].
@[simp]
theorem kernel_subobject_map_comp {X'' Y'' : C} {f'' : X'' ⟶ Y''} [HasKernel f''] (sq : Arrow.mk f ⟶ Arrow.mk f')
    (sq' : Arrow.mk f' ⟶ Arrow.mk f'') :
    kernelSubobjectMap (sq ≫ sq') = kernelSubobjectMap sq ≫ kernelSubobjectMap sq' := by
  ext
  simp

end

@[simp]
theorem kernel_subobject_zero {A B : C} : kernelSubobject (0 : A ⟶ B) = ⊤ :=
  (is_iso_iff_mk_eq_top _).mp
    (by
      infer_instance)

instance is_iso_kernel_subobject_zero_arrow : IsIso (kernelSubobject (0 : X ⟶ Y)).arrow :=
  (is_iso_arrow_iff_eq_top _).mpr kernel_subobject_zero

theorem le_kernel_subobject (A : Subobject X) (h : A.arrow ≫ f = 0) : A ≤ kernelSubobject f :=
  Subobject.le_mk_of_comm (kernel.lift f A.arrow h)
    (by
      simp )

/-- The isomorphism between the kernel of `f ≫ g` and the kernel of `g`,
when `f` is an isomorphism.
-/
def kernelSubobjectIsoComp {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobject (f ≫ g) : C) ≅ (kernelSubobject g : C) :=
  kernelSubobjectIso _ ≪≫ kernelIsIsoComp f g ≪≫ (kernelSubobjectIso _).symm

@[simp]
theorem kernel_subobject_iso_comp_hom_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobjectIsoComp f g).Hom ≫ (kernelSubobject g).arrow = (kernelSubobject (f ≫ g)).arrow ≫ f := by
  simp [← kernel_subobject_iso_comp]

@[simp]
theorem kernel_subobject_iso_comp_inv_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobjectIsoComp f g).inv ≫ (kernelSubobject (f ≫ g)).arrow = (kernelSubobject g).arrow ≫ inv f := by
  simp [← kernel_subobject_iso_comp]

/-- The kernel of `f` is always a smaller subobject than the kernel of `f ≫ h`. -/
theorem kernel_subobject_comp_le (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [HasKernel (f ≫ h)] :
    kernelSubobject f ≤ kernelSubobject (f ≫ h) :=
  le_kernel_subobject _ _
    (by
      simp )

/-- Postcomposing by an monomorphism does not change the kernel subobject. -/
@[simp]
theorem kernel_subobject_comp_mono (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] :
    kernelSubobject (f ≫ h) = kernelSubobject f :=
  le_antisymmₓ
    (le_kernel_subobject _ _
      ((cancel_mono h).mp
        (by
          simp )))
    (kernel_subobject_comp_le f h)

instance kernel_subobject_comp_mono_is_iso (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] :
    IsIso (Subobject.ofLe _ _ (kernel_subobject_comp_le f h)) := by
  rw [of_le_mk_le_mk_of_comm (kernel_comp_mono f h).inv]
  · infer_instance
    
  · simp
    

end Kernel

section Image

variable (f : X ⟶ Y) [HasImage f]

/-- The image of a morphism `f g : X ⟶ Y` as a `subobject Y`. -/
abbrev imageSubobject : Subobject Y :=
  Subobject.mk (image.ι f)

/-- The underlying object of `image_subobject f` is (up to isomorphism!)
the same as the chosen object `image f`. -/
def imageSubobjectIso : (imageSubobject f : C) ≅ image f :=
  Subobject.underlyingIso (image.ι f)

@[simp, reassoc]
theorem image_subobject_arrow : (imageSubobjectIso f).Hom ≫ image.ι f = (imageSubobject f).arrow := by
  simp [← image_subobject_iso]

@[simp, reassoc]
theorem image_subobject_arrow' : (imageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f := by
  simp [← image_subobject_iso]

/-- A factorisation of `f : X ⟶ Y` through `image_subobject f`. -/
def factorThruImageSubobject : X ⟶ imageSubobject f :=
  factorThruImage f ≫ (imageSubobjectIso f).inv

instance [HasEqualizers C] : Epi (factorThruImageSubobject f) := by
  dsimp' [← factor_thru_image_subobject]
  apply epi_comp

@[simp, reassoc, elementwise]
theorem image_subobject_arrow_comp : factorThruImageSubobject f ≫ (imageSubobject f).arrow = f := by
  simp [← factor_thru_image_subobject, ← image_subobject_arrow]

theorem image_subobject_arrow_comp_eq_zero [HasZeroMorphisms C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage f]
    [Epi (factorThruImageSubobject f)] (h : f ≫ g = 0) : (imageSubobject f).arrow ≫ g = 0 :=
  zero_of_epi_comp (factorThruImageSubobject f) <| by
    simp [← h]

theorem image_subobject_factors_comp_self {W : C} (k : W ⟶ X) : (imageSubobject f).Factors (k ≫ f) :=
  ⟨k ≫ factorThruImage f, by
    simp ⟩

@[simp]
theorem factor_thru_image_subobject_comp_self {W : C} (k : W ⟶ X) (h) :
    (imageSubobject f).factorThru (k ≫ f) h = k ≫ factorThruImageSubobject f := by
  ext
  simp

@[simp]
theorem factor_thru_image_subobject_comp_self_assoc {W W' : C} (k : W ⟶ W') (k' : W' ⟶ X) (h) :
    (imageSubobject f).factorThru (k ≫ k' ≫ f) h = k ≫ k' ≫ factorThruImageSubobject f := by
  ext
  simp

/-- The image of `h ≫ f` is always a smaller subobject than the image of `f`. -/
theorem image_subobject_comp_le {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)] :
    imageSubobject (h ≫ f) ≤ imageSubobject f :=
  Subobject.mk_le_mk_of_comm (image.preComp h f)
    (by
      simp )

section

open ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C]

@[simp]
theorem image_subobject_zero_arrow : (imageSubobject (0 : X ⟶ Y)).arrow = 0 := by
  rw [← image_subobject_arrow]
  simp

@[simp]
theorem image_subobject_zero {A B : C} : imageSubobject (0 : A ⟶ B) = ⊥ :=
  Subobject.eq_of_comm (imageSubobjectIso _ ≪≫ image_zero ≪≫ Subobject.botCoeIsoZero.symm)
    (by
      simp )

end

section

variable [HasEqualizers C]

attribute [local instance] epi_comp

/-- The morphism `image_subobject (h ≫ f) ⟶ image_subobject f`
is an epimorphism when `h` is an epimorphism.
In general this does not imply that `image_subobject (h ≫ f) = image_subobject f`,
although it will when the ambient category is abelian.
 -/
instance image_subobject_comp_le_epi_of_epi {X' : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)] :
    Epi (Subobject.ofLe _ _ (image_subobject_comp_le h f)) := by
  rw [of_le_mk_le_mk_of_comm (image.pre_comp h f)]
  · infer_instance
    
  · simp
    

end

section

variable [HasEqualizers C]

/-- Postcomposing by an isomorphism gives an isomorphism between image subobjects. -/
def imageSubobjectCompIso (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobject (f ≫ h) : C) ≅ (imageSubobject f : C) :=
  imageSubobjectIso _ ≪≫ (image.compIso _ _).symm ≪≫ (imageSubobjectIso _).symm

@[simp, reassoc]
theorem image_subobject_comp_iso_hom_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobjectCompIso f h).Hom ≫ (imageSubobject f).arrow = (imageSubobject (f ≫ h)).arrow ≫ inv h := by
  simp [← image_subobject_comp_iso]

@[simp, reassoc]
theorem image_subobject_comp_iso_inv_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobjectCompIso f h).inv ≫ (imageSubobject (f ≫ h)).arrow = (imageSubobject f).arrow ≫ h := by
  simp [← image_subobject_comp_iso]

end

theorem image_subobject_mono (f : X ⟶ Y) [Mono f] : imageSubobject f = mk f :=
  eq_of_comm (imageSubobjectIso f ≪≫ imageMonoIsoSource f ≪≫ (underlyingIso f).symm)
    (by
      simp )

/-- Precomposing by an isomorphism does not change the image subobject. -/
theorem image_subobject_iso_comp [HasEqualizers C] {X' : C} (h : X' ⟶ X) [IsIso h] (f : X ⟶ Y) [HasImage f] :
    imageSubobject (h ≫ f) = imageSubobject f :=
  le_antisymmₓ (image_subobject_comp_le h f)
    (Subobject.mk_le_mk_of_comm (inv (image.preComp h f))
      (by
        simp ))

theorem image_subobject_le {A B : C} {X : Subobject B} (f : A ⟶ B) [HasImage f] (h : A ⟶ X) (w : h ≫ X.arrow = f) :
    imageSubobject f ≤ X :=
  Subobject.le_of_comm ((imageSubobjectIso f).Hom ≫ image.lift { i := (X : C), e := h, m := X.arrow })
    (by
      simp )

theorem image_subobject_le_mk {A B : C} {X : C} (g : X ⟶ B) [Mono g] (f : A ⟶ B) [HasImage f] (h : A ⟶ X)
    (w : h ≫ g = f) : imageSubobject f ≤ Subobject.mk g :=
  image_subobject_le f (h ≫ (Subobject.underlyingIso g).inv)
    (by
      simp [← w])

/-- Given a commutative square between morphisms `f` and `g`,
we have a morphism in the category from `image_subobject f` to `image_subobject g`. -/
def imageSubobjectMap {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g)
    [HasImageMap sq] : (imageSubobject f : C) ⟶ (imageSubobject g : C) :=
  (imageSubobjectIso f).Hom ≫ image.map sq ≫ (imageSubobjectIso g).inv

@[simp, reassoc]
theorem image_subobject_map_arrow {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
    (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    imageSubobjectMap sq ≫ (imageSubobject g).arrow = (imageSubobject f).arrow ≫ sq.right := by
  simp only [← image_subobject_map, ← category.assoc, ← image_subobject_arrow']
  erw [image.map_ι, ← category.assoc, image_subobject_arrow]

end Image

end Limits

end CategoryTheory

