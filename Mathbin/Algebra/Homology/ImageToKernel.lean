/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Subobject.Limits

/-!
# Image-to-kernel comparison maps

Whenever `f : A ⟶ B` and `g : B ⟶ C` satisfy `w : f ≫ g = 0`,
we have `image_le_kernel f g w : image_subobject f ≤ kernel_subobject g`
(assuming the appropriate images and kernels exist).

`image_to_kernel f g w` is the corresponding morphism between objects in `C`.

We define `homology f g w` of such a pair as the cokernel of `image_to_kernel f g w`.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

open Classical

noncomputable section

section

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

theorem image_le_kernel (w : f ≫ g = 0) : imageSubobject f ≤ kernelSubobject g :=
  image_subobject_le_mk _ _ (kernel.lift _ _ w)
    (by
      simp )

/-- The canonical morphism `image_subobject f ⟶ kernel_subobject g` when `f ≫ g = 0`.
-/
def imageToKernel (w : f ≫ g = 0) : (imageSubobject f : V) ⟶ (kernelSubobject g : V) :=
  Subobject.ofLe _ _ (image_le_kernel _ _ w)deriving Mono

/-- Prefer `image_to_kernel`. -/
@[simp]
theorem subobject_of_le_as_image_to_kernel (w : f ≫ g = 0) (h) :
    Subobject.ofLe (imageSubobject f) (kernelSubobject g) h = imageToKernel f g w :=
  rfl

@[simp, reassoc, elementwise]
theorem image_to_kernel_arrow (w : f ≫ g = 0) :
    imageToKernel f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow := by
  simp [← imageToKernel]

-- This is less useful as a `simp` lemma than it initially appears,
-- as it "loses" the information the morphism factors through the image.
theorem factor_thru_image_subobject_comp_image_to_kernel (w : f ≫ g = 0) :
    factorThruImageSubobject f ≫ imageToKernel f g w = factorThruKernelSubobject g f w := by
  ext
  simp

end

section

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp]
theorem image_to_kernel_zero_left [HasKernels V] [HasZeroObject V] {w} : imageToKernel (0 : A ⟶ B) g w = 0 := by
  ext
  simp

theorem image_to_kernel_zero_right [HasImages V] {w} :
    imageToKernel f (0 : B ⟶ C) w = (imageSubobject f).arrow ≫ inv (kernelSubobject (0 : B ⟶ C)).arrow := by
  ext
  simp

section

variable [HasKernels V] [HasImages V]

theorem image_to_kernel_comp_right {D : V} (h : C ⟶ D) (w : f ≫ g = 0) :
    imageToKernel f (g ≫ h)
        (by
          simp [← reassoc_of w]) =
      imageToKernel f g w ≫ Subobject.ofLe _ _ (kernel_subobject_comp_le g h) :=
  by
  ext
  simp

theorem image_to_kernel_comp_left {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) :
    imageToKernel (h ≫ f) g
        (by
          simp [← w]) =
      Subobject.ofLe _ _ (image_subobject_comp_le h f) ≫ imageToKernel f g w :=
  by
  ext
  simp

@[simp]
theorem image_to_kernel_comp_mono {D : V} (h : C ⟶ D) [Mono h] (w) :
    imageToKernel f (g ≫ h) w =
      imageToKernel f g
          ((cancel_mono h).mp
            (by
              simpa using w : (f ≫ g) ≫ h = 0 ≫ h)) ≫
        (Subobject.isoOfEq _ _ (kernel_subobject_comp_mono g h)).inv :=
  by
  ext
  simp

@[simp]
theorem image_to_kernel_epi_comp {Z : V} (h : Z ⟶ A) [Epi h] (w) :
    imageToKernel (h ≫ f) g w =
      Subobject.ofLe _ _ (image_subobject_comp_le h f) ≫
        imageToKernel f g
          ((cancel_epi h).mp
            (by
              simpa using w : h ≫ f ≫ g = h ≫ 0)) :=
  by
  ext
  simp

end

@[simp]
theorem image_to_kernel_comp_hom_inv_comp [HasEqualizers V] [HasImages V] {Z : V} {i : B ≅ Z} (w) :
    imageToKernel (f ≫ i.Hom) (i.inv ≫ g) w =
      (imageSubobjectCompIso _ _).Hom ≫
        imageToKernel f g
            (by
              simpa using w) ≫
          (kernelSubobjectIsoComp i.inv g).inv :=
  by
  ext
  simp

open ZeroObject

/-- `image_to_kernel` for `A --0--> B --g--> C`, where `g` is a mono is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance image_to_kernel_epi_of_zero_of_mono [HasKernels V] [HasZeroObject V] [Mono g] :
    Epi
      (imageToKernel (0 : A ⟶ B) g
        (by
          simp )) :=
  epi_of_target_iso_zero _ (kernelSubobjectIso g ≪≫ kernel.ofMono g)

/-- `image_to_kernel` for `A --f--> B --0--> C`, where `g` is an epi is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance image_to_kernel_epi_of_epi_of_zero [HasImages V] [Epi f] :
    Epi
      (imageToKernel f (0 : B ⟶ C)
        (by
          simp )) :=
  by
  simp only [← image_to_kernel_zero_right]
  have := epi_image_of_epi f
  rw [← image_subobject_arrow]
  refine' @epi_comp _ _ _ _ _ _ (epi_comp _ _) _ _

end

section

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

/-- The homology of a pair of morphisms `f : A ⟶ B` and `g : B ⟶ C` satisfying `f ≫ g = 0`
is the cokernel of the `image_to_kernel` morphism for `f` and `g`.
-/
def homology {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g] (w : f ≫ g = 0)
    [HasCokernel (imageToKernel f g w)] : V :=
  cokernel (imageToKernel f g w)

section

variable (w : f ≫ g = 0) [HasCokernel (imageToKernel f g w)]

/-- The morphism from cycles to homology. -/
def homology.π : (kernelSubobject g : V) ⟶ homology f g w :=
  cokernel.π _

@[simp]
theorem homology.condition : imageToKernel f g w ≫ homology.π f g w = 0 :=
  cokernel.condition _

/-- To construct a map out of homology, it suffices to construct a map out of the cycles
which vanishes on boundaries.
-/
def homology.desc {D : V} (k : (kernelSubobject g : V) ⟶ D) (p : imageToKernel f g w ≫ k = 0) : homology f g w ⟶ D :=
  cokernel.desc _ k p

@[simp, reassoc, elementwise]
theorem homology.π_desc {D : V} (k : (kernelSubobject g : V) ⟶ D) (p : imageToKernel f g w ≫ k = 0) :
    homology.π f g w ≫ homology.desc f g w k p = k := by
  simp [← homology.π, ← homology.desc]

/-- To check two morphisms out of `homology f g w` are equal, it suffices to check on cycles. -/
@[ext]
theorem homology.ext {D : V} {k k' : homology f g w ⟶ D} (p : homology.π f g w ≫ k = homology.π f g w ≫ k') : k = k' :=
  by
  ext
  exact p

/-- `homology 0 0 _` is just the middle object. -/
@[simps]
def homologyZeroZero [HasZeroObject V] [HasImage (0 : A ⟶ B)]
    [HasCokernel
        (imageToKernel (0 : A ⟶ B) (0 : B ⟶ C)
          (by
            simp ))] :
    homology (0 : A ⟶ B) (0 : B ⟶ C)
        (by
          simp ) ≅
      B where
  Hom :=
    homology.desc (0 : A ⟶ B) (0 : B ⟶ C)
      (by
        simp )
      (kernelSubobject 0).arrow
      (by
        simp )
  inv := inv (kernelSubobject 0).arrow ≫ homology.π _ _ _

end

section

variable {f g} (w : f ≫ g = 0) {A' B' C' : V} {f' : A' ⟶ B'} [HasImage f'] {g' : B' ⟶ C'} [HasKernel g']
  (w' : f' ≫ g' = 0) (α : Arrow.mk f ⟶ Arrow.mk f') [HasImageMap α] (β : Arrow.mk g ⟶ Arrow.mk g') {A₁ B₁ C₁ : V}
  {f₁ : A₁ ⟶ B₁} [HasImage f₁] {g₁ : B₁ ⟶ C₁} [HasKernel g₁] (w₁ : f₁ ≫ g₁ = 0) {A₂ B₂ C₂ : V} {f₂ : A₂ ⟶ B₂}
  [HasImage f₂] {g₂ : B₂ ⟶ C₂} [HasKernel g₂] (w₂ : f₂ ≫ g₂ = 0) {A₃ B₃ C₃ : V} {f₃ : A₃ ⟶ B₃} [HasImage f₃]
  {g₃ : B₃ ⟶ C₃} [HasKernel g₃] (w₃ : f₃ ≫ g₃ = 0) (α₁ : Arrow.mk f₁ ⟶ Arrow.mk f₂) [HasImageMap α₁]
  (β₁ : Arrow.mk g₁ ⟶ Arrow.mk g₂) (α₂ : Arrow.mk f₂ ⟶ Arrow.mk f₃) [HasImageMap α₂] (β₂ : Arrow.mk g₂ ⟶ Arrow.mk g₃)

/-- Given compatible commutative squares between
a pair `f g` and a pair `f' g'` satisfying `f ≫ g = 0` and `f' ≫ g' = 0`,
the `image_to_kernel` morphisms intertwine the induced map on kernels and the induced map on images.
-/
@[reassoc]
theorem image_subobject_map_comp_image_to_kernel (p : α.right = β.left) :
    imageToKernel f g w ≫ kernelSubobjectMap β = imageSubobjectMap α ≫ imageToKernel f' g' w' := by
  ext
  simp [← p]

variable [HasCokernel (imageToKernel f g w)] [HasCokernel (imageToKernel f' g' w')]

variable [HasCokernel (imageToKernel f₁ g₁ w₁)]

variable [HasCokernel (imageToKernel f₂ g₂ w₂)]

variable [HasCokernel (imageToKernel f₃ g₃ w₃)]

/-- Given compatible commutative squares between
a pair `f g` and a pair `f' g'` satisfying `f ≫ g = 0` and `f' ≫ g' = 0`,
we get a morphism on homology.
-/
def homology.map (p : α.right = β.left) : homology f g w ⟶ homology f' g' w' :=
  cokernel.desc _ (kernelSubobjectMap β ≫ cokernel.π _)
    (by
      rw [image_subobject_map_comp_image_to_kernel_assoc w w' α β p]
      simp only [← cokernel.condition, ← comp_zero])

@[simp, reassoc, elementwise]
theorem homology.π_map (p : α.right = β.left) :
    homology.π f g w ≫ homology.map w w' α β p = kernelSubobjectMap β ≫ homology.π f' g' w' := by
  simp only [← homology.π, ← homology.map, ← cokernel.π_desc]

@[simp, reassoc, elementwise]
theorem homology.map_desc (p : α.right = β.left) {D : V} (k : (kernelSubobject g' : V) ⟶ D)
    (z : imageToKernel f' g' w' ≫ k = 0) :
    homology.map w w' α β p ≫ homology.desc f' g' w' k z =
      homology.desc f g w (kernelSubobjectMap β ≫ k)
        (by
          simp only [← image_subobject_map_comp_image_to_kernel_assoc w w' α β p, ← z, ← comp_zero]) :=
  by
  ext <;> simp only [← homology.π_desc, ← homology.π_map_assoc]

@[simp]
theorem homology.map_id : homology.map w w (𝟙 _) (𝟙 _) rfl = 𝟙 _ := by
  ext <;> simp only [← homology.π_map, ← kernel_subobject_map_id, ← category.id_comp, ← category.comp_id]

/-- Auxiliary lemma for homology computations. -/
theorem homology.comp_right_eq_comp_left {V : Type _} [Category V] {A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : V} {f₁ : A₁ ⟶ B₁}
    {g₁ : B₁ ⟶ C₁} {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} {f₃ : A₃ ⟶ B₃} {g₃ : B₃ ⟶ C₃} {α₁ : Arrow.mk f₁ ⟶ Arrow.mk f₂}
    {β₁ : Arrow.mk g₁ ⟶ Arrow.mk g₂} {α₂ : Arrow.mk f₂ ⟶ Arrow.mk f₃} {β₂ : Arrow.mk g₂ ⟶ Arrow.mk g₃}
    (p₁ : α₁.right = β₁.left) (p₂ : α₂.right = β₂.left) : (α₁ ≫ α₂).right = (β₁ ≫ β₂).left := by
  simp only [← comma.comp_left, ← comma.comp_right, ← p₁, ← p₂]

@[reassoc]
theorem homology.map_comp (p₁ : α₁.right = β₁.left) (p₂ : α₂.right = β₂.left) :
    homology.map w₁ w₂ α₁ β₁ p₁ ≫ homology.map w₂ w₃ α₂ β₂ p₂ =
      homology.map w₁ w₃ (α₁ ≫ α₂) (β₁ ≫ β₂) (homology.comp_right_eq_comp_left p₁ p₂) :=
  by
  ext <;> simp only [← kernel_subobject_map_comp, ← homology.π_map_assoc, ← homology.π_map, ← category.assoc]

/-- An isomorphism between two three-term complexes induces an isomorphism on homology. -/
def homology.mapIso (α : Arrow.mk f₁ ≅ Arrow.mk f₂) (β : Arrow.mk g₁ ≅ Arrow.mk g₂) (p : α.Hom.right = β.Hom.left) :
    homology f₁ g₁ w₁ ≅ homology f₂ g₂ w₂ where
  Hom := homology.map w₁ w₂ α.Hom β.Hom p
  inv :=
    homology.map w₂ w₁ α.inv β.inv
      (by
        rw [← cancel_mono α.hom.right, ← comma.comp_right, α.inv_hom_id, comma.id_right, p, ← comma.comp_left,
          β.inv_hom_id, comma.id_left]
        rfl)
  hom_inv_id' := by
    rw [homology.map_comp]
    convert homology.map_id _ <;> rw [iso.hom_inv_id]
  inv_hom_id' := by
    rw [homology.map_comp]
    convert homology.map_id _ <;> rw [iso.inv_hom_id]

end

end

section

variable {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) {f' : A ⟶ B} {g' : B ⟶ C} (w' : f' ≫ g' = 0) [HasKernels V]
  [HasCokernels V] [HasImages V] [HasImageMaps V]

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Custom tactic to golf and speedup boring proofs in `homology.congr`. -/
private unsafe def aux_tac : tactic Unit :=
  sorry

/-- `homology f g w ≅ homology f' g' w'` if `f = f'` and `g = g'`.
(Note the objects are not changing here.)
-/
@[simps]
def homology.congr (pf : f = f') (pg : g = g') : homology f g w ≅ homology f' g' w' where
  Hom :=
    homology.map w w'
      ⟨𝟙 _, 𝟙 _, by
        run_tac
          aux_tac⟩
      ⟨𝟙 _, 𝟙 _, by
        run_tac
          aux_tac⟩
      rfl
  inv :=
    homology.map w' w
      ⟨𝟙 _, 𝟙 _, by
        run_tac
          aux_tac⟩
      ⟨𝟙 _, 𝟙 _, by
        run_tac
          aux_tac⟩
      rfl
  hom_inv_id' := by
    cases pf
    cases pg
    rw [homology.map_comp, ← homology.map_id]
    congr 1 <;> exact category.comp_id _
  inv_hom_id' := by
    cases pf
    cases pg
    rw [homology.map_comp, ← homology.map_id]
    congr 1 <;> exact category.comp_id _

end

/-!
We provide a variant `image_to_kernel' : image f ⟶ kernel g`,
and use this to give alternative formulas for `homology f g w`.
-/


section imageToKernel'

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) [HasKernels V] [HasImages V]

/-- While `image_to_kernel f g w` provides a morphism
`image_subobject f ⟶ kernel_subobject g`
in terms of the subobject API,
this variant provides a morphism
`image f ⟶ kernel g`,
which is sometimes more convenient.
-/
def imageToKernel' (w : f ≫ g = 0) : image f ⟶ kernel g :=
  kernel.lift g (image.ι f)
    (by
      ext
      simpa using w)

@[simp]
theorem image_subobject_iso_image_to_kernel' (w : f ≫ g = 0) :
    (imageSubobjectIso f).Hom ≫ imageToKernel' f g w = imageToKernel f g w ≫ (kernelSubobjectIso g).Hom := by
  ext
  simp [← imageToKernel']

@[simp]
theorem image_to_kernel'_kernel_subobject_iso (w : f ≫ g = 0) :
    imageToKernel' f g w ≫ (kernelSubobjectIso g).inv = (imageSubobjectIso f).inv ≫ imageToKernel f g w := by
  ext
  simp [← imageToKernel']

variable [HasCokernels V]

/-- `homology f g w` can be computed as the cokernel of `image_to_kernel' f g w`.
-/
def homologyIsoCokernelImageToKernel' (w : f ≫ g = 0) : homology f g w ≅ cokernel (imageToKernel' f g w) where
  Hom :=
    cokernel.map _ _ (imageSubobjectIso f).Hom (kernelSubobjectIso g).Hom
      (by
        simp only [← image_subobject_iso_image_to_kernel'])
  inv :=
    cokernel.map _ _ (imageSubobjectIso f).inv (kernelSubobjectIso g).inv
      (by
        simp only [← image_to_kernel'_kernel_subobject_iso])
  hom_inv_id' := by
    apply coequalizer.hom_ext
    simp only [← iso.hom_inv_id_assoc, ← cokernel.π_desc, ← cokernel.π_desc_assoc, ← category.assoc, ←
      coequalizer_as_cokernel]
    exact (category.comp_id _).symm
  inv_hom_id' := by
    ext1
    simp only [← iso.inv_hom_id_assoc, ← cokernel.π_desc, ← category.comp_id, ← cokernel.π_desc_assoc, ← category.assoc]

variable [HasEqualizers V]

/-- `homology f g w` can be computed as the cokernel of `kernel.lift g f w`.
-/
def homologyIsoCokernelLift (w : f ≫ g = 0) : homology f g w ≅ cokernel (kernel.lift g f w) := by
  refine' homologyIsoCokernelImageToKernel' f g w ≪≫ _
  have p : factor_thru_image f ≫ imageToKernel' f g w = kernel.lift g f w := by
    ext
    simp [← imageToKernel']
  exact (cokernel_epi_comp _ _).symm ≪≫ cokernel_iso_of_eq p

end imageToKernel'

