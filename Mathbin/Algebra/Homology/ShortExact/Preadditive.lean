/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang
-/
import Mathbin.Algebra.Homology.Exact
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Short exact sequences, and splittings.

`short_exact f g` is the proposition that `0 ⟶ A -f⟶ B -g⟶ C ⟶ 0` is an exact sequence.

We define when a short exact sequence is left-split, right-split, and split.

## See also
In `algebra.homology.short_exact.abelian` we show that in an abelian category
a left-split short exact sequences admits a splitting.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {𝒜 : Type _} [Category 𝒜]

namespace CategoryTheory

variable {A B C A' B' C' : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')

section HasZeroMorphisms

variable [HasZeroMorphisms 𝒜] [HasKernels 𝒜] [HasImages 𝒜]

/-- If `f : A ⟶ B` and `g : B ⟶ C` then `short_exact f g` is the proposition saying
  the resulting diagram `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is an exact sequence. -/
structure ShortExact : Prop where
  [mono : Mono f]
  [Epi : Epi g]
  exact : Exact f g

/-- An exact sequence `A -f⟶ B -g⟶ C` is *left split*
if there exists a morphism `φ : B ⟶ A` such that `f ≫ φ = 𝟙 A` and `g` is epi.

Such a sequence is automatically short exact (i.e., `f` is mono). -/
structure LeftSplit : Prop where
  LeftSplit : ∃ φ : B ⟶ A, f ≫ φ = 𝟙 A
  [Epi : Epi g]
  exact : Exact f g

theorem LeftSplit.short_exact {f : A ⟶ B} {g : B ⟶ C} (h : LeftSplit f g) : ShortExact f g :=
  { mono := by
      obtain ⟨φ, hφ⟩ := h.left_split
      have : mono (f ≫ φ) := by
        rw [hφ]
        infer_instance
      exact mono_of_mono f φ,
    Epi := h.Epi, exact := h.exact }

/-- An exact sequence `A -f⟶ B -g⟶ C` is *right split*
if there exists a morphism `φ : C ⟶ B` such that `f ≫ φ = 𝟙 A` and `f` is mono.

Such a sequence is automatically short exact (i.e., `g` is epi). -/
structure RightSplit : Prop where
  RightSplit : ∃ χ : C ⟶ B, χ ≫ g = 𝟙 C
  [mono : Mono f]
  exact : Exact f g

theorem RightSplit.short_exact {f : A ⟶ B} {g : B ⟶ C} (h : RightSplit f g) : ShortExact f g :=
  { Epi := by
      obtain ⟨χ, hχ⟩ := h.right_split
      have : epi (χ ≫ g) := by
        rw [hχ]
        infer_instance
      exact epi_of_epi χ g,
    mono := h.mono, exact := h.exact }

end HasZeroMorphisms

section Preadditive

variable [Preadditive 𝒜]

/-- An exact sequence `A -f⟶ B -g⟶ C` is *split* if there exist
`φ : B ⟶ A` and `χ : C ⟶ B` such that:
* `f ≫ φ = 𝟙 A`
* `χ ≫ g = 𝟙 C`
* `f ≫ g = 0`
* `χ ≫ φ = 0`
* `φ ≫ f + g ≫ χ = 𝟙 B`

Such a sequence is automatically short exact (i.e., `f` is mono and `g` is epi). -/
structure Split : Prop where
  split : ∃ (φ : B ⟶ A)(χ : C ⟶ B), f ≫ φ = 𝟙 A ∧ χ ≫ g = 𝟙 C ∧ f ≫ g = 0 ∧ χ ≫ φ = 0 ∧ φ ≫ f + g ≫ χ = 𝟙 B

variable [HasKernels 𝒜] [HasImages 𝒜]

theorem exact_of_split {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C} {χ : C ⟶ B} {φ : B ⟶ A} (hfg : f ≫ g = 0)
    (H : φ ≫ f + g ≫ χ = 𝟙 B) : Exact f g :=
  { w := hfg,
    Epi := by
      let ψ : (kernel_subobject g : 𝒜) ⟶ image_subobject f := subobject.arrow _ ≫ φ ≫ factor_thru_image_subobject f
      suffices ψ ≫ imageToKernel f g hfg = 𝟙 _ by
        convert epi_of_epi ψ _
        rw [this]
        infer_instance
      rw [← cancel_mono (subobject.arrow _)]
      swap
      · infer_instance
        
      simp only [← image_to_kernel_arrow, ← image_subobject_arrow_comp, ← category.id_comp, ← category.assoc]
      calc (kernel_subobject g).arrow ≫ φ ≫ f = (kernel_subobject g).arrow ≫ 𝟙 B := _ _ = (kernel_subobject g).arrow :=
          category.comp_id _
      rw [← H, preadditive.comp_add]
      simp only [← add_zeroₓ, ← zero_comp, ← kernel_subobject_arrow_comp_assoc] }

section

variable {f g}

theorem Split.exact (h : Split f g) : Exact f g := by
  obtain ⟨φ, χ, -, -, h1, -, h2⟩ := h
  exact exact_of_split h1 h2

theorem Split.left_split (h : Split f g) : LeftSplit f g :=
  { LeftSplit := by
      obtain ⟨φ, χ, h1, -⟩ := h
      exact ⟨φ, h1⟩,
    Epi := by
      obtain ⟨φ, χ, -, h2, -⟩ := h
      have : epi (χ ≫ g) := by
        rw [h2]
        infer_instance
      exact epi_of_epi χ g,
    exact := h.exact }

theorem Split.right_split (h : Split f g) : RightSplit f g :=
  { RightSplit := by
      obtain ⟨φ, χ, -, h1, -⟩ := h
      exact ⟨χ, h1⟩,
    mono := by
      obtain ⟨φ, χ, h1, -⟩ := h
      have : mono (f ≫ φ) := by
        rw [h1]
        infer_instance
      exact mono_of_mono f φ,
    exact := h.exact }

theorem Split.short_exact (h : Split f g) : ShortExact f g :=
  h.LeftSplit.ShortExact

end

theorem Split.map {𝒜 ℬ : Type _} [Category 𝒜] [Preadditive 𝒜] [Category ℬ] [Preadditive ℬ] (F : 𝒜 ⥤ ℬ)
    [Functor.Additive F] {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C} (h : Split f g) : Split (F.map f) (F.map g) := by
  obtain ⟨φ, χ, h1, h2, h3, h4, h5⟩ := h
  refine' ⟨⟨F.map φ, F.map χ, _⟩⟩
  simp only [F.map_comp, F.map_id, F.map_add, ← F.map_zero, *, ← eq_self_iff_true, ← and_trueₓ]

/-- The sequence `A ⟶ A ⊞ B ⟶ B` is exact. -/
theorem exact_inl_snd [HasBinaryBiproducts 𝒜] (A B : 𝒜) : Exact (biprod.inl : A ⟶ A ⊞ B) biprod.snd :=
  exact_of_split biprod.inl_snd biprod.total

/-- The sequence `B ⟶ A ⊞ B ⟶ A` is exact. -/
theorem exact_inr_fst [HasBinaryBiproducts 𝒜] (A B : 𝒜) : Exact (biprod.inr : B ⟶ A ⊞ B) biprod.fst :=
  exact_of_split biprod.inr_fst ((add_commₓ _ _).trans biprod.total)

end Preadditive

/-- A *splitting* of a sequence `A -f⟶ B -g⟶ C` is an isomorphism
to the short exact sequence `0 ⟶ A ⟶ A ⊞ C ⟶ C ⟶ 0` such that
the vertical maps on the left and the right are the identity. -/
@[nolint has_inhabited_instance]
structure Splitting [HasZeroMorphisms 𝒜] [HasBinaryBiproducts 𝒜] where
  Iso : B ≅ A ⊞ C
  comp_iso_eq_inl : f ≫ iso.Hom = biprod.inl
  iso_comp_snd_eq : iso.Hom ≫ biprod.snd = g

variable {f g}

namespace Splitting

section HasZeroMorphisms

variable [HasZeroMorphisms 𝒜] [HasBinaryBiproducts 𝒜]

attribute [simp, reassoc] comp_iso_eq_inl iso_comp_snd_eq

variable (h : Splitting f g)

@[simp, reassoc]
theorem inl_comp_iso_eq : biprod.inl ≫ h.Iso.inv = f := by
  rw [iso.comp_inv_eq, h.comp_iso_eq_inl]

@[simp, reassoc]
theorem iso_comp_eq_snd : h.Iso.inv ≫ g = biprod.snd := by
  rw [iso.inv_comp_eq, h.iso_comp_snd_eq]

/-- If `h` is a splitting of `A -f⟶ B -g⟶ C`,
then `h.section : C ⟶ B` is the morphism satisfying `h.section ≫ g = 𝟙 C`. -/
def _root_.category_theory.splitting.section : C ⟶ B :=
  biprod.inr ≫ h.Iso.inv

/-- If `h` is a splitting of `A -f⟶ B -g⟶ C`,
then `h.retraction : B ⟶ A` is the morphism satisfying `f ≫ h.retraction = 𝟙 A`. -/
def retraction : B ⟶ A :=
  h.Iso.Hom ≫ biprod.fst

@[simp, reassoc]
theorem section_π : h.section ≫ g = 𝟙 C := by
  delta' splitting.section
  simp

@[simp, reassoc]
theorem ι_retraction : f ≫ h.retraction = 𝟙 A := by
  delta' retraction
  simp

@[simp, reassoc]
theorem section_retraction : h.section ≫ h.retraction = 0 := by
  delta' splitting.section retraction
  simp

/-- The retraction in a splitting is a split mono. -/
protected def splitMono : SplitMono f :=
  ⟨h.retraction, by
    simp ⟩

/-- The section in a splitting is a split epi. -/
protected def splitEpi : SplitEpi g :=
  ⟨h.section, by
    simp ⟩

@[simp, reassoc]
theorem inr_iso_inv : biprod.inr ≫ h.Iso.inv = h.section :=
  rfl

@[simp, reassoc]
theorem iso_hom_fst : h.Iso.Hom ≫ biprod.fst = h.retraction :=
  rfl

/-- A short exact sequence of the form `X -f⟶ Y -0⟶ Z` where `f` is an iso and `Z` is zero
has a splitting. -/
def splittingOfIsIsoZero {X Y Z : 𝒜} (f : X ⟶ Y) [IsIso f] (hZ : IsZero Z) : Splitting f (0 : Y ⟶ Z) :=
  ⟨(asIso f).symm ≪≫ isoBiprodZero hZ, by
    simp [← hZ.eq_of_tgt _ 0], by
    simp ⟩

include h

protected theorem mono : Mono f := by
  apply mono_of_mono _ h.retraction
  rw [h.ι_retraction]
  infer_instance

protected theorem epi : Epi g := by
  apply epi_of_epi h.section with { instances := false }
  rw [h.section_π]
  infer_instance

instance : Mono h.section := by
  delta' splitting.section
  infer_instance

instance : Epi h.retraction := by
  delta' retraction
  apply epi_comp

end HasZeroMorphisms

section Preadditive

variable [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]

variable (h : Splitting f g)

theorem split_add : h.retraction ≫ f + g ≫ h.section = 𝟙 _ := by
  delta' splitting.section retraction
  rw [← cancel_mono h.iso.hom, ← cancel_epi h.iso.inv]
  simp only [← category.comp_id, ← category.id_comp, ← category.assoc, ← iso.inv_hom_id_assoc, ← iso.inv_hom_id, ←
    limits.biprod.total, ← preadditive.comp_add, ← preadditive.add_comp, ← splitting.comp_iso_eq_inl, ←
    splitting.iso_comp_eq_snd_assoc]

@[reassoc]
theorem retraction_ι_eq_id_sub : h.retraction ≫ f = 𝟙 _ - g ≫ h.section :=
  eq_sub_iff_add_eq.mpr h.split_add

@[reassoc]
theorem π_section_eq_id_sub : g ≫ h.section = 𝟙 _ - h.retraction ≫ f :=
  eq_sub_iff_add_eq.mpr ((add_commₓ _ _).trans h.split_add)

theorem splittings_comm (h h' : Splitting f g) : h'.section ≫ h.retraction = -(h.section ≫ h'.retraction) := by
  have := h.mono
  rw [← cancel_mono f]
  simp [← retraction_ι_eq_id_sub]

include h

theorem split : Split f g := by
  let φ := h.iso.hom ≫ biprod.fst
  let χ := biprod.inr ≫ h.iso.inv
  refine' ⟨⟨h.retraction, h.section, h.ι_retraction, h.section_π, _, h.section_retraction, h.split_add⟩⟩
  rw [← h.inl_comp_iso_eq, category.assoc, h.iso_comp_eq_snd, biprod.inl_snd]

@[reassoc]
theorem comp_eq_zero : f ≫ g = 0 :=
  h.split.1.some_spec.some_spec.2.2.1

variable [HasKernels 𝒜] [HasImages 𝒜] [HasZeroObject 𝒜] [HasCokernels 𝒜]

protected theorem exact : Exact f g := by
  rw [exact_iff_exact_of_iso f g (biprod.inl : A ⟶ A ⊞ C) (biprod.snd : A ⊞ C ⟶ C) _ _ _]
  · exact exact_inl_snd _ _
    
  · refine' arrow.iso_mk (iso.refl _) h.iso _
    simp only [← iso.refl_hom, ← arrow.mk_hom, ← category.id_comp, ← comp_iso_eq_inl]
    
  · refine' arrow.iso_mk h.iso (iso.refl _) _
    dsimp'
    simp
    
  · rfl
    

protected theorem short_exact : ShortExact f g :=
  { mono := h.mono, Epi := h.Epi, exact := h.exact }

end Preadditive

end Splitting

end CategoryTheory

