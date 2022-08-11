/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.StrongEpi
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Definitions and basic properties of regular monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.

We give the constructions
* `split_mono → regular_mono` and
* `regular_mono → mono`
as well as the dual constructions for regular epimorphisms. Additionally, we give the construction
* `regular_epi ⟶ strong_epi`.

We also define classes `regular_mono_category` and `regular_epi_category` for categories in which
every monomorphism or epimorphism is regular, and deduce that these categories are
`strong_mono_category`s resp. `strong_epi_category`s.

-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

variable {X Y : C}

/-- A regular monomorphism is a morphism which is the equalizer of some parallel pair. -/
class RegularMono (f : X ⟶ Y) where
  z : C
  (left right : Y ⟶ Z)
  w : f ≫ left = f ≫ right
  IsLimit : IsLimit (Fork.ofι f w)

attribute [reassoc] regular_mono.w

/-- Every regular monomorphism is a monomorphism. -/
instance (priority := 100) RegularMono.mono (f : X ⟶ Y) [RegularMono f] : Mono f :=
  mono_of_is_limit_fork RegularMono.isLimit

instance equalizerRegular (g h : X ⟶ Y) [HasLimit (parallelPair g h)] : RegularMono (equalizer.ι g h) where
  z := Y
  left := g
  right := h
  w := equalizer.condition g h
  IsLimit :=
    Fork.IsLimit.mk _ (fun s => limit.lift _ s)
      (by
        simp )
      fun s m w => by
      ext1
      simp [w]

/-- Every split monomorphism is a regular monomorphism. -/
instance (priority := 100) RegularMono.ofSplitMono (f : X ⟶ Y) [SplitMono f] : RegularMono f where
  z := Y
  left := 𝟙 Y
  right := retraction f ≫ f
  w := by
    tidy
  IsLimit := splitMonoEqualizes f

/-- If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `regular_mono.left` and
    `regular_mono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def RegularMono.lift' {W : C} (f : X ⟶ Y) [RegularMono f] (k : W ⟶ Y)
    (h : k ≫ (RegularMono.left : Y ⟶ @RegularMono.z _ _ _ _ f _) = k ≫ regular_mono.right) :
    { l : W ⟶ X // l ≫ f = k } :=
  Fork.IsLimit.lift' RegularMono.isLimit _ h

/-- The second leg of a pullback cone is a regular monomorphism if the right component is too.

See also `pullback.snd_of_mono` for the basic monomorphism version, and
`regular_of_is_pullback_fst_of_regular` for the flipped version.
-/
def regularOfIsPullbackSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [hr : RegularMono h]
    (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) : RegularMono g where
  z := hr.z
  left := k ≫ hr.left
  right := k ≫ hr.right
  w := by
    rw [← reassoc_of comm, ← reassoc_of comm, hr.w]
  IsLimit := by
    apply fork.is_limit.mk' _ _
    intro s
    have l₁ : (fork.ι s ≫ k) ≫ regular_mono.left = (fork.ι s ≫ k) ≫ regular_mono.right
    rw [category.assoc, s.condition, category.assoc]
    obtain ⟨l, hl⟩ := fork.is_limit.lift' hr.is_limit _ l₁
    obtain ⟨p, hp₁, hp₂⟩ := pullback_cone.is_limit.lift' t _ _ hl
    refine' ⟨p, hp₂, _⟩
    intro m w
    have z : m ≫ g = p ≫ g := w.trans hp₂.symm
    apply t.hom_ext
    apply (pullback_cone.mk f g comm).equalizer_ext
    · erw [← cancel_mono h, category.assoc, category.assoc, comm, reassoc_of z]
      
    · exact z
      

/-- The first leg of a pullback cone is a regular monomorphism if the left component is too.

See also `pullback.fst_of_mono` for the basic monomorphism version, and
`regular_of_is_pullback_snd_of_regular` for the flipped version.
-/
def regularOfIsPullbackFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [hr : RegularMono k]
    (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) : RegularMono f :=
  regularOfIsPullbackSndOfRegular comm.symm (PullbackCone.flipIsLimit t)

instance (priority := 100) strong_mono_of_regular_mono (f : X ⟶ Y) [RegularMono f] : StrongMono f where
  mono := by
    infer_instance
  HasLift := by
    intros
    have : v ≫ (regular_mono.left : Y ⟶ regular_mono.Z f) = v ≫ regular_mono.right := by
      apply (cancel_epi z).1
      simp only [← regular_mono.w, reassoc_of h]
    obtain ⟨t, ht⟩ := regular_mono.lift' _ _ this
    refine' arrow.has_lift.mk ⟨t, (cancel_mono f).1 _, ht⟩
    simp only [← arrow.mk_hom, ← arrow.hom_mk'_left, ← category.assoc, ← ht, ← h]

/-- A regular monomorphism is an isomorphism if it is an epimorphism. -/
theorem is_iso_of_regular_mono_of_epi (f : X ⟶ Y) [RegularMono f] [e : Epi f] : IsIso f :=
  is_iso_of_epi_of_strong_mono _

section

variable (C)

/-- A regular mono category is a category in which every monomorphism is regular. -/
class RegularMonoCategory where
  regularMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], RegularMono f

end

/-- In a category in which every monomorphism is regular, we can express every monomorphism as
    an equalizer. This is not an instance because it would create an instance loop. -/
def regularMonoOfMono [RegularMonoCategory C] (f : X ⟶ Y) [Mono f] : RegularMono f :=
  RegularMonoCategory.regularMonoOfMono _

instance (priority := 100) regularMonoCategoryOfSplitMonoCategory [SplitMonoCategory C] :
    RegularMonoCategory C where regularMonoOfMono := fun _ _ f _ => by
    have := split_mono_of_mono f
    infer_instance

instance (priority := 100) strong_mono_category_of_regular_mono_category [RegularMonoCategory C] :
    StrongMonoCategory C where strong_mono_of_mono := fun _ _ f _ => by
    have := regular_mono_of_mono f
    infer_instance

/-- A regular epimorphism is a morphism which is the coequalizer of some parallel pair. -/
class RegularEpi (f : X ⟶ Y) where
  w : C
  (left right : W ⟶ X)
  w : left ≫ f = right ≫ f
  IsColimit : IsColimit (Cofork.ofπ f w)

attribute [reassoc] regular_epi.w

/-- Every regular epimorphism is an epimorphism. -/
instance (priority := 100) RegularEpi.epi (f : X ⟶ Y) [RegularEpi f] : Epi f :=
  epi_of_is_colimit_cofork RegularEpi.isColimit

instance coequalizerRegular (g h : X ⟶ Y) [HasColimit (parallelPair g h)] : RegularEpi (coequalizer.π g h) where
  w := X
  left := g
  right := h
  w := coequalizer.condition g h
  IsColimit :=
    Cofork.IsColimit.mk _ (fun s => colimit.desc _ s)
      (by
        simp )
      fun s m w => by
      ext1
      simp [w]

/-- Every split epimorphism is a regular epimorphism. -/
instance (priority := 100) RegularEpi.ofSplitEpi (f : X ⟶ Y) [SplitEpi f] : RegularEpi f where
  w := X
  left := 𝟙 X
  right := f ≫ section_ f
  w := by
    tidy
  IsColimit := splitEpiCoequalizes f

/-- If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `regular_epi.left` and
    `regular_epi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def RegularEpi.desc' {W : C} (f : X ⟶ Y) [RegularEpi f] (k : X ⟶ W)
    (h : (RegularEpi.left : RegularEpi.w f ⟶ X) ≫ k = regular_epi.right ≫ k) : { l : Y ⟶ W // f ≫ l = k } :=
  Cofork.IsColimit.desc' RegularEpi.isColimit _ h

/-- The second leg of a pushout cocone is a regular epimorphism if the right component is too.

See also `pushout.snd_of_epi` for the basic epimorphism version, and
`regular_of_is_pushout_fst_of_regular` for the flipped version.
-/
def regularOfIsPushoutSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [gr : RegularEpi g]
    (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) : RegularEpi h where
  w := gr.w
  left := gr.left ≫ f
  right := gr.right ≫ f
  w := by
    rw [category.assoc, category.assoc, comm, reassoc_of gr.w]
  IsColimit := by
    apply cofork.is_colimit.mk' _ _
    intro s
    have l₁ : gr.left ≫ f ≫ s.π = gr.right ≫ f ≫ s.π
    rw [← category.assoc, ← category.assoc, s.condition]
    obtain ⟨l, hl⟩ := cofork.is_colimit.desc' gr.is_colimit (f ≫ cofork.π s) l₁
    obtain ⟨p, hp₁, hp₂⟩ := pushout_cocone.is_colimit.desc' t _ _ hl.symm
    refine' ⟨p, hp₁, _⟩
    intro m w
    have z := w.trans hp₁.symm
    apply t.hom_ext
    apply (pushout_cocone.mk _ _ comm).coequalizer_ext
    · exact z
      
    · erw [← cancel_epi g, ← reassoc_of comm, ← reassoc_of comm, z]
      rfl
      

/-- The first leg of a pushout cocone is a regular epimorphism if the left component is too.

See also `pushout.fst_of_epi` for the basic epimorphism version, and
`regular_of_is_pushout_snd_of_regular` for the flipped version.
-/
def regularOfIsPushoutFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [fr : RegularEpi f]
    (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) : RegularEpi k :=
  regularOfIsPushoutSndOfRegular comm.symm (PushoutCocone.flipIsColimit t)

instance (priority := 100) strong_epi_of_regular_epi (f : X ⟶ Y) [RegularEpi f] : StrongEpi f where
  Epi := by
    infer_instance
  HasLift := by
    intros
    have : (regular_epi.left : regular_epi.W f ⟶ X) ≫ u = regular_epi.right ≫ u := by
      apply (cancel_mono z).1
      simp only [← category.assoc, ← h, ← regular_epi.w_assoc]
    obtain ⟨t, ht⟩ := regular_epi.desc' f u this
    exact
      arrow.has_lift.mk
        ⟨t, ht,
          (cancel_epi f).1
            (by
              simp only [category.assoc, ← ht, h, ← arrow.mk_hom, ← arrow.hom_mk'_right])⟩

/-- A regular epimorphism is an isomorphism if it is a monomorphism. -/
theorem is_iso_of_regular_epi_of_mono (f : X ⟶ Y) [RegularEpi f] [m : Mono f] : IsIso f :=
  is_iso_of_mono_of_strong_epi _

section

variable (C)

/-- A regular epi category is a category in which every epimorphism is regular. -/
class RegularEpiCategory where
  regularEpiOfEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], RegularEpi f

end

/-- In a category in which every epimorphism is regular, we can express every epimorphism as
    a coequalizer. This is not an instance because it would create an instance loop. -/
def regularEpiOfEpi [RegularEpiCategory C] (f : X ⟶ Y) [Epi f] : RegularEpi f :=
  RegularEpiCategory.regularEpiOfEpi _

instance (priority := 100) regularEpiCategoryOfSplitEpiCategory [SplitEpiCategory C] :
    RegularEpiCategory C where regularEpiOfEpi := fun _ _ f _ => by
    have := split_epi_of_epi f
    infer_instance

instance (priority := 100) strong_epi_category_of_regular_epi_category [RegularEpiCategory C] :
    StrongEpiCategory C where strong_epi_of_epi := fun _ _ f _ => by
    have := regular_epi_of_epi f
    infer_instance

end CategoryTheory

