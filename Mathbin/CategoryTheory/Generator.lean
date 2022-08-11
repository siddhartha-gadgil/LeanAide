/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Balanced
import Mathbin.CategoryTheory.Limits.Opposites
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathbin.Data.Set.Opposite

/-!
# Separating and detecting sets

There are several non-equivalent notions of a generator of a category. Here, we consider two of
them:

* We say that `𝒢` is a separating set if the functors `C(G, -)` for `G ∈ 𝒢` are collectively
    faithful, i.e., if `h ≫ f = h ≫ g` for all `h` with domain in `𝒢` implies `f = g`.
* We say that `𝒢` is a detecting set if the functors `C(G, -)` collectively reflect isomorphisms,
    i.e., if any `h` with domain in `𝒢` uniquely factors through `f`, then `f` is an isomorphism.

There are, of course, also the dual notions of coseparating and codetecting sets.

## Main results

We
* define predicates `is_separating`, `is_coseparating`, `is_detecting` and `is_codetecting` on
  sets of objects;
* show that separating and coseparating are dual notions;
* show that detecting and codetecting are dual notions;
* show that if `C` has equalizers, then detecting implies separating;
* show that if `C` has coequalizers, then codetecting implies separating;
* show that if `C` is balanced, then separating implies detecting and coseparating implies
  codetecting;
* show that `∅` is separating if and only if `∅` is coseparating if and only if `C` is thin;
* show that `∅` is detecting if and only if `∅` is codetecting if and only if `C` is a groupoid;
* define predicates `is_separator`, `is_coseparator`, `is_detector` and `is_codetector` as the
  singleton counterparts to the definitions for sets above and restate the above results in this
  situation;
* show that `G` is a separator if and only if `coyoneda.obj (op G)` is faithful (and the dual);
* show that `G` is a detector if and only if `coyoneda.obj (op G)` reflects isomorphisms (and the
  dual).

## Future work

* We currently don't have any examples yet.
* We will want typeclasses `has_separator C` and similar.
* To state the Special Adjoint Functor Theorem, we will need to be able to talk about *small*
  separating sets.

-/


universe w v u

open CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- We say that `𝒢` is a separating set if the functors `C(G, -)` for `G ∈ 𝒢` are collectively
    faithful, i.e., if `h ≫ f = h ≫ g` for all `h` with domain in `𝒢` implies `f = g`. -/
def IsSeparating (𝒢 : Set C) : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀, ∀ G ∈ 𝒢, ∀ (h : G ⟶ X), h ≫ f = h ≫ g) → f = g

/-- We say that `𝒢` is a coseparating set if the functors `C(-, G)` for `G ∈ 𝒢` are collectively
    faithful, i.e., if `f ≫ h = g ≫ h` for all `h` with codomain in `𝒢` implies `f = g`. -/
def IsCoseparating (𝒢 : Set C) : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀, ∀ G ∈ 𝒢, ∀ (h : Y ⟶ G), f ≫ h = g ≫ h) → f = g

/-- We say that `𝒢` is a detecting set if the functors `C(G, -)` collectively reflect isomorphisms,
    i.e., if any `h` with domain in `𝒢` uniquely factors through `f`, then `f` is an isomorphism. -/
def IsDetecting (𝒢 : Set C) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀, ∀ G ∈ 𝒢, ∀ (h : G ⟶ Y), ∃! h' : G ⟶ X, h' ≫ f = h) → IsIso f

/-- We say that `𝒢` is a codetecting set if the functors `C(-, G)` collectively reflect
    isomorphisms, i.e., if any `h` with codomain in `G` uniquely factors through `f`, then `f` is
    an isomorphism. -/
def IsCodetecting (𝒢 : Set C) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀, ∀ G ∈ 𝒢, ∀ (h : X ⟶ G), ∃! h' : Y ⟶ G, f ≫ h' = h) → IsIso f

section Dual

theorem is_separating_op_iff (𝒢 : Set C) : IsSeparating 𝒢.op ↔ IsCoseparating 𝒢 := by
  refine' ⟨fun h𝒢 X Y f g hfg => _, fun h𝒢 X Y f g hfg => _⟩
  · refine' Quiver.Hom.op_inj (h𝒢 _ _ fun G hG h => Quiver.Hom.unop_inj _)
    simpa only [← unop_comp, ← Quiver.Hom.unop_op] using hfg _ (Set.mem_op.1 hG) _
    
  · refine' Quiver.Hom.unop_inj (h𝒢 _ _ fun G hG h => Quiver.Hom.op_inj _)
    simpa only [← op_comp, ← Quiver.Hom.op_unop] using hfg _ (Set.op_mem_op.2 hG) _
    

theorem is_coseparating_op_iff (𝒢 : Set C) : IsCoseparating 𝒢.op ↔ IsSeparating 𝒢 := by
  refine' ⟨fun h𝒢 X Y f g hfg => _, fun h𝒢 X Y f g hfg => _⟩
  · refine' Quiver.Hom.op_inj (h𝒢 _ _ fun G hG h => Quiver.Hom.unop_inj _)
    simpa only [← unop_comp, ← Quiver.Hom.unop_op] using hfg _ (Set.mem_op.1 hG) _
    
  · refine' Quiver.Hom.unop_inj (h𝒢 _ _ fun G hG h => Quiver.Hom.op_inj _)
    simpa only [← op_comp, ← Quiver.Hom.op_unop] using hfg _ (Set.op_mem_op.2 hG) _
    

theorem is_coseparating_unop_iff (𝒢 : Set Cᵒᵖ) : IsCoseparating 𝒢.unop ↔ IsSeparating 𝒢 := by
  rw [← is_separating_op_iff, Set.unop_op]

theorem is_separating_unop_iff (𝒢 : Set Cᵒᵖ) : IsSeparating 𝒢.unop ↔ IsCoseparating 𝒢 := by
  rw [← is_coseparating_op_iff, Set.unop_op]

theorem is_detecting_op_iff (𝒢 : Set C) : IsDetecting 𝒢.op ↔ IsCodetecting 𝒢 := by
  refine' ⟨fun h𝒢 X Y f hf => _, fun h𝒢 X Y f hf => _⟩
  · refine' (is_iso_op_iff _).1 (h𝒢 _ fun G hG h => _)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) (Set.mem_op.1 hG) h.unop
    exact ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
    
  · refine' (is_iso_unop_iff _).1 (h𝒢 _ fun G hG h => _)
    obtain ⟨t, ht, ht'⟩ := hf (op G) (Set.op_mem_op.2 hG) h.op
    refine' ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ _)⟩
    exact
      Quiver.Hom.unop_inj
        (by
          simpa only using hy)
    

theorem is_codetecting_op_iff (𝒢 : Set C) : IsCodetecting 𝒢.op ↔ IsDetecting 𝒢 := by
  refine' ⟨fun h𝒢 X Y f hf => _, fun h𝒢 X Y f hf => _⟩
  · refine' (is_iso_op_iff _).1 (h𝒢 _ fun G hG h => _)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) (Set.mem_op.1 hG) h.unop
    exact ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
    
  · refine' (is_iso_unop_iff _).1 (h𝒢 _ fun G hG h => _)
    obtain ⟨t, ht, ht'⟩ := hf (op G) (Set.op_mem_op.2 hG) h.op
    refine' ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ _)⟩
    exact
      Quiver.Hom.unop_inj
        (by
          simpa only using hy)
    

theorem is_detecting_unop_iff (𝒢 : Set Cᵒᵖ) : IsDetecting 𝒢.unop ↔ IsCodetecting 𝒢 := by
  rw [← is_codetecting_op_iff, Set.unop_op]

theorem is_codetecting_unop_iff {𝒢 : Set Cᵒᵖ} : IsCodetecting 𝒢.unop ↔ IsDetecting 𝒢 := by
  rw [← is_detecting_op_iff, Set.unop_op]

end Dual

theorem IsDetecting.is_separating [HasEqualizers C] {𝒢 : Set C} (h𝒢 : IsDetecting 𝒢) : IsSeparating 𝒢 :=
  fun X Y f g hfg =>
  have : IsIso (equalizer.ι f g) := h𝒢 _ fun G hG h => equalizer.exists_unique _ (hfg _ hG _)
  eq_of_epi_equalizer

section

attribute [local instance] has_equalizers_opposite

theorem IsCodetecting.is_coseparating [HasCoequalizers C] {𝒢 : Set C} : IsCodetecting 𝒢 → IsCoseparating 𝒢 := by
  simpa only [is_separating_op_iff, is_detecting_op_iff] using is_detecting.is_separating

end

theorem IsSeparating.is_detecting [Balanced C] {𝒢 : Set C} (h𝒢 : IsSeparating 𝒢) : IsDetecting 𝒢 := by
  intro X Y f hf
  refine' (is_iso_iff_mono_and_epi _).2 ⟨⟨fun Z g h hgh => h𝒢 _ _ fun G hG i => _⟩, ⟨fun Z g h hgh => _⟩⟩
  · obtain ⟨t, -, ht⟩ := hf G hG (i ≫ g ≫ f)
    rw [ht (i ≫ g) (category.assoc _ _ _), ht (i ≫ h) (hgh.symm ▸ category.assoc _ _ _)]
    
  · refine' h𝒢 _ _ fun G hG i => _
    obtain ⟨t, rfl, -⟩ := hf G hG i
    rw [category.assoc, hgh, category.assoc]
    

section

attribute [local instance] balanced_opposite

theorem IsCoseparating.is_codetecting [Balanced C] {𝒢 : Set C} : IsCoseparating 𝒢 → IsCodetecting 𝒢 := by
  simpa only [is_detecting_op_iff, is_separating_op_iff] using is_separating.is_detecting

end

theorem is_detecting_iff_is_separating [HasEqualizers C] [Balanced C] (𝒢 : Set C) : IsDetecting 𝒢 ↔ IsSeparating 𝒢 :=
  ⟨IsDetecting.is_separating, IsSeparating.is_detecting⟩

theorem is_codetecting_iff_is_coseparating [HasCoequalizers C] [Balanced C] {𝒢 : Set C} :
    IsCodetecting 𝒢 ↔ IsCoseparating 𝒢 :=
  ⟨IsCodetecting.is_coseparating, IsCoseparating.is_codetecting⟩

section Mono

theorem IsSeparating.mono {𝒢 : Set C} (h𝒢 : IsSeparating 𝒢) {ℋ : Set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) : IsSeparating ℋ :=
  fun X Y f g hfg => (h𝒢 _ _) fun G hG h => hfg _ (h𝒢ℋ hG) _

theorem IsCoseparating.mono {𝒢 : Set C} (h𝒢 : IsCoseparating 𝒢) {ℋ : Set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) : IsCoseparating ℋ :=
  fun X Y f g hfg => (h𝒢 _ _) fun G hG h => hfg _ (h𝒢ℋ hG) _

theorem IsDetecting.mono {𝒢 : Set C} (h𝒢 : IsDetecting 𝒢) {ℋ : Set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) : IsDetecting ℋ := fun X Y f hf =>
  (h𝒢 _) fun G hG h => hf _ (h𝒢ℋ hG) _

theorem IsCodetecting.mono {𝒢 : Set C} (h𝒢 : IsCodetecting 𝒢) {ℋ : Set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) : IsCodetecting ℋ :=
  fun X Y f hf => (h𝒢 _) fun G hG h => hf _ (h𝒢ℋ hG) _

end Mono

section Empty

theorem thin_of_is_separating_empty (h : IsSeparating (∅ : Set C)) (X Y : C) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => (h _ _) fun G => False.elim⟩

theorem is_separating_empty_of_thin [∀ X Y : C, Subsingleton (X ⟶ Y)] : IsSeparating (∅ : Set C) := fun X Y f g hfg =>
  Subsingleton.elimₓ _ _

theorem thin_of_is_coseparating_empty (h : IsCoseparating (∅ : Set C)) (X Y : C) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => (h _ _) fun G => False.elim⟩

theorem is_coseparating_empty_of_thin [∀ X Y : C, Subsingleton (X ⟶ Y)] : IsCoseparating (∅ : Set C) :=
  fun X Y f g hfg => Subsingleton.elimₓ _ _

theorem groupoid_of_is_detecting_empty (h : IsDetecting (∅ : Set C)) {X Y : C} (f : X ⟶ Y) : IsIso f :=
  (h _) fun G => False.elim

theorem is_detecting_empty_of_groupoid [∀ {X Y : C} (f : X ⟶ Y), IsIso f] : IsDetecting (∅ : Set C) := fun X Y f hf =>
  inferInstance

theorem groupoid_of_is_codetecting_empty (h : IsCodetecting (∅ : Set C)) {X Y : C} (f : X ⟶ Y) : IsIso f :=
  (h _) fun G => False.elim

theorem is_codetecting_empty_of_groupoid [∀ {X Y : C} (f : X ⟶ Y), IsIso f] : IsCodetecting (∅ : Set C) :=
  fun X Y f hf => inferInstance

end Empty

/-- We say that `G` is a separator if the functor `C(G, -)` is faithful. -/
def IsSeparator (G : C) : Prop :=
  IsSeparating ({G} : Set C)

/-- We say that `G` is a coseparator if the functor `C(-, G)` is faithful. -/
def IsCoseparator (G : C) : Prop :=
  IsCoseparating ({G} : Set C)

/-- We say that `G` is a detector if the functor `C(G, -)` reflects isomorphisms. -/
def IsDetector (G : C) : Prop :=
  IsDetecting ({G} : Set C)

/-- We say that `G` is a codetector if the functor `C(-, G)` reflects isomorphisms. -/
def IsCodetector (G : C) : Prop :=
  IsCodetecting ({G} : Set C)

section Dual

theorem is_separator_op_iff (G : C) : IsSeparator (op G) ↔ IsCoseparator G := by
  rw [is_separator, is_coseparator, ← is_separating_op_iff, Set.singleton_op]

theorem is_coseparator_op_iff (G : C) : IsCoseparator (op G) ↔ IsSeparator G := by
  rw [is_separator, is_coseparator, ← is_coseparating_op_iff, Set.singleton_op]

theorem is_coseparator_unop_iff (G : Cᵒᵖ) : IsCoseparator (unop G) ↔ IsSeparator G := by
  rw [is_separator, is_coseparator, ← is_coseparating_unop_iff, Set.singleton_unop]

theorem is_separator_unop_iff (G : Cᵒᵖ) : IsSeparator (unop G) ↔ IsCoseparator G := by
  rw [is_separator, is_coseparator, ← is_separating_unop_iff, Set.singleton_unop]

theorem is_detector_op_iff (G : C) : IsDetector (op G) ↔ IsCodetector G := by
  rw [is_detector, is_codetector, ← is_detecting_op_iff, Set.singleton_op]

theorem is_codetector_op_iff (G : C) : IsCodetector (op G) ↔ IsDetector G := by
  rw [is_detector, is_codetector, ← is_codetecting_op_iff, Set.singleton_op]

theorem is_codetector_unop_iff (G : Cᵒᵖ) : IsCodetector (unop G) ↔ IsDetector G := by
  rw [is_detector, is_codetector, ← is_codetecting_unop_iff, Set.singleton_unop]

theorem is_detector_unop_iff (G : Cᵒᵖ) : IsDetector (unop G) ↔ IsCodetector G := by
  rw [is_detector, is_codetector, ← is_detecting_unop_iff, Set.singleton_unop]

end Dual

theorem IsDetector.is_separator [HasEqualizers C] {G : C} : IsDetector G → IsSeparator G :=
  is_detecting.is_separating

theorem IsCodetector.is_coseparator [HasCoequalizers C] {G : C} : IsCodetector G → IsCoseparator G :=
  is_codetecting.is_coseparating

theorem IsSeparator.is_detector [Balanced C] {G : C} : IsSeparator G → IsDetector G :=
  is_separating.is_detecting

theorem IsCospearator.is_codetector [Balanced C] {G : C} : IsCoseparator G → IsCodetector G :=
  is_coseparating.is_codetecting

theorem is_separator_def (G : C) : IsSeparator G ↔ ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = h ≫ g) → f = g :=
  ⟨fun hG X Y f g hfg =>
    (hG _ _) fun H hH h => by
      obtain rfl := Set.mem_singleton_iff.1 hH
      exact hfg h,
    fun hG X Y f g hfg => (hG _ _) fun h => hfg _ (Set.mem_singleton _) _⟩

theorem IsSeparator.def {G : C} : IsSeparator G → ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = h ≫ g) → f = g :=
  (is_separator_def _).1

theorem is_coseparator_def (G : C) :
    IsCoseparator G ↔ ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = g ≫ h) → f = g :=
  ⟨fun hG X Y f g hfg =>
    (hG _ _) fun H hH h => by
      obtain rfl := Set.mem_singleton_iff.1 hH
      exact hfg h,
    fun hG X Y f g hfg => (hG _ _) fun h => hfg _ (Set.mem_singleton _) _⟩

theorem IsCoseparator.def {G : C} : IsCoseparator G → ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = g ≫ h) → f = g :=
  (is_coseparator_def _).1

theorem is_detector_def (G : C) : IsDetector G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ Y, ∃! h', h' ≫ f = h) → IsIso f :=
  ⟨fun hG X Y f hf =>
    (hG _) fun H hH h => by
      obtain rfl := Set.mem_singleton_iff.1 hH
      exact hf h,
    fun hG X Y f hf => (hG _) fun h => hf _ (Set.mem_singleton _) _⟩

theorem IsDetector.def {G : C} : IsDetector G → ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ Y, ∃! h', h' ≫ f = h) → IsIso f :=
  (is_detector_def _).1

theorem is_codetector_def (G : C) :
    IsCodetector G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : X ⟶ G, ∃! h', f ≫ h' = h) → IsIso f :=
  ⟨fun hG X Y f hf =>
    (hG _) fun H hH h => by
      obtain rfl := Set.mem_singleton_iff.1 hH
      exact hf h,
    fun hG X Y f hf => (hG _) fun h => hf _ (Set.mem_singleton _) _⟩

theorem IsCodetector.def {G : C} :
    IsCodetector G → ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : X ⟶ G, ∃! h', f ≫ h' = h) → IsIso f :=
  (is_codetector_def _).1

theorem is_separator_iff_faithful_coyoneda_obj (G : C) : IsSeparator G ↔ Faithful (coyoneda.obj (op G)) :=
  ⟨fun hG => ⟨fun X Y f g hfg => hG.def _ _ (congr_fun hfg)⟩, fun h =>
    (is_separator_def _).2 fun X Y f g hfg => (coyoneda.obj (op G)).map_injective (funext hfg)⟩

theorem is_coseparator_iff_faithful_yoneda_obj (G : C) : IsCoseparator G ↔ Faithful (yoneda.obj G) :=
  ⟨fun hG => ⟨fun X Y f g hfg => Quiver.Hom.unop_inj (hG.def _ _ (congr_fun hfg))⟩, fun h =>
    (is_coseparator_def _).2 fun X Y f g hfg => Quiver.Hom.op_inj <| (yoneda.obj G).map_injective (funext hfg)⟩

section ZeroMorphisms

variable [HasZeroMorphisms C]

theorem is_separator_coprod (G H : C) [HasBinaryCoproduct G H] : IsSeparator (G ⨿ H) ↔ IsSeparating ({G, H} : Set C) :=
  by
  refine' ⟨fun h X Y u v huv => _, fun h => (is_separator_def _).2 fun X Y u v huv => h _ _ fun Z hZ g => _⟩
  · refine' h.def _ _ fun g => coprod.hom_ext _ _
    · simpa using
        huv G
          (by
            simp )
          (coprod.inl ≫ g)
      
    · simpa using
        huv H
          (by
            simp )
          (coprod.inr ≫ g)
      
    
  · simp only [← Set.mem_insert_iff, ← Set.mem_singleton_iff] at hZ
    rcases hZ with (rfl | rfl)
    · simpa using coprod.inl ≫= huv (coprod.desc g 0)
      
    · simpa using coprod.inr ≫= huv (coprod.desc 0 g)
      
    

theorem is_separator_coprod_of_is_separator_left (G H : C) [HasBinaryCoproduct G H] (hG : IsSeparator G) :
    IsSeparator (G ⨿ H) :=
  (is_separator_coprod _ _).2 <|
    IsSeparating.mono hG <| by
      simp

theorem is_separator_coprod_of_is_separator_right (G H : C) [HasBinaryCoproduct G H] (hH : IsSeparator H) :
    IsSeparator (G ⨿ H) :=
  (is_separator_coprod _ _).2 <|
    IsSeparating.mono hH <| by
      simp

theorem is_separator_sigma {β : Type w} (f : β → C) [HasCoproduct f] : IsSeparator (∐ f) ↔ IsSeparating (Set.Range f) :=
  by
  refine' ⟨fun h X Y u v huv => _, fun h => (is_separator_def _).2 fun X Y u v huv => h _ _ fun Z hZ g => _⟩
  · refine' h.def _ _ fun g => colimit.hom_ext fun b => _
    simpa using
      huv (f b.as)
        (by
          simp )
        (colimit.ι (discrete.functor f) _ ≫ g)
    
  · obtain ⟨b, rfl⟩ := Set.mem_range.1 hZ
    classical
    simpa using sigma.ι f b ≫= huv (sigma.desc (Pi.single b g))
    

theorem is_separator_sigma_of_is_separator {β : Type w} (f : β → C) [HasCoproduct f] (b : β) (hb : IsSeparator (f b)) :
    IsSeparator (∐ f) :=
  (is_separator_sigma _).2 <|
    IsSeparating.mono hb <| by
      simp

theorem is_coseparator_prod (G H : C) [HasBinaryProduct G H] :
    IsCoseparator (G ⨯ H) ↔ IsCoseparating ({G, H} : Set C) := by
  refine' ⟨fun h X Y u v huv => _, fun h => (is_coseparator_def _).2 fun X Y u v huv => h _ _ fun Z hZ g => _⟩
  · refine' h.def _ _ fun g => prod.hom_ext _ _
    · simpa using
        huv G
          (by
            simp )
          (g ≫ limits.prod.fst)
      
    · simpa using
        huv H
          (by
            simp )
          (g ≫ limits.prod.snd)
      
    
  · simp only [← Set.mem_insert_iff, ← Set.mem_singleton_iff] at hZ
    rcases hZ with (rfl | rfl)
    · simpa using huv (prod.lift g 0) =≫ limits.prod.fst
      
    · simpa using huv (prod.lift 0 g) =≫ limits.prod.snd
      
    

theorem is_coseparator_prod_of_is_coseparator_left (G H : C) [HasBinaryProduct G H] (hG : IsCoseparator G) :
    IsCoseparator (G ⨯ H) :=
  (is_coseparator_prod _ _).2 <|
    IsCoseparating.mono hG <| by
      simp

theorem is_coseparator_prod_of_is_coseparator_right (G H : C) [HasBinaryProduct G H] (hH : IsCoseparator H) :
    IsCoseparator (G ⨯ H) :=
  (is_coseparator_prod _ _).2 <|
    IsCoseparating.mono hH <| by
      simp

theorem is_coseparator_pi {β : Type w} (f : β → C) [HasProduct f] :
    IsCoseparator (∏ f) ↔ IsCoseparating (Set.Range f) := by
  refine' ⟨fun h X Y u v huv => _, fun h => (is_coseparator_def _).2 fun X Y u v huv => h _ _ fun Z hZ g => _⟩
  · refine' h.def _ _ fun g => limit.hom_ext fun b => _
    simpa using
      huv (f b.as)
        (by
          simp )
        (g ≫ limit.π (discrete.functor f) _)
    
  · obtain ⟨b, rfl⟩ := Set.mem_range.1 hZ
    classical
    simpa using huv (pi.lift (Pi.single b g)) =≫ pi.π f b
    

theorem is_coseparator_pi_of_is_coseparator {β : Type w} (f : β → C) [HasProduct f] (b : β) (hb : IsCoseparator (f b)) :
    IsCoseparator (∏ f) :=
  (is_coseparator_pi _).2 <|
    IsCoseparating.mono hb <| by
      simp

end ZeroMorphisms

theorem is_detector_iff_reflects_isomorphisms_coyoneda_obj (G : C) :
    IsDetector G ↔ ReflectsIsomorphisms (coyoneda.obj (op G)) := by
  refine' ⟨fun hG => ⟨fun X Y f hf => hG.def _ fun h => _⟩, fun h => (is_detector_def _).2 fun X Y f hf => _⟩
  · rw [is_iso_iff_bijective, Function.bijective_iff_exists_unique] at hf
    exact hf h
    
  · suffices is_iso ((coyoneda.obj (op G)).map f) by
      exact @is_iso_of_reflects_iso _ _ _ _ _ _ _ (coyoneda.obj (op G)) _ h
    rwa [is_iso_iff_bijective, Function.bijective_iff_exists_unique]
    

theorem is_codetector_iff_reflects_isomorphisms_yoneda_obj (G : C) :
    IsCodetector G ↔ ReflectsIsomorphisms (yoneda.obj G) := by
  refine' ⟨fun hG => ⟨fun X Y f hf => _⟩, fun h => (is_codetector_def _).2 fun X Y f hf => _⟩
  · refine' (is_iso_unop_iff _).1 (hG.def _ _)
    rwa [is_iso_iff_bijective, Function.bijective_iff_exists_unique] at hf
    
  · rw [← is_iso_op_iff]
    suffices is_iso ((yoneda.obj G).map f.op) by
      exact @is_iso_of_reflects_iso _ _ _ _ _ _ _ (yoneda.obj G) _ h
    rwa [is_iso_iff_bijective, Function.bijective_iff_exists_unique]
    

end CategoryTheory

