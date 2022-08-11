/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Analysis.Convex.Combination
import Mathbin.Analysis.Convex.Extreme

/-!
# Convex independence

This file defines convex independent families of points.

Convex independence is closely related to affine independence. In both cases, no point can be
written as a combination of others. When the combination is affine (that is, any coefficients), this
yields affine independence. When the combination is convex (that is, all coefficients are
nonnegative), then this yields convex independence. In particular, affine independence implies
convex independence.

## Main declarations

* `convex_independent p`: Convex independence of the indexed family `p : ι → E`. Every point of the
  family only belongs to convex hulls of sets of the family containing it.
* `convex_independent_iff_finset`: Carathéodory's theorem allows us to only check finsets to
  conclude convex independence.
* `convex.extreme_points_convex_independent`: Extreme points of a convex set are convex independent.

## References

* https://en.wikipedia.org/wiki/Convex_position

## TODO

Prove `affine_independent.convex_independent`. This requires some glue between `affine_combination`
and `finset.center_mass`.

## Tags

independence, convex position
-/


open Affine BigOperators Classical

open Finset Function

variable {𝕜 E ι : Type _}

section OrderedSemiring

variable (𝕜) [OrderedSemiring 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {s t : Set E}

/-- An indexed family is said to be convex independent if every point only belongs to convex hulls
of sets containing it. -/
def ConvexIndependent (p : ι → E) : Prop :=
  ∀ (s : Set ι) (x : ι), p x ∈ convexHull 𝕜 (p '' s) → x ∈ s

variable {𝕜}

/-- A family with at most one point is convex independent. -/
theorem Subsingleton.convex_independent [Subsingleton ι] (p : ι → E) : ConvexIndependent 𝕜 p := fun s x hx => by
  have : (convexHull 𝕜 (p '' s)).Nonempty := ⟨p x, hx⟩
  rw [convex_hull_nonempty_iff, Set.nonempty_image_iff] at this
  rwa [Subsingleton.mem_iff_nonempty]

/-- A convex independent family is injective. -/
protected theorem ConvexIndependent.injective {p : ι → E} (hc : ConvexIndependent 𝕜 p) : Function.Injective p := by
  refine' fun i j hij => hc {j} i _
  rw [hij, Set.image_singleton, convex_hull_singleton]
  exact Set.mem_singleton _

/-- If a family is convex independent, so is any subfamily given by composition of an embedding into
index type with the original family. -/
theorem ConvexIndependent.comp_embedding {ι' : Type _} (f : ι' ↪ ι) {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
    ConvexIndependent 𝕜 (p ∘ f) := by
  intro s x hx
  rw [← f.injective.mem_set_image]
  exact
    hc _ _
      (by
        rwa [Set.image_image])

/-- If a family is convex independent, so is any subfamily indexed by a subtype of the index type.
-/
protected theorem ConvexIndependent.subtype {p : ι → E} (hc : ConvexIndependent 𝕜 p) (s : Set ι) :
    ConvexIndependent 𝕜 fun i : s => p i :=
  hc.comp_embedding (Embedding.subtype _)

/-- If an indexed family of points is convex independent, so is the corresponding set of points. -/
protected theorem ConvexIndependent.range {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
    ConvexIndependent 𝕜 (fun x => x : Set.Range p → E) := by
  let f : Set.Range p → ι := fun x => x.property.some
  have hf : ∀ x, p (f x) = x := fun x => x.property.some_spec
  let fe : Set.Range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert hc.comp_embedding fe
  ext
  rw [embedding.coe_fn_mk, comp_app, hf]

/-- A subset of a convex independent set of points is convex independent as well. -/
protected theorem ConvexIndependent.mono {s t : Set E} (hc : ConvexIndependent 𝕜 (fun x => x : t → E)) (hs : s ⊆ t) :
    ConvexIndependent 𝕜 (fun x => x : s → E) :=
  hc.comp_embedding (s.embeddingOfSubset t hs)

/-- The range of an injective indexed family of points is convex independent iff that family is. -/
theorem Function.Injective.convex_independent_iff_set {p : ι → E} (hi : Function.Injective p) :
    ConvexIndependent 𝕜 (fun x => x : Set.Range p → E) ↔ ConvexIndependent 𝕜 p :=
  ⟨fun hc =>
    hc.comp_embedding
      (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun x y h => hi (Subtype.mk_eq_mk.1 h)⟩ : ι ↪ Set.Range p),
    ConvexIndependent.range⟩

/-- If a family is convex independent, a point in the family is in the convex hull of some of the
points given by a subset of the index type if and only if the point's index is in this subset. -/
@[simp]
protected theorem ConvexIndependent.mem_convex_hull_iff {p : ι → E} (hc : ConvexIndependent 𝕜 p) (s : Set ι) (i : ι) :
    p i ∈ convexHull 𝕜 (p '' s) ↔ i ∈ s :=
  ⟨hc _ _, fun hi => subset_convex_hull 𝕜 _ (Set.mem_image_of_mem p hi)⟩

/-- If a family is convex independent, a point in the family is not in the convex hull of the other
points. See `convex_independent_set_iff_not_mem_convex_hull_diff` for the `set` version.  -/
theorem convex_independent_iff_not_mem_convex_hull_diff {p : ι → E} :
    ConvexIndependent 𝕜 p ↔ ∀ i s, p i ∉ convexHull 𝕜 (p '' (s \ {i})) := by
  refine' ⟨fun hc i s h => _, fun h s i hi => _⟩
  · rw [hc.mem_convex_hull_iff] at h
    exact h.2 (Set.mem_singleton _)
    
  · by_contra H
    refine' h i s _
    rw [Set.diff_singleton_eq_self H]
    exact hi
    

theorem convex_independent_set_iff_inter_convex_hull_subset {s : Set E} :
    ConvexIndependent 𝕜 (fun x => x : s → E) ↔ ∀ t, t ⊆ s → s ∩ convexHull 𝕜 t ⊆ t := by
  constructor
  · rintro hc t h x ⟨hxs, hxt⟩
    refine' hc { x | ↑x ∈ t } ⟨x, hxs⟩ _
    rw [Subtype.coe_image_of_subset h]
    exact hxt
    
  · intro hc t x h
    rw [← subtype.coe_injective.mem_set_image]
    exact hc (t.image coe) (Subtype.coe_image_subset s t) ⟨x.prop, h⟩
    

/-- If a set is convex independent, a point in the set is not in the convex hull of the other
points. See `convex_independent_iff_not_mem_convex_hull_diff` for the indexed family version.  -/
theorem convex_independent_set_iff_not_mem_convex_hull_diff {s : Set E} :
    ConvexIndependent 𝕜 (fun x => x : s → E) ↔ ∀, ∀ x ∈ s, ∀, x ∉ convexHull 𝕜 (s \ {x}) := by
  rw [convex_independent_set_iff_inter_convex_hull_subset]
  constructor
  · rintro hs x hxs hx
    exact (hs _ (Set.diff_subset _ _) ⟨hxs, hx⟩).2 (Set.mem_singleton _)
    
  · rintro hs t ht x ⟨hxs, hxt⟩
    by_contra h
    exact hs _ hxs (convex_hull_mono (Set.subset_diff_singleton ht h) hxt)
    

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {s : Set E}

/-- To check convex independence, one only has to check finsets thanks to Carathéodory's theorem. -/
theorem convex_independent_iff_finset {p : ι → E} :
    ConvexIndependent 𝕜 p ↔ ∀ (s : Finset ι) (x : ι), p x ∈ convexHull 𝕜 (s.Image p : Set E) → x ∈ s := by
  refine' ⟨fun hc s x hx => hc s x _, fun h s x hx => _⟩
  · rwa [Finset.coe_image] at hx
    
  have hp : injective p := by
    rintro a b hab
    rw [← mem_singleton]
    refine' h {b} a _
    rw [hab, image_singleton, coe_singleton, convex_hull_singleton]
    exact Set.mem_singleton _
  rw [convex_hull_eq_union_convex_hull_finite_subsets] at hx
  simp_rw [Set.mem_Union] at hx
  obtain ⟨t, ht, hx⟩ := hx
  rw [← hp.mem_set_image]
  refine' ht _
  suffices x ∈ t.preimage p (hp.inj_on _) by
    rwa [mem_preimage, ← mem_coe] at this
  refine' h _ x _
  rwa [t.image_preimage p (hp.inj_on _), filter_true_of_mem]
  · exact fun y hy => s.image_subset_range p (ht <| mem_coe.2 hy)
    

/-! ### Extreme points -/


theorem Convex.convex_independent_extreme_points (hs : Convex 𝕜 s) :
    ConvexIndependent 𝕜 (fun p => p : s.ExtremePoints 𝕜 → E) :=
  convex_independent_set_iff_not_mem_convex_hull_diff.2 fun x hx h =>
    (extreme_points_convex_hull_subset
          (inter_extreme_points_subset_extreme_points_of_subset
            (convex_hull_min ((Set.diff_subset _ _).trans extreme_points_subset) hs) ⟨h, hx⟩)).2
      (Set.mem_singleton _)

end LinearOrderedField

