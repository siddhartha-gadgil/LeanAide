/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Analysis.Convex.Topology
import Mathbin.Tactic.ByContra

/-!
# Simplicial complexes

In this file, we define simplicial complexes in `𝕜`-modules. A simplicial complex is a collection
of simplices closed by inclusion (of vertices) and intersection (of underlying sets).

We model them by a downward-closed set of affine independent finite sets whose convex hulls "glue
nicely", each finite set and its convex hull corresponding respectively to the vertices and the
underlying set of a simplex.

## Main declarations

* `simplicial_complex 𝕜 E`: A simplicial complex in the `𝕜`-module `E`.
* `simplicial_complex.vertices`: The zero dimensional faces of a simplicial complex.
* `simplicial_complex.facets`: The maximal faces of a simplicial complex.

## Notation

`s ∈ K` means that `s` is a face of `K`.

`K ≤ L` means that the faces of `K` are faces of `L`.

## Implementation notes

"glue nicely" usually means that the intersection of two faces (as sets in the ambient space) is a
face. Given that we store the vertices, not the faces, this would be a bit awkward to spell.
Instead, `simplicial_complex.inter_subset_convex_hull` is an equivalent condition which works on the
vertices.

## TODO

Simplicial complexes can be generalized to affine spaces once `convex_hull` has been ported.
-/


open Finset Set

variable (𝕜 E : Type _) {ι : Type _} [OrderedRing 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

namespace Geometry

/-- A simplicial complex in a `𝕜`-module is a collection of simplices which glue nicely together.
Note that the textbook meaning of "glue nicely" is given in
`geometry.simplicial_complex.disjoint_or_exists_inter_eq_convex_hull`. It is mostly useless, as
`geometry.simplicial_complex.convex_hull_inter_convex_hull` is enough for all purposes. -/
-- TODO: update to new binder order? not sure what binder order is correct for `down_closed`.
@[ext]
structure SimplicialComplex where
  Faces : Set (Finset E)
  not_empty_mem : ∅ ∉ faces
  indep : ∀ {s}, s ∈ faces → AffineIndependent 𝕜 (coe : (s : Set E) → E)
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ≠ ∅ → t ∈ faces
  inter_subset_convex_hull :
    ∀ {s t}, s ∈ faces → t ∈ faces → convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)

namespace SimplicialComplex

variable {𝕜 E} {K : SimplicialComplex 𝕜 E} {s t : Finset E} {x : E}

/-- A `finset` belongs to a `simplicial_complex` if it's a face of it. -/
instance : HasMem (Finset E) (SimplicialComplex 𝕜 E) :=
  ⟨fun s K => s ∈ K.Faces⟩

/-- The underlying space of a simplicial complex is the union of its faces. -/
def Space (K : SimplicialComplex 𝕜 E) : Set E :=
  ⋃ s ∈ K.Faces, convexHull 𝕜 (s : Set E)

theorem mem_space_iff : x ∈ K.Space ↔ ∃ s ∈ K.Faces, x ∈ convexHull 𝕜 (s : Set E) :=
  mem_Union₂

theorem convex_hull_subset_space (hs : s ∈ K.Faces) : convexHull 𝕜 ↑s ⊆ K.Space :=
  subset_bUnion_of_mem hs

protected theorem subset_space (hs : s ∈ K.Faces) : (s : Set E) ⊆ K.Space :=
  (subset_convex_hull 𝕜 _).trans <| convex_hull_subset_space hs

theorem convex_hull_inter_convex_hull (hs : s ∈ K.Faces) (ht : t ∈ K.Faces) :
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t = convexHull 𝕜 (s ∩ t : Set E) :=
  (K.inter_subset_convex_hull hs ht).antisymm <|
    subset_inter (convex_hull_mono <| Set.inter_subset_left _ _) <| convex_hull_mono <| Set.inter_subset_right _ _

/-- The conclusion is the usual meaning of "glue nicely" in textbooks. It turns out to be quite
unusable, as it's about faces as sets in space rather than simplices. Further,  additional structure
on `𝕜` means the only choice of `u` is `s ∩ t` (but it's hard to prove). -/
theorem disjoint_or_exists_inter_eq_convex_hull (hs : s ∈ K.Faces) (ht : t ∈ K.Faces) :
    Disjoint (convexHull 𝕜 (s : Set E)) (convexHull 𝕜 ↑t) ∨
      ∃ u ∈ K.Faces, convexHull 𝕜 (s : Set E) ∩ convexHull 𝕜 ↑t = convexHull 𝕜 ↑u :=
  by
  classical
  by_contra' h
  refine'
    h.2 (s ∩ t)
      ((K.down_closed hs (inter_subset_left _ _)) fun hst => h.1 <| (K.inter_subset_convex_hull hs ht).trans _) _
  · rw [← coe_inter, hst, coe_empty, convex_hull_empty]
    rfl
    
  · rw [coe_inter, convex_hull_inter_convex_hull hs ht]
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (s t «expr ∈ » faces)
/-- Construct a simplicial complex by removing the empty face for you. -/
@[simps]
def ofErase (faces : Set (Finset E)) (indep : ∀, ∀ s ∈ faces, ∀, AffineIndependent 𝕜 (coe : (s : Set E) → E))
    (down_closed : ∀, ∀ s ∈ faces, ∀, ∀ (t) (_ : t ⊆ s), t ∈ faces)
    (inter_subset_convex_hull :
      ∀ (s t) (_ : s ∈ faces) (_ : t ∈ faces), convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)) :
    SimplicialComplex 𝕜 E where
  Faces := faces \ {∅}
  not_empty_mem := fun h => h.2 (mem_singleton _)
  indep := fun s hs => indep _ hs.1
  down_closed := fun s t hs hts ht => ⟨down_closed _ hs.1 _ hts, ht⟩
  inter_subset_convex_hull := fun s t hs ht => inter_subset_convex_hull _ hs.1 _ ht.1

/-- Construct a simplicial complex as a subset of a given simplicial complex. -/
@[simps]
def ofSubcomplex (K : SimplicialComplex 𝕜 E) (faces : Set (Finset E)) (subset : faces ⊆ K.Faces)
    (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces) : SimplicialComplex 𝕜 E :=
  { Faces, not_empty_mem := fun h => K.not_empty_mem (subset h), indep := fun s hs => K.indep (subset hs),
    down_closed := fun s t hs hts _ => down_closed hs hts,
    inter_subset_convex_hull := fun s t hs ht => K.inter_subset_convex_hull (subset hs) (subset ht) }

/-! ### Vertices -/


/-- The vertices of a simplicial complex are its zero dimensional faces. -/
def Vertices (K : SimplicialComplex 𝕜 E) : Set E :=
  { x | {x} ∈ K.Faces }

theorem mem_vertices : x ∈ K.Vertices ↔ {x} ∈ K.Faces :=
  Iff.rfl

theorem vertices_eq : K.Vertices = ⋃ k ∈ K.Faces, (k : Set E) := by
  ext x
  refine' ⟨fun h => mem_bUnion h <| mem_coe.2 <| mem_singleton_self x, fun h => _⟩
  obtain ⟨s, hs, hx⟩ := mem_Union₂.1 h
  exact K.down_closed hs (Finset.singleton_subset_iff.2 <| mem_coe.1 hx) (singleton_ne_empty _)

theorem vertices_subset_space : K.Vertices ⊆ K.Space :=
  vertices_eq.Subset.trans <| Union₂_mono fun x hx => subset_convex_hull 𝕜 x

theorem vertex_mem_convex_hull_iff (hx : x ∈ K.Vertices) (hs : s ∈ K.Faces) : x ∈ convexHull 𝕜 (s : Set E) ↔ x ∈ s := by
  refine' ⟨fun h => _, fun h => subset_convex_hull _ _ h⟩
  classical
  have h :=
    K.inter_subset_convex_hull hx hs
      ⟨by
        simp , h⟩
  by_contra H
  rwa [← coe_inter, Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_singleton_right.2 H).symm, coe_empty,
    convex_hull_empty] at h

/-- A face is a subset of another one iff its vertices are.  -/
theorem face_subset_face_iff (hs : s ∈ K.Faces) (ht : t ∈ K.Faces) :
    convexHull 𝕜 (s : Set E) ⊆ convexHull 𝕜 ↑t ↔ s ⊆ t :=
  ⟨fun h x hxs =>
    (vertex_mem_convex_hull_iff (K.down_closed hs (Finset.singleton_subset_iff.2 hxs) <| singleton_ne_empty _) ht).1
      (h (subset_convex_hull 𝕜 (↑s) hxs)),
    convex_hull_mono⟩

/-! ### Facets -/


/-- A facet of a simplicial complex is a maximal face. -/
def Facets (K : SimplicialComplex 𝕜 E) : Set (Finset E) :=
  { s ∈ K.Faces | ∀ ⦃t⦄, t ∈ K.Faces → s ⊆ t → s = t }

theorem mem_facets : s ∈ K.Facets ↔ s ∈ K.Faces ∧ ∀, ∀ t ∈ K.Faces, ∀, s ⊆ t → s = t :=
  mem_sep_iff

theorem facets_subset : K.Facets ⊆ K.Faces := fun s hs => hs.1

theorem not_facet_iff_subface (hs : s ∈ K.Faces) : s ∉ K.Facets ↔ ∃ t, t ∈ K.Faces ∧ s ⊂ t := by
  refine' ⟨fun hs' : ¬(_ ∧ _) => _, _⟩
  · push_neg  at hs'
    obtain ⟨t, ht⟩ := hs' hs
    exact ⟨t, ht.1, ⟨ht.2.1, fun hts => ht.2.2 (subset.antisymm ht.2.1 hts)⟩⟩
    
  · rintro ⟨t, ht⟩ ⟨hs, hs'⟩
    have := hs' ht.1 ht.2.1
    rw [this] at ht
    exact ht.2.2 (subset.refl t)
    

/-!
### The semilattice of simplicial complexes

`K ≤ L` means that `K.faces ⊆ L.faces`.
-/


-- `has_ssubset.ssubset.ne` would be handy here
variable (𝕜 E)

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : HasInf (SimplicialComplex 𝕜 E) :=
  ⟨fun K L =>
    { Faces := K.Faces ∩ L.Faces, not_empty_mem := fun h => K.not_empty_mem (Set.inter_subset_left _ _ h),
      indep := fun s hs => K.indep hs.1,
      down_closed := fun s t hs hst ht => ⟨K.down_closed hs.1 hst ht, L.down_closed hs.2 hst ht⟩,
      inter_subset_convex_hull := fun s t hs ht => K.inter_subset_convex_hull hs.1 ht.1 }⟩

instance : SemilatticeInf (SimplicialComplex 𝕜 E) :=
  { (PartialOrderₓ.lift Faces) fun x y => ext _ _ with inf := (·⊓·), inf_le_left := fun K L s hs => hs.1,
    inf_le_right := fun K L s hs => hs.2, le_inf := fun K L M hKL hKM s hs => ⟨hKL hs, hKM hs⟩ }

instance : HasBot (SimplicialComplex 𝕜 E) :=
  ⟨{ Faces := ∅, not_empty_mem := Set.not_mem_empty ∅, indep := fun s hs => (Set.not_mem_empty _ hs).elim,
      down_closed := fun s _ hs => (Set.not_mem_empty _ hs).elim,
      inter_subset_convex_hull := fun s _ hs => (Set.not_mem_empty _ hs).elim }⟩

instance : OrderBot (SimplicialComplex 𝕜 E) :=
  { SimplicialComplex.hasBot 𝕜 E with bot_le := fun K => Set.empty_subset _ }

instance : Inhabited (SimplicialComplex 𝕜 E) :=
  ⟨⊥⟩

variable {𝕜 E}

theorem faces_bot : (⊥ : SimplicialComplex 𝕜 E).Faces = ∅ :=
  rfl

theorem space_bot : (⊥ : SimplicialComplex 𝕜 E).Space = ∅ :=
  Set.bUnion_empty _

theorem facets_bot : (⊥ : SimplicialComplex 𝕜 E).Facets = ∅ :=
  eq_empty_of_subset_empty facets_subset

end SimplicialComplex

end Geometry

