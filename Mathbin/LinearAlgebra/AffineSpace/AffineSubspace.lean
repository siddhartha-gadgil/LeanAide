/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Data.Set.Intervals.UnorderedInterval
import Mathbin.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Affine spaces

This file defines affine subspaces (over modules) and the affine span of a set of points.

## Main definitions

* `affine_subspace k P` is the type of affine subspaces.  Unlike
  affine spaces, affine subspaces are allowed to be empty, and lemmas
  that do not apply to empty affine subspaces have `nonempty`
  hypotheses.  There is a `complete_lattice` structure on affine
  subspaces.
* `affine_subspace.direction` gives the `submodule` spanned by the
  pairwise differences of points in an `affine_subspace`.  There are
  various lemmas relating to the set of vectors in the `direction`,
  and relating the lattice structure on affine subspaces to that on
  their directions.
* `affine_span` gives the affine subspace spanned by a set of points,
  with `vector_span` giving its direction.  `affine_span` is defined
  in terms of `span_points`, which gives an explicit description of
  the points contained in the affine span; `span_points` itself should
  generally only be used when that description is required, with
  `affine_span` being the main definition for other purposes.  Two
  other descriptions of the affine span are proved equivalent: it is
  the `Inf` of affine subspaces containing the points, and (if
  `[nontrivial k]`) it contains exactly those points that are affine
  combinations of points in the given set.

## Implementation notes

`out_param` is used in the definiton of `add_torsor V P` to make `V` an implicit argument (deduced
from `P`) in most cases; `include V` is needed in many cases for `V`, and type classes using it, to
be added as implicit arguments to individual lemmas.  As for modules, `k` is an explicit argument
rather than implied by `P` or `V`.

This file only provides purely algebraic definitions and results.
Those depending on analysis or topology are defined elsewhere; see
`analysis.normed_space.add_torsor` and `topology.algebra.affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/


noncomputable section

open BigOperators Classical Affine

open Set

section

variable (k : Type _) {V : Type _} {P : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V]

variable [affine_space V P]

include V

/-- The submodule spanning the differences of a (possibly empty) set
of points. -/
def vectorSpan (s : Set P) : Submodule k V :=
  Submodule.span k (s -ᵥ s)

/-- The definition of `vector_span`, for rewriting. -/
theorem vector_span_def (s : Set P) : vectorSpan k s = Submodule.span k (s -ᵥ s) :=
  rfl

/-- `vector_span` is monotone. -/
theorem vector_span_mono {s₁ s₂ : Set P} (h : s₁ ⊆ s₂) : vectorSpan k s₁ ≤ vectorSpan k s₂ :=
  Submodule.span_mono (vsub_self_mono h)

variable (P)

/-- The `vector_span` of the empty set is `⊥`. -/
@[simp]
theorem vector_span_empty : vectorSpan k (∅ : Set P) = (⊥ : Submodule k V) := by
  rw [vector_span_def, vsub_empty, Submodule.span_empty]

variable {P}

/-- The `vector_span` of a single point is `⊥`. -/
@[simp]
theorem vector_span_singleton (p : P) : vectorSpan k ({p} : Set P) = ⊥ := by
  simp [← vector_span_def]

/-- The `s -ᵥ s` lies within the `vector_span k s`. -/
theorem vsub_set_subset_vector_span (s : Set P) : s -ᵥ s ⊆ ↑(vectorSpan k s) :=
  Submodule.subset_span

/-- Each pairwise difference is in the `vector_span`. -/
theorem vsub_mem_vector_span {s : Set P} {p1 p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) : p1 -ᵥ p2 ∈ vectorSpan k s :=
  vsub_set_subset_vector_span k s (vsub_mem_vsub hp1 hp2)

/-- The points in the affine span of a (possibly empty) set of
points. Use `affine_span` instead to get an `affine_subspace k P`. -/
def SpanPoints (s : Set P) : Set P :=
  { p | ∃ p1 ∈ s, ∃ v ∈ vectorSpan k s, p = v +ᵥ p1 }

/-- A point in a set is in its affine span. -/
theorem mem_span_points (p : P) (s : Set P) : p ∈ s → p ∈ SpanPoints k s
  | hp => ⟨p, hp, 0, Submodule.zero_mem _, (zero_vadd V p).symm⟩

/-- A set is contained in its `span_points`. -/
theorem subset_span_points (s : Set P) : s ⊆ SpanPoints k s := fun p => mem_span_points k p s

/-- The `span_points` of a set is nonempty if and only if that set
is. -/
@[simp]
theorem span_points_nonempty (s : Set P) : (SpanPoints k s).Nonempty ↔ s.Nonempty := by
  constructor
  · contrapose
    rw [Set.not_nonempty_iff_eq_empty, Set.not_nonempty_iff_eq_empty]
    intro h
    simp [← h, ← SpanPoints]
    
  · exact fun h => h.mono (subset_span_points _ _)
    

/-- Adding a point in the affine span and a vector in the spanning
submodule produces a point in the affine span. -/
theorem vadd_mem_span_points_of_mem_span_points_of_mem_vector_span {s : Set P} {p : P} {v : V} (hp : p ∈ SpanPoints k s)
    (hv : v ∈ vectorSpan k s) : v +ᵥ p ∈ SpanPoints k s := by
  rcases hp with ⟨p2, ⟨hp2, ⟨v2, ⟨hv2, hv2p⟩⟩⟩⟩
  rw [hv2p, vadd_vadd]
  use p2, hp2, v + v2, (vectorSpan k s).add_mem hv hv2, rfl

/-- Subtracting two points in the affine span produces a vector in the
spanning submodule. -/
theorem vsub_mem_vector_span_of_mem_span_points_of_mem_span_points {s : Set P} {p1 p2 : P} (hp1 : p1 ∈ SpanPoints k s)
    (hp2 : p2 ∈ SpanPoints k s) : p1 -ᵥ p2 ∈ vectorSpan k s := by
  rcases hp1 with ⟨p1a, ⟨hp1a, ⟨v1, ⟨hv1, hv1p⟩⟩⟩⟩
  rcases hp2 with ⟨p2a, ⟨hp2a, ⟨v2, ⟨hv2, hv2p⟩⟩⟩⟩
  rw [hv1p, hv2p, vsub_vadd_eq_vsub_sub (v1 +ᵥ p1a), vadd_vsub_assoc, add_commₓ, add_sub_assoc]
  have hv1v2 : v1 - v2 ∈ vectorSpan k s := by
    rw [sub_eq_add_neg]
    apply (vectorSpan k s).add_mem hv1
    rw [← neg_one_smul k v2]
    exact (vectorSpan k s).smul_mem (-1 : k) hv2
  refine' (vectorSpan k s).add_mem _ hv1v2
  exact vsub_mem_vector_span k hp1a hp2a

end

/-- An `affine_subspace k P` is a subset of an `affine_space V P`
that, if not empty, has an affine space structure induced by a
corresponding subspace of the `module k V`. -/
structure AffineSubspace (k : Type _) {V : Type _} (P : Type _) [Ringₓ k] [AddCommGroupₓ V] [Module k V]
  [affine_space V P] where
  Carrier : Set P
  smul_vsub_vadd_mem :
    ∀ (c : k) {p1 p2 p3 : P}, p1 ∈ carrier → p2 ∈ carrier → p3 ∈ carrier → c • (p1 -ᵥ p2 : V) +ᵥ p3 ∈ carrier

namespace Submodule

variable {k V : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V]

/-- Reinterpret `p : submodule k V` as an `affine_subspace k V`. -/
def toAffineSubspace (p : Submodule k V) : AffineSubspace k V where
  Carrier := p
  smul_vsub_vadd_mem := fun c p₁ p₂ p₃ h₁ h₂ h₃ => p.add_mem (p.smul_mem _ (p.sub_mem h₁ h₂)) h₃

end Submodule

namespace AffineSubspace

variable (k : Type _) {V : Type _} (P : Type _) [Ringₓ k] [AddCommGroupₓ V] [Module k V] [affine_space V P]

include V

-- TODO Refactor to use `instance : set_like (affine_subspace k P) P :=` instead
instance : Coe (AffineSubspace k P) (Set P) :=
  ⟨Carrier⟩

instance : HasMem P (AffineSubspace k P) :=
  ⟨fun p s => p ∈ (s : Set P)⟩

/-- A point is in an affine subspace coerced to a set if and only if
it is in that affine subspace. -/
@[simp]
theorem mem_coe (p : P) (s : AffineSubspace k P) : p ∈ (s : Set P) ↔ p ∈ s :=
  Iff.rfl

variable {k P}

/-- The direction of an affine subspace is the submodule spanned by
the pairwise differences of points.  (Except in the case of an empty
affine subspace, where the direction is the zero submodule, every
vector in the direction is the difference of two points in the affine
subspace.) -/
def direction (s : AffineSubspace k P) : Submodule k V :=
  vectorSpan k (s : Set P)

/-- The direction equals the `vector_span`. -/
theorem direction_eq_vector_span (s : AffineSubspace k P) : s.direction = vectorSpan k (s : Set P) :=
  rfl

/-- Alternative definition of the direction when the affine subspace
is nonempty.  This is defined so that the order on submodules (as used
in the definition of `submodule.span`) can be used in the proof of
`coe_direction_eq_vsub_set`, and is not intended to be used beyond
that proof. -/
def directionOfNonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) : Submodule k V where
  Carrier := (s : Set P) -ᵥ s
  zero_mem' := by
    cases' h with p hp
    exact vsub_self p ▸ vsub_mem_vsub hp hp
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨p1, p2, hp1, hp2, rfl⟩
    rcases hb with ⟨p3, p4, hp3, hp4, rfl⟩
    rw [← vadd_vsub_assoc]
    refine' vsub_mem_vsub _ hp4
    convert s.smul_vsub_vadd_mem 1 hp1 hp2 hp3
    rw [one_smul]
  smul_mem' := by
    intro c v hv
    rcases hv with ⟨p1, p2, hp1, hp2, rfl⟩
    rw [← vadd_vsub (c • (p1 -ᵥ p2)) p2]
    refine' vsub_mem_vsub _ hp2
    exact s.smul_vsub_vadd_mem c hp1 hp2 hp2

/-- `direction_of_nonempty` gives the same submodule as
`direction`. -/
theorem direction_of_nonempty_eq_direction {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    directionOfNonempty h = s.direction :=
  le_antisymmₓ (vsub_set_subset_vector_span k s) (Submodule.span_le.2 Set.Subset.rfl)

/-- The set of vectors in the direction of a nonempty affine subspace
is given by `vsub_set`. -/
theorem coe_direction_eq_vsub_set {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    (s.direction : Set V) = (s : Set P) -ᵥ s :=
  direction_of_nonempty_eq_direction h ▸ rfl

/-- A vector is in the direction of a nonempty affine subspace if and
only if it is the subtraction of two vectors in the subspace. -/
theorem mem_direction_iff_eq_vsub {s : AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V) :
    v ∈ s.direction ↔ ∃ p1 ∈ s, ∃ p2 ∈ s, v = p1 -ᵥ p2 := by
  rw [← SetLike.mem_coe, coe_direction_eq_vsub_set h]
  exact
    ⟨fun ⟨p1, p2, hp1, hp2, hv⟩ => ⟨p1, hp1, p2, hp2, hv.symm⟩, fun ⟨p1, hp1, p2, hp2, hv⟩ =>
      ⟨p1, p2, hp1, hp2, hv.symm⟩⟩

/-- Adding a vector in the direction to a point in the subspace
produces a point in the subspace. -/
theorem vadd_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction) {p : P} (hp : p ∈ s) :
    v +ᵥ p ∈ s := by
  rw [mem_direction_iff_eq_vsub ⟨p, hp⟩] at hv
  rcases hv with ⟨p1, hp1, p2, hp2, hv⟩
  rw [hv]
  convert s.smul_vsub_vadd_mem 1 hp1 hp2 hp
  rw [one_smul]

/-- Subtracting two points in the subspace produces a vector in the
direction. -/
theorem vsub_mem_direction {s : AffineSubspace k P} {p1 p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
    p1 -ᵥ p2 ∈ s.direction :=
  vsub_mem_vector_span k hp1 hp2

/-- Adding a vector to a point in a subspace produces a point in the
subspace if and only if the vector is in the direction. -/
theorem vadd_mem_iff_mem_direction {s : AffineSubspace k P} (v : V) {p : P} (hp : p ∈ s) :
    v +ᵥ p ∈ s ↔ v ∈ s.direction :=
  ⟨fun h => by
    simpa using vsub_mem_direction h hp, fun h => vadd_mem_of_mem_direction h hp⟩

/-- Given a point in an affine subspace, the set of vectors in its
direction equals the set of vectors subtracting that point on the
right. -/
theorem coe_direction_eq_vsub_set_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (· -ᵥ p) '' s := by
  rw [coe_direction_eq_vsub_set ⟨p, hp⟩]
  refine' le_antisymmₓ _ _
  · rintro v ⟨p1, p2, hp1, hp2, rfl⟩
    exact ⟨p1 -ᵥ p2 +ᵥ p, vadd_mem_of_mem_direction (vsub_mem_direction hp1 hp2) hp, vadd_vsub _ _⟩
    
  · rintro v ⟨p2, hp2, rfl⟩
    exact ⟨p2, p, hp2, hp, rfl⟩
    

/-- Given a point in an affine subspace, the set of vectors in its
direction equals the set of vectors subtracting that point on the
left. -/
theorem coe_direction_eq_vsub_set_left {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (· -ᵥ ·) p '' s := by
  ext v
  rw [SetLike.mem_coe, ← Submodule.neg_mem_iff, ← SetLike.mem_coe, coe_direction_eq_vsub_set_right hp,
    Set.mem_image_iff_bex, Set.mem_image_iff_bex]
  conv_lhs => congr ext rw [← neg_vsub_eq_vsub_rev, neg_inj]

/-- Given a point in an affine subspace, a vector is in its direction
if and only if it results from subtracting that point on the right. -/
theorem mem_direction_iff_eq_vsub_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p2 ∈ s, v = p2 -ᵥ p := by
  rw [← SetLike.mem_coe, coe_direction_eq_vsub_set_right hp]
  exact ⟨fun ⟨p2, hp2, hv⟩ => ⟨p2, hp2, hv.symm⟩, fun ⟨p2, hp2, hv⟩ => ⟨p2, hp2, hv.symm⟩⟩

/-- Given a point in an affine subspace, a vector is in its direction
if and only if it results from subtracting that point on the left. -/
theorem mem_direction_iff_eq_vsub_left {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p2 ∈ s, v = p -ᵥ p2 := by
  rw [← SetLike.mem_coe, coe_direction_eq_vsub_set_left hp]
  exact ⟨fun ⟨p2, hp2, hv⟩ => ⟨p2, hp2, hv.symm⟩, fun ⟨p2, hp2, hv⟩ => ⟨p2, hp2, hv.symm⟩⟩

/-- Given a point in an affine subspace, a result of subtracting that
point on the right is in the direction if and only if the other point
is in the subspace. -/
theorem vsub_right_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (p2 : P) :
    p2 -ᵥ p ∈ s.direction ↔ p2 ∈ s := by
  rw [mem_direction_iff_eq_vsub_right hp]
  simp

/-- Given a point in an affine subspace, a result of subtracting that
point on the left is in the direction if and only if the other point
is in the subspace. -/
theorem vsub_left_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (p2 : P) :
    p -ᵥ p2 ∈ s.direction ↔ p2 ∈ s := by
  rw [mem_direction_iff_eq_vsub_left hp]
  simp

/-- Two affine subspaces are equal if they have the same points. -/
@[ext]
theorem coe_injective : Function.Injective (coe : AffineSubspace k P → Set P) := fun s1 s2 h => by
  cases s1
  cases s2
  congr
  exact h

@[simp]
theorem ext_iff (s₁ s₂ : AffineSubspace k P) : (s₁ : Set P) = s₂ ↔ s₁ = s₂ :=
  ⟨fun h => coe_injective h, by
    tidy⟩

/-- Two affine subspaces with the same direction and nonempty
intersection are equal. -/
theorem ext_of_direction_eq {s1 s2 : AffineSubspace k P} (hd : s1.direction = s2.direction)
    (hn : ((s1 : Set P) ∩ s2).Nonempty) : s1 = s2 := by
  ext p
  have hq1 := Set.mem_of_mem_inter_left hn.some_mem
  have hq2 := Set.mem_of_mem_inter_right hn.some_mem
  constructor
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine' vadd_mem_of_mem_direction _ hq2
    rw [← hd]
    exact vsub_mem_direction hp hq1
    
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine' vadd_mem_of_mem_direction _ hq1
    rw [hd]
    exact vsub_mem_direction hp hq2
    

instance toAddTorsor (s : AffineSubspace k P) [Nonempty s] : AddTorsor s.direction s where
  vadd := fun a b => ⟨(a : V) +ᵥ (b : P), vadd_mem_of_mem_direction a.2 b.2⟩
  zero_vadd := by
    simp
  add_vadd := fun a b c => by
    ext
    apply add_vadd
  vsub := fun a b => ⟨(a : P) -ᵥ (b : P), (vsub_left_mem_direction_iff_mem a.2 _).mpr b.2⟩
  Nonempty := by
    infer_instance
  vsub_vadd' := fun a b => by
    ext
    apply AddTorsor.vsub_vadd'
  vadd_vsub' := fun a b => by
    ext
    apply AddTorsor.vadd_vsub'

@[simp, norm_cast]
theorem coe_vsub (s : AffineSubspace k P) [Nonempty s] (a b : s) : ↑(a -ᵥ b) = (a : P) -ᵥ (b : P) :=
  rfl

@[simp, norm_cast]
theorem coe_vadd (s : AffineSubspace k P) [Nonempty s] (a : s.direction) (b : s) : ↑(a +ᵥ b) = (a : V) +ᵥ (b : P) :=
  rfl

/-- Two affine subspaces with nonempty intersection are equal if and
only if their directions are equal. -/
theorem eq_iff_direction_eq_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p ∈ s₁) (h₂ : p ∈ s₂) :
    s₁ = s₂ ↔ s₁.direction = s₂.direction :=
  ⟨fun h => h ▸ rfl, fun h => ext_of_direction_eq h ⟨p, h₁, h₂⟩⟩

/-- Construct an affine subspace from a point and a direction. -/
def mk' (p : P) (direction : Submodule k V) : AffineSubspace k P where
  Carrier := { q | ∃ v ∈ direction, q = v +ᵥ p }
  smul_vsub_vadd_mem := fun c p1 p2 p3 hp1 hp2 hp3 => by
    rcases hp1 with ⟨v1, hv1, hp1⟩
    rcases hp2 with ⟨v2, hv2, hp2⟩
    rcases hp3 with ⟨v3, hv3, hp3⟩
    use c • (v1 - v2) + v3, direction.add_mem (direction.smul_mem c (direction.sub_mem hv1 hv2)) hv3
    simp [← hp1, ← hp2, ← hp3, ← vadd_vadd]

/-- An affine subspace constructed from a point and a direction contains
that point. -/
theorem self_mem_mk' (p : P) (direction : Submodule k V) : p ∈ mk' p direction :=
  ⟨0, ⟨direction.zero_mem, (zero_vadd _ _).symm⟩⟩

/-- An affine subspace constructed from a point and a direction contains
the result of adding a vector in that direction to that point. -/
theorem vadd_mem_mk' {v : V} (p : P) {direction : Submodule k V} (hv : v ∈ direction) : v +ᵥ p ∈ mk' p direction :=
  ⟨v, hv, rfl⟩

/-- An affine subspace constructed from a point and a direction is
nonempty. -/
theorem mk'_nonempty (p : P) (direction : Submodule k V) : (mk' p direction : Set P).Nonempty :=
  ⟨p, self_mem_mk' p direction⟩

/-- The direction of an affine subspace constructed from a point and a
direction. -/
@[simp]
theorem direction_mk' (p : P) (direction : Submodule k V) : (mk' p direction).direction = direction := by
  ext v
  rw [mem_direction_iff_eq_vsub (mk'_nonempty _ _)]
  constructor
  · rintro ⟨p1, ⟨v1, hv1, hp1⟩, p2, ⟨v2, hv2, hp2⟩, hv⟩
    rw [hv, hp1, hp2, vadd_vsub_vadd_cancel_right]
    exact direction.sub_mem hv1 hv2
    
  · exact fun hv => ⟨v +ᵥ p, vadd_mem_mk' _ hv, p, self_mem_mk' _ _, (vadd_vsub _ _).symm⟩
    

/-- Constructing an affine subspace from a point in a subspace and
that subspace's direction yields the original subspace. -/
@[simp]
theorem mk'_eq {s : AffineSubspace k P} {p : P} (hp : p ∈ s) : mk' p s.direction = s :=
  ext_of_direction_eq (direction_mk' p s.direction) ⟨p, Set.mem_inter (self_mem_mk' _ _) hp⟩

/-- If an affine subspace contains a set of points, it contains the
`span_points` of that set. -/
theorem span_points_subset_coe_of_subset_coe {s : Set P} {s1 : AffineSubspace k P} (h : s ⊆ s1) : SpanPoints k s ⊆ s1 :=
  by
  rintro p ⟨p1, hp1, v, hv, hp⟩
  rw [hp]
  have hp1s1 : p1 ∈ (s1 : Set P) := Set.mem_of_mem_of_subset hp1 h
  refine' vadd_mem_of_mem_direction _ hp1s1
  have hs : vectorSpan k s ≤ s1.direction := vector_span_mono k h
  rw [SetLike.le_def] at hs
  rw [← SetLike.mem_coe]
  exact Set.mem_of_mem_of_subset hv hs

end AffineSubspace

theorem AffineMap.line_map_mem {k V P : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V] [AddTorsor V P]
    {Q : AffineSubspace k P} {p₀ p₁ : P} (c : k) (h₀ : p₀ ∈ Q) (h₁ : p₁ ∈ Q) : AffineMap.lineMap p₀ p₁ c ∈ Q := by
  rw [AffineMap.line_map_apply]
  exact Q.smul_vsub_vadd_mem c h₁ h₀ h₀

section affineSpan

variable (k : Type _) {V : Type _} {P : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V] [affine_space V P]

include V

/-- The affine span of a set of points is the smallest affine subspace
containing those points. (Actually defined here in terms of spans in
modules.) -/
def affineSpan (s : Set P) : AffineSubspace k P where
  Carrier := SpanPoints k s
  smul_vsub_vadd_mem := fun c p1 p2 p3 hp1 hp2 hp3 =>
    vadd_mem_span_points_of_mem_span_points_of_mem_vector_span k hp3
      ((vectorSpan k s).smul_mem c (vsub_mem_vector_span_of_mem_span_points_of_mem_span_points k hp1 hp2))

/-- The affine span, converted to a set, is `span_points`. -/
@[simp]
theorem coe_affine_span (s : Set P) : (affineSpan k s : Set P) = SpanPoints k s :=
  rfl

/-- A set is contained in its affine span. -/
theorem subset_affine_span (s : Set P) : s ⊆ affineSpan k s :=
  subset_span_points k s

/-- The direction of the affine span is the `vector_span`. -/
theorem direction_affine_span (s : Set P) : (affineSpan k s).direction = vectorSpan k s := by
  apply le_antisymmₓ
  · refine' Submodule.span_le.2 _
    rintro v ⟨p1, p3, ⟨p2, hp2, v1, hv1, hp1⟩, ⟨p4, hp4, v2, hv2, hp3⟩, rfl⟩
    rw [hp1, hp3, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, SetLike.mem_coe]
    exact (vectorSpan k s).sub_mem ((vectorSpan k s).add_mem hv1 (vsub_mem_vector_span k hp2 hp4)) hv2
    
  · exact vector_span_mono k (subset_span_points k s)
    

/-- A point in a set is in its affine span. -/
theorem mem_affine_span {p : P} {s : Set P} (hp : p ∈ s) : p ∈ affineSpan k s :=
  mem_span_points k p s hp

end affineSpan

namespace AffineSubspace

variable {k : Type _} {V : Type _} {P : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V] [S : affine_space V P]

include S

instance : CompleteLattice (AffineSubspace k P) :=
  { PartialOrderₓ.lift (coe : AffineSubspace k P → Set P) coe_injective with sup := fun s1 s2 => affineSpan k (s1 ∪ s2),
    le_sup_left := fun s1 s2 => Set.Subset.trans (Set.subset_union_left s1 s2) (subset_span_points k _),
    le_sup_right := fun s1 s2 => Set.Subset.trans (Set.subset_union_right s1 s2) (subset_span_points k _),
    sup_le := fun s1 s2 s3 hs1 hs2 => span_points_subset_coe_of_subset_coe (Set.union_subset hs1 hs2),
    inf := fun s1 s2 =>
      mk (s1 ∩ s2) fun c p1 p2 p3 hp1 hp2 hp3 =>
        ⟨s1.smul_vsub_vadd_mem c hp1.1 hp2.1 hp3.1, s2.smul_vsub_vadd_mem c hp1.2 hp2.2 hp3.2⟩,
    inf_le_left := fun _ _ => Set.inter_subset_left _ _, inf_le_right := fun _ _ => Set.inter_subset_right _ _,
    le_inf := fun _ _ _ => Set.subset_inter,
    top := { Carrier := Set.Univ, smul_vsub_vadd_mem := fun _ _ _ _ _ _ _ => Set.mem_univ _ },
    le_top := fun _ _ _ => Set.mem_univ _, bot := { Carrier := ∅, smul_vsub_vadd_mem := fun _ _ _ _ => False.elim },
    bot_le := fun _ _ => False.elim, sup := fun s => affineSpan k (⋃ s' ∈ s, (s' : Set P)),
    inf := fun s =>
      mk (⋂ s' ∈ s, (s' : Set P)) fun c p1 p2 p3 hp1 hp2 hp3 =>
        Set.mem_Inter₂.2 fun s2 hs2 => by
          rw [Set.mem_Inter₂] at *
          exact s2.smul_vsub_vadd_mem c (hp1 s2 hs2) (hp2 s2 hs2) (hp3 s2 hs2),
    le_Sup := fun _ _ h => Set.Subset.trans (Set.subset_bUnion_of_mem h) (subset_span_points k _),
    Sup_le := fun _ _ h => span_points_subset_coe_of_subset_coe (Set.Union₂_subset h),
    Inf_le := fun _ _ => Set.bInter_subset_of_mem, le_Inf := fun _ _ => Set.subset_Inter₂ }

instance : Inhabited (AffineSubspace k P) :=
  ⟨⊤⟩

/-- The `≤` order on subspaces is the same as that on the corresponding
sets. -/
theorem le_def (s1 s2 : AffineSubspace k P) : s1 ≤ s2 ↔ (s1 : Set P) ⊆ s2 :=
  Iff.rfl

/-- One subspace is less than or equal to another if and only if all
its points are in the second subspace. -/
theorem le_def' (s1 s2 : AffineSubspace k P) : s1 ≤ s2 ↔ ∀, ∀ p ∈ s1, ∀, p ∈ s2 :=
  Iff.rfl

/-- The `<` order on subspaces is the same as that on the corresponding
sets. -/
theorem lt_def (s1 s2 : AffineSubspace k P) : s1 < s2 ↔ (s1 : Set P) ⊂ s2 :=
  Iff.rfl

/-- One subspace is not less than or equal to another if and only if
it has a point not in the second subspace. -/
theorem not_le_iff_exists (s1 s2 : AffineSubspace k P) : ¬s1 ≤ s2 ↔ ∃ p ∈ s1, p ∉ s2 :=
  Set.not_subset

/-- If a subspace is less than another, there is a point only in the
second. -/
theorem exists_of_lt {s1 s2 : AffineSubspace k P} (h : s1 < s2) : ∃ p ∈ s2, p ∉ s1 :=
  Set.exists_of_ssubset h

/-- A subspace is less than another if and only if it is less than or
equal to the second subspace and there is a point only in the
second. -/
theorem lt_iff_le_and_exists (s1 s2 : AffineSubspace k P) : s1 < s2 ↔ s1 ≤ s2 ∧ ∃ p ∈ s2, p ∉ s1 := by
  rw [lt_iff_le_not_leₓ, not_le_iff_exists]

/-- If an affine subspace is nonempty and contained in another with
the same direction, they are equal. -/
theorem eq_of_direction_eq_of_nonempty_of_le {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction)
    (hn : (s₁ : Set P).Nonempty) (hle : s₁ ≤ s₂) : s₁ = s₂ :=
  let ⟨p, hp⟩ := hn
  ext_of_direction_eq hd ⟨p, hp, hle hp⟩

variable (k V)

/-- The affine span is the `Inf` of subspaces containing the given
points. -/
theorem affine_span_eq_Inf (s : Set P) : affineSpan k s = inf { s' | s ⊆ s' } :=
  le_antisymmₓ (span_points_subset_coe_of_subset_coe <| Set.subset_Inter₂ fun _ => id) (Inf_le (subset_span_points k _))

variable (P)

/-- The Galois insertion formed by `affine_span` and coercion back to
a set. -/
protected def gi : GaloisInsertion (affineSpan k) (coe : AffineSubspace k P → Set P) where
  choice := fun s _ => affineSpan k s
  gc := fun s1 s2 => ⟨fun h => Set.Subset.trans (subset_span_points k s1) h, span_points_subset_coe_of_subset_coe⟩
  le_l_u := fun _ => subset_span_points k _
  choice_eq := fun _ _ => rfl

/-- The span of the empty set is `⊥`. -/
@[simp]
theorem span_empty : affineSpan k (∅ : Set P) = ⊥ :=
  (AffineSubspace.gi k V P).gc.l_bot

/-- The span of `univ` is `⊤`. -/
@[simp]
theorem span_univ : affineSpan k (Set.Univ : Set P) = ⊤ :=
  eq_top_iff.2 <| subset_span_points k _

variable {k V P}

theorem _root_.affine_span_le {s : Set P} {Q : AffineSubspace k P} : affineSpan k s ≤ Q ↔ s ⊆ (Q : Set P) :=
  (AffineSubspace.gi k V P).gc _ _

variable (k V) {P}

/-- The affine span of a single point, coerced to a set, contains just
that point. -/
@[simp]
theorem coe_affine_span_singleton (p : P) : (affineSpan k ({p} : Set P) : Set P) = {p} := by
  ext x
  rw [mem_coe, ← vsub_right_mem_direction_iff_mem (mem_affine_span k (Set.mem_singleton p)) _, direction_affine_span]
  simp

/-- A point is in the affine span of a single point if and only if
they are equal. -/
@[simp]
theorem mem_affine_span_singleton (p1 p2 : P) : p1 ∈ affineSpan k ({p2} : Set P) ↔ p1 = p2 := by
  simp [mem_coe]

/-- The span of a union of sets is the sup of their spans. -/
theorem span_union (s t : Set P) : affineSpan k (s ∪ t) = affineSpan k s⊔affineSpan k t :=
  (AffineSubspace.gi k V P).gc.l_sup

/-- The span of a union of an indexed family of sets is the sup of
their spans. -/
theorem span_Union {ι : Type _} (s : ι → Set P) : affineSpan k (⋃ i, s i) = ⨆ i, affineSpan k (s i) :=
  (AffineSubspace.gi k V P).gc.l_supr

variable (P)

/-- `⊤`, coerced to a set, is the whole set of points. -/
@[simp]
theorem top_coe : ((⊤ : AffineSubspace k P) : Set P) = Set.Univ :=
  rfl

variable {P}

/-- All points are in `⊤`. -/
theorem mem_top (p : P) : p ∈ (⊤ : AffineSubspace k P) :=
  Set.mem_univ p

variable (P)

/-- The direction of `⊤` is the whole module as a submodule. -/
@[simp]
theorem direction_top : (⊤ : AffineSubspace k P).direction = ⊤ := by
  cases' S.nonempty with p
  ext v
  refine' ⟨imp_intro Submodule.mem_top, fun hv => _⟩
  have hpv : (v +ᵥ p -ᵥ p : V) ∈ (⊤ : AffineSubspace k P).direction :=
    vsub_mem_direction (mem_top k V _) (mem_top k V _)
  rwa [vadd_vsub] at hpv

/-- `⊥`, coerced to a set, is the empty set. -/
@[simp]
theorem bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅ :=
  rfl

theorem bot_ne_top : (⊥ : AffineSubspace k P) ≠ ⊤ := by
  intro contra
  rw [← ext_iff, bot_coe, top_coe] at contra
  exact Set.empty_ne_univ contra

instance : Nontrivial (AffineSubspace k P) :=
  ⟨⟨⊥, ⊤, bot_ne_top k V P⟩⟩

theorem nonempty_of_affine_span_eq_top {s : Set P} (h : affineSpan k s = ⊤) : s.Nonempty := by
  rw [← Set.ne_empty_iff_nonempty]
  rintro rfl
  rw [AffineSubspace.span_empty] at h
  exact bot_ne_top k V P h

/-- If the affine span of a set is `⊤`, then the vector span of the same set is the `⊤`. -/
theorem vector_span_eq_top_of_affine_span_eq_top {s : Set P} (h : affineSpan k s = ⊤) : vectorSpan k s = ⊤ := by
  rw [← direction_affine_span, h, direction_top]

/-- For a nonempty set, the affine span is `⊤` iff its vector span is `⊤`. -/
theorem affine_span_eq_top_iff_vector_span_eq_top_of_nonempty {s : Set P} (hs : s.Nonempty) :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  refine' ⟨vector_span_eq_top_of_affine_span_eq_top k V P, _⟩
  intro h
  suffices Nonempty (affineSpan k s) by
    obtain ⟨p, hp : p ∈ affineSpan k s⟩ := this
    rw [eq_iff_direction_eq_of_mem hp (mem_top k V p), direction_affine_span, h, direction_top]
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨x, mem_affine_span k hx⟩⟩

/-- For a non-trivial space, the affine span of a set is `⊤` iff its vector span is `⊤`. -/
theorem affine_span_eq_top_iff_vector_span_eq_top_of_nontrivial {s : Set P} [Nontrivial P] :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  cases' s.eq_empty_or_nonempty with hs hs
  · simp [← hs, ← subsingleton_iff_bot_eq_top, ← AddTorsor.subsingleton_iff V P, ← not_subsingleton]
    
  · rw [affine_span_eq_top_iff_vector_span_eq_top_of_nonempty k V P hs]
    

theorem card_pos_of_affine_span_eq_top {ι : Type _} [Fintype ι] {p : ι → P} (h : affineSpan k (Range p) = ⊤) :
    0 < Fintype.card ι := by
  obtain ⟨-, ⟨i, -⟩⟩ := nonempty_of_affine_span_eq_top k V P h
  exact fintype.card_pos_iff.mpr ⟨i⟩

variable {P}

/-- No points are in `⊥`. -/
theorem not_mem_bot (p : P) : p ∉ (⊥ : AffineSubspace k P) :=
  Set.not_mem_empty p

variable (P)

/-- The direction of `⊥` is the submodule `⊥`. -/
@[simp]
theorem direction_bot : (⊥ : AffineSubspace k P).direction = ⊥ := by
  rw [direction_eq_vector_span, bot_coe, vector_span_def, vsub_empty, Submodule.span_empty]

variable {k V P}

@[simp]
theorem coe_eq_bot_iff (Q : AffineSubspace k P) : (Q : Set P) = ∅ ↔ Q = ⊥ :=
  coe_injective.eq_iff' (bot_coe _ _ _)

@[simp]
theorem coe_eq_univ_iff (Q : AffineSubspace k P) : (Q : Set P) = univ ↔ Q = ⊤ :=
  coe_injective.eq_iff' (top_coe _ _ _)

theorem nonempty_iff_ne_bot (Q : AffineSubspace k P) : (Q : Set P).Nonempty ↔ Q ≠ ⊥ := by
  rw [← ne_empty_iff_nonempty]
  exact not_congr Q.coe_eq_bot_iff

theorem eq_bot_or_nonempty (Q : AffineSubspace k P) : Q = ⊥ ∨ (Q : Set P).Nonempty := by
  rw [nonempty_iff_ne_bot]
  apply eq_or_ne

theorem subsingleton_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton) (h₂ : affineSpan k s = ⊤) :
    Subsingleton P := by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affine_span_eq_top k V P h₂
  have : s = {p} :=
    subset.antisymm (fun q hq => h₁ hq hp)
      (by
        simp [← hp])
  rw [this, ← AffineSubspace.ext_iff, AffineSubspace.coe_affine_span_singleton, AffineSubspace.top_coe, eq_comm, ←
    subsingleton_iff_singleton (mem_univ _)] at h₂
  exact subsingleton_of_univ_subsingleton h₂

theorem eq_univ_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton) (h₂ : affineSpan k s = ⊤) :
    s = (Univ : Set P) := by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affine_span_eq_top k V P h₂
  have : s = {p} :=
    subset.antisymm (fun q hq => h₁ hq hp)
      (by
        simp [← hp])
  rw [this, eq_comm, ← subsingleton_iff_singleton (mem_univ p), subsingleton_univ_iff]
  exact subsingleton_of_subsingleton_span_eq_top h₁ h₂

/-- A nonempty affine subspace is `⊤` if and only if its direction is
`⊤`. -/
@[simp]
theorem direction_eq_top_iff_of_nonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    s.direction = ⊤ ↔ s = ⊤ := by
  constructor
  · intro hd
    rw [← direction_top k V P] at hd
    refine' ext_of_direction_eq hd _
    simp [← h]
    
  · rintro rfl
    simp
    

/-- The inf of two affine subspaces, coerced to a set, is the
intersection of the two sets of points. -/
@[simp]
theorem inf_coe (s1 s2 : AffineSubspace k P) : (s1⊓s2 : Set P) = s1 ∩ s2 :=
  rfl

/-- A point is in the inf of two affine subspaces if and only if it is
in both of them. -/
theorem mem_inf_iff (p : P) (s1 s2 : AffineSubspace k P) : p ∈ s1⊓s2 ↔ p ∈ s1 ∧ p ∈ s2 :=
  Iff.rfl

/-- The direction of the inf of two affine subspaces is less than or
equal to the inf of their directions. -/
theorem direction_inf (s1 s2 : AffineSubspace k P) : (s1⊓s2).direction ≤ s1.direction⊓s2.direction := by
  repeat'
    rw [direction_eq_vector_span, vector_span_def]
  exact
    le_inf (Inf_le_Inf fun p hp => trans (vsub_self_mono (inter_subset_left _ _)) hp)
      (Inf_le_Inf fun p hp => trans (vsub_self_mono (inter_subset_right _ _)) hp)

/-- If two affine subspaces have a point in common, the direction of
their inf equals the inf of their directions. -/
theorem direction_inf_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p ∈ s₁) (h₂ : p ∈ s₂) :
    (s₁⊓s₂).direction = s₁.direction⊓s₂.direction := by
  ext v
  rw [Submodule.mem_inf, ← vadd_mem_iff_mem_direction v h₁, ← vadd_mem_iff_mem_direction v h₂, ←
    vadd_mem_iff_mem_direction v ((mem_inf_iff p s₁ s₂).2 ⟨h₁, h₂⟩), mem_inf_iff]

/-- If two affine subspaces have a point in their inf, the direction
of their inf equals the inf of their directions. -/
theorem direction_inf_of_mem_inf {s₁ s₂ : AffineSubspace k P} {p : P} (h : p ∈ s₁⊓s₂) :
    (s₁⊓s₂).direction = s₁.direction⊓s₂.direction :=
  direction_inf_of_mem ((mem_inf_iff p s₁ s₂).1 h).1 ((mem_inf_iff p s₁ s₂).1 h).2

/-- If one affine subspace is less than or equal to another, the same
applies to their directions. -/
theorem direction_le {s1 s2 : AffineSubspace k P} (h : s1 ≤ s2) : s1.direction ≤ s2.direction := by
  repeat'
    rw [direction_eq_vector_span, vector_span_def]
  exact vector_span_mono k h

/-- If one nonempty affine subspace is less than another, the same
applies to their directions -/
theorem direction_lt_of_nonempty {s1 s2 : AffineSubspace k P} (h : s1 < s2) (hn : (s1 : Set P).Nonempty) :
    s1.direction < s2.direction := by
  cases' hn with p hp
  rw [lt_iff_le_and_exists] at h
  rcases h with ⟨hle, p2, hp2, hp2s1⟩
  rw [SetLike.lt_iff_le_and_exists]
  use direction_le hle, p2 -ᵥ p, vsub_mem_direction hp2 (hle hp)
  intro hm
  rw [vsub_right_mem_direction_iff_mem hp p2] at hm
  exact hp2s1 hm

/-- The sup of the directions of two affine subspaces is less than or
equal to the direction of their sup. -/
theorem sup_direction_le (s1 s2 : AffineSubspace k P) : s1.direction⊔s2.direction ≤ (s1⊔s2).direction := by
  repeat'
    rw [direction_eq_vector_span, vector_span_def]
  exact
    sup_le (Inf_le_Inf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_left : s1 ≤ s1⊔s2)) hp)
      (Inf_le_Inf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_right : s2 ≤ s1⊔s2)) hp)

/-- The sup of the directions of two nonempty affine subspaces with
empty intersection is less than the direction of their sup. -/
theorem sup_direction_lt_of_nonempty_of_inter_empty {s1 s2 : AffineSubspace k P} (h1 : (s1 : Set P).Nonempty)
    (h2 : (s2 : Set P).Nonempty) (he : (s1 ∩ s2 : Set P) = ∅) : s1.direction⊔s2.direction < (s1⊔s2).direction := by
  cases' h1 with p1 hp1
  cases' h2 with p2 hp2
  rw [SetLike.lt_iff_le_and_exists]
  use sup_direction_le s1 s2, p2 -ᵥ p1,
    vsub_mem_direction ((le_sup_right : s2 ≤ s1⊔s2) hp2) ((le_sup_left : s1 ≤ s1⊔s2) hp1)
  intro h
  rw [Submodule.mem_sup] at h
  rcases h with ⟨v1, hv1, v2, hv2, hv1v2⟩
  rw [← sub_eq_zero, sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_commₓ v1, add_assocₓ, ← vadd_vsub_assoc, ← neg_negₓ v2,
    add_commₓ, ← sub_eq_add_neg, ← vsub_vadd_eq_vsub_sub, vsub_eq_zero_iff_eq] at hv1v2
  refine' Set.Nonempty.ne_empty _ he
  use v1 +ᵥ p1, vadd_mem_of_mem_direction hv1 hp1
  rw [hv1v2]
  exact vadd_mem_of_mem_direction (Submodule.neg_mem _ hv2) hp2

/-- If the directions of two nonempty affine subspaces span the whole
module, they have nonempty intersection. -/
theorem inter_nonempty_of_nonempty_of_sup_direction_eq_top {s1 s2 : AffineSubspace k P} (h1 : (s1 : Set P).Nonempty)
    (h2 : (s2 : Set P).Nonempty) (hd : s1.direction⊔s2.direction = ⊤) : ((s1 : Set P) ∩ s2).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hlt := sup_direction_lt_of_nonempty_of_inter_empty h1 h2 h
  rw [hd] at hlt
  exact not_top_lt hlt

/-- If the directions of two nonempty affine subspaces are complements
of each other, they intersect in exactly one point. -/
theorem inter_eq_singleton_of_nonempty_of_is_compl {s1 s2 : AffineSubspace k P} (h1 : (s1 : Set P).Nonempty)
    (h2 : (s2 : Set P).Nonempty) (hd : IsCompl s1.direction s2.direction) : ∃ p, (s1 : Set P) ∩ s2 = {p} := by
  cases' inter_nonempty_of_nonempty_of_sup_direction_eq_top h1 h2 hd.sup_eq_top with p hp
  use p
  ext q
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq1, hq2⟩
    have hqp : q -ᵥ p ∈ s1.direction⊓s2.direction := ⟨vsub_mem_direction hq1 hp.1, vsub_mem_direction hq2 hp.2⟩
    rwa [hd.inf_eq_bot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hqp
    
  · exact fun h => h.symm ▸ hp
    

/-- Coercing a subspace to a set then taking the affine span produces
the original subspace. -/
@[simp]
theorem affine_span_coe (s : AffineSubspace k P) : affineSpan k (s : Set P) = s := by
  refine' le_antisymmₓ _ (subset_span_points _ _)
  rintro p ⟨p1, hp1, v, hv, rfl⟩
  exact vadd_mem_of_mem_direction hv hp1

end AffineSubspace

section AffineSpace'

variable (k : Type _) {V : Type _} {P : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V] [affine_space V P]

variable {ι : Type _}

include V

open AffineSubspace Set

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the left. -/
theorem vector_span_eq_span_vsub_set_left {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((· -ᵥ ·) p '' s) := by
  rw [vector_span_def]
  refine' le_antisymmₓ _ (Submodule.span_mono _)
  · rw [Submodule.span_le]
    rintro v ⟨p1, p2, hp1, hp2, hv⟩
    rw [← vsub_sub_vsub_cancel_left p1 p2 p] at hv
    rw [← hv, SetLike.mem_coe, Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm ⟨p2, hp2, rfl⟩) (hm ⟨p1, hp1, rfl⟩)
    
  · rintro v ⟨p2, hp2, hv⟩
    exact ⟨p, p2, hp, hp2, hv⟩
    

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the right. -/
theorem vector_span_eq_span_vsub_set_right {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((· -ᵥ p) '' s) := by
  rw [vector_span_def]
  refine' le_antisymmₓ _ (Submodule.span_mono _)
  · rw [Submodule.span_le]
    rintro v ⟨p1, p2, hp1, hp2, hv⟩
    rw [← vsub_sub_vsub_cancel_right p1 p2 p] at hv
    rw [← hv, SetLike.mem_coe, Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm ⟨p1, hp1, rfl⟩) (hm ⟨p2, hp2, rfl⟩)
    
  · rintro v ⟨p2, hp2, hv⟩
    exact ⟨p2, p, hp2, hp, hv⟩
    

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the left, excluding the subtraction of that point from
itself. -/
theorem vector_span_eq_span_vsub_set_left_ne {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((· -ᵥ ·) p '' (s \ {p})) := by
  conv_lhs =>
    rw [vector_span_eq_span_vsub_set_left k hp, ← Set.insert_eq_of_mem hp, ← Set.insert_diff_singleton,
      Set.image_insert_eq]
  simp [← Submodule.span_insert_eq_span]

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the right, excluding the subtraction of that point from
itself. -/
theorem vector_span_eq_span_vsub_set_right_ne {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((· -ᵥ p) '' (s \ {p})) := by
  conv_lhs =>
    rw [vector_span_eq_span_vsub_set_right k hp, ← Set.insert_eq_of_mem hp, ← Set.insert_diff_singleton,
      Set.image_insert_eq]
  simp [← Submodule.span_insert_eq_span]

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the right, excluding the subtraction of that point from
itself. -/
theorem vector_span_eq_span_vsub_finset_right_ne {s : Finset P} {p : P} (hp : p ∈ s) :
    vectorSpan k (s : Set P) = Submodule.span k ((s.erase p).Image (· -ᵥ p)) := by
  simp [← vector_span_eq_span_vsub_set_right_ne _ (finset.mem_coe.mpr hp)]

/-- The `vector_span` of the image of a function is the span of the
pairwise subtractions with a given point on the left, excluding the
subtraction of that point from itself. -/
theorem vector_span_image_eq_span_vsub_set_left_ne (p : ι → P) {s : Set ι} {i : ι} (hi : i ∈ s) :
    vectorSpan k (p '' s) = Submodule.span k ((· -ᵥ ·) (p i) '' (p '' (s \ {i}))) := by
  conv_lhs =>
    rw [vector_span_eq_span_vsub_set_left k (Set.mem_image_of_mem p hi), ← Set.insert_eq_of_mem hi, ←
      Set.insert_diff_singleton, Set.image_insert_eq, Set.image_insert_eq]
  simp [← Submodule.span_insert_eq_span]

/-- The `vector_span` of the image of a function is the span of the
pairwise subtractions with a given point on the right, excluding the
subtraction of that point from itself. -/
theorem vector_span_image_eq_span_vsub_set_right_ne (p : ι → P) {s : Set ι} {i : ι} (hi : i ∈ s) :
    vectorSpan k (p '' s) = Submodule.span k ((· -ᵥ p i) '' (p '' (s \ {i}))) := by
  conv_lhs =>
    rw [vector_span_eq_span_vsub_set_right k (Set.mem_image_of_mem p hi), ← Set.insert_eq_of_mem hi, ←
      Set.insert_diff_singleton, Set.image_insert_eq, Set.image_insert_eq]
  simp [← Submodule.span_insert_eq_span]

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the left. -/
theorem vector_span_range_eq_span_range_vsub_left (p : ι → P) (i0 : ι) :
    vectorSpan k (Set.Range p) = Submodule.span k (Set.Range fun i : ι => p i0 -ᵥ p i) := by
  rw [vector_span_eq_span_vsub_set_left k (Set.mem_range_self i0), ← Set.range_comp]

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the right. -/
theorem vector_span_range_eq_span_range_vsub_right (p : ι → P) (i0 : ι) :
    vectorSpan k (Set.Range p) = Submodule.span k (Set.Range fun i : ι => p i -ᵥ p i0) := by
  rw [vector_span_eq_span_vsub_set_right k (Set.mem_range_self i0), ← Set.range_comp]

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the left, excluding the subtraction
of that point from itself. -/
theorem vector_span_range_eq_span_range_vsub_left_ne (p : ι → P) (i₀ : ι) :
    vectorSpan k (Set.Range p) = Submodule.span k (Set.Range fun i : { x // x ≠ i₀ } => p i₀ -ᵥ p i) := by
  rw [← Set.image_univ, vector_span_image_eq_span_vsub_set_left_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [← Set.mem_range, ← Set.mem_image, ← Set.mem_diff, ← Set.mem_singleton_iff, ← Subtype.exists, ←
    Subtype.coe_mk]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨hi₁u, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
    
  · exact fun ⟨i₁, hi₁, hv⟩ => ⟨p i₁, ⟨i₁, ⟨Set.mem_univ _, hi₁⟩, rfl⟩, hv⟩
    

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the right, excluding the subtraction
of that point from itself. -/
theorem vector_span_range_eq_span_range_vsub_right_ne (p : ι → P) (i₀ : ι) :
    vectorSpan k (Set.Range p) = Submodule.span k (Set.Range fun i : { x // x ≠ i₀ } => p i -ᵥ p i₀) := by
  rw [← Set.image_univ, vector_span_image_eq_span_vsub_set_right_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [← Set.mem_range, ← Set.mem_image, ← Set.mem_diff, ← Set.mem_singleton_iff, ← Subtype.exists, ←
    Subtype.coe_mk]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨hi₁u, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
    
  · exact fun ⟨i₁, hi₁, hv⟩ => ⟨p i₁, ⟨i₁, ⟨Set.mem_univ _, hi₁⟩, rfl⟩, hv⟩
    

/-- The affine span of a set is nonempty if and only if that set
is. -/
theorem affine_span_nonempty (s : Set P) : (affineSpan k s : Set P).Nonempty ↔ s.Nonempty :=
  span_points_nonempty k s

/-- The affine span of a nonempty set is nonempty. -/
instance {s : Set P} [Nonempty s] : Nonempty (affineSpan k s) :=
  ((affine_span_nonempty k s).mpr (nonempty_subtype.mp ‹_›)).to_subtype

variable {k}

/-- Suppose a set of vectors spans `V`.  Then a point `p`, together
with those vectors added to `p`, spans `P`. -/
theorem affine_span_singleton_union_vadd_eq_top_of_span_eq_top {s : Set V} (p : P)
    (h : Submodule.span k (Set.Range (coe : s → V)) = ⊤) : affineSpan k ({p} ∪ (fun v => v +ᵥ p) '' s) = ⊤ := by
  convert ext_of_direction_eq _ ⟨p, mem_affine_span k (Set.mem_union_left _ (Set.mem_singleton _)), mem_top k V p⟩
  rw [direction_affine_span, direction_top,
    vector_span_eq_span_vsub_set_right k (Set.mem_union_left _ (Set.mem_singleton _) : p ∈ _), eq_top_iff, ← h]
  apply Submodule.span_mono
  rintro v ⟨v', rfl⟩
  use (v' : V) +ᵥ p
  simp

variable (k)

/-- `affine_span` is monotone. -/
@[mono]
theorem affine_span_mono {s₁ s₂ : Set P} (h : s₁ ⊆ s₂) : affineSpan k s₁ ≤ affineSpan k s₂ :=
  span_points_subset_coe_of_subset_coe (Set.Subset.trans h (subset_affine_span k _))

/-- Taking the affine span of a set, adding a point and taking the
span again produces the same results as adding the point to the set
and taking the span. -/
theorem affine_span_insert_affine_span (p : P) (ps : Set P) :
    affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (insert p ps) := by
  rw [Set.insert_eq, Set.insert_eq, span_union, span_union, affine_span_coe]

/-- If a point is in the affine span of a set, adding it to that set
does not change the affine span. -/
theorem affine_span_insert_eq_affine_span {p : P} {ps : Set P} (h : p ∈ affineSpan k ps) :
    affineSpan k (insert p ps) = affineSpan k ps := by
  rw [← mem_coe] at h
  rw [← affine_span_insert_affine_span, Set.insert_eq_of_mem h, affine_span_coe]

end AffineSpace'

namespace AffineSubspace

variable {k : Type _} {V : Type _} {P : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V] [affine_space V P]

include V

/-- The direction of the sup of two nonempty affine subspaces is the
sup of the two directions and of any one difference between points in
the two subspaces. -/
theorem direction_sup {s1 s2 : AffineSubspace k P} {p1 p2 : P} (hp1 : p1 ∈ s1) (hp2 : p2 ∈ s2) :
    (s1⊔s2).direction = s1.direction⊔s2.direction⊔k∙p2 -ᵥ p1 := by
  refine' le_antisymmₓ _ _
  · change (affineSpan k ((s1 : Set P) ∪ s2)).direction ≤ _
    rw [← mem_coe] at hp1
    rw [direction_affine_span, vector_span_eq_span_vsub_set_right k (Set.mem_union_left _ hp1), Submodule.span_le]
    rintro v ⟨p3, hp3, rfl⟩
    cases hp3
    · rw [sup_assoc, sup_comm, SetLike.mem_coe, Submodule.mem_sup]
      use 0, Submodule.zero_mem _, p3 -ᵥ p1, vsub_mem_direction hp3 hp1
      rw [zero_addₓ]
      
    · rw [sup_assoc, SetLike.mem_coe, Submodule.mem_sup]
      use 0, Submodule.zero_mem _, p3 -ᵥ p1
      rw [and_comm, zero_addₓ]
      use rfl
      rw [← vsub_add_vsub_cancel p3 p2 p1, Submodule.mem_sup]
      use p3 -ᵥ p2, vsub_mem_direction hp3 hp2, p2 -ᵥ p1, Submodule.mem_span_singleton_self _
      
    
  · refine' sup_le (sup_direction_le _ _) _
    rw [direction_eq_vector_span, vector_span_def]
    exact
      Inf_le_Inf fun p hp =>
        Set.Subset.trans
          (Set.singleton_subset_iff.2
            (vsub_mem_vsub (mem_span_points k p2 _ (Set.mem_union_right _ hp2))
              (mem_span_points k p1 _ (Set.mem_union_left _ hp1))))
          hp
    

/-- The direction of the span of the result of adding a point to a
nonempty affine subspace is the sup of the direction of that subspace
and of any one difference between that point and a point in the
subspace. -/
theorem direction_affine_span_insert {s : AffineSubspace k P} {p1 p2 : P} (hp1 : p1 ∈ s) :
    (affineSpan k (insert p2 (s : Set P))).direction = Submodule.span k {p2 -ᵥ p1}⊔s.direction := by
  rw [sup_comm, ← Set.union_singleton, ← coe_affine_span_singleton k V p2]
  change (s⊔affineSpan k {p2}).direction = _
  rw [direction_sup hp1 (mem_affine_span k (Set.mem_singleton _)), direction_affine_span]
  simp

/-- Given a point `p1` in an affine subspace `s`, and a point `p2`, a
point `p` is in the span of `s` with `p2` added if and only if it is a
multiple of `p2 -ᵥ p1` added to a point in `s`. -/
theorem mem_affine_span_insert_iff {s : AffineSubspace k P} {p1 : P} (hp1 : p1 ∈ s) (p2 p : P) :
    p ∈ affineSpan k (insert p2 (s : Set P)) ↔ ∃ (r : k)(p0 : P)(hp0 : p0 ∈ s), p = r • (p2 -ᵥ p1 : V) +ᵥ p0 := by
  rw [← mem_coe] at hp1
  rw [← vsub_right_mem_direction_iff_mem (mem_affine_span k (Set.mem_insert_of_mem _ hp1)),
    direction_affine_span_insert hp1, Submodule.mem_sup]
  constructor
  · rintro ⟨v1, hv1, v2, hv2, hp⟩
    rw [Submodule.mem_span_singleton] at hv1
    rcases hv1 with ⟨r, rfl⟩
    use r, v2 +ᵥ p1, vadd_mem_of_mem_direction hv2 hp1
    symm'  at hp
    rw [← sub_eq_zero, ← vsub_vadd_eq_vsub_sub, vsub_eq_zero_iff_eq] at hp
    rw [hp, vadd_vadd]
    
  · rintro ⟨r, p3, hp3, rfl⟩
    use r • (p2 -ᵥ p1), Submodule.mem_span_singleton.2 ⟨r, rfl⟩, p3 -ᵥ p1, vsub_mem_direction hp3 hp1
    rw [vadd_vsub_assoc, add_commₓ]
    

end AffineSubspace

section MapComap

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type _} [Ringₓ k]

variable [AddCommGroupₓ V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroupₓ V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroupₓ V₃] [Module k V₃] [AddTorsor V₃ P₃]

include V₁ V₂

section

variable (f : P₁ →ᵃ[k] P₂)

@[simp]
theorem AffineMap.vector_span_image_eq_submodule_map {s : Set P₁} :
    Submodule.map f.linear (vectorSpan k s) = vectorSpan k (f '' s) := by
  simp [← f.image_vsub_image, ← vector_span_def]

namespace AffineSubspace

/-- The image of an affine subspace under an affine map as an affine subspace. -/
def map (s : AffineSubspace k P₁) : AffineSubspace k P₂ where
  Carrier := f '' s
  smul_vsub_vadd_mem := by
    rintro t - - - ⟨p₁, h₁, rfl⟩ ⟨p₂, h₂, rfl⟩ ⟨p₃, h₃, rfl⟩
    use t • (p₁ -ᵥ p₂) +ᵥ p₃
    suffices t • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ s by
      simp [← this]
    exact s.smul_vsub_vadd_mem t h₁ h₂ h₃

@[simp]
theorem coe_map (s : AffineSubspace k P₁) : (s.map f : Set P₂) = f '' s :=
  rfl

@[simp]
theorem mem_map {f : P₁ →ᵃ[k] P₂} {x : P₂} {s : AffineSubspace k P₁} : x ∈ s.map f ↔ ∃ y ∈ s, f y = x :=
  mem_image_iff_bex

@[simp]
theorem map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥ :=
  coe_injective <| image_empty f

omit V₂

@[simp]
theorem map_id (s : AffineSubspace k P₁) : s.map (AffineMap.id k P₁) = s :=
  coe_injective <| image_id _

include V₂ V₃

theorem map_map (s : AffineSubspace k P₁) (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P₃) : (s.map f).map g = s.map (g.comp f) :=
  coe_injective <| image_image _ _ _

omit V₃

@[simp]
theorem map_direction (s : AffineSubspace k P₁) : (s.map f).direction = s.direction.map f.linear := by
  simp [← direction_eq_vector_span]

theorem map_span (s : Set P₁) : (affineSpan k s).map f = affineSpan k (f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · simp
    
  apply ext_of_direction_eq
  · simp [← direction_affine_span]
    
  · exact ⟨f p, mem_image_of_mem f (subset_affine_span k _ hp), subset_affine_span k _ (mem_image_of_mem f hp)⟩
    

end AffineSubspace

namespace AffineMap

@[simp]
theorem map_top_of_surjective (hf : Function.Surjective f) : AffineSubspace.map f ⊤ = ⊤ := by
  rw [← AffineSubspace.ext_iff]
  exact image_univ_of_surjective hf

theorem span_eq_top_of_surjective {s : Set P₁} (hf : Function.Surjective f) (h : affineSpan k s = ⊤) :
    affineSpan k (f '' s) = ⊤ := by
  rw [← AffineSubspace.map_span, h, map_top_of_surjective f hf]

end AffineMap

namespace AffineEquiv

theorem span_eq_top_iff {s : Set P₁} (e : P₁ ≃ᵃ[k] P₂) : affineSpan k s = ⊤ ↔ affineSpan k (e '' s) = ⊤ := by
  refine' ⟨(e : P₁ →ᵃ[k] P₂).span_eq_top_of_surjective e.surjective, _⟩
  intro h
  have : s = e.symm '' (e '' s) := by
    simp [image_comp]
  rw [this]
  exact (e.symm : P₂ →ᵃ[k] P₁).span_eq_top_of_surjective e.symm.surjective h

end AffineEquiv

end

namespace AffineSubspace

/-- The preimage of an affine subspace under an affine map as an affine subspace. -/
def comap (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : AffineSubspace k P₁ where
  Carrier := f ⁻¹' s
  smul_vsub_vadd_mem := fun t p₁ p₂ p₃ (hp₁ : f p₁ ∈ s) (hp₂ : f p₂ ∈ s) (hp₃ : f p₃ ∈ s) =>
    show f _ ∈ s by
      rw [AffineMap.map_vadd, LinearMap.map_smul, AffineMap.linear_map_vsub]
      apply s.smul_vsub_vadd_mem _ hp₁ hp₂ hp₃

@[simp]
theorem coe_comap (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f : Set P₁) = f ⁻¹' ↑s :=
  rfl

@[simp]
theorem mem_comap {f : P₁ →ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₂} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_mono {f : P₁ →ᵃ[k] P₂} {s t : AffineSubspace k P₂} : s ≤ t → s.comap f ≤ t.comap f :=
  preimage_mono

@[simp]
theorem comap_top {f : P₁ →ᵃ[k] P₂} : (⊤ : AffineSubspace k P₂).comap f = ⊤ := by
  rw [← ext_iff]
  exact preimage_univ

omit V₂

@[simp]
theorem comap_id (s : AffineSubspace k P₁) : s.comap (AffineMap.id k P₁) = s :=
  coe_injective rfl

include V₂ V₃

theorem comap_comap (s : AffineSubspace k P₃) (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P₃) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  coe_injective rfl

omit V₃

-- lemmas about map and comap derived from the galois connection
theorem map_le_iff_le_comap {f : P₁ →ᵃ[k] P₂} {s : AffineSubspace k P₁} {t : AffineSubspace k P₂} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  image_subset_iff

theorem gc_map_comap (f : P₁ →ᵃ[k] P₂) : GaloisConnection (map f) (comap f) := fun _ _ => map_le_iff_le_comap

theorem map_comap_le (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f).map f ≤ s :=
  (gc_map_comap f).l_u_le _

theorem le_comap_map (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₁) : s ≤ (s.map f).comap f :=
  (gc_map_comap f).le_u_l _

theorem map_sup (s t : AffineSubspace k P₁) (f : P₁ →ᵃ[k] P₂) : (s⊔t).map f = s.map f⊔t.map f :=
  (gc_map_comap f).l_sup

theorem map_supr {ι : Sort _} (f : P₁ →ᵃ[k] P₂) (s : ι → AffineSubspace k P₁) : (supr s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_supr

theorem comap_inf (s t : AffineSubspace k P₂) (f : P₁ →ᵃ[k] P₂) : (s⊓t).comap f = s.comap f⊓t.comap f :=
  (gc_map_comap f).u_inf

theorem comap_supr {ι : Sort _} (f : P₁ →ᵃ[k] P₂) (s : ι → AffineSubspace k P₂) :
    (infi s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_infi

end AffineSubspace

end MapComap

