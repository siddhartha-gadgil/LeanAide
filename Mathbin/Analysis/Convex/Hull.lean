/-
Copyright (c) 2020 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Yaël Dillies
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Order.Closure

/-!
# Convex hull

This file defines the convex hull of a set `s` in a module. `convex_hull 𝕜 s` is the smallest convex
set containing `s`. In order theory speak, this is a closure operator.

## Implementation notes

`convex_hull` is defined as a closure operator. This gives access to the `closure_operator` API
while the impact on writing code is minimal as `convex_hull 𝕜 s` is automatically elaborated as
`⇑(convex_hull 𝕜) s`.
-/


open Set

open Pointwise

variable {𝕜 E F : Type _}

section convexHull

section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoidₓ

variable (𝕜) [AddCommMonoidₓ E] [AddCommMonoidₓ F] [Module 𝕜 E] [Module 𝕜 F]

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convexHull : ClosureOperator (Set E) :=
  ClosureOperator.mk₃ (fun s => ⋂ (t : Set E) (hst : s ⊆ t) (ht : Convex 𝕜 t), t) (Convex 𝕜)
    (fun s => Set.subset_Inter fun t => Set.subset_Inter fun hst => Set.subset_Inter fun ht => hst)
    (fun s => convex_Inter fun t => convex_Inter fun ht => convex_Inter id) fun s t hst ht =>
    Set.Inter_subset_of_subset t <| Set.Inter_subset_of_subset hst <| Set.Inter_subset _ ht

variable (s : Set E)

theorem subset_convex_hull : s ⊆ convexHull 𝕜 s :=
  (convexHull 𝕜).le_closure s

theorem convex_convex_hull : Convex 𝕜 (convexHull 𝕜 s) :=
  ClosureOperator.closure_mem_mk₃ s

theorem convex_hull_eq_Inter : convexHull 𝕜 s = ⋂ (t : Set E) (hst : s ⊆ t) (ht : Convex 𝕜 t), t :=
  rfl

variable {𝕜 s} {t : Set E} {x y : E}

theorem mem_convex_hull_iff : x ∈ convexHull 𝕜 s ↔ ∀ t, s ⊆ t → Convex 𝕜 t → x ∈ t := by
  simp_rw [convex_hull_eq_Inter, mem_Inter]

theorem convex_hull_min (hst : s ⊆ t) (ht : Convex 𝕜 t) : convexHull 𝕜 s ⊆ t :=
  ClosureOperator.closure_le_mk₃_iff (show s ≤ t from hst) ht

theorem Convex.convex_hull_subset_iff (ht : Convex 𝕜 t) : convexHull 𝕜 s ⊆ t ↔ s ⊆ t :=
  ⟨(subset_convex_hull _ _).trans, fun h => convex_hull_min h ht⟩

@[mono]
theorem convex_hull_mono (hst : s ⊆ t) : convexHull 𝕜 s ⊆ convexHull 𝕜 t :=
  (convexHull 𝕜).Monotone hst

theorem Convex.convex_hull_eq (hs : Convex 𝕜 s) : convexHull 𝕜 s = s :=
  ClosureOperator.mem_mk₃_closed hs

@[simp]
theorem convex_hull_univ : convexHull 𝕜 (Univ : Set E) = univ :=
  ClosureOperator.closure_top (convexHull 𝕜)

@[simp]
theorem convex_hull_empty : convexHull 𝕜 (∅ : Set E) = ∅ :=
  convex_empty.convex_hull_eq

@[simp]
theorem convex_hull_empty_iff : convexHull 𝕜 s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    rw [← Set.subset_empty_iff, ← h]
    exact subset_convex_hull 𝕜 _
    
  · rintro rfl
    exact convex_hull_empty
    

@[simp]
theorem convex_hull_nonempty_iff : (convexHull 𝕜 s).Nonempty ↔ s.Nonempty := by
  rw [← ne_empty_iff_nonempty, ← ne_empty_iff_nonempty, Ne.def, Ne.def]
  exact not_congr convex_hull_empty_iff

alias convex_hull_nonempty_iff ↔ _ Set.Nonempty.convex_hull

attribute [protected] Set.Nonempty.convex_hull

theorem segment_subset_convex_hull (hx : x ∈ s) (hy : y ∈ s) : Segment 𝕜 x y ⊆ convexHull 𝕜 s :=
  (convex_convex_hull _ _).segment_subset (subset_convex_hull _ _ hx) (subset_convex_hull _ _ hy)

@[simp]
theorem convex_hull_singleton (x : E) : convexHull 𝕜 ({x} : Set E) = {x} :=
  (convex_singleton x).convex_hull_eq

@[simp]
theorem convex_hull_pair (x y : E) : convexHull 𝕜 {x, y} = Segment 𝕜 x y := by
  refine'
    (convex_hull_min _ <| convex_segment _ _).antisymm
      (segment_subset_convex_hull (mem_insert _ _) <| mem_insert_of_mem _ <| mem_singleton _)
  rw [insert_subset, singleton_subset_iff]
  exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩

theorem convex_hull_convex_hull_union_left (s t : Set E) : convexHull 𝕜 (convexHull 𝕜 s ∪ t) = convexHull 𝕜 (s ∪ t) :=
  ClosureOperator.closure_sup_closure_left _ _ _

theorem convex_hull_convex_hull_union_right (s t : Set E) : convexHull 𝕜 (s ∪ convexHull 𝕜 t) = convexHull 𝕜 (s ∪ t) :=
  ClosureOperator.closure_sup_closure_right _ _ _

theorem Convex.convex_remove_iff_not_mem_convex_hull_remove {s : Set E} (hs : Convex 𝕜 s) (x : E) :
    Convex 𝕜 (s \ {x}) ↔ x ∉ convexHull 𝕜 (s \ {x}) := by
  constructor
  · rintro hsx hx
    rw [hsx.convex_hull_eq] at hx
    exact hx.2 (mem_singleton _)
    
  rintro hx
  suffices h : s \ {x} = convexHull 𝕜 (s \ {x})
  · convert convex_convex_hull 𝕜 _
    
  exact
    subset.antisymm (subset_convex_hull 𝕜 _) fun y hy =>
      ⟨convex_hull_min (diff_subset _ _) hs hy, by
        rintro (rfl : y = x)
        exact hx hy⟩

theorem IsLinearMap.convex_hull_image {f : E → F} (hf : IsLinearMap 𝕜 f) (s : Set E) :
    convexHull 𝕜 (f '' s) = f '' convexHull 𝕜 s :=
  Set.Subset.antisymm
    (convex_hull_min (image_subset _ (subset_convex_hull 𝕜 s)) <| (convex_convex_hull 𝕜 s).is_linear_image hf)
    (image_subset_iff.2 <|
      convex_hull_min (image_subset_iff.1 <| subset_convex_hull 𝕜 _) ((convex_convex_hull 𝕜 _).is_linear_preimage hf))

theorem LinearMap.convex_hull_image (f : E →ₗ[𝕜] F) (s : Set E) : convexHull 𝕜 (f '' s) = f '' convexHull 𝕜 s :=
  f.is_linear.convex_hull_image s

end AddCommMonoidₓ

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜] [AddCommMonoidₓ E] [Module 𝕜 E]

theorem convex_hull_smul (a : 𝕜) (s : Set E) : convexHull 𝕜 (a • s) = a • convexHull 𝕜 s :=
  (LinearMap.lsmul _ _ a).convex_hull_image _

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing 𝕜]

section AddCommGroupₓ

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F] (s : Set E)

theorem AffineMap.image_convex_hull (f : E →ᵃ[𝕜] F) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) := by
  apply Set.Subset.antisymm
  · rw [Set.image_subset_iff]
    refine' convex_hull_min _ ((convex_convex_hull 𝕜 (⇑f '' s)).affine_preimage f)
    rw [← Set.image_subset_iff]
    exact subset_convex_hull 𝕜 (f '' s)
    
  · exact convex_hull_min (Set.image_subset _ (subset_convex_hull 𝕜 s)) ((convex_convex_hull 𝕜 s).affine_image f)
    

theorem convex_hull_subset_affine_span : convexHull 𝕜 s ⊆ (affineSpan 𝕜 s : Set E) :=
  convex_hull_min (subset_affine_span 𝕜 s) (affineSpan 𝕜 s).Convex

@[simp]
theorem affine_span_convex_hull : affineSpan 𝕜 (convexHull 𝕜 s) = affineSpan 𝕜 s := by
  refine' le_antisymmₓ _ (affine_span_mono 𝕜 (subset_convex_hull 𝕜 s))
  rw [affine_span_le]
  exact convex_hull_subset_affine_span s

theorem convex_hull_neg (s : Set E) : convexHull 𝕜 (-s) = -convexHull 𝕜 s := by
  simp_rw [← image_neg]
  exact (AffineMap.image_convex_hull _ <| -1).symm

end AddCommGroupₓ

end OrderedRing

end convexHull

