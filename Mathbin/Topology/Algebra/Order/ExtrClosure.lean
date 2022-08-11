/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Topology.LocalExtr
import Mathbin.Topology.Algebra.Order.Basic

/-!
# Maximum/minimum on the closure of a set

In this file we prove several versions of the following statement: if `f : X → Y` has a (local or
not) maximum (or minimum) on a set `s` at a point `a` and is continuous on the closure of `s`, then
`f` has an extremum of the same type on `closure s` at `a`.
-/


open Filter Set

open TopologicalSpace

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] [Preorderₓ Y] [OrderClosedTopology Y] {f g : X → Y}
  {s : Set X} {a : X}

protected theorem IsMaxOn.closure (h : IsMaxOn f s a) (hc : ContinuousOn f (Closure s)) : IsMaxOn f (Closure s) a :=
  fun x hx => ContinuousWithinAt.closure_le hx ((hc x hx).mono subset_closure) continuous_within_at_const h

protected theorem IsMinOn.closure (h : IsMinOn f s a) (hc : ContinuousOn f (Closure s)) : IsMinOn f (Closure s) a :=
  h.dual.closure hc

protected theorem IsExtrOn.closure (h : IsExtrOn f s a) (hc : ContinuousOn f (Closure s)) : IsExtrOn f (Closure s) a :=
  h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr <| h.closure hc

protected theorem IsLocalMaxOn.closure (h : IsLocalMaxOn f s a) (hc : ContinuousOn f (Closure s)) :
    IsLocalMaxOn f (Closure s) a := by
  rcases mem_nhds_within.1 h with ⟨U, Uo, aU, hU⟩
  refine' mem_nhds_within.2 ⟨U, Uo, aU, _⟩
  rintro x ⟨hxU, hxs⟩
  refine' ContinuousWithinAt.closure_le _ _ continuous_within_at_const hU
  · rwa [mem_closure_iff_nhds_within_ne_bot, nhds_within_inter_of_mem, ← mem_closure_iff_nhds_within_ne_bot]
    exact nhds_within_le_nhds (Uo.mem_nhds hxU)
    
  · exact (hc _ hxs).mono ((inter_subset_right _ _).trans subset_closure)
    

protected theorem IsLocalMinOn.closure (h : IsLocalMinOn f s a) (hc : ContinuousOn f (Closure s)) :
    IsLocalMinOn f (Closure s) a :=
  IsLocalMaxOn.closure h.dual hc

protected theorem IsLocalExtrOn.closure (h : IsLocalExtrOn f s a) (hc : ContinuousOn f (Closure s)) :
    IsLocalExtrOn f (Closure s) a :=
  h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr <| h.closure hc

