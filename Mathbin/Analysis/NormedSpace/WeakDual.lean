/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Yury Kudryashov
-/
import Mathbin.Topology.Algebra.Module.WeakDual
import Mathbin.Analysis.NormedSpace.Dual
import Mathbin.Analysis.NormedSpace.OperatorNorm

/-!
# Weak dual of normed space

Let `E` be a normed space over a field `𝕜`. This file is concerned with properties of the weak-*
topology on the dual of `E`. By the dual, we mean either of the type synonyms
`normed_space.dual 𝕜 E` or `weak_dual 𝕜 E`, depending on whether it is viewed as equipped with its
usual operator norm topology or the weak-* topology.

It is shown that the canonical mapping `normed_space.dual 𝕜 E → weak_dual 𝕜 E` is continuous, and
as a consequence the weak-* topology is coarser than the topology obtained from the operator norm
(dual norm).

In this file, we also establish the Banach-Alaoglu theorem about the compactness of closed balls
in the dual of `E` (as well as sets of somewhat more general form) with respect to the weak-*
topology.

## Main definitions

The main definitions concern the canonical mapping `dual 𝕜 E → weak_dual 𝕜 E`.

* `normed_space.dual.to_weak_dual` and `weak_dual.to_normed_dual`: Linear equivalences from
  `dual 𝕜 E` to `weak_dual 𝕜 E` and in the converse direction.
* `normed_space.dual.continuous_linear_map_to_weak_dual`: A continuous linear mapping from
  `dual 𝕜 E` to `weak_dual 𝕜 E` (same as `normed_space.dual.to_weak_dual` but different bundled
  data).

## Main results

The first main result concerns the comparison of the operator norm topology on `dual 𝕜 E` and the
weak-* topology on (its type synonym) `weak_dual 𝕜 E`:
* `dual_norm_topology_le_weak_dual_topology`: The weak-* topology on the dual of a normed space is
  coarser (not necessarily strictly) than the operator norm topology.
* `weak_dual.is_compact_polar` (a version of the Banach-Alaoglu theorem): The polar set of a
  neighborhood of the origin in a normed space `E` over `𝕜` is compact in `weak_dual _ E`, if the
  nondiscrete normed field `𝕜` is proper as a topological space.
* `weak_dual.is_compact_closed_ball` (the most common special case of the Banach-Alaoglu theorem):
  Closed balls in the dual of a normed space `E` over `ℝ` or `ℂ` are compact in the weak-star
  topology.

TODOs:
* Add that in finite dimensions, the weak-* topology and the dual norm topology coincide.
* Add that in infinite dimensions, the weak-* topology is strictly coarser than the dual norm
  topology.
* Add metrizability of the dual unit ball (more generally weak-star compact subsets) of
  `weak_dual 𝕜 E` under the assumption of separability of `E`.
* Add the sequential Banach-Alaoglu theorem: the dual unit ball of a separable normed space `E`
  is sequentially compact in the weak-star topology. This would follow from the metrizability above.

## Notations

No new notation is introduced.

## Implementation notes

Weak-* topology is defined generally in the file `topology.algebra.module.weak_dual`.

When `E` is a normed space, the duals `dual 𝕜 E` and `weak_dual 𝕜 E` are type synonyms with
different topology instances.

For the proof of Banach-Alaoglu theorem, the weak dual of `E` is embedded in the space of
functions `E → 𝕜` with the topology of pointwise convergence.

The polar set `polar 𝕜 s` of a subset `s` of `E` is originally defined as a subset of the dual
`dual 𝕜 E`. We care about properties of these w.r.t. weak-* topology, and for this purpose give
the definition `weak_dual.polar 𝕜 s` for the "same" subset viewed as a subset of `weak_dual 𝕜 E`
(a type synonym of the dual but with a different topology instance).

## References

* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology
* https://en.wikipedia.org/wiki/Banach%E2%80%93Alaoglu_theorem

## Tags

weak-star, weak dual

-/


noncomputable section

open Filter Function Metric Set

open TopologicalSpace Filter

/-!
### Weak star topology on duals of normed spaces

In this section, we prove properties about the weak-* topology on duals of normed spaces.
We prove in particular that the canonical mapping `dual 𝕜 E → weak_dual 𝕜 E` is continuous,
i.e., that the weak-* topology is coarser (not necessarily strictly) than the topology given
by the dual-norm (i.e. the operator-norm).
-/


variable {𝕜 : Type _} [NondiscreteNormedField 𝕜]

variable {E : Type _} [SemiNormedGroup E] [NormedSpace 𝕜 E]

namespace NormedSpace

namespace Dual

/-- For normed spaces `E`, there is a canonical map `dual 𝕜 E → weak_dual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
def toWeakDual : Dual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E :=
  LinearEquiv.refl 𝕜 (E →L[𝕜] 𝕜)

@[simp]
theorem coe_to_weak_dual (x' : Dual 𝕜 E) : ⇑x'.toWeakDual = x' :=
  rfl

@[simp]
theorem to_weak_dual_eq_iff (x' y' : Dual 𝕜 E) : x'.toWeakDual = y'.toWeakDual ↔ x' = y' :=
  toWeakDual.Injective.eq_iff

theorem to_weak_dual_continuous : Continuous fun x' : Dual 𝕜 E => x'.toWeakDual :=
  (WeakBilin.continuous_of_continuous_eval _) fun z => (inclusionInDoubleDual 𝕜 E z).Continuous

/-- For a normed space `E`, according to `to_weak_dual_continuous` the "identity mapping"
`dual 𝕜 E → weak_dual 𝕜 E` is continuous. This definition implements it as a continuous linear
map. -/
def continuousLinearMapToWeakDual : Dual 𝕜 E →L[𝕜] WeakDual 𝕜 E :=
  { toWeakDual with cont := to_weak_dual_continuous }

/-- The weak-star topology is coarser than the dual-norm topology. -/
theorem dual_norm_topology_le_weak_dual_topology :
    (by
        infer_instance : TopologicalSpace (Dual 𝕜 E)) ≤
      (by
        infer_instance : TopologicalSpace (WeakDual 𝕜 E)) :=
  by
  convert to_weak_dual_continuous.le_induced
  exact induced_id.symm

end Dual

end NormedSpace

namespace WeakDual

open NormedSpace

/-- For normed spaces `E`, there is a canonical map `weak_dual 𝕜 E → dual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. Here it is implemented as the inverse of the linear
equivalence `normed_space.dual.to_weak_dual` in the other direction. -/
def toNormedDual : WeakDual 𝕜 E ≃ₗ[𝕜] Dual 𝕜 E :=
  NormedSpace.Dual.toWeakDual.symm

theorem to_normed_dual_apply (x : WeakDual 𝕜 E) (y : E) : (toNormedDual x) y = x y :=
  rfl

@[simp]
theorem coe_to_normed_dual (x' : WeakDual 𝕜 E) : ⇑x'.toNormedDual = x' :=
  rfl

@[simp]
theorem to_normed_dual_eq_iff (x' y' : WeakDual 𝕜 E) : x'.toNormedDual = y'.toNormedDual ↔ x' = y' :=
  WeakDual.toNormedDual.Injective.eq_iff

theorem is_closed_closed_ball (x' : Dual 𝕜 E) (r : ℝ) : IsClosed (to_normed_dual ⁻¹' ClosedBall x' r) :=
  is_closed_induced_iff'.2 (ContinuousLinearMap.is_weak_closed_closed_ball x' r)

/-!
### Polar sets in the weak dual space
-/


variable (𝕜)

/-- The polar set `polar 𝕜 s` of `s : set E` seen as a subset of the dual of `E` with the
weak-star topology is `weak_dual.polar 𝕜 s`. -/
def Polar (s : Set E) : Set (WeakDual 𝕜 E) :=
  to_normed_dual ⁻¹' Polar 𝕜 s

theorem polar_def (s : Set E) : Polar 𝕜 s = { f : WeakDual 𝕜 E | ∀, ∀ x ∈ s, ∀, ∥f x∥ ≤ 1 } :=
  rfl

/-- The polar `polar 𝕜 s` of a set `s : E` is a closed subset when the weak star topology
is used. -/
theorem is_closed_polar (s : Set E) : IsClosed (Polar 𝕜 s) := by
  simp only [← polar_def, ← set_of_forall]
  exact is_closed_bInter fun x hx => is_closed_Iic.preimage (WeakBilin.eval_continuous _ _).norm

variable {𝕜}

/-- While the coercion `coe_fn : weak_dual 𝕜 E → (E → 𝕜)` is not a closed map, it sends *bounded*
closed sets to closed sets. -/
theorem is_closed_image_coe_of_bounded_of_closed {s : Set (WeakDual 𝕜 E)} (hb : Bounded (dual.to_weak_dual ⁻¹' s))
    (hc : IsClosed s) : IsClosed ((coeFn : WeakDual 𝕜 E → E → 𝕜) '' s) :=
  ContinuousLinearMap.is_closed_image_coe_of_bounded_of_weak_closed hb (is_closed_induced_iff'.1 hc)

theorem is_compact_of_bounded_of_closed [ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)}
    (hb : Bounded (dual.to_weak_dual ⁻¹' s)) (hc : IsClosed s) : IsCompact s :=
  (Embedding.is_compact_iff_is_compact_image FunLike.coe_injective.embedding_induced).mpr <|
    ContinuousLinearMap.is_compact_image_coe_of_bounded_of_closed_image hb <|
      is_closed_image_coe_of_bounded_of_closed hb hc

variable (𝕜)

/-- The image under `coe_fn : weak_dual 𝕜 E → (E → 𝕜)` of a polar `weak_dual.polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
theorem is_closed_image_polar_of_mem_nhds {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
    IsClosed ((coeFn : WeakDual 𝕜 E → E → 𝕜) '' Polar 𝕜 s) :=
  is_closed_image_coe_of_bounded_of_closed (bounded_polar_of_mem_nhds_zero 𝕜 s_nhd) (is_closed_polar _ _)

/-- The image under `coe_fn : normed_space.dual 𝕜 E → (E → 𝕜)` of a polar `polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
theorem _root_.normed_space.dual.is_closed_image_polar_of_mem_nhds {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
    IsClosed ((coeFn : Dual 𝕜 E → E → 𝕜) '' NormedSpace.Polar 𝕜 s) :=
  is_closed_image_polar_of_mem_nhds 𝕜 s_nhd

/-- The **Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origin in a
normed space `E` is a compact subset of `weak_dual 𝕜 E`. -/
theorem is_compact_polar [ProperSpace 𝕜] {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) : IsCompact (Polar 𝕜 s) :=
  is_compact_of_bounded_of_closed (bounded_polar_of_mem_nhds_zero 𝕜 s_nhd) (is_closed_polar _ _)

/-- The **Banach-Alaoglu theorem**: closed balls of the dual of a normed space `E` are compact in
the weak-star topology. -/
theorem is_compact_closed_ball [ProperSpace 𝕜] (x' : Dual 𝕜 E) (r : ℝ) :
    IsCompact (to_normed_dual ⁻¹' ClosedBall x' r) :=
  is_compact_of_bounded_of_closed bounded_closed_ball (is_closed_closed_ball x' r)

end WeakDual

