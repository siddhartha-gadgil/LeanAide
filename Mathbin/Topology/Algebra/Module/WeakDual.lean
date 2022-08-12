/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
import Mathbin.Topology.Algebra.Module.Basic

/-!
# Weak dual topology

This file defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `λ x, B x y` is continuous.

In the case that `F = E →L[𝕜] 𝕜` and `B` being the canonical pairing, we obtain the weak-* topology,
`weak_dual 𝕜 E := (E →L[𝕜] 𝕜)`. Interchanging the arguments in the bilinear form yields the
weak topology `weak_space 𝕜 E := E`.

## Main definitions

The main definitions are the types `weak_bilin B` for the general case and the two special cases
`weak_dual 𝕜 E` and `weak_space 𝕜 E` with the respective topology instances on it.

* Given `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the type `weak_bilin B` is a type synonym for `E`.
* The instance `weak_bilin.topological_space` is the weak topology induced by the bilinear form `B`.
* `weak_dual 𝕜 E` is a type synonym for `dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `weak_dual.topological_space` is the weak-* topology on `weak_dual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `weak_space 𝕜 E` is a type synonym for `E` (when the latter is defined).
* The instance `weak_dual.topological_space` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : dual 𝕜 E` remain continuous.

## Main results

We establish that `weak_bilin B` has the following structure:
* `weak_bilin.has_continuous_add`: The addition in `weak_bilin B` is continuous.
* `weak_bilin.has_continuous_smul`: The scalar multiplication in `weak_bilin B` is continuous.

We prove the following results characterizing the weak topology:
* `eval_continuous`: For any `y : F`, the evaluation mapping `λ x, B x y` is continuous.
* `continuous_of_continuous_eval`: For a mapping to `weak_bilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `tendsto_iff_forall_eval_tendsto`: Convergence in `weak_bilin B` can be characterized
  in terms of convergence of the evaluations at all points `y : F`.

## Notations

No new notation is introduced.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/


noncomputable section

open Filter

open TopologicalSpace

variable {α 𝕜 𝕝 R E F M : Type _}

section WeakTopology

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module 𝕜
/-- The space `E` equipped with the weak topology induced by the bilinear form `B`. -/
@[nolint has_inhabited_instance unused_arguments]
def WeakBilin [CommSemiringₓ 𝕜] [AddCommMonoidₓ E] [Module 𝕜 E] [AddCommMonoidₓ F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :=
  E deriving AddCommMonoidₓ, «./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module 𝕜»

namespace WeakBilin

instance [CommSemiringₓ 𝕜] [a : AddCommGroupₓ E] [Module 𝕜 E] [AddCommMonoidₓ F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    AddCommGroupₓ (WeakBilin B) :=
  a

instance (priority := 100) module' [CommSemiringₓ 𝕜] [CommSemiringₓ 𝕝] [AddCommGroupₓ E] [Module 𝕜 E] [AddCommGroupₓ F]
    [Module 𝕜 F] [m : Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Module 𝕝 (WeakBilin B) :=
  m

instance [CommSemiringₓ 𝕜] [CommSemiringₓ 𝕝] [AddCommGroupₓ E] [Module 𝕜 E] [AddCommGroupₓ F] [Module 𝕜 F] [HasSmul 𝕝 𝕜]
    [Module 𝕝 E] [s : IsScalarTower 𝕝 𝕜 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : IsScalarTower 𝕝 𝕜 (WeakBilin B) :=
  s

section Semiringₓ

variable [TopologicalSpace 𝕜] [CommSemiringₓ 𝕜]

variable [AddCommMonoidₓ E] [Module 𝕜 E]

variable [AddCommMonoidₓ F] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

instance : TopologicalSpace (WeakBilin B) :=
  TopologicalSpace.induced (fun x y => B x y) Pi.topologicalSpace

theorem coe_fn_continuous : Continuous fun (x : WeakBilin B) y => B x y :=
  continuous_induced_dom

theorem eval_continuous (y : F) : Continuous fun x : WeakBilin B => B x y :=
  (continuous_pi_iff.mp (coe_fn_continuous B)) y

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakBilin B}
    (h : ∀ y, Continuous fun a => B (g a) y) : Continuous g :=
  continuous_induced_rng (continuous_pi_iff.mpr h)

/-- The coercion `(λ x y, B x y) : E → (F → 𝕜)` is an embedding. -/
theorem embedding {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : Function.Injective B) : Embedding fun (x : WeakBilin B) y => B x y :=
  Function.Injective.embedding_induced <| LinearMap.coe_injective.comp hB

theorem tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α → WeakBilin B} {x : WeakBilin B}
    (hB : Function.Injective B) : Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i => B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds, Embedding.tendsto_nhds_iff (Embedding hB)]

/-- Addition in `weak_space B` is continuous. -/
instance [HasContinuousAdd 𝕜] : HasContinuousAdd (WeakBilin B) := by
  refine' ⟨continuous_induced_rng _⟩
  refine'
    cast (congr_arg _ _) (((coe_fn_continuous B).comp continuous_fst).add ((coe_fn_continuous B).comp continuous_snd))
  ext
  simp only [← Function.comp_app, ← Pi.add_apply, ← map_add, ← LinearMap.add_apply]

/-- Scalar multiplication by `𝕜` on `weak_bilin B` is continuous. -/
instance [HasContinuousSmul 𝕜 𝕜] : HasContinuousSmul 𝕜 (WeakBilin B) := by
  refine' ⟨continuous_induced_rng _⟩
  refine' cast (congr_arg _ _) (continuous_fst.smul ((coe_fn_continuous B).comp continuous_snd))
  ext
  simp only [← Function.comp_app, ← Pi.smul_apply, ← LinearMap.map_smulₛₗ, ← RingHom.id_apply, ← LinearMap.smul_apply]

end Semiringₓ

section Ringₓ

variable [TopologicalSpace 𝕜] [CommRingₓ 𝕜]

variable [AddCommGroupₓ E] [Module 𝕜 E]

variable [AddCommGroupₓ F] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- `weak_space B` is a `topological_add_group`, meaning that addition and negation are
continuous. -/
instance [HasContinuousAdd 𝕜] : TopologicalAddGroup (WeakBilin B) where
  to_has_continuous_add := by
    infer_instance
  continuous_neg := by
    refine' continuous_induced_rng (continuous_pi_iff.mpr fun y => _)
    refine' cast (congr_arg _ _) (eval_continuous B (-y))
    ext
    simp only [← map_neg, ← Function.comp_app, ← LinearMap.neg_apply]

end Ringₓ

end WeakBilin

end WeakTopology

section WeakStarTopology

/-- The canonical pairing of a vector space and its topological dual. -/
def topDualPairing (𝕜 E) [CommSemiringₓ 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜] [AddCommMonoidₓ E] [Module 𝕜 E]
    [TopologicalSpace E] [HasContinuousConstSmul 𝕜 𝕜] : (E →L[𝕜] 𝕜) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLm 𝕜

variable [CommSemiringₓ 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜]

variable [HasContinuousConstSmul 𝕜 𝕜]

variable [AddCommMonoidₓ E] [Module 𝕜 E] [TopologicalSpace E]

theorem dual_pairing_apply (v : E →L[𝕜] 𝕜) (x : E) : topDualPairing 𝕜 E v x = v x :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module 𝕜
/-- The weak star topology is the topology coarsest topology on `E →L[𝕜] 𝕜` such that all
functionals `λ v, top_dual_pairing 𝕜 E v x` are continuous. -/
def WeakDual (𝕜 E) [CommSemiringₓ 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜] [HasContinuousConstSmul 𝕜 𝕜]
    [AddCommMonoidₓ E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E)deriving AddCommMonoidₓ,
  «./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module 𝕜», TopologicalSpace,
  HasContinuousAdd

namespace WeakDual

instance : Inhabited (WeakDual 𝕜 E) :=
  ContinuousLinearMap.inhabited

instance WeakDual.continuousLinearMapClass : ContinuousLinearMapClass (WeakDual 𝕜 E) 𝕜 E 𝕜 :=
  ContinuousLinearMap.continuousSemilinearMapClass

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (WeakDual 𝕜 E) fun _ => E → 𝕜 :=
  FunLike.hasCoeToFun

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts on `weak_dual 𝕜 E`. -/
instance (M) [Monoidₓ M] [DistribMulAction M 𝕜] [SmulCommClass 𝕜 M 𝕜] [HasContinuousConstSmul M 𝕜] :
    MulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.mulAction

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts distributively on `weak_dual 𝕜 E`. -/
instance (M) [Monoidₓ M] [DistribMulAction M 𝕜] [SmulCommClass 𝕜 M 𝕜] [HasContinuousConstSmul M 𝕜] :
    DistribMulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.distribMulAction

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `weak_dual 𝕜 E` is a module over `R`. -/
instance module' (R) [Semiringₓ R] [Module R 𝕜] [SmulCommClass 𝕜 R 𝕜] [HasContinuousConstSmul R 𝕜] :
    Module R (WeakDual 𝕜 E) :=
  ContinuousLinearMap.module

instance (M) [Monoidₓ M] [DistribMulAction M 𝕜] [SmulCommClass 𝕜 M 𝕜] [HasContinuousConstSmul M 𝕜] :
    HasContinuousConstSmul M (WeakDual 𝕜 E) :=
  ⟨fun m => continuous_induced_rng <| (WeakBilin.coe_fn_continuous (topDualPairing 𝕜 E)).const_smul m⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it continuously acts on `weak_dual 𝕜 E`. -/
instance (M) [Monoidₓ M] [DistribMulAction M 𝕜] [SmulCommClass 𝕜 M 𝕜] [TopologicalSpace M] [HasContinuousSmul M 𝕜] :
    HasContinuousSmul M (WeakDual 𝕜 E) :=
  ⟨continuous_induced_rng <|
      continuous_fst.smul ((WeakBilin.coe_fn_continuous (topDualPairing 𝕜 E)).comp continuous_snd)⟩

theorem coe_fn_continuous : Continuous fun (x : WeakDual 𝕜 E) y => x y :=
  continuous_induced_dom

theorem eval_continuous (y : E) : Continuous fun x : WeakDual 𝕜 E => x y :=
  continuous_pi_iff.mp coe_fn_continuous y

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
    (h : ∀ y, Continuous fun a => (g a) y) : Continuous g :=
  continuous_induced_rng (continuous_pi_iff.mpr h)

end WeakDual

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module 𝕜
/-- The weak topology is the topology coarsest topology on `E` such that all
functionals `λ x, top_dual_pairing 𝕜 E v x` are continuous. -/
@[nolint has_inhabited_instance]
def WeakSpace (𝕜 E) [CommSemiringₓ 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜] [HasContinuousConstSmul 𝕜 𝕜]
    [AddCommMonoidₓ E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E).flip deriving AddCommMonoidₓ,
  «./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module 𝕜», TopologicalSpace,
  HasContinuousAdd

theorem tendsto_iff_forall_eval_tendsto_top_dual_pairing {l : Filter α} {f : α → WeakDual 𝕜 E} {x : WeakDual 𝕜 E} :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i => topDualPairing 𝕜 E (f i) y) l (𝓝 (topDualPairing 𝕜 E x y)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective

end WeakStarTopology

