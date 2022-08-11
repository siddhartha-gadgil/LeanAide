/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Star.Pi
import Mathbin.Algebra.Star.Prod
import Mathbin.Topology.Algebra.Group

/-!
# Continuity of `star`

This file defines the `has_continuous_star` typeclass, along with instances on `pi`, `prod`,
`mul_opposite`, and `units`.
-/


open Filter TopologicalSpace

open Filter

universe u

variable {ι α R S : Type _}

/-- Basic hypothesis to talk about a topological space with a continuous `star` operator. -/
class HasContinuousStar (R : Type u) [TopologicalSpace R] [HasStar R] : Prop where
  continuous_star : Continuous (star : R → R)

export HasContinuousStar (continuous_star)

section Continuity

variable [TopologicalSpace R] [HasStar R] [HasContinuousStar R]

theorem continuous_on_star {s : Set R} : ContinuousOn star s :=
  continuous_star.ContinuousOn

theorem continuous_within_at_star {s : Set R} {x : R} : ContinuousWithinAt star s x :=
  continuous_star.ContinuousWithinAt

theorem continuous_at_star {x : R} : ContinuousAt star x :=
  continuous_star.ContinuousAt

theorem tendsto_star (a : R) : Tendsto star (𝓝 a) (𝓝 (star a)) :=
  continuous_at_star

theorem Filter.Tendsto.star {f : α → R} {l : Filter α} {y : R} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => star (f x)) l (𝓝 (star y)) :=
  (continuous_star.Tendsto y).comp h

variable [TopologicalSpace α] {f : α → R} {s : Set α} {x : α}

@[continuity]
theorem Continuous.star (hf : Continuous f) : Continuous fun x => star (f x) :=
  continuous_star.comp hf

theorem ContinuousAt.star (hf : ContinuousAt f x) : ContinuousAt (fun x => star (f x)) x :=
  continuous_at_star.comp hf

theorem ContinuousOn.star (hf : ContinuousOn f s) : ContinuousOn (fun x => star (f x)) s :=
  continuous_star.comp_continuous_on hf

theorem ContinuousWithinAt.star (hf : ContinuousWithinAt f s x) : ContinuousWithinAt (fun x => star (f x)) s x :=
  hf.star

/-- The star operation bundled as a continuous map. -/
@[simps]
def starContinuousMap : C(R, R) :=
  ⟨star, continuous_star⟩

end Continuity

section Instances

instance [HasStar R] [HasStar S] [TopologicalSpace R] [TopologicalSpace S] [HasContinuousStar R] [HasContinuousStar S] :
    HasContinuousStar (R × S) :=
  ⟨(continuous_star.comp continuous_fst).prod_mk (continuous_star.comp continuous_snd)⟩

instance {C : ι → Type _} [∀ i, TopologicalSpace (C i)] [∀ i, HasStar (C i)] [∀ i, HasContinuousStar (C i)] :
    HasContinuousStar (∀ i, C i) where continuous_star := continuous_pi fun i => Continuous.star (continuous_apply i)

instance [HasStar R] [TopologicalSpace R] [HasContinuousStar R] : HasContinuousStar Rᵐᵒᵖ :=
  ⟨MulOpposite.continuous_op.comp <| MulOpposite.continuous_unop.star⟩

instance [Monoidₓ R] [StarSemigroup R] [TopologicalSpace R] [HasContinuousStar R] : HasContinuousStar Rˣ :=
  ⟨continuous_induced_rng Units.continuous_embed_product.star⟩

end Instances

