/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.Topology.Homeomorph

/-!
# Topological space structure on the opposite monoid and on the units group

In this file we define `topological_space` structure on `Mᵐᵒᵖ`, `Mᵃᵒᵖ`, `Mˣ`, and `add_units M`.
This file does not import definitions of a topological monoid and/or a continuous multiplicative
action, so we postpone the proofs of `has_continuous_mul Mᵐᵒᵖ` etc till we have these definitions.

## Tags

topological space, opposite monoid, units
-/


variable {M X : Type _}

open Filter

open TopologicalSpace

namespace MulOpposite

/-- Put the same topological space structure on the opposite monoid as on the original space. -/
@[to_additive]
instance [TopologicalSpace M] : TopologicalSpace Mᵐᵒᵖ :=
  TopologicalSpace.induced (unop : Mᵐᵒᵖ → M) ‹_›

variable [TopologicalSpace M]

@[continuity, to_additive]
theorem continuous_unop : Continuous (unop : Mᵐᵒᵖ → M) :=
  continuous_induced_dom

@[continuity, to_additive]
theorem continuous_op : Continuous (op : M → Mᵐᵒᵖ) :=
  continuous_induced_rng continuous_id

@[to_additive]
instance [T2Space M] : T2Space Mᵐᵒᵖ :=
  ⟨fun x y h => separated_by_continuous MulOpposite.continuous_unop <| unop_injective.Ne h⟩

/-- `mul_opposite.op` as a homeomorphism. -/
@[to_additive "`add_opposite.op` as a homeomorphism."]
def opHomeomorph : M ≃ₜ Mᵐᵒᵖ where
  toEquiv := opEquiv
  continuous_to_fun := continuous_op
  continuous_inv_fun := continuous_unop

@[simp, to_additive]
theorem map_op_nhds (x : M) : map (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.map_nhds_eq x

@[simp, to_additive]
theorem map_unop_nhds (x : Mᵐᵒᵖ) : map (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.symm.map_nhds_eq x

@[simp, to_additive]
theorem comap_op_nhds (x : Mᵐᵒᵖ) : comap (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.comap_nhds_eq x

@[simp, to_additive]
theorem comap_unop_nhds (x : M) : comap (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.symm.comap_nhds_eq x

end MulOpposite

namespace Units

open MulOpposite

variable [TopologicalSpace M] [Monoidₓ M]

/-- The units of a monoid are equipped with a topology, via the embedding into `M × M`. -/
@[to_additive]
instance : TopologicalSpace Mˣ :=
  TopologicalSpace.induced (embedProduct M) Prod.topologicalSpace

@[to_additive]
theorem continuous_embed_product : Continuous (embedProduct M) :=
  continuous_induced_dom

@[to_additive]
theorem continuous_coe : Continuous (coe : Mˣ → M) :=
  (@continuous_embed_product M _ _).fst

end Units

