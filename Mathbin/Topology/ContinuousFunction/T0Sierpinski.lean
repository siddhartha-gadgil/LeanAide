/-
Copyright (c) 2022 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
import Mathbin.Topology.Order
import Mathbin.Topology.Sets.Opens
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Any T0 space embeds in a product of copies of the Sierpinski space.

We consider `Prop` with the Sierpinski topology. If `X` is a topological space, there is a
continuous map `product_of_mem_opens` from `X` to `opens X → Prop` which is the product of the maps
`X → Prop` given by `x ↦ x ∈ u`.

The map `product_of_mem_opens` is always inducing. Whenever `X` is T0, `product_of_mem_opens` is
also injective and therefore an embedding.
-/


noncomputable section

namespace TopologicalSpace

theorem eq_induced_by_maps_to_sierpinski (X : Type _) [t : TopologicalSpace X] :
    t = ⨅ u : Opens X, sierpinskiSpace.induced (· ∈ u) := by
  apply le_antisymmₓ
  · rw [le_infi_iff]
    exact fun u => Continuous.le_induced (is_open_iff_continuous_mem.mp u.2)
    
  · intro u h
    rw [← generate_from_Union_is_open]
    apply is_open_generate_from_of_mem
    simp only [← Set.mem_Union, ← Set.mem_set_of_eq, ← is_open_induced_iff']
    exact
      ⟨⟨u, h⟩, {True}, is_open_singleton_true, by
        simp [← Set.Preimage]⟩
    

variable (X : Type _) [TopologicalSpace X]

/-- The continuous map from `X` to the product of copies of the Sierpinski space, (one copy for each
open subset `u` of `X`). The `u` coordinate of `product_of_mem_opens x` is given by `x ∈ u`.
-/
def productOfMemOpens : ContinuousMap X (Opens X → Prop) where
  toFun := fun x u => x ∈ u
  continuous_to_fun := continuous_pi_iff.2 fun u => continuous_Prop.2 u.property

theorem product_of_mem_opens_inducing : Inducing (productOfMemOpens X) := by
  convert inducing_infi_to_pi fun (u : opens X) (x : X) => x ∈ u
  apply eq_induced_by_maps_to_sierpinski

theorem product_of_mem_opens_injective [T0Space X] : Function.Injective (productOfMemOpens X) := by
  intro x1 x2 h
  apply Inseparable.eq
  rw [← Inducing.inseparable_iff (product_of_mem_opens_inducing X), h]

theorem product_of_mem_opens_embedding [T0Space X] : Embedding (productOfMemOpens X) :=
  Embedding.mk (product_of_mem_opens_inducing X) (product_of_mem_opens_injective X)

end TopologicalSpace

