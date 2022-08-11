/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Mathbin.Analysis.Convex.Contractible
import Mathbin.Analysis.Convex.Topology
import Mathbin.Analysis.Convex.Complex
import Mathbin.Analysis.Complex.ReImTopology
import Mathbin.Topology.Homotopy.Contractible

/-!
# Topology on the upper half plane

In this file we introduce a `topological_space` structure on the upper half plane and provide
various instances.
-/


noncomputable section

open Set Filter Function TopologicalSpace Complex

open Filter TopologicalSpace UpperHalfPlane

namespace UpperHalfPlane

instance : TopologicalSpace ℍ :=
  Subtype.topologicalSpace

theorem open_embedding_coe : OpenEmbedding (coe : ℍ → ℂ) :=
  IsOpen.open_embedding_subtype_coe <| is_open_lt continuous_const Complex.continuous_im

theorem embedding_coe : Embedding (coe : ℍ → ℂ) :=
  embedding_subtype_coe

theorem continuous_coe : Continuous (coe : ℍ → ℂ) :=
  embedding_coe.Continuous

theorem continuous_re : Continuous re :=
  Complex.continuous_re.comp continuous_coe

theorem continuous_im : Continuous im :=
  Complex.continuous_im.comp continuous_coe

instance : TopologicalSpace.SecondCountableTopology ℍ :=
  TopologicalSpace.Subtype.second_countable_topology _ _

instance : T3Space ℍ :=
  Subtype.t3_space

instance : NormalSpace ℍ :=
  normal_space_of_t3_second_countable ℍ

instance : ContractibleSpace ℍ :=
  (convex_halfspace_im_gt 0).ContractibleSpace ⟨i, one_pos.trans_eq I_im.symm⟩

instance : LocPathConnectedSpace ℍ :=
  loc_path_connected_of_is_open <| is_open_lt continuous_const Complex.continuous_im

instance : NoncompactSpace ℍ := by
  refine' ⟨fun h => _⟩
  have : IsCompact (Complex.im ⁻¹' Ioi 0) := is_compact_iff_is_compact_univ.2 h
  replace := this.is_closed.closure_eq
  rw [closure_preimage_im, closure_Ioi, Set.ext_iff] at this
  exact absurd ((this 0).1 left_mem_Ici) (lt_irreflₓ _)

instance : LocallyCompactSpace ℍ :=
  open_embedding_coe.LocallyCompactSpace

end UpperHalfPlane

