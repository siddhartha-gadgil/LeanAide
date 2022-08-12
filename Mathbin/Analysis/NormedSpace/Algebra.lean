/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Topology.Algebra.Module.CharacterSpace
import Mathbin.Analysis.NormedSpace.WeakDual
import Mathbin.Analysis.NormedSpace.Spectrum

/-!
# Normed algebras

This file contains basic facts about normed algebras.

## Main results

* We show that the character space of a normed algebra is compact using the Banach-Alaoglu theorem.

## TODO

* Show compactness for topological vector spaces; this requires the TVS version of Banach-Alaoglu.

## Tags

normed algebra, character space, continuous functional calculus

-/


variable {𝕜 : Type _} {A : Type _}

namespace WeakDual

namespace CharacterSpace

variable [NondiscreteNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [NormOneClass A]

theorem norm_one (φ : CharacterSpace 𝕜 A) : ∥toNormedDual (φ : WeakDual 𝕜 A)∥ = 1 := by
  refine' ContinuousLinearMap.op_norm_eq_of_bounds zero_le_one (fun a => _) fun x hx h => _
  · rw [one_mulₓ]
    exact Spectrum.norm_le_norm_of_mem (apply_mem_spectrum φ a)
    
  · have : ∥φ 1∥ ≤ x * ∥(1 : A)∥ := h 1
    simpa only [← norm_one, ← mul_oneₓ, ← map_one] using this
    

instance [ProperSpace 𝕜] : CompactSpace (CharacterSpace 𝕜 A) := by
  rw [← is_compact_iff_compact_space]
  have h : character_space 𝕜 A ⊆ to_normed_dual ⁻¹' Metric.ClosedBall 0 1 := by
    intro φ hφ
    rw [Set.mem_preimage, mem_closed_ball_zero_iff]
    exact (le_of_eqₓ <| norm_one ⟨φ, ⟨hφ.1, hφ.2⟩⟩ : _)
  exact compact_of_is_closed_subset (is_compact_closed_ball 𝕜 0 1) IsClosed h

end CharacterSpace

end WeakDual

