/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.Normed.Group.Completion
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Topology.Algebra.UniformMulAction

/-!
# Normed space structure on the completion of a normed space

If `E` is a normed space over `𝕜`, then so is `uniform_space.completion E`. In this file we provide
necessary instances and define `uniform_space.completion.to_complₗᵢ` - coercion
`E → uniform_space.completion E` as a bundled linear isometry.
-/


noncomputable section

namespace UniformSpace

namespace Completion

variable (𝕜 E : Type _) [NormedField 𝕜] [NormedGroup E] [NormedSpace 𝕜 E]

instance (priority := 100) NormedSpace.to_has_uniform_continuous_const_smul : HasUniformContinuousConstSmul 𝕜 E :=
  ⟨fun c => (lipschitz_with_smul c).UniformContinuous⟩

instance : NormedSpace 𝕜 (Completion E) :=
  { Completion.module with smul := (· • ·),
    norm_smul_le := fun c x =>
      (induction_on x (is_closed_le (continuous_const_smul _).norm (continuous_const.mul continuous_norm))) fun y => by
        simp only [coe_smul, ← norm_coe, ← norm_smul] }

variable {𝕜 E}

/-- Embedding of a normed space to its completion as a linear isometry. -/
def toComplₗᵢ : E →ₗᵢ[𝕜] Completion E :=
  { toCompl with toFun := coe, map_smul' := coe_smul, norm_map' := norm_coe }

@[simp]
theorem coe_to_complₗᵢ : ⇑(toComplₗᵢ : E →ₗᵢ[𝕜] Completion E) = coe :=
  rfl

/-- Embedding of a normed space to its completion as a continuous linear map. -/
def toComplL : E →L[𝕜] Completion E :=
  toComplₗᵢ.toContinuousLinearMap

@[simp]
theorem coe_to_complL : ⇑(toComplL : E →L[𝕜] Completion E) = coe :=
  rfl

@[simp]
theorem norm_to_complL {𝕜 E : Type _} [NondiscreteNormedField 𝕜] [NormedGroup E] [NormedSpace 𝕜 E] [Nontrivial E] :
    ∥(toComplL : E →L[𝕜] Completion E)∥ = 1 :=
  (toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).norm_to_continuous_linear_map

end Completion

end UniformSpace

