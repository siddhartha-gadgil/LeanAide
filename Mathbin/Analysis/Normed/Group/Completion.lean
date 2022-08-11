/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.Algebra.GroupCompletion
import Mathbin.Topology.MetricSpace.Completion

/-!
# Completion of a normed group

In this file we prove that the completion of a (semi)normed group is a normed group.

## Tags

normed group, completion
-/


noncomputable section

namespace UniformSpace

namespace Completion

variable (E : Type _)

instance [UniformSpace E] [HasNorm E] : HasNorm (Completion E) where norm := Completion.extension HasNorm.norm

@[simp]
theorem norm_coe {E} [SemiNormedGroup E] (x : E) : ∥(x : Completion E)∥ = ∥x∥ :=
  Completion.extension_coe uniform_continuous_norm x

instance [SemiNormedGroup E] : NormedGroup (Completion E) :=
  { Completion.addCommGroup, Completion.metricSpace with
    dist_eq := by
      intro x y
      apply completion.induction_on₂ x y <;> clear x y
      · refine' is_closed_eq (completion.uniform_continuous_extension₂ _).Continuous _
        exact Continuous.comp completion.continuous_extension continuous_sub
        
      · intro x y
        rw [← completion.coe_sub, norm_coe, completion.dist_eq, dist_eq_norm]
         }

end Completion

end UniformSpace

