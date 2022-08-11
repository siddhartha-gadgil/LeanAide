/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Analysis.NormedSpace.ContinuousAffineMap
import Mathbin.Analysis.Calculus.ContDiff

/-!
# Smooth affine maps

This file contains results about smoothness of affine maps.

## Main definitions:

 * `continuous_affine_map.cont_diff`: a continuous affine map is smooth

-/


namespace ContinuousAffineMap

variable {𝕜 V W : Type _} [NondiscreteNormedField 𝕜]

variable [NormedGroup V] [NormedSpace 𝕜 V]

variable [NormedGroup W] [NormedSpace 𝕜 W]

/-- A continuous affine map between normed vector spaces is smooth. -/
theorem cont_diff {n : WithTop ℕ} (f : V →A[𝕜] W) : ContDiff 𝕜 n f := by
  rw [f.decomp]
  apply f.cont_linear.cont_diff.add
  simp only
  exact cont_diff_const

end ContinuousAffineMap

