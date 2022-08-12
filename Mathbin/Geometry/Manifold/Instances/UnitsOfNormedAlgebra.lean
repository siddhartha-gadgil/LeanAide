/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Heather Macbeth
-/
import Mathbin.Geometry.Manifold.SmoothManifoldWithCorners
import Mathbin.Analysis.NormedSpace.Units

/-!
# Units of a normed algebra

This file is a stub, containing a construction of the charted space structure on the group of units
of a complete normed ring `R`, and of the smooth manifold structure on the group of units of a
complete normed `𝕜`-algebra `R`.

This manifold is actually a Lie group, which eventually should be the main result of this file.

An important special case of this construction is the general linear group.  For a normed space `V`
over a field `𝕜`, the `𝕜`-linear endomorphisms of `V` are a normed `𝕜`-algebra (see
`continuous_linear_map.to_normed_algebra`), so this construction provides a Lie group structure on
its group of units, the general linear group GL(`𝕜`, `V`).

## TODO

The Lie group instance requires the following fields:
```
instance : lie_group 𝓘(𝕜, R) Rˣ :=
{ smooth_mul := sorry,
  smooth_inv := sorry,
  ..units.smooth_manifold_with_corners }
```

The ingredients needed for the construction are
* smoothness of multiplication and inversion in the charts, i.e. as functions on the normed
  `𝕜`-space `R`:  see `cont_diff_at_ring_inverse` for the inversion result, and
  `cont_diff_mul` (needs to be generalized from field to algebra) for the multiplication
  result
* for an open embedding `f`, whose domain is equipped with the induced manifold structure
  `f.singleton_smooth_manifold_with_corners`, characterization of smoothness of functions to/from
  this manifold in terms of smoothness in the target space.  See the pair of lemmas
  `cont_mdiff_coe_sphere` and `cont_mdiff.cod_restrict_sphere` for a model.
None of this should be particularly difficult.

-/


noncomputable section

open Manifold

namespace Units

variable {R : Type _} [NormedRing R] [CompleteSpace R]

instance : ChartedSpace R Rˣ :=
  open_embedding_coe.singletonChartedSpace

theorem chart_at_apply {a : Rˣ} {b : Rˣ} : chartAt R a b = b :=
  rfl

theorem chart_at_source {a : Rˣ} : (chartAt R a).Source = Set.Univ :=
  rfl

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] [NormedAlgebra 𝕜 R]

instance : SmoothManifoldWithCorners 𝓘(𝕜, R) Rˣ :=
  open_embedding_coe.singleton_smooth_manifold_with_corners 𝓘(𝕜, R)

end Units

