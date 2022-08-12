/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth structures

In this file we define smooth structures that build on Lie groups. We prefer using the term smooth
instead of Lie mainly because Lie ring has currently another use in mathematics.
-/


open Manifold

section SmoothRing

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _} [NormedGroup E]
  [NormedSpace 𝕜 E]

-- ./././Mathport/Syntax/Translate/Basic.lean:304:40: warning: unsupported option default_priority
set_option default_priority 100

/-- A smooth (semi)ring is a (semi)ring `R` where addition and multiplication are smooth.
If `R` is a ring, then negation is automatically smooth, as it is multiplication with `-1`. -/
-- see Note [default priority]
-- See note [Design choices about smooth algebraic structures]
class SmoothRing (I : ModelWithCorners 𝕜 E H) (R : Type _) [Semiringₓ R] [TopologicalSpace R] [ChartedSpace H R] extends
  HasSmoothAdd I R : Prop where
  smooth_mul : Smooth (I.Prod I) I fun p : R × R => p.1 * p.2

instance SmoothRing.to_has_smooth_mul (I : ModelWithCorners 𝕜 E H) (R : Type _) [Semiringₓ R] [TopologicalSpace R]
    [ChartedSpace H R] [h : SmoothRing I R] : HasSmoothMul I R :=
  { h with }

instance SmoothRing.to_lie_add_group (I : ModelWithCorners 𝕜 E H) (R : Type _) [Ringₓ R] [TopologicalSpace R]
    [ChartedSpace H R] [SmoothRing I R] : LieAddGroup I R where
  compatible := fun e e' => HasGroupoid.compatible (contDiffGroupoid ⊤ I)
  smooth_add := smooth_add I
  smooth_neg := by
    simpa only [← neg_one_mul] using @smooth_mul_left 𝕜 _ H _ E _ _ I R _ _ _ _ (-1)

end SmoothRing

instance field_smooth_ring {𝕜 : Type _} [NondiscreteNormedField 𝕜] : SmoothRing 𝓘(𝕜) 𝕜 :=
  { normed_space_lie_add_group with
    smooth_mul := by
      rw [smooth_iff]
      refine' ⟨continuous_mul, fun x y => _⟩
      simp' only [← Prod.mk.eta] with mfld_simps
      rw [cont_diff_on_univ]
      exact cont_diff_mul }

variable {𝕜 R E H : Type _} [TopologicalSpace R] [TopologicalSpace H] [NondiscreteNormedField 𝕜] [NormedGroup E]
  [NormedSpace 𝕜 E] [ChartedSpace H R] (I : ModelWithCorners 𝕜 E H)

/-- A smooth (semi)ring is a topological (semi)ring. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
theorem topological_semiring_of_smooth [Semiringₓ R] [SmoothRing I R] : TopologicalSemiring R :=
  { has_continuous_mul_of_smooth I, has_continuous_add_of_smooth I with }

