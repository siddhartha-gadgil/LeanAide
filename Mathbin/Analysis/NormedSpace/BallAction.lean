/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathbin.Analysis.Normed.Field.UnitBall
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Multiplicative actions of/on balls and spheres

Let `E` be a normed vector space over a normed field `𝕜`. In this file we define the following
multiplicative actions.

- The closed unit ball in `𝕜` acts on open balls and closed balls centered at `0` in `E`.
- The unit sphere in `𝕜` acts on open balls, closed balls, and spheres centered at `0` in `E`.
-/


open Metric Set

variable {𝕜 E : Type _} [NormedField 𝕜] [SemiNormedGroup E] [NormedSpace 𝕜 E] {r : ℝ}

section ClosedBall

instance mulActionClosedBallBall : MulAction (ClosedBall (0 : 𝕜) 1) (Ball (0 : E) r) where
  smul := fun c x =>
    ⟨(c : 𝕜) • x,
      mem_ball_zero_iff.2 <| by
        simpa only [← norm_smul, ← one_mulₓ] using
          mul_lt_mul' (mem_closed_ball_zero_iff.1 c.2) (mem_ball_zero_iff.1 x.2) (norm_nonneg _) one_pos⟩
  one_smul := fun x => Subtype.ext <| one_smul 𝕜 _
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_closed_ball_ball : HasContinuousSmul (ClosedBall (0 : 𝕜) 1) (Ball (0 : E) r) :=
  ⟨continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)⟩

instance mulActionClosedBallClosedBall : MulAction (ClosedBall (0 : 𝕜) 1) (ClosedBall (0 : E) r) where
  smul := fun c x =>
    ⟨(c : 𝕜) • x,
      mem_closed_ball_zero_iff.2 <| by
        simpa only [← norm_smul, ← one_mulₓ] using
          mul_le_mul (mem_closed_ball_zero_iff.1 c.2) (mem_closed_ball_zero_iff.1 x.2) (norm_nonneg _) zero_le_one⟩
  one_smul := fun x => Subtype.ext <| one_smul 𝕜 _
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_closed_ball_closed_ball :
    HasContinuousSmul (ClosedBall (0 : 𝕜) 1) (ClosedBall (0 : E) r) :=
  ⟨continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)⟩

end ClosedBall

section Sphere

instance mulActionSphereBall : MulAction (Sphere (0 : 𝕜) 1) (Ball (0 : E) r) where
  smul := fun c x => inclusion sphere_subset_closed_ball c • x
  one_smul := fun x => Subtype.ext <| one_smul _ _
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_sphere_ball : HasContinuousSmul (Sphere (0 : 𝕜) 1) (Ball (0 : E) r) :=
  ⟨continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)⟩

instance mulActionSphereClosedBall : MulAction (Sphere (0 : 𝕜) 1) (ClosedBall (0 : E) r) where
  smul := fun c x => inclusion sphere_subset_closed_ball c • x
  one_smul := fun x => Subtype.ext <| one_smul _ _
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_sphere_closed_ball : HasContinuousSmul (Sphere (0 : 𝕜) 1) (ClosedBall (0 : E) r) :=
  ⟨continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)⟩

instance mulActionSphereSphere : MulAction (Sphere (0 : 𝕜) 1) (Sphere (0 : E) r) where
  smul := fun c x =>
    ⟨(c : 𝕜) • x,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_smul, mem_sphere_zero_iff_norm.1 c.coe_prop, mem_sphere_zero_iff_norm.1 x.coe_prop, one_mulₓ]⟩
  one_smul := fun x => Subtype.ext <| one_smul _ _
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_sphere_sphere : HasContinuousSmul (Sphere (0 : 𝕜) 1) (Sphere (0 : E) r) :=
  ⟨continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)⟩

end Sphere

variable (𝕜) [CharZero 𝕜]

theorem ne_neg_of_mem_sphere {r : ℝ} (hr : r ≠ 0) (x : Sphere (0 : E) r) : x ≠ -x := fun h =>
  ne_zero_of_mem_sphere hr x
    ((self_eq_neg 𝕜 _).mp
      (by
        conv_lhs => rw [h]
        simp ))

theorem ne_neg_of_mem_unit_sphere (x : Sphere (0 : E) 1) : x ≠ -x :=
  ne_neg_of_mem_sphere 𝕜 one_ne_zero x

