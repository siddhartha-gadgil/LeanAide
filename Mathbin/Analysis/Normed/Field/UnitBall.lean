/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathbin.Analysis.Normed.Field.Basic
import Mathbin.Analysis.Normed.Group.BallSphere

/-!
# Algebraic structures on unit balls and spheres

In this file we define algebraic structures (`semigroup`, `comm_semigroup`, `monoid`, `comm_monoid`,
`group`, `comm_group`) on `metric.ball (0 : 𝕜) 1`, `metric.closed_ball (0 : 𝕜) 1`, and
`metric.sphere (0 : 𝕜) 1`. In each case we use the weakest possible typeclass assumption on `𝕜`,
from `non_unital_semi_normed_ring` to `normed_field`.
-/


open Set Metric

variable {𝕜 : Type _}

/-- Unit ball in a non unital semi normed ring as a bundled `subsemigroup`. -/
def Subsemigroup.unitBall (𝕜 : Type _) [NonUnitalSemiNormedRing 𝕜] : Subsemigroup 𝕜 where
  Carrier := Ball (0 : 𝕜) 1
  mul_mem' := fun x y hx hy => by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le x y).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)

instance [NonUnitalSemiNormedRing 𝕜] : Semigroupₓ (Ball (0 : 𝕜) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitBall 𝕜)

instance [NonUnitalSemiNormedRing 𝕜] : HasContinuousMul (Ball (0 : 𝕜) 1) :=
  ⟨continuous_subtype_mk _ <|
      Continuous.mul (continuous_subtype_val.comp continuous_fst) (continuous_subtype_val.comp continuous_snd)⟩

instance [SemiNormedCommRing 𝕜] : CommSemigroupₓ (Ball (0 : 𝕜) 1) :=
  MulMemClass.toCommSemigroup (Subsemigroup.unitBall 𝕜)

instance [NonUnitalSemiNormedRing 𝕜] : HasDistribNeg (Ball (0 : 𝕜) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : Ball (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

/-- Closed unit ball in a non unital semi normed ring as a bundled `subsemigroup`. -/
def Subsemigroup.unitClosedBall (𝕜 : Type _) [NonUnitalSemiNormedRing 𝕜] : Subsemigroup 𝕜 where
  Carrier := ClosedBall 0 1
  mul_mem' := fun x y hx hy => by
    rw [mem_closed_ball_zero_iff] at *
    exact (norm_mul_le x y).trans (mul_le_one hx (norm_nonneg _) hy)

instance [NonUnitalSemiNormedRing 𝕜] : Semigroupₓ (ClosedBall (0 : 𝕜) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitClosedBall 𝕜)

instance [NonUnitalSemiNormedRing 𝕜] : HasDistribNeg (ClosedBall (0 : 𝕜) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : ClosedBall (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

instance [NonUnitalSemiNormedRing 𝕜] : HasContinuousMul (ClosedBall (0 : 𝕜) 1) :=
  ⟨continuous_subtype_mk _ <|
      Continuous.mul (continuous_subtype_val.comp continuous_fst) (continuous_subtype_val.comp continuous_snd)⟩

/-- Closed unit ball in a semi normed ring as a bundled `submonoid`. -/
def Submonoid.unitClosedBall (𝕜 : Type _) [SemiNormedRing 𝕜] [NormOneClass 𝕜] : Submonoid 𝕜 :=
  { Subsemigroup.unitClosedBall 𝕜 with Carrier := ClosedBall 0 1, one_mem' := mem_closed_ball_zero_iff.2 norm_one.le }

instance [SemiNormedRing 𝕜] [NormOneClass 𝕜] : Monoidₓ (ClosedBall (0 : 𝕜) 1) :=
  SubmonoidClass.toMonoid (Submonoid.unitClosedBall 𝕜)

instance [SemiNormedCommRing 𝕜] [NormOneClass 𝕜] : CommMonoidₓ (ClosedBall (0 : 𝕜) 1) :=
  SubmonoidClass.toCommMonoid (Submonoid.unitClosedBall 𝕜)

/-- Unit sphere in a normed division ring as a bundled `submonoid`. -/
def Submonoid.unitSphere (𝕜 : Type _) [NormedDivisionRing 𝕜] : Submonoid 𝕜 where
  Carrier := Sphere (0 : 𝕜) 1
  mul_mem' := fun x y hx hy => by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one

instance [NormedDivisionRing 𝕜] : Groupₓ (Sphere (0 : 𝕜) 1) :=
  { SubmonoidClass.toMonoid (Submonoid.unitSphere 𝕜) with
    inv := fun x =>
      ⟨x⁻¹,
        mem_sphere_zero_iff_norm.2 <| by
          rw [norm_inv, mem_sphere_zero_iff_norm.1 x.coe_prop, inv_one]⟩,
    mul_left_inv := fun x => Subtype.coe_injective <| inv_mul_cancel <| ne_zero_of_mem_unit_sphere x }

instance [NormedDivisionRing 𝕜] : HasDistribNeg (Sphere (0 : 𝕜) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : Sphere (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

/-- Monoid homomorphism from the unit sphere to the group of units. -/
def unitSphereToUnits (𝕜 : Type _) [NormedDivisionRing 𝕜] : Sphere (0 : 𝕜) 1 →* Units 𝕜 :=
  Units.liftRight (Submonoid.unitSphere 𝕜).Subtype (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun x => rfl

instance [NormedDivisionRing 𝕜] : TopologicalGroup (Sphere (0 : 𝕜) 1) where
  continuous_mul :=
    continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_inv := continuous_subtype_mk _ <| continuous_subtype_coe.inv₀ ne_zero_of_mem_unit_sphere

instance [NormedField 𝕜] : CommGroupₓ (Sphere (0 : 𝕜) 1) :=
  { Metric.Sphere.group, SubmonoidClass.toCommMonoid (Submonoid.unitSphere 𝕜) with }

