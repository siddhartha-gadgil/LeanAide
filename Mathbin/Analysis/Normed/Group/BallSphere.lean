/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathbin.Analysis.Normed.Group.Basic

/-!
# Negation on spheres and balls

In this file we define `has_involutive_neg` instances for spheres, open balls, and closed balls in a
semi normed group.
-/


open Metric Set

variable {E : Type _} [SemiNormedGroup E] {r : ℝ}

/-- We equip the sphere, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance : HasInvolutiveNeg (Sphere (0 : E) r) where
  neg := fun w =>
    ⟨-↑w, by
      simp ⟩
  neg_neg := fun x => Subtype.ext <| neg_negₓ x

@[simp]
theorem coe_neg_sphere {r : ℝ} (v : Sphere (0 : E) r) : ↑(-v) = (-v : E) :=
  rfl

instance : HasContinuousNeg (Sphere (0 : E) r) :=
  ⟨continuous_subtype_mk _ continuous_subtype_coe.neg⟩

/-- We equip the ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : HasInvolutiveNeg (Ball (0 : E) r) where
  neg := fun w =>
    ⟨-↑w, by
      simpa using w.coe_prop⟩
  neg_neg := fun x => Subtype.ext <| neg_negₓ x

@[simp]
theorem coe_neg_ball {r : ℝ} (v : Ball (0 : E) r) : ↑(-v) = (-v : E) :=
  rfl

instance : HasContinuousNeg (Ball (0 : E) r) :=
  ⟨continuous_subtype_mk _ continuous_subtype_coe.neg⟩

/-- We equip the closed ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : HasInvolutiveNeg (ClosedBall (0 : E) r) where
  neg := fun w =>
    ⟨-↑w, by
      simpa using w.coe_prop⟩
  neg_neg := fun x => Subtype.ext <| neg_negₓ x

@[simp]
theorem coe_neg_closed_ball {r : ℝ} (v : ClosedBall (0 : E) r) : ↑(-v) = (-v : E) :=
  rfl

instance : HasContinuousNeg (ClosedBall (0 : E) r) :=
  ⟨continuous_subtype_mk _ continuous_subtype_coe.neg⟩

