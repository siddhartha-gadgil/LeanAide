/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.Complex.Circle
import Mathbin.Analysis.SpecialFunctions.Complex.Log

/-!
# Maps on the unit circle

In this file we prove some basic lemmas about `exp_map_circle` and the restriction of `complex.arg`
to the unit circle. These two maps define a local equivalence between `circle` and `ℝ`, see
`circle.arg_local_equiv` and `circle.arg_equiv`, that sends the whole circle to `(-π, π]`.
-/


open Complex Function Set

open Real

namespace circle

theorem injective_arg : Injective fun z : circle => arg z := fun z w h =>
  Subtype.ext <| ext_abs_arg ((abs_coe_circle z).trans (abs_coe_circle w).symm) h

@[simp]
theorem arg_eq_arg {z w : circle} : arg z = arg w ↔ z = w :=
  injective_arg.eq_iff

end circle

theorem arg_exp_map_circle {x : ℝ} (h₁ : -π < x) (h₂ : x ≤ π) : arg (expMapCircle x) = x := by
  rw [exp_map_circle_apply, exp_mul_I, arg_cos_add_sin_mul_I ⟨h₁, h₂⟩]

@[simp]
theorem exp_map_circle_arg (z : circle) : expMapCircle (arg z) = z :=
  circle.injective_arg <| arg_exp_map_circle (neg_pi_lt_arg _) (arg_le_pi _)

namespace circle

/-- `complex.arg ∘ coe` and `exp_map_circle` define a local equivalence between `circle and `ℝ` with
`source = set.univ` and `target = set.Ioc (-π) π`. -/
@[simps (config := { fullyApplied := false })]
noncomputable def argLocalEquiv : LocalEquiv circle ℝ where
  toFun := arg ∘ coe
  invFun := expMapCircle
  Source := Univ
  Target := Ioc (-π) π
  map_source' := fun z _ => ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  map_target' := maps_to_univ _ _
  left_inv' := fun z _ => exp_map_circle_arg z
  right_inv' := fun x hx => arg_exp_map_circle hx.1 hx.2

/-- `complex.arg` and `exp_map_circle` define an equivalence between `circle and `(-π, π]`. -/
@[simps (config := { fullyApplied := false })]
noncomputable def argEquiv : circle ≃ Ioc (-π) π where
  toFun := fun z => ⟨arg z, neg_pi_lt_arg _, arg_le_pi _⟩
  invFun := expMapCircle ∘ coe
  left_inv := fun z => argLocalEquiv.left_inv trivialₓ
  right_inv := fun x => Subtype.ext <| argLocalEquiv.right_inv x.2

end circle

theorem left_inverse_exp_map_circle_arg : LeftInverse expMapCircle (arg ∘ coe) :=
  exp_map_circle_arg

theorem inv_on_arg_exp_map_circle : InvOn (arg ∘ coe) expMapCircle (Ioc (-π) π) Univ :=
  circle.argLocalEquiv.symm.InvOn

theorem surj_on_exp_map_circle_neg_pi_pi : SurjOn expMapCircle (Ioc (-π) π) Univ :=
  circle.argLocalEquiv.symm.SurjOn

theorem exp_map_circle_eq_exp_map_circle {x y : ℝ} : expMapCircle x = expMapCircle y ↔ ∃ m : ℤ, x = y + m * (2 * π) :=
  by
  rw [Subtype.ext_iff, exp_map_circle_apply, exp_map_circle_apply, exp_eq_exp_iff_exists_int]
  refine' exists_congr fun n => _
  rw [← mul_assoc, ← add_mulₓ, mul_left_inj' I_ne_zero, ← of_real_one, ← of_real_bit0, ← of_real_mul, ←
    of_real_int_cast, ← of_real_mul, ← of_real_add, of_real_inj]

theorem periodic_exp_map_circle : Periodic expMapCircle (2 * π) := fun z =>
  exp_map_circle_eq_exp_map_circle.2
    ⟨1, by
      rw [Int.cast_oneₓ, one_mulₓ]⟩

@[simp]
theorem exp_map_circle_two_pi : expMapCircle (2 * π) = 1 :=
  periodic_exp_map_circle.Eq.trans exp_map_circle_zero

theorem exp_map_circle_sub_two_pi (x : ℝ) : expMapCircle (x - 2 * π) = expMapCircle x :=
  periodic_exp_map_circle.sub_eq x

theorem exp_map_circle_add_two_pi (x : ℝ) : expMapCircle (x + 2 * π) = expMapCircle x :=
  periodic_exp_map_circle x

/-- `exp_map_circle`, applied to a `real.angle`. -/
noncomputable def Real.Angle.expMapCircle (θ : Real.Angle) : circle :=
  periodic_exp_map_circle.lift θ

@[simp]
theorem Real.Angle.exp_map_circle_coe (x : ℝ) : Real.Angle.expMapCircle x = expMapCircle x :=
  rfl

@[simp]
theorem Real.Angle.exp_map_circle_zero : Real.Angle.expMapCircle 0 = 1 := by
  rw [← Real.Angle.coe_zero, Real.Angle.exp_map_circle_coe, exp_map_circle_zero]

@[simp]
theorem Real.Angle.exp_map_circle_neg (θ : Real.Angle) : Real.Angle.expMapCircle (-θ) = (Real.Angle.expMapCircle θ)⁻¹ :=
  by
  induction θ using Real.Angle.induction_on
  simp_rw [← Real.Angle.coe_neg, Real.Angle.exp_map_circle_coe, exp_map_circle_neg]

@[simp]
theorem Real.Angle.exp_map_circle_add (θ₁ θ₂ : Real.Angle) :
    Real.Angle.expMapCircle (θ₁ + θ₂) = Real.Angle.expMapCircle θ₁ * Real.Angle.expMapCircle θ₂ := by
  induction θ₁ using Real.Angle.induction_on
  induction θ₂ using Real.Angle.induction_on
  exact exp_map_circle_add θ₁ θ₂

@[simp]
theorem Real.Angle.arg_exp_map_circle (θ : Real.Angle) : (arg (Real.Angle.expMapCircle θ) : Real.Angle) = θ := by
  induction θ using Real.Angle.induction_on
  rw [Real.Angle.exp_map_circle_coe, exp_map_circle_apply, exp_mul_I, ← of_real_cos, ← of_real_sin, ←
    Real.Angle.cos_coe, ← Real.Angle.sin_coe, arg_cos_add_sin_mul_I_coe_angle]

