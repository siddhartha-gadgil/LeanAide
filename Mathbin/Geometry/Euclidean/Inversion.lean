/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Geometry.Euclidean.Basic

/-!
# Inversion in an affine space

In this file we define inversion in a sphere in an affine space. This map sends each point `x` to
the point `y` such that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center
and the radius the sphere.

In many applications, it is convenient to assume that the inversions swaps the center and the point
at infinity. In order to stay in the original affine space, we define the map so that it sends
center to itself.

Currently, we prove only a few basic lemmas needed to prove Ptolemy's inequality, see
`euclidean_geometry.mul_dist_le_mul_dist_add_mul_dist`.
-/


noncomputable section

open Metric Real Function

namespace EuclideanGeometry

variable {V P : Type _} [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {a b c d x y z : P} {R : ℝ}

include V

/-- Inversion in a sphere in an affine space. This map sends each point `x` to the point `y` such
that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center and the radius the
sphere. -/
def inversion (c : P) (R : ℝ) (x : P) : P :=
  (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c

theorem inversion_vsub_center (c : P) (R : ℝ) (x : P) : inversion c R x -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c) :=
  vadd_vsub _ _

@[simp]
theorem inversion_self (c : P) (R : ℝ) : inversion c R c = c := by
  simp [← inversion]

@[simp]
theorem inversion_dist_center (c x : P) : inversion c (dist x c) x = x := by
  rcases eq_or_ne x c with (rfl | hne)
  · apply inversion_self
    
  · rw [inversion, div_self, one_pow, one_smul, vsub_vadd]
    rwa [dist_ne_zero]
    

theorem inversion_of_mem_sphere (h : x ∈ Sphere c R) : inversion c R x = x :=
  h.out ▸ inversion_dist_center c x

/-- Distance from the image of a point under inversion to the center. This formula accidentally
works for `x = c`. -/
theorem dist_inversion_center (c x : P) (R : ℝ) : dist (inversion c R x) c = R ^ 2 / dist x c := by
  rcases eq_or_ne x c with (rfl | hx)
  · simp
    
  have : dist x c ≠ 0 := dist_ne_zero.2 hx
  field_simp [← inversion, ← norm_smul, ← abs_div, dist_eq_norm_vsub, ← sq, ← mul_assoc]

/-- Distance from the center of an inversion to the image of a point under the inversion. This
formula accidentally works for `x = c`. -/
theorem dist_center_inversion (c x : P) (R : ℝ) : dist c (inversion c R x) = R ^ 2 / dist c x := by
  rw [dist_comm c, dist_comm c, dist_inversion_center]

@[simp]
theorem inversion_inversion (c : P) {R : ℝ} (hR : R ≠ 0) (x : P) : inversion c R (inversion c R x) = x := by
  rcases eq_or_ne x c with (rfl | hne)
  · rw [inversion_self, inversion_self]
    
  · rw [inversion, dist_inversion_center, inversion_vsub_center, smul_smul, ← mul_powₓ, div_mul_div_comm,
      div_mul_cancel _ (dist_ne_zero.2 hne), ← sq, div_self, one_pow, one_smul, vsub_vadd]
    exact pow_ne_zero _ hR
    

theorem inversion_involutive (c : P) {R : ℝ} (hR : R ≠ 0) : Involutive (inversion c R) :=
  inversion_inversion c hR

theorem inversion_surjective (c : P) {R : ℝ} (hR : R ≠ 0) : Surjective (inversion c R) :=
  (inversion_involutive c hR).Surjective

theorem inversion_injective (c : P) {R : ℝ} (hR : R ≠ 0) : Injective (inversion c R) :=
  (inversion_involutive c hR).Injective

theorem inversion_bijective (c : P) {R : ℝ} (hR : R ≠ 0) : Bijective (inversion c R) :=
  (inversion_involutive c hR).Bijective

/-- Distance between the images of two points under an inversion. -/
theorem dist_inversion_inversion (hx : x ≠ c) (hy : y ≠ c) (R : ℝ) :
    dist (inversion c R x) (inversion c R y) = R ^ 2 / (dist x c * dist y c) * dist x y := by
  dunfold inversion
  simp_rw [dist_vadd_cancel_right, dist_eq_norm_vsub V _ c]
  simpa only [← dist_vsub_cancel_right] using dist_div_norm_sq_smul (vsub_ne_zero.2 hx) (vsub_ne_zero.2 hy) R

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- **Ptolemy's inequality**: in a quadrangle `ABCD`, `|AC| * |BD| ≤ |AB| * |CD| + |BC| * |AD|`. If
`ABCD` is a convex cyclic polygon, then this inequality becomes an equality, see
`euclidean_geometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`.  -/
theorem mul_dist_le_mul_dist_add_mul_dist (a b c d : P) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d := by
  -- If one of the points `b`, `c`, `d` is equal to `a`, then the inequality is trivial.
  rcases eq_or_ne b a with (rfl | hb)
  · rw [dist_self, zero_mul, zero_addₓ]
    
  rcases eq_or_ne c a with (rfl | hc)
  · rw [dist_self, zero_mul]
    apply_rules [add_nonneg, mul_nonneg, dist_nonneg]
    
  rcases eq_or_ne d a with (rfl | hd)
  · rw [dist_self, mul_zero, add_zeroₓ, dist_comm d, dist_comm d, mul_comm]
    
  /- Otherwise, we apply the triangle inequality to `euclidean_geometry.inversion a 1 b`,
    `euclidean_geometry.inversion a 1 c`, and `euclidean_geometry.inversion a 1 d`. -/
  have H := dist_triangle (inversion a 1 b) (inversion a 1 c) (inversion a 1 d)
  rw [dist_inversion_inversion hb hd, dist_inversion_inversion hb hc, dist_inversion_inversion hc hd, one_pow] at H
  rw [← dist_pos] at hb hc hd
  rw [← div_le_div_right (mul_pos hb (mul_pos hc hd))]
  convert H <;>
    · field_simp [← hb.ne', ← hc.ne', ← hd.ne', ← dist_comm a]
      ring
      

end EuclideanGeometry

