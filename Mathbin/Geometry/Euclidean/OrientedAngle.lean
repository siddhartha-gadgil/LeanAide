/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Analysis.InnerProductSpace.Orientation
import Mathbin.Analysis.InnerProductSpace.PiL2
import Mathbin.Analysis.SpecialFunctions.Complex.Circle

/-!
# Oriented angles.

This file defines oriented angles in real inner product spaces.

## Main definitions

* `orientation.oangle` is the oriented angle between two vectors with respect to an orientation.

* `orientation.rotation` is the rotation by an oriented angle with respect to an orientation.

## Implementation notes

The definitions here use the `real.angle` type, angles modulo `2 * π`. For some purposes,
angles modulo `π` are more convenient, because results are true for such angles with less
configuration dependence. Results that are only equalities modulo `π` can be represented
modulo `2 * π` as equalities of `(2 : ℤ) • θ`.

Definitions and results in the `orthonormal` namespace, with respect to a particular choice
of orthonormal basis, are mainly for use in setting up the API and proving that certain
definitions do not depend on the choice of basis for a given orientation. Applications should
generally use the definitions and results in the `orientation` namespace instead.

## References

* Evan Chen, Euclidean Geometry in Mathematical Olympiads.

-/


noncomputable section

open Real

namespace Orthonormal

variable {V : Type _} [InnerProductSpace ℝ V]

variable {b : Basis (Finₓ 2) ℝ V} (hb : Orthonormal ℝ b)

include hb

/-- The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. -/
def oangle (x y : V) : Real.Angle :=
  Complex.arg ((Complex.isometryOfOrthonormal hb).symm y / (Complex.isometryOfOrthonormal hb).symm x)

/-- Oriented angles are continuous when the vectors involved are nonzero. -/
theorem continuous_at_oangle {x : V × V} (hx1 : x.1 ≠ 0) (hx2 : x.2 ≠ 0) :
    ContinuousAt (fun y : V × V => hb.oangle y.1 y.2) x :=
  (Complex.continuous_at_arg_coe_angle
        (by
          simp [← hx1, ← hx2])).comp <|
    ContinuousAt.div ((Complex.isometryOfOrthonormal hb).symm.Continuous.comp continuous_snd).ContinuousAt
      ((Complex.isometryOfOrthonormal hb).symm.Continuous.comp continuous_fst).ContinuousAt
      (by
        simp [← hx1])

/-- If the first vector passed to `oangle` is 0, the result is 0. -/
@[simp]
theorem oangle_zero_left (x : V) : hb.oangle 0 x = 0 := by
  simp [← oangle]

/-- If the second vector passed to `oangle` is 0, the result is 0. -/
@[simp]
theorem oangle_zero_right (x : V) : hb.oangle x 0 = 0 := by
  simp [← oangle]

/-- If the two vectors passed to `oangle` are the same, the result is 0. -/
@[simp]
theorem oangle_self (x : V) : hb.oangle x x = 0 := by
  by_cases' h : x = 0 <;> simp [← oangle, ← h]

/-- Swapping the two vectors passed to `oangle` negates the angle. -/
theorem oangle_rev (x y : V) : hb.oangle y x = -hb.oangle x y := by
  simp only [← oangle]
  convert Complex.arg_inv_coe_angle _
  exact (inv_div _ _).symm

/-- Adding the angles between two vectors in each order results in 0. -/
@[simp]
theorem oangle_add_oangle_rev (x y : V) : hb.oangle x y + hb.oangle y x = 0 := by
  simp [← hb.oangle_rev y x]

/-- Negating the first vector passed to `oangle` adds `π` to the angle. -/
theorem oangle_neg_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : hb.oangle (-x) y = hb.oangle x y + π := by
  simp only [← oangle, ← div_neg_eq_neg_div, ← map_neg]
  refine' Complex.arg_neg_coe_angle _
  simp [← hx, ← hy]

/-- Negating the second vector passed to `oangle` adds `π` to the angle. -/
theorem oangle_neg_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : hb.oangle x (-y) = hb.oangle x y + π := by
  simp only [← oangle, ← neg_div, ← map_neg]
  refine' Complex.arg_neg_coe_angle _
  simp [← hx, ← hy]

/-- Negating the first vector passed to `oangle` does not change twice the angle. -/
@[simp]
theorem two_zsmul_oangle_neg_left (x y : V) : (2 : ℤ) • hb.oangle (-x) y = (2 : ℤ) • hb.oangle x y := by
  by_cases' hx : x = 0
  · simp [← hx]
    
  · by_cases' hy : y = 0
    · simp [← hy]
      
    · simp [← hb.oangle_neg_left hx hy]
      
    

/-- Negating the second vector passed to `oangle` does not change twice the angle. -/
@[simp]
theorem two_zsmul_oangle_neg_right (x y : V) : (2 : ℤ) • hb.oangle x (-y) = (2 : ℤ) • hb.oangle x y := by
  by_cases' hx : x = 0
  · simp [← hx]
    
  · by_cases' hy : y = 0
    · simp [← hy]
      
    · simp [← hb.oangle_neg_right hx hy]
      
    

/-- Negating both vectors passed to `oangle` does not change the angle. -/
@[simp]
theorem oangle_neg_neg (x y : V) : hb.oangle (-x) (-y) = hb.oangle x y := by
  simp [← oangle, ← neg_div_neg_eq]

/-- Negating the first vector produces the same angle as negating the second vector. -/
theorem oangle_neg_left_eq_neg_right (x y : V) : hb.oangle (-x) y = hb.oangle x (-y) := by
  rw [← neg_negₓ y, oangle_neg_neg, neg_negₓ]

/-- The angle between the negation of a nonzero vector and that vector is `π`. -/
@[simp]
theorem oangle_neg_self_left {x : V} (hx : x ≠ 0) : hb.oangle (-x) x = π := by
  simp [← oangle_neg_left, ← hx]

/-- The angle between a nonzero vector and its negation is `π`. -/
@[simp]
theorem oangle_neg_self_right {x : V} (hx : x ≠ 0) : hb.oangle x (-x) = π := by
  simp [← oangle_neg_right, ← hx]

/-- Twice the angle between the negation of a vector and that vector is 0. -/
@[simp]
theorem two_zsmul_oangle_neg_self_left (x : V) : (2 : ℤ) • hb.oangle (-x) x = 0 := by
  by_cases' hx : x = 0 <;> simp [← hx]

/-- Twice the angle between a vector and its negation is 0. -/
@[simp]
theorem two_zsmul_oangle_neg_self_right (x : V) : (2 : ℤ) • hb.oangle x (-x) = 0 := by
  by_cases' hx : x = 0 <;> simp [← hx]

/-- Adding the angles between two vectors in each order, with the first vector in each angle
negated, results in 0. -/
@[simp]
theorem oangle_add_oangle_rev_neg_left (x y : V) : hb.oangle (-x) y + hb.oangle (-y) x = 0 := by
  rw [oangle_neg_left_eq_neg_right, oangle_rev, add_left_negₓ]

/-- Adding the angles between two vectors in each order, with the second vector in each angle
negated, results in 0. -/
@[simp]
theorem oangle_add_oangle_rev_neg_right (x y : V) : hb.oangle x (-y) + hb.oangle y (-x) = 0 := by
  rw [hb.oangle_rev (-x), oangle_neg_left_eq_neg_right, add_neg_selfₓ]

/-- Multiplying the first vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp]
theorem oangle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : hb.oangle (r • x) y = hb.oangle x y := by
  simp only [← oangle, ← LinearIsometryEquiv.map_smul, ← Complex.real_smul]
  rw [mul_comm, div_mul_eq_div_mul_one_div, one_div, mul_comm, ← Complex.of_real_inv]
  congr 1
  exact Complex.arg_real_mul _ (inv_pos.2 hr)

/-- Multiplying the second vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp]
theorem oangle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : hb.oangle x (r • y) = hb.oangle x y := by
  simp only [← oangle, ← LinearIsometryEquiv.map_smul, ← Complex.real_smul]
  congr 1
  rw [mul_div_assoc]
  exact Complex.arg_real_mul _ hr

/-- Multiplying the first vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp]
theorem oangle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) : hb.oangle (r • x) y = hb.oangle (-x) y := by
  rw [← neg_negₓ r, neg_smul, ← smul_neg, hb.oangle_smul_left_of_pos _ _ (neg_pos_of_neg hr)]

/-- Multiplying the second vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp]
theorem oangle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) : hb.oangle x (r • y) = hb.oangle x (-y) := by
  rw [← neg_negₓ r, neg_smul, ← smul_neg, hb.oangle_smul_right_of_pos _ _ (neg_pos_of_neg hr)]

/-- The angle between a nonnegative multiple of a vector and that vector is 0. -/
@[simp]
theorem oangle_smul_left_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) : hb.oangle (r • x) x = 0 := by
  rcases hr.lt_or_eq with (h | h)
  · simp [← h]
    
  · simp [← h.symm]
    

/-- The angle between a vector and a nonnegative multiple of that vector is 0. -/
@[simp]
theorem oangle_smul_right_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) : hb.oangle x (r • x) = 0 := by
  rcases hr.lt_or_eq with (h | h)
  · simp [← h]
    
  · simp [← h.symm]
    

/-- The angle between two nonnegative multiples of the same vector is 0. -/
@[simp]
theorem oangle_smul_smul_self_of_nonneg (x : V) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    hb.oangle (r₁ • x) (r₂ • x) = 0 := by
  rcases hr₁.lt_or_eq with (h | h)
  · simp [← h, ← hr₂]
    
  · simp [← h.symm]
    

/-- Multiplying the first vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp]
theorem two_zsmul_oangle_smul_left_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
    (2 : ℤ) • hb.oangle (r • x) y = (2 : ℤ) • hb.oangle x y := by
  rcases hr.lt_or_lt with (h | h) <;> simp [← h]

/-- Multiplying the second vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp]
theorem two_zsmul_oangle_smul_right_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
    (2 : ℤ) • hb.oangle x (r • y) = (2 : ℤ) • hb.oangle x y := by
  rcases hr.lt_or_lt with (h | h) <;> simp [← h]

/-- Twice the angle between a multiple of a vector and that vector is 0. -/
@[simp]
theorem two_zsmul_oangle_smul_left_self (x : V) {r : ℝ} : (2 : ℤ) • hb.oangle (r • x) x = 0 := by
  rcases lt_or_leₓ r 0 with (h | h) <;> simp [← h]

/-- Twice the angle between a vector and a multiple of that vector is 0. -/
@[simp]
theorem two_zsmul_oangle_smul_right_self (x : V) {r : ℝ} : (2 : ℤ) • hb.oangle x (r • x) = 0 := by
  rcases lt_or_leₓ r 0 with (h | h) <;> simp [← h]

/-- Twice the angle between two multiples of a vector is 0. -/
@[simp]
theorem two_zsmul_oangle_smul_smul_self (x : V) {r₁ r₂ : ℝ} : (2 : ℤ) • hb.oangle (r₁ • x) (r₂ • x) = 0 := by
  by_cases' h : r₁ = 0 <;> simp [← h]

/-- Two vectors are equal if and only if they have equal norms and zero angle between them. -/
theorem eq_iff_norm_eq_and_oangle_eq_zero (x y : V) : x = y ↔ ∥x∥ = ∥y∥ ∧ hb.oangle x y = 0 := by
  constructor
  · intro h
    simp [← h]
    
  · rintro ⟨hn, ha⟩
    rw [oangle] at ha
    by_cases' hy0 : y = 0
    · simpa [← hy0] using hn
      
    · have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (hn.symm ▸ norm_ne_zero_iff.2 hy0)
      have hx0' : (Complex.isometryOfOrthonormal hb).symm x ≠ 0 := by
        simp [← hx0]
      have hy0' : (Complex.isometryOfOrthonormal hb).symm y ≠ 0 := by
        simp [← hy0]
      rw [Complex.arg_div_coe_angle hy0' hx0', sub_eq_zero, Complex.arg_coe_angle_eq_iff,
        Complex.arg_eq_arg_iff hy0' hx0', ← Complex.norm_eq_abs, ← Complex.norm_eq_abs, LinearIsometryEquiv.norm_map,
        LinearIsometryEquiv.norm_map, hn, ← Complex.of_real_div, div_self (norm_ne_zero_iff.2 hy0), Complex.of_real_one,
        one_mulₓ, LinearIsometryEquiv.map_eq_iff] at ha
      exact ha.symm
      
    

/-- Two vectors with equal norms are equal if and only if they have zero angle between them. -/
theorem eq_iff_oangle_eq_zero_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) : x = y ↔ hb.oangle x y = 0 :=
  ⟨fun he => ((hb.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).2, fun ha =>
    (hb.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨h, ha⟩⟩

/-- Two vectors with zero angle between them are equal if and only if they have equal norms. -/
theorem eq_iff_norm_eq_of_oangle_eq_zero {x y : V} (h : hb.oangle x y = 0) : x = y ↔ ∥x∥ = ∥y∥ :=
  ⟨fun he => ((hb.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).1, fun hn =>
    (hb.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨hn, h⟩⟩

/-- Given three nonzero vectors, the angle between the first and the second plus the angle
between the second and the third equals the angle between the first and the third. -/
@[simp]
theorem oangle_add {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) : hb.oangle x y + hb.oangle y z = hb.oangle x z :=
  by
  simp_rw [oangle]
  rw [← Complex.arg_mul_coe_angle]
  · rw [mul_comm, div_mul_div_cancel]
    simp [← hy]
    
  · simp [← hx, ← hy]
    
  · simp [← hy, ← hz]
    

/-- Given three nonzero vectors, the angle between the second and the third plus the angle
between the first and the second equals the angle between the first and the third. -/
@[simp]
theorem oangle_add_swap {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    hb.oangle y z + hb.oangle x y = hb.oangle x z := by
  rw [add_commₓ, hb.oangle_add hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the first and the second equals the angle between the second and the third. -/
@[simp]
theorem oangle_sub_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    hb.oangle x z - hb.oangle x y = hb.oangle y z := by
  rw [sub_eq_iff_eq_add, hb.oangle_add_swap hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the second and the third equals the angle between the first and the second. -/
@[simp]
theorem oangle_sub_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    hb.oangle x z - hb.oangle y z = hb.oangle x y := by
  rw [sub_eq_iff_eq_add, hb.oangle_add hx hy hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order results in 0. -/
@[simp]
theorem oangle_add_cyc3 {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    hb.oangle x y + hb.oangle y z + hb.oangle z x = 0 := by
  simp [← hx, ← hy, ← hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the first
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp]
theorem oangle_add_cyc3_neg_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    hb.oangle (-x) y + hb.oangle (-y) z + hb.oangle (-z) x = π := by
  rw [hb.oangle_neg_left hx hy, hb.oangle_neg_left hy hz, hb.oangle_neg_left hz hx,
    show
      hb.oangle x y + π + (hb.oangle y z + π) + (hb.oangle z x + π) =
        hb.oangle x y + hb.oangle y z + hb.oangle z x + (π + π + π : Real.Angle)
      by
      abel,
    hb.oangle_add_cyc3 hx hy hz, Real.Angle.coe_pi_add_coe_pi, zero_addₓ, zero_addₓ]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the second
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp]
theorem oangle_add_cyc3_neg_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    hb.oangle x (-y) + hb.oangle y (-z) + hb.oangle z (-x) = π := by
  simp_rw [← oangle_neg_left_eq_neg_right, hb.oangle_add_cyc3_neg_left hx hy hz]

/-- Pons asinorum, oriented vector angle form. -/
theorem oangle_sub_eq_oangle_sub_rev_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) : hb.oangle x (x - y) = hb.oangle (y - x) y :=
  by
  by_cases' hx : x = 0
  · simp [← hx]
    
  · have hy : y ≠ 0 := norm_ne_zero_iff.1 (h ▸ norm_ne_zero_iff.2 hx)
    simp_rw [hb.oangle_rev y, oangle, LinearIsometryEquiv.map_sub, ← Complex.arg_conj_coe_angle, sub_div,
      div_self ((Complex.isometryOfOrthonormal hb).symm.map_eq_zero_iff.Not.2 hx),
      div_self ((Complex.isometryOfOrthonormal hb).symm.map_eq_zero_iff.Not.2 hy), map_sub, map_one]
    rw [← inv_div]
    simp_rw [Complex.inv_def, Complex.norm_sq_div, ← Complex.sq_abs, ← Complex.norm_eq_abs,
      LinearIsometryEquiv.norm_map, h]
    simp [← hy]
    

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:92:4: warning: unsupported: rw with cfg: { occs := occurrences.pos «expr[ ,]»([1]) }
/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
vector angle form. -/
theorem oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x ≠ y) (h : ∥x∥ = ∥y∥) :
    hb.oangle y x = π - (2 : ℤ) • hb.oangle (y - x) y := by
  rw [two_zsmul]
  rw [← hb.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]
  rw [eq_sub_iff_add_eq, ← oangle_neg_neg, ← add_assocₓ]
  have hy : y ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at h
    exact hn h
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (h.symm ▸ norm_ne_zero_iff.2 hy)
  convert hb.oangle_add_cyc3_neg_right (neg_ne_zero.2 hy) hx (sub_ne_zero_of_ne hn.symm) <;> simp

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form. -/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z) (hxy : ∥x∥ = ∥y∥)
    (hxz : ∥x∥ = ∥z∥) : hb.oangle y z = (2 : ℤ) • hb.oangle (y - x) (z - x) := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at hxy
    exact hxyne hxy
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (hxy.symm ▸ norm_ne_zero_iff.2 hy)
  have hz : z ≠ 0 := norm_ne_zero_iff.1 (hxz ▸ norm_ne_zero_iff.2 hx)
  calc hb.oangle y z = hb.oangle x z - hb.oangle x y :=
      (hb.oangle_sub_left hx hy hz).symm _ = π - (2 : ℤ) • hb.oangle (x - z) x - (π - (2 : ℤ) • hb.oangle (x - y) x) :=
      by
      rw [hb.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxzne.symm hxz.symm,
        hb.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxyne.symm
          hxy.symm]_ = (2 : ℤ) • (hb.oangle (x - y) x - hb.oangle (x - z) x) :=
      by
      abel _ = (2 : ℤ) • hb.oangle (x - y) (x - z) := by
      rw
        [hb.oangle_sub_right (sub_ne_zero_of_ne hxyne) (sub_ne_zero_of_ne hxzne)
          hx]_ = (2 : ℤ) • hb.oangle (y - x) (z - x) :=
      by
      rw [← oangle_neg_neg, neg_sub, neg_sub]

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form with radius specified. -/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z) {r : ℝ}
    (hx : ∥x∥ = r) (hy : ∥y∥ = r) (hz : ∥z∥ = r) : hb.oangle y z = (2 : ℤ) • hb.oangle (y - x) (z - x) :=
  hb.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne (hy.symm ▸ hx) (hz.symm ▸ hx)

/-- Oriented vector angle version of "angles in same segment are equal" and "opposite angles of
a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same
result), represented here as equality of twice the angles. -/
theorem two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x₁ ≠ y) (hx₁zne : x₁ ≠ z)
    (hx₂yne : x₂ ≠ y) (hx₂zne : x₂ ≠ z) {r : ℝ} (hx₁ : ∥x₁∥ = r) (hx₂ : ∥x₂∥ = r) (hy : ∥y∥ = r) (hz : ∥z∥ = r) :
    (2 : ℤ) • hb.oangle (y - x₁) (z - x₁) = (2 : ℤ) • hb.oangle (y - x₂) (z - x₂) :=
  hb.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₁yne hx₁zne hx₁ hy hz ▸
    hb.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₂yne hx₂zne hx₂ hy hz

/-- A rotation by the oriented angle `θ`. -/
def rotation (θ : Real.Angle) : V ≃ₗᵢ[ℝ] V :=
  ((Complex.isometryOfOrthonormal hb).symm.trans (rotation (Real.Angle.expMapCircle θ))).trans
    (Complex.isometryOfOrthonormal hb)

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
theorem det_rotation (θ : Real.Angle) : ((hb.rotation θ).toLinearEquiv : V →ₗ[ℝ] V).det = 1 := by
  simp [← rotation, LinearIsometryEquiv.to_linear_equiv_symm, LinearEquiv.comp_coe]

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
theorem linear_equiv_det_rotation (θ : Real.Angle) : (hb.rotation θ).toLinearEquiv.det = 1 := by
  simp [← rotation, LinearIsometryEquiv.to_linear_equiv_symm]

/-- The inverse of `rotation` is rotation by the negation of the angle. -/
@[simp]
theorem rotation_symm (θ : Real.Angle) : (hb.rotation θ).symm = hb.rotation (-θ) := by
  simp [← rotation, ← LinearIsometryEquiv.trans_assoc]

/-- Rotation by 0 is the identity. -/
@[simp]
theorem rotation_zero : hb.rotation 0 = LinearIsometryEquiv.refl ℝ V := by
  simp [← rotation]

/-- Rotation by π is negation. -/
theorem rotation_pi : hb.rotation π = LinearIsometryEquiv.neg ℝ := by
  ext x
  simp [← rotation]

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp]
theorem rotation_trans (θ₁ θ₂ : Real.Angle) : (hb.rotation θ₁).trans (hb.rotation θ₂) = hb.rotation (θ₂ + θ₁) := by
  simp only [← rotation, LinearIsometryEquiv.trans_assoc]
  ext1 x
  simp

/-- Rotating the first vector by `θ` subtracts `θ` from the angle between two vectors. -/
@[simp]
theorem oangle_rotation_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    hb.oangle (hb.rotation θ x) y = hb.oangle x y - θ := by
  simp [← oangle, ← rotation, ← Complex.arg_div_coe_angle, ← Complex.arg_mul_coe_angle, ← hx, ← hy, ←
    ne_zero_of_mem_circle]
  abel

/-- Rotating the second vector by `θ` adds `θ` to the angle between two vectors. -/
@[simp]
theorem oangle_rotation_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    hb.oangle x (hb.rotation θ y) = hb.oangle x y + θ := by
  simp [← oangle, ← rotation, ← Complex.arg_div_coe_angle, ← Complex.arg_mul_coe_angle, ← hx, ← hy, ←
    ne_zero_of_mem_circle]
  abel

/-- The rotation of a vector by `θ` has an angle of `-θ` from that vector. -/
@[simp]
theorem oangle_rotation_self_left {x : V} (hx : x ≠ 0) (θ : Real.Angle) : hb.oangle (hb.rotation θ x) x = -θ := by
  simp [← hx]

/-- A vector has an angle of `θ` from the rotation of that vector by `θ`. -/
@[simp]
theorem oangle_rotation_self_right {x : V} (hx : x ≠ 0) (θ : Real.Angle) : hb.oangle x (hb.rotation θ x) = θ := by
  simp [← hx]

/-- Rotating the first vector by the angle between the two vectors results an an angle of 0. -/
@[simp]
theorem oangle_rotation_oangle_left (x y : V) : hb.oangle (hb.rotation (hb.oangle x y) x) y = 0 := by
  by_cases' hx : x = 0
  · simp [← hx]
    
  · by_cases' hy : y = 0
    · simp [← hy]
      
    · simp [← hx, ← hy]
      
    

/-- Rotating the first vector by the angle between the two vectors and swapping the vectors
results an an angle of 0. -/
@[simp]
theorem oangle_rotation_oangle_right (x y : V) : hb.oangle y (hb.rotation (hb.oangle x y) x) = 0 := by
  rw [oangle_rev]
  simp

/-- Rotating both vectors by the same angle does not change the angle between those vectors. -/
@[simp]
theorem oangle_rotation (x y : V) (θ : Real.Angle) : hb.oangle (hb.rotation θ x) (hb.rotation θ y) = hb.oangle x y := by
  by_cases' hx : x = 0 <;> by_cases' hy : y = 0 <;> simp [← hx, ← hy]

/-- A rotation of a nonzero vector equals that vector if and only if the angle is zero. -/
@[simp]
theorem rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : Real.Angle) : hb.rotation θ x = x ↔ θ = 0 := by
  constructor
  · intro h
    rw [eq_comm]
    simpa [← hx, ← h] using hb.oangle_rotation_right hx hx θ
    
  · intro h
    simp [← h]
    

/-- A nonzero vector equals a rotation of that vector if and only if the angle is zero. -/
@[simp]
theorem eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : Real.Angle) : x = hb.rotation θ x ↔ θ = 0 := by
  rw [← hb.rotation_eq_self_iff_angle_eq_zero hx, eq_comm]

/-- A rotation of a vector equals that vector if and only if the vector or the angle is zero. -/
theorem rotation_eq_self_iff (x : V) (θ : Real.Angle) : hb.rotation θ x = x ↔ x = 0 ∨ θ = 0 := by
  by_cases' h : x = 0 <;> simp [← h]

/-- A vector equals a rotation of that vector if and only if the vector or the angle is zero. -/
theorem eq_rotation_self_iff (x : V) (θ : Real.Angle) : x = hb.rotation θ x ↔ x = 0 ∨ θ = 0 := by
  rw [← rotation_eq_self_iff, eq_comm]

/-- Rotating a vector by the angle to another vector gives the second vector if and only if the
norms are equal. -/
@[simp]
theorem rotation_oangle_eq_iff_norm_eq (x y : V) : hb.rotation (hb.oangle x y) x = y ↔ ∥x∥ = ∥y∥ := by
  constructor
  · intro h
    rw [← h, LinearIsometryEquiv.norm_map]
    
  · intro h
    rw [hb.eq_iff_oangle_eq_zero_of_norm_eq] <;> simp [← h]
    

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by the ratio of the norms. -/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    hb.oangle x y = θ ↔ y = (∥y∥ / ∥x∥) • hb.rotation θ x := by
  have hp := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx)
  constructor
  · rintro rfl
    rw [← LinearIsometryEquiv.map_smul, ← hb.oangle_smul_left_of_pos x y hp, eq_comm, rotation_oangle_eq_iff_norm_eq,
      norm_smul, Real.norm_of_nonneg hp.le, div_mul_cancel _ (norm_ne_zero_iff.2 hx)]
    
  · intro hye
    rw [hye, hb.oangle_smul_right_of_pos _ _ hp, hb.oangle_rotation_self_right hx]
    

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by a positive real. -/
theorem oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    hb.oangle x y = θ ↔ ∃ r : ℝ, 0 < r ∧ y = r • hb.rotation θ x := by
  constructor
  · intro h
    rw [hb.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy] at h
    exact ⟨∥y∥ / ∥x∥, div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx), h⟩
    
  · rintro ⟨r, hr, rfl⟩
    rw [hb.oangle_smul_right_of_pos _ _ hr, hb.oangle_rotation_self_right hx]
    

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by the ratio of the norms, or `θ` and at least one of the
vectors are zero. -/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    hb.oangle x y = θ ↔ x ≠ 0 ∧ y ≠ 0 ∧ y = (∥y∥ / ∥x∥) • hb.rotation θ x ∨ θ = 0 ∧ (x = 0 ∨ y = 0) := by
  by_cases' hx : x = 0
  · simp [← hx, ← eq_comm]
    
  · by_cases' hy : y = 0
    · simp [← hy, ← eq_comm]
      
    · rw [hb.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy]
      simp [← hx, ← hy]
      
    

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by a positive real, or `θ` and at least one of the
vectors are zero. -/
theorem oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    hb.oangle x y = θ ↔ (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • hb.rotation θ x) ∨ θ = 0 ∧ (x = 0 ∨ y = 0) := by
  by_cases' hx : x = 0
  · simp [← hx, ← eq_comm]
    
  · by_cases' hy : y = 0
    · simp [← hy, ← eq_comm]
      
    · rw [hb.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy]
      simp [← hx, ← hy]
      
    

/-- Complex conjugation as a linear isometric equivalence in `V`. Note that this definition
depends on the choice of basis, not just on its orientation; for most geometrical purposes,
the `reflection` definitions should be preferred instead. -/
def conjLie : V ≃ₗᵢ[ℝ] V :=
  ((Complex.isometryOfOrthonormal hb).symm.trans Complex.conjLie).trans (Complex.isometryOfOrthonormal hb)

/-- The determinant of `conj_lie` (as a linear map) is equal to `-1`. -/
@[simp]
theorem det_conj_lie : (hb.conjLie.toLinearEquiv : V →ₗ[ℝ] V).det = -1 := by
  simp [← conj_lie, LinearIsometryEquiv.to_linear_equiv_symm, LinearEquiv.comp_coe]

/-- The determinant of `conj_lie` (as a linear equiv) is equal to `-1`. -/
@[simp]
theorem linear_equiv_det_conj_lie : hb.conjLie.toLinearEquiv.det = -1 := by
  simp [← conj_lie, LinearIsometryEquiv.to_linear_equiv_symm]

/-- `conj_lie` is its own inverse. -/
@[simp]
theorem conj_lie_symm : hb.conjLie.symm = hb.conjLie :=
  rfl

/-- Applying `conj_lie` to both vectors negates the angle between those vectors. -/
@[simp]
theorem oangle_conj_lie (x y : V) : hb.oangle (hb.conjLie x) (hb.conjLie y) = -hb.oangle x y := by
  simp only [← Orthonormal.conjLie, ← LinearIsometryEquiv.symm_apply_apply, ← Orthonormal.oangle, ← eq_self_iff_true, ←
    Function.comp_app, ← Complex.arg_coe_angle_eq_iff, ← LinearIsometryEquiv.coe_trans, ← neg_inj, ←
    Complex.conj_lie_apply, ← Complex.arg_conj_coe_angle, (starRingEnd ℂ).map_div]

/-- Any linear isometric equivalence in `V` is `rotation` or `conj_lie` composed with
`rotation`. -/
theorem exists_linear_isometry_equiv_eq (f : V ≃ₗᵢ[ℝ] V) :
    ∃ θ : Real.Angle, f = hb.rotation θ ∨ f = hb.conjLie.trans (hb.rotation θ) := by
  cases'
    linear_isometry_complex
      (((Complex.isometryOfOrthonormal hb).trans f).trans (Complex.isometryOfOrthonormal hb).symm) with
    a ha
  use Complex.arg a
  rcases ha with (ha | ha)
  · left
    simp only [← rotation, ha, ← LinearIsometryEquiv.trans_assoc, ← LinearIsometryEquiv.refl_trans, ←
      LinearIsometryEquiv.symm_trans_self, ← Real.Angle.exp_map_circle_coe, ← exp_map_circle_arg]
    simp [LinearIsometryEquiv.trans_assoc]
    
  · right
    simp only [← rotation, ← conj_lie, ← LinearIsometryEquiv.trans_assoc, ← Real.Angle.exp_map_circle_coe, ←
      exp_map_circle_arg]
    simp only [LinearIsometryEquiv.trans_assoc, ← LinearIsometryEquiv.self_trans_symm, ← LinearIsometryEquiv.trans_refl]
    simp_rw [LinearIsometryEquiv.trans_assoc Complex.conjLie, ← ha]
    simp only [← LinearIsometryEquiv.trans_assoc, ← LinearIsometryEquiv.refl_trans, ←
      LinearIsometryEquiv.symm_trans_self]
    simp [LinearIsometryEquiv.trans_assoc]
    

/-- Any linear isometric equivalence in `V` with positive determinant is `rotation`. -/
theorem exists_linear_isometry_equiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V} (hd : 0 < (f.toLinearEquiv : V →ₗ[ℝ] V).det) :
    ∃ θ : Real.Angle, f = hb.rotation θ := by
  rcases hb.exists_linear_isometry_equiv_eq f with ⟨θ, hf | hf⟩
  · exact ⟨θ, hf⟩
    
  · simp [← hf, LinearEquiv.coe_det] at hd
    norm_num  at hd
    

/-- Any linear isometric equivalence in `V` with negative determinant is `conj_lie` composed
with `rotation`. -/
theorem exists_linear_isometry_equiv_eq_of_det_neg {f : V ≃ₗᵢ[ℝ] V} (hd : (f.toLinearEquiv : V →ₗ[ℝ] V).det < 0) :
    ∃ θ : Real.Angle, f = hb.conjLie.trans (hb.rotation θ) := by
  rcases hb.exists_linear_isometry_equiv_eq f with ⟨θ, hf | hf⟩
  · simp [← hf, LinearEquiv.coe_det] at hd
    norm_num  at hd
    
  · exact ⟨θ, hf⟩
    

/-- Two bases with the same orientation are related by a `rotation`. -/
theorem exists_linear_isometry_equiv_map_eq_of_orientation_eq {b₂ : Basis (Finₓ 2) ℝ V} (hb₂ : Orthonormal ℝ b₂)
    (ho : b.Orientation = b₂.Orientation) : ∃ θ : Real.Angle, b₂ = b.map (hb.rotation θ).toLinearEquiv := by
  have h : b₂ = b.map (hb.equiv hb₂ (Equivₓ.refl _)).toLinearEquiv := by
    rw [hb.map_equiv]
    simp
  rw [eq_comm, h, b.orientation_comp_linear_equiv_eq_iff_det_pos] at ho
  cases' hb.exists_linear_isometry_equiv_eq_of_det_pos ho with θ hθ
  rw [hθ] at h
  exact ⟨θ, h⟩

/-- Two bases with opposite orientations are related by `conj_lie` composed with a `rotation`. -/
theorem exists_linear_isometry_equiv_map_eq_of_orientation_eq_neg {b₂ : Basis (Finₓ 2) ℝ V} (hb₂ : Orthonormal ℝ b₂)
    (ho : b.Orientation = -b₂.Orientation) :
    ∃ θ : Real.Angle, b₂ = b.map (hb.conjLie.trans (hb.rotation θ)).toLinearEquiv := by
  have h : b₂ = b.map (hb.equiv hb₂ (Equivₓ.refl _)).toLinearEquiv := by
    rw [hb.map_equiv]
    simp
  rw [eq_neg_iff_eq_neg, h, b.orientation_comp_linear_equiv_eq_neg_iff_det_neg] at ho
  cases' hb.exists_linear_isometry_equiv_eq_of_det_neg ho with θ hθ
  rw [hθ] at h
  exact ⟨θ, h⟩

/-- The angle between two vectors, with respect to a basis given by `basis.map` with a linear
isometric equivalence, equals the angle between those two vectors, transformed by the inverse of
that equivalence, with respect to the original basis. -/
@[simp]
theorem oangle_map (x y : V) (f : V ≃ₗᵢ[ℝ] V) :
    (hb.map_linear_isometry_equiv f).oangle x y = hb.oangle (f.symm x) (f.symm y) := by
  simp [← oangle]

/-- The value of `oangle` does not depend on the choice of basis for a given orientation. -/
theorem oangle_eq_of_orientation_eq {b₂ : Basis (Finₓ 2) ℝ V} (hb₂ : Orthonormal ℝ b₂)
    (ho : b.Orientation = b₂.Orientation) (x y : V) : hb.oangle x y = hb₂.oangle x y := by
  obtain ⟨θ, rfl⟩ := hb.exists_linear_isometry_equiv_map_eq_of_orientation_eq hb₂ ho
  simp [← hb]

/-- Negating the orientation negates the value of `oangle`. -/
theorem oangle_eq_neg_of_orientation_eq_neg {b₂ : Basis (Finₓ 2) ℝ V} (hb₂ : Orthonormal ℝ b₂)
    (ho : b.Orientation = -b₂.Orientation) (x y : V) : hb.oangle x y = -hb₂.oangle x y := by
  obtain ⟨θ, rfl⟩ := hb.exists_linear_isometry_equiv_map_eq_of_orientation_eq_neg hb₂ ho
  rw [hb.oangle_map]
  simp [← hb]

/-- `rotation` does not depend on the choice of basis for a given orientation. -/
theorem rotation_eq_of_orientation_eq {b₂ : Basis (Finₓ 2) ℝ V} (hb₂ : Orthonormal ℝ b₂)
    (ho : b.Orientation = b₂.Orientation) (θ : Real.Angle) : hb.rotation θ = hb₂.rotation θ := by
  obtain ⟨θ₂, rfl⟩ := hb.exists_linear_isometry_equiv_map_eq_of_orientation_eq hb₂ ho
  simp_rw [rotation, Complex.map_isometry_of_orthonormal hb]
  simp only [← LinearIsometryEquiv.trans_assoc, ← LinearIsometryEquiv.self_trans_symm, ← LinearIsometryEquiv.refl_trans,
    ← LinearIsometryEquiv.symm_trans]
  simp only [LinearIsometryEquiv.trans_assoc, ← _root_.rotation_symm, ← _root_.rotation_trans, ←
    mul_comm (Real.Angle.expMapCircle θ), mul_assoc, ← mul_right_invₓ, ← one_mulₓ]

/-- Negating the orientation negates the angle in `rotation`. -/
theorem rotation_eq_rotation_neg_of_orientation_eq_neg {b₂ : Basis (Finₓ 2) ℝ V} (hb₂ : Orthonormal ℝ b₂)
    (ho : b.Orientation = -b₂.Orientation) (θ : Real.Angle) : hb.rotation θ = hb₂.rotation (-θ) := by
  obtain ⟨θ₂, rfl⟩ := hb.exists_linear_isometry_equiv_map_eq_of_orientation_eq_neg hb₂ ho
  simp_rw [rotation, Complex.map_isometry_of_orthonormal hb, conj_lie]
  simp only [← LinearIsometryEquiv.trans_assoc, ← LinearIsometryEquiv.self_trans_symm, ← LinearIsometryEquiv.refl_trans,
    ← LinearIsometryEquiv.symm_trans]
  congr 1
  simp only [LinearIsometryEquiv.trans_assoc, ← _root_.rotation_symm, ← LinearIsometryEquiv.symm_symm, ←
    LinearIsometryEquiv.self_trans_symm, ← LinearIsometryEquiv.trans_refl, ← Complex.conj_lie_symm]
  congr 1
  ext1 x
  simp only [← LinearIsometryEquiv.coe_trans, ← Function.comp_app, ← rotation_apply, ← Complex.conj_lie_apply, ←
    map_mul, ← star_ring_end_self_apply, coe_inv_circle_eq_conj, ← inv_invₓ, ← Real.Angle.exp_map_circle_neg, mul_assoc]
  congr 1
  simp only [← mul_comm (Real.Angle.expMapCircle θ₂ : ℂ), ← mul_assoc]
  rw [← Submonoid.coe_mul, mul_left_invₓ, Submonoid.coe_one, mul_oneₓ]

end Orthonormal

namespace Orientation

open FiniteDimensional

variable {V : Type _} [InnerProductSpace ℝ V]

variable [hd2 : Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Finₓ 2))

include hd2 o

-- mathport name: «exprob»
local notation "ob" =>
  o.fin_orthonormal_basis_orthonormal
    (by
      decide)
    hd2.out

/-- The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0.
See `inner_product_geometry.angle` for the corresponding unoriented angle definition. -/
def oangle (x y : V) : Real.Angle :=
  ob.oangle x y

/-- Oriented angles are continuous when the vectors involved are nonzero. -/
theorem continuous_at_oangle {x : V × V} (hx1 : x.1 ≠ 0) (hx2 : x.2 ≠ 0) :
    ContinuousAt (fun y : V × V => o.oangle y.1 y.2) x :=
  ob.continuous_at_oangle hx1 hx2

/-- If the first vector passed to `oangle` is 0, the result is 0. -/
@[simp]
theorem oangle_zero_left (x : V) : o.oangle 0 x = 0 :=
  ob.oangle_zero_left x

/-- If the second vector passed to `oangle` is 0, the result is 0. -/
@[simp]
theorem oangle_zero_right (x : V) : o.oangle x 0 = 0 :=
  ob.oangle_zero_right x

/-- If the two vectors passed to `oangle` are the same, the result is 0. -/
@[simp]
theorem oangle_self (x : V) : o.oangle x x = 0 :=
  ob.oangle_self x

/-- Swapping the two vectors passed to `oangle` negates the angle. -/
theorem oangle_rev (x y : V) : o.oangle y x = -o.oangle x y :=
  ob.oangle_rev x y

/-- Adding the angles between two vectors in each order results in 0. -/
@[simp]
theorem oangle_add_oangle_rev (x y : V) : o.oangle x y + o.oangle y x = 0 :=
  ob.oangle_add_oangle_rev x y

/-- Negating the first vector passed to `oangle` adds `π` to the angle. -/
theorem oangle_neg_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : o.oangle (-x) y = o.oangle x y + π :=
  ob.oangle_neg_left hx hy

/-- Negating the second vector passed to `oangle` adds `π` to the angle. -/
theorem oangle_neg_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : o.oangle x (-y) = o.oangle x y + π :=
  ob.oangle_neg_right hx hy

/-- Negating the first vector passed to `oangle` does not change twice the angle. -/
@[simp]
theorem two_zsmul_oangle_neg_left (x y : V) : (2 : ℤ) • o.oangle (-x) y = (2 : ℤ) • o.oangle x y :=
  ob.two_zsmul_oangle_neg_left x y

/-- Negating the second vector passed to `oangle` does not change twice the angle. -/
@[simp]
theorem two_zsmul_oangle_neg_right (x y : V) : (2 : ℤ) • o.oangle x (-y) = (2 : ℤ) • o.oangle x y :=
  ob.two_zsmul_oangle_neg_right x y

/-- Negating both vectors passed to `oangle` does not change the angle. -/
@[simp]
theorem oangle_neg_neg (x y : V) : o.oangle (-x) (-y) = o.oangle x y :=
  ob.oangle_neg_neg x y

/-- Negating the first vector produces the same angle as negating the second vector. -/
theorem oangle_neg_left_eq_neg_right (x y : V) : o.oangle (-x) y = o.oangle x (-y) :=
  ob.oangle_neg_left_eq_neg_right x y

/-- The angle between the negation of a nonzero vector and that vector is `π`. -/
@[simp]
theorem oangle_neg_self_left {x : V} (hx : x ≠ 0) : o.oangle (-x) x = π :=
  ob.oangle_neg_self_left hx

/-- The angle between a nonzero vector and its negation is `π`. -/
@[simp]
theorem oangle_neg_self_right {x : V} (hx : x ≠ 0) : o.oangle x (-x) = π :=
  ob.oangle_neg_self_right hx

/-- Twice the angle between the negation of a vector and that vector is 0. -/
@[simp]
theorem two_zsmul_oangle_neg_self_left (x : V) : (2 : ℤ) • o.oangle (-x) x = 0 :=
  ob.two_zsmul_oangle_neg_self_left x

/-- Twice the angle between a vector and its negation is 0. -/
@[simp]
theorem two_zsmul_oangle_neg_self_right (x : V) : (2 : ℤ) • o.oangle x (-x) = 0 :=
  ob.two_zsmul_oangle_neg_self_right x

/-- Adding the angles between two vectors in each order, with the first vector in each angle
negated, results in 0. -/
@[simp]
theorem oangle_add_oangle_rev_neg_left (x y : V) : o.oangle (-x) y + o.oangle (-y) x = 0 :=
  ob.oangle_add_oangle_rev_neg_left x y

/-- Adding the angles between two vectors in each order, with the second vector in each angle
negated, results in 0. -/
@[simp]
theorem oangle_add_oangle_rev_neg_right (x y : V) : o.oangle x (-y) + o.oangle y (-x) = 0 :=
  ob.oangle_add_oangle_rev_neg_right x y

/-- Multiplying the first vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp]
theorem oangle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : o.oangle (r • x) y = o.oangle x y :=
  ob.oangle_smul_left_of_pos x y hr

/-- Multiplying the second vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp]
theorem oangle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : o.oangle x (r • y) = o.oangle x y :=
  ob.oangle_smul_right_of_pos x y hr

/-- Multiplying the first vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp]
theorem oangle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) : o.oangle (r • x) y = o.oangle (-x) y :=
  ob.oangle_smul_left_of_neg x y hr

/-- Multiplying the second vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp]
theorem oangle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) : o.oangle x (r • y) = o.oangle x (-y) :=
  ob.oangle_smul_right_of_neg x y hr

/-- The angle between a nonnegative multiple of a vector and that vector is 0. -/
@[simp]
theorem oangle_smul_left_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) : o.oangle (r • x) x = 0 :=
  ob.oangle_smul_left_self_of_nonneg x hr

/-- The angle between a vector and a nonnegative multiple of that vector is 0. -/
@[simp]
theorem oangle_smul_right_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) : o.oangle x (r • x) = 0 :=
  ob.oangle_smul_right_self_of_nonneg x hr

/-- The angle between two nonnegative multiples of the same vector is 0. -/
@[simp]
theorem oangle_smul_smul_self_of_nonneg (x : V) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    o.oangle (r₁ • x) (r₂ • x) = 0 :=
  ob.oangle_smul_smul_self_of_nonneg x hr₁ hr₂

/-- Multiplying the first vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp]
theorem two_zsmul_oangle_smul_left_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
    (2 : ℤ) • o.oangle (r • x) y = (2 : ℤ) • o.oangle x y :=
  ob.two_zsmul_oangle_smul_left_of_ne_zero x y hr

/-- Multiplying the second vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp]
theorem two_zsmul_oangle_smul_right_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
    (2 : ℤ) • o.oangle x (r • y) = (2 : ℤ) • o.oangle x y :=
  ob.two_zsmul_oangle_smul_right_of_ne_zero x y hr

/-- Twice the angle between a multiple of a vector and that vector is 0. -/
@[simp]
theorem two_zsmul_oangle_smul_left_self (x : V) {r : ℝ} : (2 : ℤ) • o.oangle (r • x) x = 0 :=
  ob.two_zsmul_oangle_smul_left_self x

/-- Twice the angle between a vector and a multiple of that vector is 0. -/
@[simp]
theorem two_zsmul_oangle_smul_right_self (x : V) {r : ℝ} : (2 : ℤ) • o.oangle x (r • x) = 0 :=
  ob.two_zsmul_oangle_smul_right_self x

/-- Twice the angle between two multiples of a vector is 0. -/
@[simp]
theorem two_zsmul_oangle_smul_smul_self (x : V) {r₁ r₂ : ℝ} : (2 : ℤ) • o.oangle (r₁ • x) (r₂ • x) = 0 :=
  ob.two_zsmul_oangle_smul_smul_self x

/-- Two vectors are equal if and only if they have equal norms and zero angle between them. -/
theorem eq_iff_norm_eq_and_oangle_eq_zero (x y : V) : x = y ↔ ∥x∥ = ∥y∥ ∧ o.oangle x y = 0 :=
  ob.eq_iff_norm_eq_and_oangle_eq_zero x y

/-- Two vectors with equal norms are equal if and only if they have zero angle between them. -/
theorem eq_iff_oangle_eq_zero_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) : x = y ↔ o.oangle x y = 0 :=
  ob.eq_iff_oangle_eq_zero_of_norm_eq h

/-- Two vectors with zero angle between them are equal if and only if they have equal norms. -/
theorem eq_iff_norm_eq_of_oangle_eq_zero {x y : V} (h : o.oangle x y = 0) : x = y ↔ ∥x∥ = ∥y∥ :=
  ob.eq_iff_norm_eq_of_oangle_eq_zero h

/-- Given three nonzero vectors, the angle between the first and the second plus the angle
between the second and the third equals the angle between the first and the third. -/
@[simp]
theorem oangle_add {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) : o.oangle x y + o.oangle y z = o.oangle x z :=
  ob.oangle_add hx hy hz

/-- Given three nonzero vectors, the angle between the second and the third plus the angle
between the first and the second equals the angle between the first and the third. -/
@[simp]
theorem oangle_add_swap {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle y z + o.oangle x y = o.oangle x z :=
  ob.oangle_add_swap hx hy hz

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the first and the second equals the angle between the second and the third. -/
@[simp]
theorem oangle_sub_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x z - o.oangle x y = o.oangle y z :=
  ob.oangle_sub_left hx hy hz

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the second and the third equals the angle between the first and the second. -/
@[simp]
theorem oangle_sub_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x z - o.oangle y z = o.oangle x y :=
  ob.oangle_sub_right hx hy hz

/-- Given three nonzero vectors, adding the angles between them in cyclic order results in 0. -/
@[simp]
theorem oangle_add_cyc3 {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x y + o.oangle y z + o.oangle z x = 0 :=
  ob.oangle_add_cyc3 hx hy hz

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the first
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp]
theorem oangle_add_cyc3_neg_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle (-x) y + o.oangle (-y) z + o.oangle (-z) x = π :=
  ob.oangle_add_cyc3_neg_left hx hy hz

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the second
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp]
theorem oangle_add_cyc3_neg_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x (-y) + o.oangle y (-z) + o.oangle z (-x) = π :=
  ob.oangle_add_cyc3_neg_right hx hy hz

/-- Pons asinorum, oriented vector angle form. -/
theorem oangle_sub_eq_oangle_sub_rev_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) : o.oangle x (x - y) = o.oangle (y - x) y :=
  ob.oangle_sub_eq_oangle_sub_rev_of_norm_eq h

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
vector angle form. -/
theorem oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x ≠ y) (h : ∥x∥ = ∥y∥) :
    o.oangle y x = π - (2 : ℤ) • o.oangle (y - x) y :=
  ob.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hn h

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form. -/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z) (hxy : ∥x∥ = ∥y∥)
    (hxz : ∥x∥ = ∥z∥) : o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
  ob.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne hxy hxz

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form with radius specified. -/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z) {r : ℝ}
    (hx : ∥x∥ = r) (hy : ∥y∥ = r) (hz : ∥z∥ = r) : o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
  ob.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hxyne hxzne hx hy hz

/-- Oriented vector angle version of "angles in same segment are equal" and "opposite angles of
a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same
result), represented here as equality of twice the angles. -/
theorem two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x₁ ≠ y) (hx₁zne : x₁ ≠ z)
    (hx₂yne : x₂ ≠ y) (hx₂zne : x₂ ≠ z) {r : ℝ} (hx₁ : ∥x₁∥ = r) (hx₂ : ∥x₂∥ = r) (hy : ∥y∥ = r) (hz : ∥z∥ = r) :
    (2 : ℤ) • o.oangle (y - x₁) (z - x₁) = (2 : ℤ) • o.oangle (y - x₂) (z - x₂) :=
  ob.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq hx₁yne hx₁zne hx₂yne hx₂zne hx₁ hx₂ hy hz

/-- A rotation by the oriented angle `θ`. -/
def rotation (θ : Real.Angle) : V ≃ₗᵢ[ℝ] V :=
  ob.rotation θ

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
theorem det_rotation (θ : Real.Angle) : ((o.rotation θ).toLinearEquiv : V →ₗ[ℝ] V).det = 1 :=
  ob.det_rotation θ

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
theorem linear_equiv_det_rotation (θ : Real.Angle) : (o.rotation θ).toLinearEquiv.det = 1 :=
  ob.linear_equiv_det_rotation θ

/-- The inverse of `rotation` is rotation by the negation of the angle. -/
@[simp]
theorem rotation_symm (θ : Real.Angle) : (o.rotation θ).symm = o.rotation (-θ) :=
  ob.rotation_symm θ

/-- Rotation by 0 is the identity. -/
@[simp]
theorem rotation_zero : o.rotation 0 = LinearIsometryEquiv.refl ℝ V :=
  ob.rotation_zero

/-- Rotation by π is negation. -/
theorem rotation_pi : o.rotation π = LinearIsometryEquiv.neg ℝ :=
  ob.rotation_pi

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp]
theorem rotation_trans (θ₁ θ₂ : Real.Angle) : (o.rotation θ₁).trans (o.rotation θ₂) = o.rotation (θ₂ + θ₁) :=
  ob.rotation_trans θ₁ θ₂

/-- Rotating the first vector by `θ` subtracts `θ` from the angle between two vectors. -/
@[simp]
theorem oangle_rotation_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) y = o.oangle x y - θ :=
  ob.oangle_rotation_left hx hy θ

/-- Rotating the second vector by `θ` adds `θ` to the angle between two vectors. -/
@[simp]
theorem oangle_rotation_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    o.oangle x (o.rotation θ y) = o.oangle x y + θ :=
  ob.oangle_rotation_right hx hy θ

/-- The rotation of a vector by `θ` has an angle of `-θ` from that vector. -/
@[simp]
theorem oangle_rotation_self_left {x : V} (hx : x ≠ 0) (θ : Real.Angle) : o.oangle (o.rotation θ x) x = -θ :=
  ob.oangle_rotation_self_left hx θ

/-- A vector has an angle of `θ` from the rotation of that vector by `θ`. -/
@[simp]
theorem oangle_rotation_self_right {x : V} (hx : x ≠ 0) (θ : Real.Angle) : o.oangle x (o.rotation θ x) = θ :=
  ob.oangle_rotation_self_right hx θ

/-- Rotating the first vector by the angle between the two vectors results an an angle of 0. -/
@[simp]
theorem oangle_rotation_oangle_left (x y : V) : o.oangle (o.rotation (o.oangle x y) x) y = 0 :=
  ob.oangle_rotation_oangle_left x y

/-- Rotating the first vector by the angle between the two vectors and swapping the vectors
results an an angle of 0. -/
@[simp]
theorem oangle_rotation_oangle_right (x y : V) : o.oangle y (o.rotation (o.oangle x y) x) = 0 :=
  ob.oangle_rotation_oangle_right x y

/-- Rotating both vectors by the same angle does not change the angle between those vectors. -/
@[simp]
theorem oangle_rotation (x y : V) (θ : Real.Angle) : o.oangle (o.rotation θ x) (o.rotation θ y) = o.oangle x y :=
  ob.oangle_rotation x y θ

/-- A rotation of a nonzero vector equals that vector if and only if the angle is zero. -/
@[simp]
theorem rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : Real.Angle) : o.rotation θ x = x ↔ θ = 0 :=
  ob.rotation_eq_self_iff_angle_eq_zero hx θ

/-- A nonzero vector equals a rotation of that vector if and only if the angle is zero. -/
@[simp]
theorem eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : Real.Angle) : x = o.rotation θ x ↔ θ = 0 :=
  ob.eq_rotation_self_iff_angle_eq_zero hx θ

/-- A rotation of a vector equals that vector if and only if the vector or the angle is zero. -/
theorem rotation_eq_self_iff (x : V) (θ : Real.Angle) : o.rotation θ x = x ↔ x = 0 ∨ θ = 0 :=
  ob.rotation_eq_self_iff x θ

/-- A vector equals a rotation of that vector if and only if the vector or the angle is zero. -/
theorem eq_rotation_self_iff (x : V) (θ : Real.Angle) : x = o.rotation θ x ↔ x = 0 ∨ θ = 0 :=
  ob.eq_rotation_self_iff x θ

/-- Rotating a vector by the angle to another vector gives the second vector if and only if the
norms are equal. -/
@[simp]
theorem rotation_oangle_eq_iff_norm_eq (x y : V) : o.rotation (o.oangle x y) x = y ↔ ∥x∥ = ∥y∥ :=
  ob.rotation_oangle_eq_iff_norm_eq x y

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by the ratio of the norms. -/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    o.oangle x y = θ ↔ y = (∥y∥ / ∥x∥) • o.rotation θ x :=
  ob.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy θ

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by a positive real. -/
theorem oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    o.oangle x y = θ ↔ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x :=
  ob.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy θ

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by the ratio of the norms, or `θ` and at least one of the
vectors are zero. -/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    o.oangle x y = θ ↔ x ≠ 0 ∧ y ≠ 0 ∧ y = (∥y∥ / ∥x∥) • o.rotation θ x ∨ θ = 0 ∧ (x = 0 ∨ y = 0) :=
  ob.oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero θ

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by a positive real, or `θ` and at least one of the
vectors are zero. -/
theorem oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    o.oangle x y = θ ↔ (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x) ∨ θ = 0 ∧ (x = 0 ∨ y = 0) :=
  ob.oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero θ

/-- Any linear isometric equivalence in `V` with positive determinant is `rotation`. -/
theorem exists_linear_isometry_equiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V} (hd : 0 < (f.toLinearEquiv : V →ₗ[ℝ] V).det) :
    ∃ θ : Real.Angle, f = o.rotation θ :=
  ob.exists_linear_isometry_equiv_eq_of_det_pos hd

/-- The angle between two vectors, with respect to an orientation given by `orientation.map`
with a linear isometric equivalence, equals the angle between those two vectors, transformed by
the inverse of that equivalence, with respect to the original orientation. -/
@[simp]
theorem oangle_map (x y : V) (f : V ≃ₗᵢ[ℝ] V) :
    (Orientation.map (Finₓ 2) f.toLinearEquiv o).oangle x y = o.oangle (f.symm x) (f.symm y) := by
  convert ob.oangle_map x y f using 1
  refine' Orthonormal.oangle_eq_of_orientation_eq _ _ _ _ _
  simp_rw [Basis.orientation_map, Orientation.fin_orthonormal_basis_orientation]

/-- `orientation.oangle` equals `orthonormal.oangle` for any orthonormal basis with that
orientation. -/
theorem oangle_eq_basis_oangle {b : Basis (Finₓ 2) ℝ V} (hb : Orthonormal ℝ b) (h : b.Orientation = o) (x y : V) :
    o.oangle x y = hb.oangle x y := by
  rw [oangle]
  refine' Orthonormal.oangle_eq_of_orientation_eq _ _ _ _ _
  simp [← h]

/-- Negating the orientation negates the value of `oangle`. -/
theorem oangle_neg_orientation_eq_neg (x y : V) : (-o).oangle x y = -o.oangle x y := by
  simp_rw [oangle]
  refine' Orthonormal.oangle_eq_neg_of_orientation_eq_neg _ _ _ _ _
  simp_rw [Orientation.fin_orthonormal_basis_orientation]

/-- `orientation.rotation` equals `orthonormal.rotation` for any orthonormal basis with that
orientation. -/
theorem rotation_eq_basis_rotation {b : Basis (Finₓ 2) ℝ V} (hb : Orthonormal ℝ b) (h : b.Orientation = o) (θ : ℝ) :
    o.rotation θ = hb.rotation θ := by
  rw [rotation]
  refine' Orthonormal.rotation_eq_of_orientation_eq _ _ _ _
  simp [← h]

/-- Negating the orientation negates the angle in `rotation`. -/
theorem rotation_neg_orientation_eq_neg (θ : Real.Angle) : (-o).rotation θ = o.rotation (-θ) := by
  simp_rw [rotation]
  refine' Orthonormal.rotation_eq_rotation_neg_of_orientation_eq_neg _ _ _ _
  simp_rw [Orientation.fin_orthonormal_basis_orientation]

end Orientation

