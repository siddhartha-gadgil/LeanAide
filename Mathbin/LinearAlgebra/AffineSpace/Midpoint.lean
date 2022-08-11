/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.CharP.Invertible
import Mathbin.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Midpoint of a segment

## Main definitions

* `midpoint R x y`: midpoint of the segment `[x, y]`. We define it for `x` and `y`
  in a module over a ring `R` with invertible `2`.
* `add_monoid_hom.of_map_midpoint`: construct an `add_monoid_hom` given a map `f` such that
  `f` sends zero to zero and midpoints to midpoints.

## Main theorems

* `midpoint_eq_iff`: `z` is the midpoint of `[x, y]` if and only if `x + y = z + z`,
* `midpoint_unique`: `midpoint R x y` does not depend on `R`;
* `midpoint x y` is linear both in `x` and `y`;
* `point_reflection_midpoint_left`, `point_reflection_midpoint_right`:
  `equiv.point_reflection (midpoint R x y)` swaps `x` and `y`.

We do not mark most lemmas as `@[simp]` because it is hard to tell which side is simpler.

## Tags

midpoint, add_monoid_hom
-/


open AffineMap AffineEquiv

section

variable (R : Type _) {V V' P P' : Type _} [Ringₓ R] [Invertible (2 : R)] [AddCommGroupₓ V] [Module R V] [AddTorsor V P]
  [AddCommGroupₓ V'] [Module R V'] [AddTorsor V' P']

include V

/-- `midpoint x y` is the midpoint of the segment `[x, y]`. -/
def midpoint (x y : P) : P :=
  lineMap x y (⅟ 2 : R)

variable {R} {x y z : P}

include V'

@[simp]
theorem AffineMap.map_midpoint (f : P →ᵃ[R] P') (a b : P) : f (midpoint R a b) = midpoint R (f a) (f b) :=
  f.apply_line_map a b _

@[simp]
theorem AffineEquiv.map_midpoint (f : P ≃ᵃ[R] P') (a b : P) : f (midpoint R a b) = midpoint R (f a) (f b) :=
  f.apply_line_map a b _

omit V'

@[simp]
theorem AffineEquiv.point_reflection_midpoint_left (x y : P) : pointReflection R (midpoint R x y) x = y := by
  rw [midpoint, point_reflection_apply, line_map_apply, vadd_vsub, vadd_vadd, ← add_smul, ← two_mul, mul_inv_of_self,
    one_smul, vsub_vadd]

theorem midpoint_comm (x y : P) : midpoint R x y = midpoint R y x := by
  rw [midpoint, ← line_map_apply_one_sub, one_sub_inv_of_two, midpoint]

@[simp]
theorem AffineEquiv.point_reflection_midpoint_right (x y : P) : pointReflection R (midpoint R x y) y = x := by
  rw [midpoint_comm, AffineEquiv.point_reflection_midpoint_left]

theorem midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) :
    midpoint R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) :=
  line_map_vsub_line_map _ _ _ _ _

theorem midpoint_vadd_midpoint (v v' : V) (p p' : P) :
    midpoint R v v' +ᵥ midpoint R p p' = midpoint R (v +ᵥ p) (v' +ᵥ p') :=
  line_map_vadd_line_map _ _ _ _ _

theorem midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ pointReflection R z x = y :=
  eq_comm.trans
    ((injective_point_reflection_left_of_module R x).eq_iff' (AffineEquiv.point_reflection_midpoint_left x y)).symm

@[simp]
theorem midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₁ = (⅟ 2 : R) • (p₂ -ᵥ p₁) :=
  line_map_vsub_left _ _ _

@[simp]
theorem midpoint_vsub_right (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₂ = (⅟ 2 : R) • (p₁ -ᵥ p₂) := by
  rw [midpoint_comm, midpoint_vsub_left]

@[simp]
theorem left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁ p₂ = (⅟ 2 : R) • (p₁ -ᵥ p₂) :=
  left_vsub_line_map _ _ _

@[simp]
theorem right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R p₁ p₂ = (⅟ 2 : R) • (p₂ -ᵥ p₁) := by
  rw [midpoint_comm, left_vsub_midpoint]

@[simp]
theorem midpoint_sub_left (v₁ v₂ : V) : midpoint R v₁ v₂ - v₁ = (⅟ 2 : R) • (v₂ - v₁) :=
  midpoint_vsub_left v₁ v₂

@[simp]
theorem midpoint_sub_right (v₁ v₂ : V) : midpoint R v₁ v₂ - v₂ = (⅟ 2 : R) • (v₁ - v₂) :=
  midpoint_vsub_right v₁ v₂

@[simp]
theorem left_sub_midpoint (v₁ v₂ : V) : v₁ - midpoint R v₁ v₂ = (⅟ 2 : R) • (v₁ - v₂) :=
  left_vsub_midpoint v₁ v₂

@[simp]
theorem right_sub_midpoint (v₁ v₂ : V) : v₂ - midpoint R v₁ v₂ = (⅟ 2 : R) • (v₂ - v₁) :=
  right_vsub_midpoint v₁ v₂

variable (R)

theorem midpoint_eq_midpoint_iff_vsub_eq_vsub {x x' y y' : P} : midpoint R x y = midpoint R x' y' ↔ x -ᵥ x' = y' -ᵥ y :=
  by
  rw [← @vsub_eq_zero_iff_eq V, midpoint_vsub_midpoint, midpoint_eq_iff, point_reflection_apply, vsub_eq_sub, zero_sub,
    vadd_eq_add, add_zeroₓ, neg_eq_iff_neg_eq, neg_vsub_eq_vsub_rev, eq_comm]

theorem midpoint_eq_iff' {x y z : P} : midpoint R x y = z ↔ Equivₓ.pointReflection z x = y :=
  midpoint_eq_iff

/-- `midpoint` does not depend on the ring `R`. -/
theorem midpoint_unique (R' : Type _) [Ringₓ R'] [Invertible (2 : R')] [Module R' V] (x y : P) :
    midpoint R x y = midpoint R' x y :=
  (midpoint_eq_iff' R).2 <| (midpoint_eq_iff' R').1 rfl

@[simp]
theorem midpoint_self (x : P) : midpoint R x x = x :=
  line_map_same_apply _ _

@[simp]
theorem midpoint_add_self (x y : V) : midpoint R x y + midpoint R x y = x + y :=
  calc
    midpoint R x y +ᵥ midpoint R x y = midpoint R x y +ᵥ midpoint R y x := by
      rw [midpoint_comm]
    _ = x + y := by
      rw [midpoint_vadd_midpoint, vadd_eq_add, vadd_eq_add, add_commₓ, midpoint_self]
    

theorem midpoint_zero_add (x y : V) : midpoint R 0 (x + y) = midpoint R x y :=
  (midpoint_eq_midpoint_iff_vsub_eq_vsub R).2 <| by
    simp [← sub_add_eq_sub_sub_swap]

theorem midpoint_eq_smul_add (x y : V) : midpoint R x y = (⅟ 2 : R) • (x + y) := by
  rw [midpoint_eq_iff, point_reflection_apply, vsub_eq_sub, vadd_eq_add, sub_add_eq_add_sub, ← two_smul R, smul_smul,
    mul_inv_of_self, one_smul, add_sub_cancel']

@[simp]
theorem midpoint_self_neg (x : V) : midpoint R x (-x) = 0 := by
  rw [midpoint_eq_smul_add, add_neg_selfₓ, smul_zero]

@[simp]
theorem midpoint_neg_self (x : V) : midpoint R (-x) x = 0 := by
  simpa using midpoint_self_neg R (-x)

@[simp]
theorem midpoint_sub_add (x y : V) : midpoint R (x - y) (x + y) = x := by
  rw [sub_eq_add_neg, ← vadd_eq_add, ← vadd_eq_add, ← midpoint_vadd_midpoint] <;> simp

@[simp]
theorem midpoint_add_sub (x y : V) : midpoint R (x + y) (x - y) = x := by
  rw [midpoint_comm] <;> simp

end

theorem line_map_inv_two {R : Type _} {V P : Type _} [DivisionRing R] [CharZero R] [AddCommGroupₓ V] [Module R V]
    [AddTorsor V P] (a b : P) : lineMap a b (2⁻¹ : R) = midpoint R a b :=
  rfl

theorem line_map_one_half {R : Type _} {V P : Type _} [DivisionRing R] [CharZero R] [AddCommGroupₓ V] [Module R V]
    [AddTorsor V P] (a b : P) : lineMap a b (1 / 2 : R) = midpoint R a b := by
  rw [one_div, line_map_inv_two]

theorem homothety_inv_of_two {R : Type _} {V P : Type _} [CommRingₓ R] [Invertible (2 : R)] [AddCommGroupₓ V]
    [Module R V] [AddTorsor V P] (a b : P) : homothety a (⅟ 2 : R) b = midpoint R a b :=
  rfl

theorem homothety_inv_two {k : Type _} {V P : Type _} [Field k] [CharZero k] [AddCommGroupₓ V] [Module k V]
    [AddTorsor V P] (a b : P) : homothety a (2⁻¹ : k) b = midpoint k a b :=
  rfl

theorem homothety_one_half {k : Type _} {V P : Type _} [Field k] [CharZero k] [AddCommGroupₓ V] [Module k V]
    [AddTorsor V P] (a b : P) : homothety a (1 / 2 : k) b = midpoint k a b := by
  rw [one_div, homothety_inv_two]

@[simp]
theorem pi_midpoint_apply {k ι : Type _} {V : ∀ i : ι, Type _} {P : ∀ i : ι, Type _} [Field k] [Invertible (2 : k)]
    [∀ i, AddCommGroupₓ (V i)] [∀ i, Module k (V i)] [∀ i, AddTorsor (V i) (P i)] (f g : ∀ i, P i) (i : ι) :
    midpoint k f g i = midpoint k (f i) (g i) :=
  rfl

namespace AddMonoidHom

variable (R R' : Type _) {E F : Type _} [Ringₓ R] [Invertible (2 : R)] [AddCommGroupₓ E] [Module R E] [Ringₓ R']
  [Invertible (2 : R')] [AddCommGroupₓ F] [Module R' F]

/-- A map `f : E → F` sending zero to zero and midpoints to midpoints is an `add_monoid_hom`. -/
def ofMapMidpoint (f : E → F) (h0 : f 0 = 0) (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) : E →+ F where
  toFun := f
  map_zero' := h0
  map_add' := fun x y =>
    calc
      f (x + y) = f 0 + f (x + y) := by
        rw [h0, zero_addₓ]
      _ = midpoint R' (f 0) (f (x + y)) + midpoint R' (f 0) (f (x + y)) := (midpoint_add_self _ _ _).symm
      _ = f (midpoint R x y) + f (midpoint R x y) := by
        rw [← hm, midpoint_zero_add]
      _ = f x + f y := by
        rw [hm, midpoint_add_self]
      

@[simp]
theorem coe_of_map_midpoint (f : E → F) (h0 : f 0 = 0) (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) :
    ⇑(ofMapMidpoint R R' f h0 hm) = f :=
  rfl

end AddMonoidHom

