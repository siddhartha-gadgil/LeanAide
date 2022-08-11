/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
import Mathbin.Algebra.Order.Field

/-!
# Absolute values

This file defines a bundled type of absolute values `absolute_value R S`.

## Main definitions

 * `absolute_value R S` is the type of absolute values on `R` mapping to `S`.
 * `absolute_value.abs` is the "standard" absolute value on `S`, mapping negative `x` to `-x`.
 * `absolute_value.to_monoid_with_zero_hom`: absolute values mapping to a
   linear ordered field preserve `0`, `*` and `1`
 * `is_absolute_value`: a type class stating that `f : β → α` satisfies the axioms of an abs val
-/


/-- `absolute_value R S` is the type of absolute values on `R` mapping to `S`:
the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle equality. -/
structure AbsoluteValue (R S : Type _) [Semiringₓ R] [OrderedSemiring S] extends R →ₙ* S where
  nonneg' : ∀ x, 0 ≤ to_fun x
  eq_zero' : ∀ x, to_fun x = 0 ↔ x = 0
  add_le' : ∀ x y, to_fun (x + y) ≤ to_fun x + to_fun y

namespace AbsoluteValue

attribute [nolint doc_blame] AbsoluteValue.toMulHom

initialize_simps_projections AbsoluteValue (to_mul_hom_to_fun → apply)

section OrderedSemiring

variable {R S : Type _} [Semiringₓ R] [OrderedSemiring S] (abv : AbsoluteValue R S)

instance : CoeFun (AbsoluteValue R S) fun f => R → S :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem coe_to_mul_hom : ⇑abv.toMulHom = abv :=
  rfl

protected theorem nonneg (x : R) : 0 ≤ abv x :=
  abv.nonneg' x

@[simp]
protected theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 :=
  abv.eq_zero' x

protected theorem add_le (x y : R) : abv (x + y) ≤ abv x + abv y :=
  abv.add_le' x y

@[simp]
protected theorem map_mul (x y : R) : abv (x * y) = abv x * abv y :=
  abv.map_mul' x y

protected theorem pos {x : R} (hx : x ≠ 0) : 0 < abv x :=
  lt_of_le_of_neₓ (abv.Nonneg x) (Ne.symm <| mt abv.eq_zero.mp hx)

@[simp]
protected theorem pos_iff {x : R} : 0 < abv x ↔ x ≠ 0 :=
  ⟨fun h₁ => mt abv.eq_zero.mpr h₁.ne', abv.Pos⟩

protected theorem ne_zero {x : R} (hx : x ≠ 0) : abv x ≠ 0 :=
  (abv.Pos hx).ne'

@[simp]
protected theorem map_zero : abv 0 = 0 :=
  abv.eq_zero.2 rfl

end OrderedSemiring

section OrderedRing

variable {R S : Type _} [Ringₓ R] [OrderedRing S] (abv : AbsoluteValue R S)

protected theorem sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [← sub_eq_add_neg, ← add_assocₓ] using abv.add_le (a - b) (b - c)

protected theorem le_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
  sub_le_iff_le_add.2 <| by
    simpa using abv.add_le (a - b) b

@[simp]
theorem map_sub_eq_zero_iff (a b : R) : abv (a - b) = 0 ↔ a = b :=
  abv.eq_zero.trans sub_eq_zero

end OrderedRing

section LinearOrderedRing

variable {R S : Type _} [Semiringₓ R] [LinearOrderedRing S] (abv : AbsoluteValue R S)

/-- `absolute_value.abs` is `abs` as a bundled `absolute_value`. -/
@[simps]
protected def abs : AbsoluteValue S S where
  toFun := abs
  nonneg' := abs_nonneg
  eq_zero' := fun _ => abs_eq_zero
  add_le' := abs_add
  map_mul' := abs_mul

instance : Inhabited (AbsoluteValue S S) :=
  ⟨AbsoluteValue.abs⟩

variable [Nontrivial R]

@[simp]
protected theorem map_one : abv 1 = 1 :=
  (mul_right_inj' <| abv.ne_zero one_ne_zero).1 <| by
    rw [← abv.map_mul, mul_oneₓ, mul_oneₓ]

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*`, `0` and `1`. -/
def toMonoidWithZeroHom : R →*₀ S :=
  { abv with toFun := abv, map_zero' := abv.map_zero, map_one' := abv.map_one }

@[simp]
theorem coe_to_monoid_with_zero_hom : ⇑abv.toMonoidWithZeroHom = abv :=
  rfl

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*` and `1`. -/
def toMonoidHom : MonoidHom R S :=
  { abv with toFun := abv, map_one' := abv.map_one }

@[simp]
theorem coe_to_monoid_hom : ⇑abv.toMonoidHom = abv :=
  rfl

@[simp]
protected theorem map_pow (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
  abv.toMonoidHom.map_pow a n

end LinearOrderedRing

section LinearOrderedCommRing

section Ringₓ

variable {R S : Type _} [Ringₓ R] [LinearOrderedCommRing S] (abv : AbsoluteValue R S)

@[simp]
protected theorem map_neg (a : R) : abv (-a) = abv a := by
  by_cases' ha : a = 0
  · simp [← ha]
    
  refine'
    (mul_self_eq_mul_self_iff.mp
          (by
            rw [← abv.map_mul, neg_mul_neg, abv.map_mul])).resolve_right
      _
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'

protected theorem map_sub (a b : R) : abv (a - b) = abv (b - a) := by
  rw [← neg_sub, abv.map_neg]

theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) :=
  abs_sub_le_iff.2
    ⟨abv.le_sub _ _, by
      rw [abv.map_sub] <;> apply abv.le_sub⟩

end Ringₓ

end LinearOrderedCommRing

section LinearOrderedField

section Field

variable {R S : Type _} [DivisionRing R] [LinearOrderedField S] (abv : AbsoluteValue R S)

@[simp]
protected theorem map_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ :=
  abv.toMonoidWithZeroHom.map_inv a

@[simp]
protected theorem map_div (a b : R) : abv (a / b) = abv a / abv b :=
  abv.toMonoidWithZeroHom.map_div a b

end Field

end LinearOrderedField

end AbsoluteValue

section IsAbsoluteValue

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`abv_nonneg] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`abv_eq_zero] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`abv_add] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`abv_mul] []
/-- A function `f` is an absolute value if it is nonnegative, zero only at 0, additive, and
multiplicative.

See also the type `absolute_value` which represents a bundled version of absolute values.
-/
class IsAbsoluteValue {S} [OrderedSemiring S] {R} [Semiringₓ R] (f : R → S) : Prop where
  abv_nonneg : ∀ x, 0 ≤ f x
  abv_eq_zero : ∀ {x}, f x = 0 ↔ x = 0
  abv_add : ∀ x y, f (x + y) ≤ f x + f y
  abv_mul : ∀ x y, f (x * y) = f x * f y

namespace IsAbsoluteValue

section OrderedSemiring

variable {S : Type _} [OrderedSemiring S]

variable {R : Type _} [Semiringₓ R] (abv : R → S) [IsAbsoluteValue abv]

/-- A bundled absolute value is an absolute value. -/
instance AbsoluteValue.is_absolute_value (abv : AbsoluteValue R S) : IsAbsoluteValue abv where
  abv_nonneg := abv.Nonneg
  abv_eq_zero := fun _ => abv.eq_zero
  abv_add := abv.add_le
  abv_mul := abv.map_mul

/-- Convert an unbundled `is_absolute_value` to a bundled `absolute_value`. -/
@[simps]
def toAbsoluteValue : AbsoluteValue R S where
  toFun := abv
  add_le' := abv_add abv
  eq_zero' := fun _ => abv_eq_zero abv
  nonneg' := abv_nonneg abv
  map_mul' := abv_mul abv

theorem abv_zero : abv 0 = 0 :=
  (abv_eq_zero abv).2 rfl

theorem abv_pos {a : R} : 0 < abv a ↔ a ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm] <;> simp [← abv_eq_zero abv, ← abv_nonneg abv]

end OrderedSemiring

section LinearOrderedRing

variable {S : Type _} [LinearOrderedRing S]

variable {R : Type _} [Semiringₓ R] (abv : R → S) [IsAbsoluteValue abv]

instance abs_is_absolute_value {S} [LinearOrderedRing S] : IsAbsoluteValue (abs : S → S) where
  abv_nonneg := abs_nonneg
  abv_eq_zero := fun _ => abs_eq_zero
  abv_add := abs_add
  abv_mul := abs_mul

end LinearOrderedRing

section LinearOrderedCommRing

variable {S : Type _} [LinearOrderedCommRing S]

section Semiringₓ

variable {R : Type _} [Semiringₓ R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_one [Nontrivial R] : abv 1 = 1 :=
  (mul_right_inj' <| mt (abv_eq_zero abv).1 one_ne_zero).1 <| by
    rw [← abv_mul abv, mul_oneₓ, mul_oneₓ]

/-- `abv` as a `monoid_with_zero_hom`. -/
def abvHom [Nontrivial R] : R →*₀ S :=
  ⟨abv, abv_zero abv, abv_one abv, abv_mul abv⟩

theorem abv_pow [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv] (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
  (abvHom abv).toMonoidHom.map_pow a n

end Semiringₓ

end LinearOrderedCommRing

section LinearOrderedField

variable {S : Type _} [LinearOrderedField S]

section Ringₓ

variable {R : Type _} [Ringₓ R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_neg (a : R) : abv (-a) = abv a := by
  rw [← mul_self_inj_of_nonneg (abv_nonneg abv _) (abv_nonneg abv _), ← abv_mul abv, ← abv_mul abv] <;> simp

theorem abv_sub (a b : R) : abv (a - b) = abv (b - a) := by
  rw [← neg_sub, abv_neg abv]

theorem abv_sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [← sub_eq_add_neg, ← add_assocₓ] using abv_add abv (a - b) (b - c)

theorem sub_abv_le_abv_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
  sub_le_iff_le_add.2 <| by
    simpa using abv_add abv (a - b) b

theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) :=
  abs_sub_le_iff.2
    ⟨sub_abv_le_abv_sub abv _ _, by
      rw [abv_sub abv] <;> apply sub_abv_le_abv_sub abv⟩

end Ringₓ

section Field

variable {R : Type _} [DivisionRing R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ :=
  (abvHom abv).map_inv a

theorem abv_div (a b : R) : abv (a / b) = abv a / abv b :=
  (abvHom abv).map_div a b

end Field

end LinearOrderedField

end IsAbsoluteValue

end IsAbsoluteValue

