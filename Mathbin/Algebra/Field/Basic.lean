/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Algebra.Hom.Ring
import Mathbin.Data.Rat.Defs

/-!
# Division (semi)rings and (semi)fields

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `field_theory` folder.

## Main definitions

* `division_semiring`: Nontrivial semiring with multiplicative inverses for nonzero elements.
* `division_ring`: : Nontrivial ring with multiplicative inverses for nonzero elements.
* `semifield`: Commutative division semiring.
* `field`: Commutative division ring.
* `is_field`: Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
  commutative, that it has more than one element and that all non-zero elements have a
  multiplicative inverse. In contrast to `field`, which contains the data of a function associating
  to an element of the field its multiplicative inverse, this predicate only assumes the existence
  and can therefore more easily be used to e.g. transfer along ring isomorphisms.

## Implementation details

By convention `0⁻¹ = 0` in a field or division ring. This is due to the fact that working with total
functions has the advantage of not constantly having to check that `x ≠ 0` when writing `x⁻¹`. With
this convention in place, some statements like `(a + b) * c⁻¹ = a * c⁻¹ + b * c⁻¹` still remain
true, while others like the defining property `a * a⁻¹ = 1` need the assumption `a ≠ 0`. If you are
a beginner in using Lean and are confused by that, you can read more about why this convention is
taken in Kevin Buzzard's
[blogpost](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)

A division ring or field is an example of a `group_with_zero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `group_with_zero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/


open Function Set

universe u

variable {α β K : Type _}

/-- A `division_semiring` is a `semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj, ancestor Semiringₓ GroupWithZeroₓ]
class DivisionSemiring (α : Type _) extends Semiringₓ α, GroupWithZeroₓ α

/-- A `division_ring` is a `ring` with multiplicative inverses for nonzero elements. -/
@[protect_proj, ancestor Ringₓ DivisionSemiring]
class DivisionRing (α : Type _) extends Ringₓ α, DivInvMonoidₓ α, Nontrivial α where
  mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : α)⁻¹ = 0

/-- A `semifield` is a `comm_semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj, ancestor CommSemiringₓ DivisionSemiring CommGroupWithZero]
class Semifield (α : Type _) extends CommSemiringₓ α, DivisionSemiring α, CommGroupWithZero α

/-- A `field` is a `comm_ring` with multiplicative inverses for nonzero elements. -/
@[protect_proj, ancestor CommRingₓ DivisionRing]
class Field (α : Type _) extends CommRingₓ α, DivisionRing α

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing α] : DivisionSemiring α :=
  { ‹DivisionRing α›, (inferInstance : Semiringₓ α) with }

section DivisionSemiring

variable [DivisionSemiring α] {a b c : α}

theorem add_div (a b c : α) : (a + b) / c = a / c + b / c := by
  simp_rw [div_eq_mul_inv, add_mulₓ]

@[field_simps]
theorem div_add_div_same (a b c : α) : a / c + b / c = (a + b) / c :=
  (add_div _ _ _).symm

theorem same_add_div (h : b ≠ 0) : (b + a) / b = 1 + a / b := by
  rw [← div_self h, add_div]

theorem div_add_same (h : b ≠ 0) : (a + b) / b = a / b + 1 := by
  rw [← div_self h, add_div]

theorem one_add_div (h : b ≠ 0) : 1 + a / b = (b + a) / b :=
  (same_add_div h).symm

theorem div_add_one (h : b ≠ 0) : a / b + 1 = (a + b) / b :=
  (div_add_same h).symm

theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (a + b) * (1 / b) = 1 / a + 1 / b := by
  rw [mul_addₓ, one_div_mul_cancel ha, add_mulₓ, one_mulₓ, mul_assoc, mul_one_div_cancel hb, mul_oneₓ, add_commₓ]

theorem add_div_eq_mul_add_div (a b : α) (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
  (eq_div_iff_mul_eq hc).2 <| by
    rw [right_distrib, div_mul_cancel _ hc]

@[field_simps]
theorem add_div' (a b c : α) (hc : c ≠ 0) : b + a / c = (b * c + a) / c := by
  rw [add_div, mul_div_cancel _ hc]

@[field_simps]
theorem div_add' (a b c : α) (hc : c ≠ 0) : a / c + b = (a + b * c) / c := by
  rwa [add_commₓ, add_div', add_commₓ]

end DivisionSemiring

section DivisionRing

variable [DivisionRing K] {a b : K}

attribute [local simp] division_def mul_comm mul_assoc mul_left_commₓ mul_inv_cancel inv_mul_cancel

theorem one_div_neg_one_eq_neg_one : (1 : K) / -1 = -1 :=
  have : -1 * -1 = (1 : K) := by
    rw [neg_mul_neg, one_mulₓ]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)

theorem one_div_neg_eq_neg_one_div (a : K) : 1 / -a = -(1 / a) :=
  calc
    1 / -a = 1 / (-1 * a) := by
      rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by
      rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by
      rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by
      rw [mul_neg, mul_oneₓ]
    

theorem div_neg_eq_neg_div (a b : K) : b / -a = -(b / a) :=
  calc
    b / -a = b * (1 / -a) := by
      rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by
      rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by
      rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by
      rw [mul_one_div]
    

theorem neg_div (a b : K) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

@[field_simps]
theorem neg_div' (a b : K) : -(b / a) = -b / a := by
  simp [← neg_div]

theorem neg_div_neg_eq (a b : K) : -a / -b = a / b := by
  rw [div_neg_eq_neg_div, neg_div, neg_negₓ]

@[simp]
theorem div_neg_self {a : K} (h : a ≠ 0) : a / -a = -1 := by
  rw [div_neg_eq_neg_div, div_self h]

@[simp]
theorem neg_div_self {a : K} (h : a ≠ 0) : -a / a = -1 := by
  rw [neg_div, div_self h]

theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by
  rw [sub_eq_add_neg, ← neg_div, div_add_div_same, sub_eq_add_neg]

theorem same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b := by
  simpa only [@div_self _ _ b h] using (div_sub_div_same b a b).symm

theorem one_sub_div {a b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b :=
  (same_sub_div h).symm

theorem div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 := by
  simpa only [@div_self _ _ b h] using (div_sub_div_same a b b).symm

theorem div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b :=
  (div_sub_same h).symm

theorem neg_inv : -a⁻¹ = (-a)⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

theorem sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
  (div_sub_div_same _ _ _).symm

theorem div_neg (a : K) : a / -b = -(a / b) := by
  rw [← div_neg_eq_neg_div]

theorem inv_neg : (-a)⁻¹ = -a⁻¹ := by
  rw [neg_inv]

theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (b - a) * (1 / b) = 1 / a - 1 / b := by
  rw [mul_sub_left_distrib (1 / a), one_div_mul_cancel ha, mul_sub_right_distrib, one_mulₓ, mul_assoc,
    mul_one_div_cancel hb, mul_oneₓ]

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.is_domain : IsDomain K :=
  { ‹DivisionRing K›,
    (by
      infer_instance : NoZeroDivisors K) with }

end DivisionRing

section Semifield

variable [Semifield α] {a b c d : α}

theorem div_add_div (a : α) (c : α) (hb : b ≠ 0) (hd : d ≠ 0) : a / b + c / d = (a * d + b * c) / (b * d) := by
  rw [← mul_div_mul_right _ b hd, ← mul_div_mul_left c d hb, div_add_div_same]

theorem one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) := by
  rw [div_add_div _ _ ha hb, one_mulₓ, mul_oneₓ, add_commₓ]

theorem inv_add_inv (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) := by
  rw [inv_eq_one_div, inv_eq_one_div, one_div_add_one_div ha hb]

end Semifield

section Field

variable [Field K]

-- see Note [lower instance priority]
instance (priority := 100) Field.toSemifield : Semifield K :=
  { ‹Field K›, (inferInstance : Semiringₓ K) with }

attribute [local simp] mul_assoc mul_comm mul_left_commₓ

@[field_simps]
theorem div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - b * c) / (b * d) := by
  simp [← sub_eq_add_neg]
  rw [neg_eq_neg_one_mul, ← mul_div_assoc, div_add_div _ _ hb hd, ← mul_assoc, mul_comm b, mul_assoc, ←
    neg_eq_neg_one_mul]

theorem inv_sub_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mulₓ, mul_oneₓ]

@[field_simps]
theorem sub_div' (a b c : K) (hc : c ≠ 0) : b - a / c = (b * c - a) / c := by
  simpa using div_sub_div b a one_ne_zero hc

@[field_simps]
theorem div_sub' (a b c : K) (hc : c ≠ 0) : a / c - b = (a - c * b) / c := by
  simpa using div_sub_div a b hc one_ne_zero

-- see Note [lower instance priority]
instance (priority := 100) Field.is_domain : IsDomain K :=
  { DivisionRing.is_domain with }

end Field

section IsField

/-- A predicate to express that a (semi)ring is a (semi)field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionaly, this is useful when trying to prove that
a particular ring structure extends to a (semi)field. -/
structure IsField (R : Type u) [Semiringₓ R] : Prop where
  exists_pair_ne : ∃ x y : R, x ≠ y
  mul_comm : ∀ x y : R, x * y = y * x
  mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1

/-- Transferring from `semifield` to `is_field`. -/
theorem Semifield.to_is_field (R : Type u) [Semifield R] : IsField R :=
  { ‹Semifield R› with mul_inv_cancel := fun a ha => ⟨a⁻¹, mul_inv_cancel ha⟩ }

/-- Transferring from `field` to `is_field`. -/
theorem Field.to_is_field (R : Type u) [Field R] : IsField R :=
  Semifield.to_is_field _

@[simp]
theorem IsField.nontrivial {R : Type u} [Semiringₓ R] (h : IsField R) : Nontrivial R :=
  ⟨h.exists_pair_ne⟩

@[simp]
theorem not_is_field_of_subsingleton (R : Type u) [Semiringₓ R] [Subsingleton R] : ¬IsField R := fun h =>
  let ⟨x, y, h⟩ := h.exists_pair_ne
  h (Subsingleton.elimₓ _ _)

open Classical

/-- Transferring from `is_field` to `semifield`. -/
noncomputable def IsField.toSemifield {R : Type u} [Semiringₓ R] (h : IsField R) : Semifield R :=
  { ‹Semiringₓ R›, h with inv := fun a => if ha : a = 0 then 0 else Classical.some (IsField.mul_inv_cancel h ha),
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a ha => by
      convert Classical.some_spec (IsField.mul_inv_cancel h ha)
      exact dif_neg ha }

/-- Transferring from `is_field` to `field`. -/
noncomputable def IsField.toField {R : Type u} [Ringₓ R] (h : IsField R) : Field R :=
  { ‹Ringₓ R›, IsField.toSemifield h with }

/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `is_field` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem uniq_inv_of_is_field (R : Type u) [Ringₓ R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by
  intro x hx
  apply exists_unique_of_exists_of_unique
  · exact hf.mul_inv_cancel hx
    
  · intro y z hxy hxz
    calc y = y * (x * z) := by
        rw [hxz, mul_oneₓ]_ = x * y * z := by
        rw [← mul_assoc, hf.mul_comm y x]_ = z := by
        rw [hxy, one_mulₓ]
    

end IsField

namespace RingHom

section Semiringₓ

variable [Semiringₓ α] [DivisionSemiring β]

@[simp]
theorem map_units_inv (f : α →+* β) (u : αˣ) : f ↑u⁻¹ = (f ↑u)⁻¹ :=
  (f : α →* β).map_units_inv u

variable [Nontrivial α] (f : β →+* α) {a : β}

@[simp]
theorem map_eq_zero : f a = 0 ↔ a = 0 :=
  f.toMonoidWithZeroHom.map_eq_zero

theorem map_ne_zero : f a ≠ 0 ↔ a ≠ 0 :=
  f.toMonoidWithZeroHom.map_ne_zero

end Semiringₓ

section DivisionSemiring

variable [DivisionSemiring α] [DivisionSemiring β] (f : α →+* β) (a b : α)

theorem map_inv : f a⁻¹ = (f a)⁻¹ :=
  f.toMonoidWithZeroHom.map_inv _

theorem map_div : f (a / b) = f a / f b :=
  f.toMonoidWithZeroHom.map_div _ _

end DivisionSemiring

protected theorem injective [DivisionRing α] [Semiringₓ β] [Nontrivial β] (f : α →+* β) : Injective f :=
  (injective_iff_map_eq_zero f).2 fun x => f.map_eq_zero.1

end RingHom

section NoncomputableDefs

variable {R : Type _} [Nontrivial R]

/-- Constructs a `division_ring` structure on a `ring` consisting only of units and 0. -/
noncomputable def divisionRingOfIsUnitOrEqZero [hR : Ringₓ R] (h : ∀ a : R, IsUnit a ∨ a = 0) : DivisionRing R :=
  { groupWithZeroOfIsUnitOrEqZero h, hR with }

/-- Constructs a `field` structure on a `comm_ring` consisting only of units and 0.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def fieldOfIsUnitOrEqZero [hR : CommRingₓ R] (h : ∀ a : R, IsUnit a ∨ a = 0) : Field R :=
  { groupWithZeroOfIsUnitOrEqZero h, hR with }

end NoncomputableDefs

/-- Pullback a `division_semiring` along an injective function. -/
-- See note [reducible non-instances]
@[reducible]
protected def Function.Injective.divisionSemiring [DivisionSemiring β] [Zero α] [Mul α] [Add α] [One α] [Inv α] [Div α]
    [HasSmul ℕ α] [Pow α ℕ] [Pow α ℤ] [HasNatCast α] (f : α → β) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : DivisionSemiring α :=
  { hf.GroupWithZero f zero one mul inv div npow zpow, hf.Semiring f zero one add mul nsmul npow nat_cast with }

/-- Pullback a `division_ring` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.divisionRing [DivisionRing K] {K'} [Zero K'] [One K'] [Add K'] [Mul K'] [Neg K']
    [Sub K'] [Inv K'] [Div K'] [HasSmul ℕ K'] [HasSmul ℤ K'] [Pow K' ℕ] [Pow K' ℤ] [HasNatCast K'] [HasIntCast K']
    (f : K' → K) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
    DivisionRing K' :=
  { hf.GroupWithZero f zero one mul inv div npow zpow,
    hf.Ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with }

/-- Pullback a `field` along an injective function. -/
-- See note [reducible non-instances]
@[reducible]
protected def Function.Injective.semifield [Semifield β] [Zero α] [Mul α] [Add α] [One α] [Inv α] [Div α] [HasSmul ℕ α]
    [Pow α ℕ] [Pow α ℤ] [HasNatCast α] (f : α → β) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semifield α :=
  { hf.CommGroupWithZero f zero one mul inv div npow zpow, hf.CommSemiring f zero one add mul nsmul npow nat_cast with }

/-- Pullback a `field` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.field [Field K] {K'} [Zero K'] [Mul K'] [Add K'] [Neg K'] [Sub K'] [One K'] [Inv K']
    [Div K'] [HasSmul ℕ K'] [HasSmul ℤ K'] [Pow K' ℕ] [Pow K' ℤ] [HasNatCast K'] [HasIntCast K'] (f : K' → K)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
    Field K' :=
  { hf.CommGroupWithZero f zero one mul inv div npow zpow,
    hf.CommRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with }

