/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathbin.Algebra.Field.Basic
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.Algebra.GroupPower.Order
import Mathbin.Algebra.Order.Ring
import Mathbin.Order.Bounds
import Mathbin.Tactic.Monotonicity.Basic

/-!
# Linear ordered (semi)fields

A linear ordered (semi)field is a (semi)field equipped with a linear order such that
* addition respects the order: `a ≤ b → c + a ≤ c + b`;
* multiplication of positives is positive: `0 < a → 0 < b → 0 < a * b`;
* `0 < 1`.

## Main Definitions

* `linear_ordered_semifield`: Typeclass for linear order semifields.
* `linear_ordered_field`: Typeclass for linear ordered fields.
-/


variable {α β : Type _}

/-- A linear ordered semifield is a field with a linear order respecting the operations. -/
@[protect_proj]
class LinearOrderedSemifield (α : Type _) extends LinearOrderedSemiring α, Semifield α

/-- A linear ordered field is a field with a linear order respecting the operations. -/
@[protect_proj]
class LinearOrderedField (α : Type _) extends LinearOrderedCommRing α, Field α

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedField.toLinearOrderedSemifield [LinearOrderedField α] :
    LinearOrderedSemifield α :=
  { LinearOrderedRing.toLinearOrderedSemiring, ‹LinearOrderedField α› with }

namespace Function

/-- Pullback a `linear_ordered_semifield` under an injective map. -/
-- See note [reducible non-instances]
@[reducible]
def Injective.linearOrderedSemifield [LinearOrderedSemifield α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ] [HasSmul ℕ β]
    [HasNatCast β] [Inv β] [Div β] [Pow β ℤ] [HasSup β] [HasInf β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (hsup : ∀ x y, f (x⊔y) = max (f x) (f y)) (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) :
    LinearOrderedSemifield β :=
  { hf.LinearOrderedSemiring f zero one add mul nsmul npow nat_cast hsup hinf,
    hf.Semifield f zero one add mul inv div nsmul npow zpow nat_cast with }

/-- Pullback a `linear_ordered_field` under an injective map. -/
-- See note [reducible non-instances]
@[reducible]
def Injective.linearOrderedField [LinearOrderedField α] [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [Pow β ℕ]
    [HasSmul ℕ β] [HasSmul ℤ β] [HasNatCast β] [HasIntCast β] [Inv β] [Div β] [Pow β ℤ] [HasSup β] [HasInf β]
    (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n)
    (hsup : ∀ x y, f (x⊔y) = max (f x) (f y)) (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) : LinearOrderedField β :=
  { hf.LinearOrderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast hsup hinf,
    hf.Field f zero one add mul neg sub inv div nsmul zsmul npow zpow nat_cast int_cast with }

end Function

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] {a b c d e : α}

/-- `equiv.mul_left₀` as an order_iso. -/
@[simps (config := { simpRhs := true })]
def OrderIso.mulLeft₀ (a : α) (ha : 0 < a) : α ≃o α :=
  { Equivₓ.mulLeft₀ a ha.ne' with map_rel_iff' := fun _ _ => mul_le_mul_left ha }

/-- `equiv.mul_right₀` as an order_iso. -/
@[simps (config := { simpRhs := true })]
def OrderIso.mulRight₀ (a : α) (ha : 0 < a) : α ≃o α :=
  { Equivₓ.mulRight₀ a ha.ne' with map_rel_iff' := fun _ _ => mul_le_mul_right ha }

/-!
### Lemmas about pos, nonneg, nonpos, neg
-/


@[simp]
theorem inv_pos : 0 < a⁻¹ ↔ 0 < a :=
  suffices ∀ a : α, 0 < a → 0 < a⁻¹ from ⟨fun h => inv_invₓ a ▸ this _ h, this a⟩
  fun a ha =>
  flip lt_of_mul_lt_mul_left ha.le <| by
    simp [← ne_of_gtₓ ha, ← zero_lt_one]

@[simp]
theorem inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by
  simp only [← le_iff_eq_or_lt, ← inv_pos, ← zero_eq_inv]

@[simp]
theorem inv_lt_zero : a⁻¹ < 0 ↔ a < 0 := by
  simp only [not_leₓ, ← inv_nonneg]

@[simp]
theorem inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 := by
  simp only [not_ltₓ, ← inv_pos]

theorem one_div_pos : 0 < 1 / a ↔ 0 < a :=
  inv_eq_one_div a ▸ inv_pos

theorem one_div_neg : 1 / a < 0 ↔ a < 0 :=
  inv_eq_one_div a ▸ inv_lt_zero

theorem one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a :=
  inv_eq_one_div a ▸ inv_nonneg

theorem one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 :=
  inv_eq_one_div a ▸ inv_nonpos

theorem div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]
  exact mul_pos ha (inv_pos.2 hb)

theorem div_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [div_eq_mul_inv]
  exact mul_nonneg ha (inv_nonneg.2 hb)

theorem div_nonpos_of_nonpos_of_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]
  exact mul_nonpos_of_nonpos_of_nonneg ha (inv_nonneg.2 hb)

theorem div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]
  exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

/-!
### Relating one division with another term.
-/


theorem le_div_iff (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
  ⟨fun h => div_mul_cancel b (ne_of_ltₓ hc).symm ▸ mul_le_mul_of_nonneg_right h hc.le, fun h =>
    calc
      a = a * c * (1 / c) := mul_mul_div a (ne_of_ltₓ hc).symm
      _ ≤ b * (1 / c) := mul_le_mul_of_nonneg_right h (one_div_pos.2 hc).le
      _ = b / c := (div_eq_mul_one_div b c).symm
      ⟩

theorem le_div_iff' (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b := by
  rw [mul_comm, le_div_iff hc]

theorem div_le_iff (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b :=
  ⟨fun h =>
    calc
      a = a / b * b := by
        rw [div_mul_cancel _ (ne_of_ltₓ hb).symm]
      _ ≤ c * b := mul_le_mul_of_nonneg_right h hb.le
      ,
    fun h =>
    calc
      a / b = a * (1 / b) := div_eq_mul_one_div a b
      _ ≤ c * b * (1 / b) := mul_le_mul_of_nonneg_right h (one_div_pos.2 hb).le
      _ = c * b / b := (div_eq_mul_one_div (c * b) b).symm
      _ = c := by
        refine' (div_eq_iff (ne_of_gtₓ hb)).mpr rfl
      ⟩

theorem div_le_iff' (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c := by
  rw [mul_comm, div_le_iff hb]

theorem lt_div_iff (hc : 0 < c) : a < b / c ↔ a * c < b :=
  lt_iff_lt_of_le_iff_le <| div_le_iff hc

theorem lt_div_iff' (hc : 0 < c) : a < b / c ↔ c * a < b := by
  rw [mul_comm, lt_div_iff hc]

theorem div_lt_iff (hc : 0 < c) : b / c < a ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le (le_div_iff hc)

theorem div_lt_iff' (hc : 0 < c) : b / c < a ↔ b < c * a := by
  rw [mul_comm, div_lt_iff hc]

theorem inv_mul_le_iff (h : 0 < b) : b⁻¹ * a ≤ c ↔ a ≤ b * c := by
  rw [inv_eq_one_div, mul_comm, ← div_eq_mul_one_div]
  exact div_le_iff' h

theorem inv_mul_le_iff' (h : 0 < b) : b⁻¹ * a ≤ c ↔ a ≤ c * b := by
  rw [inv_mul_le_iff h, mul_comm]

theorem mul_inv_le_iff (h : 0 < b) : a * b⁻¹ ≤ c ↔ a ≤ b * c := by
  rw [mul_comm, inv_mul_le_iff h]

theorem mul_inv_le_iff' (h : 0 < b) : a * b⁻¹ ≤ c ↔ a ≤ c * b := by
  rw [mul_comm, inv_mul_le_iff' h]

theorem div_self_le_one (a : α) : a / a ≤ 1 :=
  if h : a = 0 then by
    simp [← h]
  else by
    simp [← h]

theorem inv_mul_lt_iff (h : 0 < b) : b⁻¹ * a < c ↔ a < b * c := by
  rw [inv_eq_one_div, mul_comm, ← div_eq_mul_one_div]
  exact div_lt_iff' h

theorem inv_mul_lt_iff' (h : 0 < b) : b⁻¹ * a < c ↔ a < c * b := by
  rw [inv_mul_lt_iff h, mul_comm]

theorem mul_inv_lt_iff (h : 0 < b) : a * b⁻¹ < c ↔ a < b * c := by
  rw [mul_comm, inv_mul_lt_iff h]

theorem mul_inv_lt_iff' (h : 0 < b) : a * b⁻¹ < c ↔ a < c * b := by
  rw [mul_comm, inv_mul_lt_iff' h]

theorem inv_pos_le_iff_one_le_mul (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a := by
  rw [inv_eq_one_div]
  exact div_le_iff ha

theorem inv_pos_le_iff_one_le_mul' (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [inv_eq_one_div]
  exact div_le_iff' ha

theorem inv_pos_lt_iff_one_lt_mul (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a := by
  rw [inv_eq_one_div]
  exact div_lt_iff ha

theorem inv_pos_lt_iff_one_lt_mul' (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b := by
  rw [inv_eq_one_div]
  exact div_lt_iff' ha

/-- One direction of `div_le_iff` where `b` is allowed to be `0` (but `c` must be nonnegative) -/
theorem div_le_of_nonneg_of_le_mul (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c := by
  rcases eq_or_lt_of_le hb with (rfl | hb')
  simp [← hc]
  rwa [div_le_iff hb']

theorem div_le_one_of_le (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 :=
  div_le_of_nonneg_of_le_mul hb zero_le_one <| by
    rwa [one_mulₓ]

/-!
### Bi-implications of inequalities using inversions
-/


theorem inv_le_inv_of_le (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  rwa [← one_div a, le_div_iff' ha, ← div_eq_mul_inv, div_le_iff (ha.trans_le h), one_mulₓ]

/-- See `inv_le_inv_of_le` for the implication from right-to-left with one fewer assumption. -/
theorem inv_le_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [← one_div, div_le_iff ha, ← div_eq_inv_mul, le_div_iff hb, one_mulₓ]

/-- In a linear ordered field, for positive `a` and `b` we have `a⁻¹ ≤ b ↔ b⁻¹ ≤ a`.
See also `inv_le_of_inv_le` for a one-sided implication with one fewer assumption. -/
theorem inv_le (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv hb (inv_pos.2 ha), inv_invₓ]

theorem inv_le_of_inv_le (ha : 0 < a) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
  (inv_le ha ((inv_pos.2 ha).trans_le h)).1 h

theorem le_inv (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv (inv_pos.2 hb) ha, inv_invₓ]

/-- See `inv_lt_inv_of_lt` for the implication from right-to-left with one fewer assumption. -/
theorem inv_lt_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a :=
  lt_iff_lt_of_le_iff_le (inv_le_inv hb ha)

theorem inv_lt_inv_of_lt (hb : 0 < b) (h : b < a) : a⁻¹ < b⁻¹ :=
  (inv_lt_inv (hb.trans h) hb).2 h

/-- In a linear ordered field, for positive `a` and `b` we have `a⁻¹ < b ↔ b⁻¹ < a`.
See also `inv_lt_of_inv_lt` for a one-sided implication with one fewer assumption. -/
theorem inv_lt (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a :=
  lt_iff_lt_of_le_iff_le (le_inv hb ha)

theorem inv_lt_of_inv_lt (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a :=
  (inv_lt ha ((inv_pos.2 ha).trans h)).1 h

theorem lt_inv (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ :=
  lt_iff_lt_of_le_iff_le (inv_le hb ha)

theorem inv_lt_one (ha : 1 < a) : a⁻¹ < 1 := by
  rwa [inv_lt ((@zero_lt_one α _ _).trans ha) zero_lt_one, inv_one]

theorem one_lt_inv (h₁ : 0 < a) (h₂ : a < 1) : 1 < a⁻¹ := by
  rwa [lt_inv (@zero_lt_one α _ _) h₁, inv_one]

theorem inv_le_one (ha : 1 ≤ a) : a⁻¹ ≤ 1 := by
  rwa [inv_le ((@zero_lt_one α _ _).trans_le ha) zero_lt_one, inv_one]

theorem one_le_inv (h₁ : 0 < a) (h₂ : a ≤ 1) : 1 ≤ a⁻¹ := by
  rwa [le_inv (@zero_lt_one α _ _) h₁, inv_one]

theorem inv_lt_one_iff_of_pos (h₀ : 0 < a) : a⁻¹ < 1 ↔ 1 < a :=
  ⟨fun h₁ => inv_invₓ a ▸ one_lt_inv (inv_pos.2 h₀) h₁, inv_lt_one⟩

theorem inv_lt_one_iff : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a := by
  cases' le_or_ltₓ a 0 with ha ha
  · simp [← ha, ← (inv_nonpos.2 ha).trans_lt zero_lt_one]
    
  · simp only [← ha.not_le, ← false_orₓ, ← inv_lt_one_iff_of_pos ha]
    

theorem one_lt_inv_iff : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 :=
  ⟨fun h => ⟨inv_pos.1 (zero_lt_one.trans h), inv_invₓ a ▸ inv_lt_one h⟩, and_imp.2 one_lt_inv⟩

theorem inv_le_one_iff : a⁻¹ ≤ 1 ↔ a ≤ 0 ∨ 1 ≤ a := by
  rcases em (a = 1) with (rfl | ha)
  · simp [← le_rfl]
    
  · simp only [← Ne.le_iff_lt (Ne.symm ha), ← Ne.le_iff_lt (mt inv_eq_one.1 ha), ← inv_lt_one_iff]
    

theorem one_le_inv_iff : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 :=
  ⟨fun h => ⟨inv_pos.1 (zero_lt_one.trans_le h), inv_invₓ a ▸ inv_le_one h⟩, and_imp.2 one_le_inv⟩

/-!
### Relating two divisions.
-/


@[mono]
theorem div_le_div_of_le (hc : 0 ≤ c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_le_mul_of_nonneg_right h (one_div_nonneg.2 hc)

-- Not a `mono` lemma b/c `div_le_div` is strictly more general
theorem div_le_div_of_le_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv (hc.trans_le h) hc).mpr h) ha

theorem div_le_div_of_le_of_nonneg (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c :=
  div_le_div_of_le hc hab

theorem div_lt_div_of_lt (hc : 0 < c) (h : a < b) : a / c < b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_lt_mul_of_pos_right h (one_div_pos.2 hc)

theorem div_le_div_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b :=
  ⟨le_imp_le_of_lt_imp_ltₓ <| div_lt_div_of_lt hc, div_le_div_of_le <| hc.le⟩

theorem div_lt_div_right (hc : 0 < c) : a / c < b / c ↔ a < b :=
  lt_iff_lt_of_le_iff_le <| div_le_div_right hc

theorem div_lt_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b := by
  simp only [← div_eq_mul_inv, ← mul_lt_mul_left ha, ← inv_lt_inv hb hc]

theorem div_le_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b ≤ a / c ↔ c ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 (div_lt_div_left ha hc hb)

theorem div_lt_div_iff (b0 : 0 < b) (d0 : 0 < d) : a / b < c / d ↔ a * d < c * b := by
  rw [lt_div_iff d0, div_mul_eq_mul_div, div_lt_iff b0]

theorem div_le_div_iff (b0 : 0 < b) (d0 : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b := by
  rw [le_div_iff d0, div_mul_eq_mul_div, div_le_iff b0]

@[mono]
theorem div_le_div (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hbd : d ≤ b) : a / b ≤ c / d := by
  rw [div_le_div_iff (hd.trans_le hbd) hd]
  exact mul_le_mul hac hbd hd.le hc

theorem div_lt_div (hac : a < c) (hbd : d ≤ b) (c0 : 0 ≤ c) (d0 : 0 < d) : a / b < c / d :=
  (div_lt_div_iff (d0.trans_le hbd) d0).2 (mul_lt_mul hac hbd d0 c0)

theorem div_lt_div' (hac : a ≤ c) (hbd : d < b) (c0 : 0 < c) (d0 : 0 < d) : a / b < c / d :=
  (div_lt_div_iff (d0.trans hbd) d0).2 (mul_lt_mul' hac hbd d0.le c0)

theorem div_lt_div_of_lt_left (hc : 0 < c) (hb : 0 < b) (h : b < a) : c / a < c / b :=
  (div_lt_div_left hc (hb.trans h) hb).mpr h

/-!
### Relating one division and involving `1`
-/


theorem div_le_self (ha : 0 ≤ a) (hb : 1 ≤ b) : a / b ≤ a := by
  simpa only [← div_one] using div_le_div_of_le_left ha zero_lt_one hb

theorem div_lt_self (ha : 0 < a) (hb : 1 < b) : a / b < a := by
  simpa only [← div_one] using div_lt_div_of_lt_left ha zero_lt_one hb

theorem le_div_self (ha : 0 ≤ a) (hb₀ : 0 < b) (hb₁ : b ≤ 1) : a ≤ a / b := by
  simpa only [← div_one] using div_le_div_of_le_left ha hb₀ hb₁

theorem one_le_div (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by
  rw [le_div_iff hb, one_mulₓ]

theorem div_le_one (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b := by
  rw [div_le_iff hb, one_mulₓ]

theorem one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a := by
  rw [lt_div_iff hb, one_mulₓ]

theorem div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b := by
  rw [div_lt_iff hb, one_mulₓ]

theorem one_div_le (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ b ↔ 1 / b ≤ a := by
  simpa using inv_le ha hb

theorem one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a := by
  simpa using inv_lt ha hb

theorem le_one_div (ha : 0 < a) (hb : 0 < b) : a ≤ 1 / b ↔ b ≤ 1 / a := by
  simpa using le_inv ha hb

theorem lt_one_div (ha : 0 < a) (hb : 0 < b) : a < 1 / b ↔ b < 1 / a := by
  simpa using lt_inv ha hb

/-!
### Relating two divisions, involving `1`
-/


theorem one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  simpa using inv_le_inv_of_le ha h

theorem one_div_lt_one_div_of_lt (ha : 0 < a) (h : a < b) : 1 / b < 1 / a := by
  rwa [lt_div_iff' ha, ← div_eq_mul_one_div, div_lt_one (ha.trans h)]

theorem le_of_one_div_le_one_div (ha : 0 < a) (h : 1 / a ≤ 1 / b) : b ≤ a :=
  le_imp_le_of_lt_imp_ltₓ (one_div_lt_one_div_of_lt ha) h

theorem lt_of_one_div_lt_one_div (ha : 0 < a) (h : 1 / a < 1 / b) : b < a :=
  lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_le ha) h

/-- For the single implications with fewer assumptions, see `one_div_le_one_div_of_le` and
  `le_of_one_div_le_one_div` -/
theorem one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
  div_le_div_left zero_lt_one ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
  div_lt_div_left zero_lt_one ha hb

theorem one_lt_one_div (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a := by
  rwa [lt_one_div (@zero_lt_one α _ _) h1, one_div_one]

theorem one_le_one_div (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a := by
  rwa [le_one_div (@zero_lt_one α _ _) h1, one_div_one]

/-!
### Results about halving.

The equalities also hold in semifields of characteristic `0`.
-/


/- TODO: Unify `add_halves` and `add_halves'` into a single lemma about
`division_semiring` + `char_zero` -/
theorem add_halves (a : α) : a / 2 + a / 2 = a := by
  rw [div_add_div_same, ← two_mul, mul_div_cancel_left a two_ne_zero]

-- TODO: Generalize to `division_semiring`
theorem add_self_div_two (a : α) : (a + a) / 2 = a := by
  rw [← mul_two, mul_div_cancel a two_ne_zero]

theorem half_pos (h : 0 < a) : 0 < a / 2 :=
  div_pos h zero_lt_two

theorem one_half_pos : (0 : α) < 1 / 2 :=
  half_pos zero_lt_one

theorem div_two_lt_of_pos (h : 0 < a) : a / 2 < a := by
  rw [div_lt_iff (@zero_lt_two α _ _)]
  exact lt_mul_of_one_lt_right h one_lt_two

theorem half_lt_self : 0 < a → a / 2 < a :=
  div_two_lt_of_pos

theorem half_le_self (ha_nonneg : 0 ≤ a) : a / 2 ≤ a := by
  by_cases' h0 : a = 0
  · simp [← h0]
    
  · rw [← Ne.def] at h0
    exact (half_lt_self (lt_of_le_of_neₓ ha_nonneg h0.symm)).le
    

theorem one_half_lt_one : (1 / 2 : α) < 1 :=
  half_lt_self zero_lt_one

theorem left_lt_add_div_two : a < (a + b) / 2 ↔ a < b := by
  simp [← lt_div_iff, ← mul_two]

theorem add_div_two_lt_right : (a + b) / 2 < b ↔ a < b := by
  simp [← div_lt_iff, ← mul_two]

/-!
### Miscellaneous lemmas
-/


theorem mul_le_mul_of_mul_div_le (h : a * (b / c) ≤ d) (hc : 0 < c) : b * a ≤ d * c := by
  rw [← mul_div_assoc] at h
  rwa [mul_comm b, ← div_le_iff hc]

theorem div_mul_le_div_mul_of_div_le_div (h : a / b ≤ c / d) (he : 0 ≤ e) : a / (b * e) ≤ c / (d * e) := by
  rw [div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div]
  exact mul_le_mul_of_nonneg_right h (one_div_nonneg.2 he)

theorem exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b * c < a := by
  have : 0 < a / max (b + 1) 1 := div_pos h (lt_max_iff.2 (Or.inr zero_lt_one))
  refine' ⟨a / max (b + 1) 1, this, _⟩
  rw [← lt_div_iff this, div_div_cancel' h.ne']
  exact lt_max_iff.2 (Or.inl <| lt_add_one _)

theorem Monotone.div_const {β : Type _} [Preorderₓ β] {f : β → α} (hf : Monotone f) {c : α} (hc : 0 ≤ c) :
    Monotone fun x => f x / c := by
  simpa only [← div_eq_mul_inv] using hf.mul_const (inv_nonneg.2 hc)

theorem StrictMono.div_const {β : Type _} [Preorderₓ β] {f : β → α} (hf : StrictMono f) {c : α} (hc : 0 < c) :
    StrictMono fun x => f x / c := by
  simpa only [← div_eq_mul_inv] using hf.mul_const (inv_pos.2 hc)

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedField.to_densely_ordered :
    DenselyOrdered α where dense := fun a₁ a₂ h =>
    ⟨(a₁ + a₂) / 2,
      calc
        a₁ = (a₁ + a₁) / 2 := (add_self_div_two a₁).symm
        _ < (a₁ + a₂) / 2 := div_lt_div_of_lt zero_lt_two (add_lt_add_left h _)
        ,
      calc
        (a₁ + a₂) / 2 < (a₂ + a₂) / 2 := div_lt_div_of_lt zero_lt_two (add_lt_add_right h _)
        _ = a₂ := add_self_div_two a₂
        ⟩

theorem min_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : min (a / c) (b / c) = min a b / c :=
  Eq.symm <| Monotone.map_min fun x y => div_le_div_of_le hc

theorem max_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : max (a / c) (b / c) = max a b / c :=
  Eq.symm <| Monotone.map_max fun x y => div_le_div_of_le hc

theorem one_div_strict_anti_on : StrictAntiOn (fun x : α => 1 / x) (Set.Ioi 0) := fun x x1 y y1 xy =>
  (one_div_lt_one_div (Set.mem_Ioi.mp y1) (Set.mem_Ioi.mp x1)).mpr xy

theorem one_div_pow_le_one_div_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) : 1 / a ^ n ≤ 1 / a ^ m := by
  refine' (one_div_le_one_div _ _).mpr (pow_le_pow a1 mn) <;> exact pow_pos (zero_lt_one.trans_le a1) _

theorem one_div_pow_lt_one_div_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) : 1 / a ^ n < 1 / a ^ m := by
  refine' (one_div_lt_one_div _ _).mpr (pow_lt_pow a1 mn) <;> exact pow_pos (trans zero_lt_one a1) _

theorem one_div_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => 1 / a ^ n := fun m n =>
  one_div_pow_le_one_div_pow_of_le a1

theorem one_div_pow_strict_anti (a1 : 1 < a) : StrictAnti fun n : ℕ => 1 / a ^ n := fun m n =>
  one_div_pow_lt_one_div_pow_of_lt a1

theorem inv_strict_anti_on : StrictAntiOn (fun x : α => x⁻¹) (Set.Ioi 0) := fun x hx y hy xy => (inv_lt_inv hy hx).2 xy

theorem inv_pow_le_inv_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) : (a ^ n)⁻¹ ≤ (a ^ m)⁻¹ := by
  convert one_div_pow_le_one_div_pow_of_le a1 mn <;> simp

theorem inv_pow_lt_inv_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) : (a ^ n)⁻¹ < (a ^ m)⁻¹ := by
  convert one_div_pow_lt_one_div_pow_of_lt a1 mn <;> simp

theorem inv_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => (a ^ n)⁻¹ := fun m n => inv_pow_le_inv_pow_of_le a1

theorem inv_pow_strict_anti (a1 : 1 < a) : StrictAnti fun n : ℕ => (a ^ n)⁻¹ := fun m n => inv_pow_lt_inv_pow_of_lt a1

/-! ### Results about `is_lub` and `is_glb` -/


theorem IsGlb.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsGlb s b) : IsGlb ((fun b => a * b) '' s) (a * b) := by
  rcases lt_or_eq_of_leₓ ha with (ha | rfl)
  · exact (OrderIso.mulLeft₀ _ ha).is_glb_image'.2 hs
    
  · simp_rw [zero_mul]
    rw [hs.nonempty.image_const]
    exact is_glb_singleton
    

theorem IsGlb.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsGlb s b) : IsGlb ((fun b => b * a) '' s) (b * a) := by
  simpa [← mul_comm] using hs.mul_left ha

end LinearOrderedSemifield

section

variable [LinearOrderedField α] {a b c d : α}

/-! ### Lemmas about pos, nonneg, nonpos, neg -/


theorem div_pos_iff : 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  simp [← division_def, ← mul_pos_iff]

theorem div_neg_iff : a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  simp [← division_def, ← mul_neg_iff]

theorem div_nonneg_iff : 0 ≤ a / b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp [← division_def, ← mul_nonneg_iff]

theorem div_nonpos_iff : a / b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  simp [← division_def, ← mul_nonpos_iff]

theorem div_nonneg_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a / b :=
  div_nonneg_iff.2 <| Or.inr ⟨ha, hb⟩

theorem div_pos_of_neg_of_neg (ha : a < 0) (hb : b < 0) : 0 < a / b :=
  div_pos_iff.2 <| Or.inr ⟨ha, hb⟩

theorem div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
  div_neg_iff.2 <| Or.inr ⟨ha, hb⟩

theorem div_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
  div_neg_iff.2 <| Or.inl ⟨ha, hb⟩

/-! ### Relating one division with another term -/


theorem div_le_iff_of_neg (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b :=
  ⟨fun h => div_mul_cancel b (ne_of_ltₓ hc) ▸ mul_le_mul_of_nonpos_right h hc.le, fun h =>
    calc
      a = a * c * (1 / c) := mul_mul_div a (ne_of_ltₓ hc)
      _ ≥ b * (1 / c) := mul_le_mul_of_nonpos_right h (one_div_neg.2 hc).le
      _ = b / c := (div_eq_mul_one_div b c).symm
      ⟩

theorem div_le_iff_of_neg' (hc : c < 0) : b / c ≤ a ↔ c * a ≤ b := by
  rw [mul_comm, div_le_iff_of_neg hc]

theorem le_div_iff_of_neg (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c := by
  rw [← neg_negₓ c, mul_neg, div_neg, le_neg, div_le_iff (neg_pos.2 hc), neg_mul]

theorem le_div_iff_of_neg' (hc : c < 0) : a ≤ b / c ↔ b ≤ c * a := by
  rw [mul_comm, le_div_iff_of_neg hc]

theorem div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < b :=
  lt_iff_lt_of_le_iff_le <| le_div_iff_of_neg hc

theorem div_lt_iff_of_neg' (hc : c < 0) : b / c < a ↔ c * a < b := by
  rw [mul_comm, div_lt_iff_of_neg hc]

theorem lt_div_iff_of_neg (hc : c < 0) : a < b / c ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le <| div_le_iff_of_neg hc

theorem lt_div_iff_of_neg' (hc : c < 0) : a < b / c ↔ b < c * a := by
  rw [mul_comm, lt_div_iff_of_neg hc]

/-! ### Bi-implications of inequalities using inversions -/


theorem inv_le_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [← one_div, div_le_iff_of_neg ha, ← div_eq_inv_mul, div_le_iff_of_neg hb, one_mulₓ]

theorem inv_le_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv_of_neg hb (inv_lt_zero.2 ha), inv_invₓ]

theorem le_inv_of_neg (ha : a < 0) (hb : b < 0) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv_of_neg (inv_lt_zero.2 hb) ha, inv_invₓ]

theorem inv_lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b⁻¹ ↔ b < a :=
  lt_iff_lt_of_le_iff_le (inv_le_inv_of_neg hb ha)

theorem inv_lt_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b ↔ b⁻¹ < a :=
  lt_iff_lt_of_le_iff_le (le_inv_of_neg hb ha)

theorem lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a < b⁻¹ ↔ b < a⁻¹ :=
  lt_iff_lt_of_le_iff_le (inv_le_of_neg hb ha)

/-! ### Relating two divisions -/


theorem div_le_div_of_nonpos_of_le (hc : c ≤ 0) (h : b ≤ a) : a / c ≤ b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_le_mul_of_nonpos_right h (one_div_nonpos.2 hc)

theorem div_lt_div_of_neg_of_lt (hc : c < 0) (h : b < a) : a / c < b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_lt_mul_of_neg_right h (one_div_neg.2 hc)

theorem div_le_div_right_of_neg (hc : c < 0) : a / c ≤ b / c ↔ b ≤ a :=
  ⟨le_imp_le_of_lt_imp_ltₓ <| div_lt_div_of_neg_of_lt hc, div_le_div_of_nonpos_of_le <| hc.le⟩

theorem div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a :=
  lt_iff_lt_of_le_iff_le <| div_le_div_right_of_neg hc

/-! ### Relating one division and involving `1` -/


theorem one_le_div_of_neg (hb : b < 0) : 1 ≤ a / b ↔ a ≤ b := by
  rw [le_div_iff_of_neg hb, one_mulₓ]

theorem div_le_one_of_neg (hb : b < 0) : a / b ≤ 1 ↔ b ≤ a := by
  rw [div_le_iff_of_neg hb, one_mulₓ]

theorem one_lt_div_of_neg (hb : b < 0) : 1 < a / b ↔ a < b := by
  rw [lt_div_iff_of_neg hb, one_mulₓ]

theorem div_lt_one_of_neg (hb : b < 0) : a / b < 1 ↔ b < a := by
  rw [div_lt_iff_of_neg hb, one_mulₓ]

theorem one_div_le_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ b ↔ 1 / b ≤ a := by
  simpa using inv_le_of_neg ha hb

theorem one_div_lt_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < b ↔ 1 / b < a := by
  simpa using inv_lt_of_neg ha hb

theorem le_one_div_of_neg (ha : a < 0) (hb : b < 0) : a ≤ 1 / b ↔ b ≤ 1 / a := by
  simpa using le_inv_of_neg ha hb

theorem lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : a < 1 / b ↔ b < 1 / a := by
  simpa using lt_inv_of_neg ha hb

theorem one_lt_div_iff : 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a < b := by
  rcases lt_trichotomyₓ b 0 with (hb | rfl | hb)
  · simp [← hb, ← hb.not_lt, ← one_lt_div_of_neg]
    
  · simp [← lt_irreflₓ, ← zero_le_one]
    
  · simp [← hb, ← hb.not_lt, ← one_lt_div]
    

theorem one_le_div_iff : 1 ≤ a / b ↔ 0 < b ∧ b ≤ a ∨ b < 0 ∧ a ≤ b := by
  rcases lt_trichotomyₓ b 0 with (hb | rfl | hb)
  · simp [← hb, ← hb.not_lt, ← one_le_div_of_neg]
    
  · simp [← lt_irreflₓ, ← zero_lt_one.not_le, ← zero_lt_one]
    
  · simp [← hb, ← hb.not_lt, ← one_le_div]
    

theorem div_lt_one_iff : a / b < 1 ↔ 0 < b ∧ a < b ∨ b = 0 ∨ b < 0 ∧ b < a := by
  rcases lt_trichotomyₓ b 0 with (hb | rfl | hb)
  · simp [← hb, ← hb.not_lt, ← hb.ne, ← div_lt_one_of_neg]
    
  · simp [← zero_lt_one]
    
  · simp [← hb, ← hb.not_lt, ← div_lt_one, ← hb.ne.symm]
    

theorem div_le_one_iff : a / b ≤ 1 ↔ 0 < b ∧ a ≤ b ∨ b = 0 ∨ b < 0 ∧ b ≤ a := by
  rcases lt_trichotomyₓ b 0 with (hb | rfl | hb)
  · simp [← hb, ← hb.not_lt, ← hb.ne, ← div_le_one_of_neg]
    
  · simp [← zero_le_one]
    
  · simp [← hb, ← hb.not_lt, ← div_le_one, ← hb.ne.symm]
    

/-! ### Relating two divisions, involving `1` -/


theorem one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  rwa [div_le_iff_of_neg' hb, ← div_eq_mul_one_div, div_le_one_of_neg (h.trans_lt hb)]

theorem one_div_lt_one_div_of_neg_of_lt (hb : b < 0) (h : a < b) : 1 / b < 1 / a := by
  rwa [div_lt_iff_of_neg' hb, ← div_eq_mul_one_div, div_lt_one_of_neg (h.trans hb)]

theorem le_of_neg_of_one_div_le_one_div (hb : b < 0) (h : 1 / a ≤ 1 / b) : b ≤ a :=
  le_imp_le_of_lt_imp_ltₓ (one_div_lt_one_div_of_neg_of_lt hb) h

theorem lt_of_neg_of_one_div_lt_one_div (hb : b < 0) (h : 1 / a < 1 / b) : b < a :=
  lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_neg_of_le hb) h

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_neg_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_le_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ 1 / b ↔ b ≤ a := by
  simpa [← one_div] using inv_le_inv_of_neg ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < 1 / b ↔ b < a :=
  lt_iff_lt_of_le_iff_le (one_div_le_one_div_of_neg hb ha)

theorem one_div_lt_neg_one (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 :=
  suffices 1 / a < 1 / -1 by
    rwa [one_div_neg_one_eq_neg_one] at this
  one_div_lt_one_div_of_neg_of_lt h1 h2

theorem one_div_le_neg_one (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 :=
  suffices 1 / a ≤ 1 / -1 by
    rwa [one_div_neg_one_eq_neg_one] at this
  one_div_le_one_div_of_neg_of_le h1 h2

/-! ### Results about halving -/


theorem sub_self_div_two (a : α) : a - a / 2 = a / 2 := by
  suffices a / 2 + a / 2 - a / 2 = a / 2 by
    rwa [add_halves] at this
  rw [add_sub_cancel]

theorem div_two_sub_self (a : α) : a / 2 - a = -(a / 2) := by
  suffices a / 2 - (a / 2 + a / 2) = -(a / 2) by
    rwa [add_halves] at this
  rw [sub_add_eq_sub_sub, sub_self, zero_sub]

theorem add_sub_div_two_lt (h : a < b) : a + (b - a) / 2 < b := by
  rwa [← div_sub_div_same, sub_eq_add_neg, add_commₓ (b / 2), ← add_assocₓ, ← sub_eq_add_neg, ← lt_sub_iff_add_lt,
    sub_self_div_two, sub_self_div_two, div_lt_div_right (@zero_lt_two α _ _)]

/-- An inequality involving `2`. -/
theorem sub_one_div_inv_le_two (a2 : 2 ≤ a) : (1 - 1 / a)⁻¹ ≤ 2 := by
  -- Take inverses on both sides to obtain `2⁻¹ ≤ 1 - 1 / a`
  refine' (inv_le_inv_of_le (inv_pos.2 zero_lt_two) _).trans_eq (inv_invₓ (2 : α))
  -- move `1 / a` to the left and `1 - 1 / 2 = 1 / 2` to the right to obtain `1 / a ≤ ⅟ 2`
  refine' (le_sub_iff_add_le.2 (_ : _ + 2⁻¹ = _).le).trans ((sub_le_sub_iff_left 1).2 _)
  · -- show 2⁻¹ + 2⁻¹ = 1
    exact (two_mul _).symm.trans (mul_inv_cancel two_ne_zero)
    
  · -- take inverses on both sides and use the assumption `2 ≤ a`.
    exact (one_div a).le.trans (inv_le_inv_of_le zero_lt_two a2)
    

/-! ### Results about `is_lub` and `is_glb` -/


-- TODO: Generalize to `linear_ordered_semifield`
theorem IsLub.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsLub s b) : IsLub ((fun b => a * b) '' s) (a * b) := by
  rcases lt_or_eq_of_leₓ ha with (ha | rfl)
  · exact (OrderIso.mulLeft₀ _ ha).is_lub_image'.2 hs
    
  · simp_rw [zero_mul]
    rw [hs.nonempty.image_const]
    exact is_lub_singleton
    

-- TODO: Generalize to `linear_ordered_semifield`
theorem IsLub.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsLub s b) : IsLub ((fun b => b * a) '' s) (b * a) := by
  simpa [← mul_comm] using hs.mul_left ha

/-! ### Miscellaneous lemmmas -/


theorem mul_sub_mul_div_mul_neg_iff (hc : c ≠ 0) (hd : d ≠ 0) : (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d := by
  rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_lt_zero]

theorem mul_sub_mul_div_mul_nonpos_iff (hc : c ≠ 0) (hd : d ≠ 0) : (a * d - b * c) / (c * d) ≤ 0 ↔ a / c ≤ b / d := by
  rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_nonpos]

alias mul_sub_mul_div_mul_neg_iff ↔ div_lt_div_of_mul_sub_mul_div_neg mul_sub_mul_div_mul_neg

alias mul_sub_mul_div_mul_nonpos_iff ↔ div_le_div_of_mul_sub_mul_div_nonpos mul_sub_mul_div_mul_nonpos

theorem exists_add_lt_and_pos_of_lt (h : b < a) : ∃ c, b + c < a ∧ 0 < c :=
  ⟨(a - b) / 2, add_sub_div_two_lt h, div_pos (sub_pos_of_lt h) zero_lt_two⟩

theorem le_of_forall_sub_le (h : ∀, ∀ ε > 0, ∀, b - ε ≤ a) : b ≤ a := by
  contrapose! h
  simpa only [← and_comm ((0 : α) < _), ← lt_sub_iff_add_lt, ← gt_iff_lt] using exists_add_lt_and_pos_of_lt h

theorem mul_self_inj_of_nonneg (a0 : 0 ≤ a) (b0 : 0 ≤ b) : a * a = b * b ↔ a = b :=
  mul_self_eq_mul_self_iff.trans <|
    or_iff_left_of_imp fun h => by
      subst a
      have : b = 0 := le_antisymmₓ (neg_nonneg.1 a0) b0
      rw [this, neg_zero]

theorem min_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) : min (a / c) (b / c) = max a b / c :=
  Eq.symm <| Antitone.map_max fun x y => div_le_div_of_nonpos_of_le hc

theorem max_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) : max (a / c) (b / c) = min a b / c :=
  Eq.symm <| Antitone.map_min fun x y => div_le_div_of_nonpos_of_le hc

theorem abs_inv (a : α) : abs a⁻¹ = (abs a)⁻¹ :=
  (absHom : α →*₀ α).map_inv a

theorem abs_div (a b : α) : abs (a / b) = abs a / abs b :=
  (absHom : α →*₀ α).map_div a b

theorem abs_one_div (a : α) : abs (1 / a) = 1 / abs a := by
  rw [abs_div, abs_one]

theorem pow_minus_two_nonneg : 0 ≤ a ^ (-2 : ℤ) := by
  simp only [← inv_nonneg, ← zpow_neg]
  change 0 ≤ a ^ ((2 : ℕ) : ℤ)
  rw [zpow_coe_nat]
  apply sq_nonneg

/-- Bernoulli's inequality reformulated to estimate `(n : α)`. -/
theorem Nat.cast_le_pow_sub_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ (a ^ n - 1) / (a - 1) :=
  (le_div_iff (sub_pos.2 H)).2 <|
    le_sub_left_of_add_le <| one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

/-- For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the numerator. -/
theorem Nat.cast_le_pow_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ a ^ n / (a - 1) :=
  (n.cast_le_pow_sub_div_sub H).trans <| div_le_div_of_le (sub_nonneg.2 H.le) (sub_le_self _ zero_le_one)

end

