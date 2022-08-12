/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/
import Mathbin.Algebra.Order.Group
import Mathbin.Tactic.Abel

/-!
# Linearly ordered commutative groups and monoids with a zero element adjoined

This file sets up a special class of linearly ordered commutative monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative group Γ and formally adjoining a zero element: Γ ∪ {0}.

The disadvantage is that a type such as `nnreal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.

Note that to avoid issues with import cycles, `linear_ordered_comm_monoid_with_zero` is defined
in another file. However, the lemmas about it are stated here.
-/


/-- A linearly ordered commutative group with a zero element. -/
class LinearOrderedCommGroupWithZero (α : Type _) extends LinearOrderedCommMonoidWithZero α, CommGroupWithZero α

variable {α : Type _}

variable {a b c d x y z : α}

instance [LinearOrderedAddCommMonoidWithTop α] : LinearOrderedCommMonoidWithZero (Multiplicative αᵒᵈ) :=
  { Multiplicative.orderedCommMonoid, Multiplicative.linearOrder with zero := Multiplicative.ofAdd (⊤ : α),
    zero_mul := top_add, mul_zero := add_top, zero_le_one := (le_top : (0 : α) ≤ ⊤) }

instance [LinearOrderedAddCommGroupWithTop α] : LinearOrderedCommGroupWithZero (Multiplicative αᵒᵈ) :=
  { Multiplicative.divInvMonoid, Multiplicative.linearOrderedCommMonoidWithZero, Multiplicative.nontrivial with
    inv_zero := LinearOrderedAddCommGroupWithTop.neg_top,
    mul_inv_cancel := LinearOrderedAddCommGroupWithTop.add_neg_cancel }

section Monoidₓ

variable [Monoidₓ α]

section Preorderₓ

variable [Preorderₓ α]

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

theorem Left.one_le_pow_of_le : ∀ {n : ℕ} {x : α}, 1 ≤ x → 1 ≤ x ^ n
  | 0, x, _ => (pow_zeroₓ x).symm.le
  | n + 1, x, H =>
    calc
      1 ≤ x := H
      _ = x * 1 := (mul_oneₓ x).symm
      _ ≤ x * x ^ n := mul_le_mul_left' (Left.one_le_pow_of_le H) x
      _ = x ^ n.succ := (pow_succₓ x n).symm
      

end Left

section Right

variable [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

theorem Right.one_le_pow_of_le {x : α} (H : 1 ≤ x) : ∀ {n : ℕ}, 1 ≤ x ^ n
  | 0 => (pow_zeroₓ _).symm.le
  | n + 1 =>
    calc
      1 ≤ x := H
      _ = 1 * x := (one_mulₓ x).symm
      _ ≤ x ^ n * x := mul_le_mul_right' Right.one_le_pow_of_le x
      _ = x ^ n.succ := (pow_succ'ₓ x n).symm
      

theorem Right.pow_le_one_of_le {x : α} (H : x ≤ 1) : ∀ {n : ℕ}, x ^ n ≤ 1
  | 0 => (pow_zeroₓ _).le
  | n + 1 =>
    calc
      x ^ n.succ = x ^ n * x := pow_succ'ₓ x n
      _ ≤ 1 * x := mul_le_mul_right' Right.pow_le_one_of_le x
      _ = x := one_mulₓ x
      _ ≤ 1 := H
      

end Right

theorem pow_le_pow_of_le [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]
    {x y : α} (H : x ≤ y) : ∀ {n : ℕ}, x ^ n ≤ y ^ n
  | 0 => (pow_zeroₓ _).le.trans (pow_zeroₓ _).symm.le
  | n + 1 =>
    calc
      x ^ n.succ = x * x ^ n := pow_succₓ x n
      _ ≤ y * x ^ n := mul_le_mul_right' H (x ^ n)
      _ ≤ y * y ^ n := mul_le_mul_left' pow_le_pow_of_le y
      _ = y ^ n.succ := (pow_succₓ y n).symm
      

theorem Left.pow_lt_one_of_lt [CovariantClass α α (· * ·) (· < ·)] {n : ℕ} {x : α} (n0 : 0 < n) (H : x < 1) :
    x ^ n < 1 := by
  refine' Nat.le_induction ((pow_oneₓ _).le.trans_lt H) (fun n n1 hn => _) _ (nat.succ_le_iff.mpr n0)
  calc x ^ (n + 1) = x * x ^ n := pow_succₓ x n _ < x * 1 := mul_lt_mul_left' hn x _ = x := mul_oneₓ x _ < 1 := H

theorem Left.pow_lt_one_iff {α : Type _} [Monoidₓ α] [LinearOrderₓ α] [CovariantClass α α (· * ·) (· < ·)] {n : ℕ}
    {x : α} (n0 : 0 < n) : x ^ n < 1 ↔ x < 1 :=
  ⟨fun H =>
    not_leₓ.mp fun k =>
      not_leₓ.mpr H
        (by
          have := Mul.to_covariant_class_left α
          exact Left.one_le_pow_of_le k),
    Left.pow_lt_one_of_lt n0⟩

theorem Right.pow_lt_one_of_lt [CovariantClass α α (Function.swap (· * ·)) (· < ·)] {n : ℕ} {x : α} (n0 : 0 < n)
    (H : x < 1) : x ^ n < 1 := by
  refine' Nat.le_induction ((pow_oneₓ _).le.trans_lt H) (fun n n1 hn => _) _ (nat.succ_le_iff.mpr n0)
  calc x ^ (n + 1) = x ^ n * x := pow_succ'ₓ x n _ < 1 * x := mul_lt_mul_right' hn x _ = x := one_mulₓ x _ < 1 := H

theorem Right.pow_lt_one_iff {α : Type _} [Monoidₓ α] [LinearOrderₓ α]
    [CovariantClass α α (Function.swap (· * ·)) (· < ·)] {n : ℕ} {x : α} (n0 : 0 < n) : x ^ n < 1 ↔ x < 1 :=
  ⟨fun H =>
    not_leₓ.mp fun k =>
      not_leₓ.mpr H
        (by
          have := Mul.to_covariant_class_right α
          exact Right.one_le_pow_of_le k),
    Right.pow_lt_one_of_lt n0⟩

end Preorderₓ

section LeftRight

variable [LinearOrderₓ α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

end LeftRight

end Monoidₓ

instance [LinearOrderedCommMonoid α] : LinearOrderedCommMonoidWithZero (WithZero α) :=
  { WithZero.linearOrder, WithZero.commMonoidWithZero with mul_le_mul_left := fun x y => mul_le_mul_left',
    zero_le_one := WithZero.zero_le _ }

instance [LinearOrderedCommGroup α] : LinearOrderedCommGroupWithZero (WithZero α) :=
  { WithZero.linearOrderedCommMonoidWithZero, WithZero.commGroupWithZero with }

section LinearOrderedCommMonoid

variable [LinearOrderedCommMonoidWithZero α]

/-- Pullback a `linear_ordered_comm_monoid_with_zero` under an injective map.
See note [reducible non-instances]. -/
/-
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/
@[reducible]
def Function.Injective.linearOrderedCommMonoidWithZero {β : Type _} [Zero β] [One β] [Mul β] [Pow β ℕ] [HasSup β]
    [HasInf β] (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x⊔y) = max (f x) (f y)) (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) :
    LinearOrderedCommMonoidWithZero β :=
  { LinearOrderₓ.lift f hf hsup hinf, hf.OrderedCommMonoid f one mul npow,
    hf.CommMonoidWithZero f zero one mul npow with
    zero_le_one :=
      show f 0 ≤ f 1 by
        simp only [← zero, ← one, ← LinearOrderedCommMonoidWithZero.zero_le_one] }

@[simp]
theorem zero_le' : 0 ≤ a := by
  simpa only [← mul_zero, ← mul_oneₓ] using mul_le_mul_left' zero_le_one a

@[simp]
theorem not_lt_zero' : ¬a < 0 :=
  not_lt_of_le zero_le'

@[simp]
theorem le_zero_iff : a ≤ 0 ↔ a = 0 :=
  ⟨fun h => le_antisymmₓ h zero_le', fun h => h ▸ le_rfl⟩

theorem zero_lt_iff : 0 < a ↔ a ≠ 0 :=
  ⟨ne_of_gtₓ, fun h => lt_of_le_of_neₓ zero_le' h.symm⟩

theorem ne_zero_of_lt (h : b < a) : a ≠ 0 := fun h1 => not_lt_zero' <| show b < 0 from h1 ▸ h

theorem pow_pos_iff [NoZeroDivisors α] {n : ℕ} (hn : 0 < n) : 0 < a ^ n ↔ 0 < a := by
  simp_rw [zero_lt_iff, pow_ne_zero_iff hn]

instance : LinearOrderedAddCommMonoidWithTop (Additive αᵒᵈ) :=
  { Additive.orderedAddCommMonoid, Additive.linearOrder with top := (0 : α),
    top_add' := fun a => (zero_mul a : (0 : α) * a = 0), le_top := fun _ => zero_le' }

end LinearOrderedCommMonoid

variable [LinearOrderedCommGroupWithZero α]

theorem zero_lt_one₀ : (0 : α) < 1 :=
  lt_of_le_of_neₓ zero_le_one zero_ne_one

theorem le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b := by
  simpa only [← mul_inv_cancel_right₀ h] using mul_le_mul_right' hab c⁻¹

theorem le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
  le_of_le_mul_right h
    (by
      simpa [← h] using hab)

theorem mul_inv_le_of_le_mul (hab : a ≤ b * c) : a * c⁻¹ ≤ b := by
  by_cases' h : c = 0
  · simp [← h]
    
  · exact
      le_of_le_mul_right h
        (by
          simpa [← h] using hab)
    

theorem le_mul_inv_iff₀ (hc : c ≠ 0) : a ≤ b * c⁻¹ ↔ a * c ≤ b :=
  ⟨fun h => inv_invₓ c ▸ mul_inv_le_of_le_mul h, le_mul_inv_of_mul_le hc⟩

theorem mul_inv_le_iff₀ (hc : c ≠ 0) : a * c⁻¹ ≤ b ↔ a ≤ b * c :=
  ⟨fun h => inv_invₓ c ▸ le_mul_inv_of_mul_le (inv_ne_zero hc) h, mul_inv_le_of_le_mul⟩

theorem div_le_div₀ (a b c d : α) (hb : b ≠ 0) (hd : d ≠ 0) : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
  if ha : a = 0 then by
    simp [← ha]
  else
    if hc : c = 0 then by
      simp [← inv_ne_zero hb, ← hc, ← hd]
    else
      show
        Units.mk0 a ha * (Units.mk0 b hb)⁻¹ ≤ Units.mk0 c hc * (Units.mk0 d hd)⁻¹ ↔
          Units.mk0 a ha * Units.mk0 d hd ≤ Units.mk0 c hc * Units.mk0 b hb
        from mul_inv_le_mul_inv_iff'

@[simp]
theorem Units.zero_lt (u : αˣ) : (0 : α) < u :=
  zero_lt_iff.2 <| u.ne_zero

theorem mul_lt_mul_of_lt_of_le₀ (hab : a ≤ b) (hb : b ≠ 0) (hcd : c < d) : a * c < b * d :=
  have hd : d ≠ 0 := ne_zero_of_lt hcd
  if ha : a = 0 then by
    rw [ha, zero_mul, zero_lt_iff]
    exact mul_ne_zero hb hd
  else
    if hc : c = 0 then by
      rw [hc, mul_zero, zero_lt_iff]
      exact mul_ne_zero hb hd
    else show Units.mk0 a ha * Units.mk0 c hc < Units.mk0 b hb * Units.mk0 d hd from mul_lt_mul_of_le_of_lt hab hcd

theorem mul_lt_mul₀ (hab : a < b) (hcd : c < d) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le₀ hab.le (ne_zero_of_lt hab) hcd

theorem mul_inv_lt_of_lt_mul₀ (h : x < y * z) : x * z⁻¹ < y := by
  contrapose! h
  simpa only [← inv_invₓ] using mul_inv_le_of_le_mul h

theorem inv_mul_lt_of_lt_mul₀ (h : x < y * z) : y⁻¹ * x < z := by
  rw [mul_comm] at *
  exact mul_inv_lt_of_lt_mul₀ h

theorem mul_lt_right₀ (c : α) (h : a < b) (hc : c ≠ 0) : a * c < b * c := by
  contrapose! h
  exact le_of_le_mul_right hc h

theorem pow_lt_pow_succ {x : α} {n : ℕ} (hx : 1 < x) : x ^ n < x ^ n.succ := by
  rw [← one_mulₓ (x ^ n), pow_succₓ]
  exact mul_lt_right₀ _ hx (pow_ne_zero _ <| ne_of_gtₓ (lt_transₓ zero_lt_one₀ hx))

theorem pow_lt_pow₀ {x : α} {m n : ℕ} (hx : 1 < x) (hmn : m < n) : x ^ m < x ^ n := by
  induction' hmn with n hmn ih
  exacts[pow_lt_pow_succ hx, lt_transₓ ih (pow_lt_pow_succ hx)]

theorem inv_lt_inv₀ (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ < b⁻¹ ↔ b < a :=
  show (Units.mk0 a ha)⁻¹ < (Units.mk0 b hb)⁻¹ ↔ Units.mk0 b hb < Units.mk0 a ha from inv_lt_inv_iff

theorem inv_le_inv₀ (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  show (Units.mk0 a ha)⁻¹ ≤ (Units.mk0 b hb)⁻¹ ↔ Units.mk0 b hb ≤ Units.mk0 a ha from inv_le_inv_iff

theorem lt_of_mul_lt_mul_of_le₀ (h : a * b < c * d) (hc : 0 < c) (hh : c ≤ a) : b < d := by
  have ha : a ≠ 0 := ne_of_gtₓ (lt_of_lt_of_leₓ hc hh)
  simp_rw [← inv_le_inv₀ ha (ne_of_gtₓ hc)] at hh
  have := mul_lt_mul_of_lt_of_le₀ hh (inv_ne_zero (ne_of_gtₓ hc)) h
  simpa [← inv_mul_cancel_left₀ ha, ← inv_mul_cancel_left₀ (ne_of_gtₓ hc)] using this

theorem mul_le_mul_right₀ (hc : c ≠ 0) : a * c ≤ b * c ↔ a ≤ b :=
  ⟨le_of_le_mul_right hc, fun hab => mul_le_mul_right' hab _⟩

theorem mul_le_mul_left₀ (ha : a ≠ 0) : a * b ≤ a * c ↔ b ≤ c := by
  simp only [← mul_comm a]
  exact mul_le_mul_right₀ ha

theorem div_le_div_right₀ (hc : c ≠ 0) : a / c ≤ b / c ↔ a ≤ b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_le_mul_right₀ (inv_ne_zero hc)]

theorem div_le_div_left₀ (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a / b ≤ a / c ↔ c ≤ b := by
  simp only [← div_eq_mul_inv, ← mul_le_mul_left₀ ha, ← inv_le_inv₀ hb hc]

theorem le_div_iff₀ (hc : c ≠ 0) : a ≤ b / c ↔ a * c ≤ b := by
  rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]

theorem div_le_iff₀ (hc : c ≠ 0) : a / c ≤ b ↔ a ≤ b * c := by
  rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]

/-- `equiv.mul_left₀` as an order_iso on a `linear_ordered_comm_group_with_zero.`.

Note that `order_iso.mul_left₀` refers to the `linear_ordered_field` version. -/
@[simps (config := { simpRhs := true }) apply toEquiv]
def OrderIso.mulLeft₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
  { Equivₓ.mulLeft₀ a ha with map_rel_iff' := fun x y => mul_le_mul_left₀ ha }

theorem OrderIso.mul_left₀'_symm {a : α} (ha : a ≠ 0) :
    (OrderIso.mulLeft₀' ha).symm = OrderIso.mulLeft₀' (inv_ne_zero ha) := by
  ext
  rfl

/-- `equiv.mul_right₀` as an order_iso on a `linear_ordered_comm_group_with_zero.`.

Note that `order_iso.mul_right₀` refers to the `linear_ordered_field` version. -/
@[simps (config := { simpRhs := true }) apply toEquiv]
def OrderIso.mulRight₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
  { Equivₓ.mulRight₀ a ha with map_rel_iff' := fun _ _ => mul_le_mul_right₀ ha }

theorem OrderIso.mul_right₀'_symm {a : α} (ha : a ≠ 0) :
    (OrderIso.mulRight₀' ha).symm = OrderIso.mulRight₀' (inv_ne_zero ha) := by
  ext
  rfl

instance : LinearOrderedAddCommGroupWithTop (Additive αᵒᵈ) :=
  { Additive.subNegMonoid, Additive.linearOrderedAddCommMonoidWithTop, Additive.nontrivial with neg_top := inv_zero,
    add_neg_cancel := fun a ha => mul_inv_cancel ha }

namespace MonoidHom

variable {R : Type _} [Ringₓ R] (f : R →* α)

theorem map_neg_one : f (-1) = 1 :=
  (pow_eq_one_iff (Nat.succ_ne_zero 1)).1 <|
    calc
      f (-1) ^ 2 = f (-1) * f (-1) := sq _
      _ = f (-1 * -1) := (f.map_mul _ _).symm
      _ = f (- -1) := congr_arg _ (neg_one_mul _)
      _ = f 1 := congr_arg _ (neg_negₓ _)
      _ = 1 := map_one f
      

@[simp]
theorem map_neg (x : R) : f (-x) = f x :=
  calc
    f (-x) = f (-1 * x) := congr_arg _ (neg_one_mul _).symm
    _ = f (-1) * f x := map_mul _ _ _
    _ = 1 * f x := congr_arg (fun g => g * f x) (map_neg_one f)
    _ = f x := one_mulₓ _
    

theorem map_sub_swap (x y : R) : f (x - y) = f (y - x) :=
  calc
    f (x - y) = f (-(y - x)) := congr_arg _ (neg_sub _ _).symm
    _ = _ := map_neg _ _
    

end MonoidHom

