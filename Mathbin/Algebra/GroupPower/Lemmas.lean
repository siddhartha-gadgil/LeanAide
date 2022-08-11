/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathbin.Algebra.Invertible
import Mathbin.Algebra.GroupPower.Ring
import Mathbin.Data.Int.Cast

/-!
# Lemmas about power operations on monoids and groups

This file contains lemmas about `monoid.pow`, `group.pow`, `nsmul`, `zsmul`
which require additional imports besides those available in `algebra.group_power.basic`.
-/


open Function Int Nat

universe u v w x y z u₁ u₂

variable {α : Type _} {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z} {R : Type u₁}
  {S : Type u₂}

/-!
### (Additive) monoid
-/


section Monoidₓ

@[simp]
theorem nsmul_one [AddMonoidWithOneₓ A] : ∀ n : ℕ, n • (1 : A) = n := by
  refine' eq_nat_cast' (⟨_, _, _⟩ : ℕ →+ A) _
  · show 0 • (1 : A) = 0
    simp [← zero_nsmul]
    
  · show ∀ x y : ℕ, (x + y) • (1 : A) = x • 1 + y • 1
    simp [← add_nsmul]
    
  · show 1 • (1 : A) = 1
    simp
    

variable [Monoidₓ M] [Monoidₓ N] [AddMonoidₓ A] [AddMonoidₓ B]

instance invertiblePow (m : M) [Invertible m] (n : ℕ) : Invertible (m ^ n) where
  invOf := ⅟ m ^ n
  inv_of_mul_self := by
    rw [← (commute_inv_of m).symm.mul_pow, inv_of_mul_self, one_pow]
  mul_inv_of_self := by
    rw [← (commute_inv_of m).mul_pow, mul_inv_of_self, one_pow]

theorem inv_of_pow (m : M) [Invertible m] (n : ℕ) [Invertible (m ^ n)] : ⅟ (m ^ n) = ⅟ m ^ n :=
  @invertible_unique M _ (m ^ n) (m ^ n) _ (invertiblePow m n) rfl

theorem IsUnit.pow {m : M} (n : ℕ) : IsUnit m → IsUnit (m ^ n) := fun ⟨u, hu⟩ =>
  ⟨u ^ n, by
    simp [*]⟩

@[simp]
theorem is_unit_pow_succ_iff {m : M} {n : ℕ} : IsUnit (m ^ (n + 1)) ↔ IsUnit m := by
  refine' ⟨_, fun h => h.pow _⟩
  rw [pow_succₓ, ((Commute.refl _).pow_right _).is_unit_mul_iff]
  exact And.left

theorem is_unit_pos_pow_iff {m : M} : ∀ {n : ℕ} (h : 0 < n), IsUnit (m ^ n) ↔ IsUnit m
  | n + 1, _ => is_unit_pow_succ_iff

/-- If `x ^ n.succ = 1` then `x` has an inverse, `x^n`. -/
def invertibleOfPowSuccEqOne (x : M) (n : ℕ) (hx : x ^ n.succ = 1) : Invertible x :=
  ⟨x ^ n, (pow_succ'ₓ x n).symm.trans hx, (pow_succₓ x n).symm.trans hx⟩

/-- If `x ^ n = 1` then `x` has an inverse, `x^(n - 1)`. -/
def invertibleOfPowEqOne (x : M) (n : ℕ) (hx : x ^ n = 1) (hn : 0 < n) : Invertible x := by
  apply invertibleOfPowSuccEqOne x (n - 1)
  convert hx
  exact tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ hn)

theorem is_unit_of_pow_eq_one (x : M) (n : ℕ) (hx : x ^ n = 1) (hn : 0 < n) : IsUnit x := by
  have := invertibleOfPowEqOne x n hx hn
  exact is_unit_of_invertible x

theorem smul_pow [MulAction M N] [IsScalarTower M N N] [SmulCommClass M N N] (k : M) (x : N) (p : ℕ) :
    (k • x) ^ p = k ^ p • x ^ p := by
  induction' p with p IH
  · simp
    
  · rw [pow_succ'ₓ, IH, smul_mul_smul, ← pow_succ'ₓ, ← pow_succ'ₓ]
    

@[simp]
theorem smul_pow' [MulDistribMulAction M N] (x : M) (m : N) (n : ℕ) : x • m ^ n = (x • m) ^ n := by
  induction' n with n ih
  · rw [pow_zeroₓ, pow_zeroₓ]
    exact smul_one x
    
  · rw [pow_succₓ, pow_succₓ]
    exact (smul_mul' x m (m ^ n)).trans (congr_arg _ ih)
    

end Monoidₓ

theorem zsmul_one [AddGroupWithOneₓ A] (n : ℤ) : n • (1 : A) = n := by
  cases n <;> simp

section DivisionMonoid

variable [DivisionMonoid α]

-- Note that `mul_zsmul` and `zpow_mul` have the primes swapped since their argument order,
-- and therefore the more "natural" choice of lemma, is reversed.
@[to_additive mul_zsmul']
theorem zpow_mul (a : α) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by
    rw [zpow_coe_nat, zpow_coe_nat, ← pow_mulₓ, ← zpow_coe_nat]
    rfl
  | (m : ℕ), -[1+ n] => by
    rw [zpow_coe_nat, zpow_neg_succ_of_nat, ← pow_mulₓ, coe_nat_mul_neg_succ, zpow_neg, inv_inj, ← zpow_coe_nat]
    rfl
  | -[1+ m], (n : ℕ) => by
    rw [zpow_coe_nat, zpow_neg_succ_of_nat, ← inv_pow, ← pow_mulₓ, neg_succ_mul_coe_nat, zpow_neg, inv_pow, inv_inj, ←
      zpow_coe_nat]
    rfl
  | -[1+ m], -[1+ n] => by
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, neg_succ_mul_neg_succ, inv_pow, inv_invₓ, ← pow_mulₓ, ←
      zpow_coe_nat]
    rfl

@[to_additive mul_zsmul]
theorem zpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m := by
  rw [mul_comm, zpow_mul]

@[to_additive bit0_zsmul]
theorem zpow_bit0 (a : α) : ∀ n : ℤ, a ^ bit0 n = a ^ n * a ^ n
  | (n : ℕ) => by
    simp only [← zpow_coe_nat, Int.coe_nat_bit0, ← pow_bit0]
  | -[1+ n] => by
    simp [mul_inv_rev, pow_bit0]
    rw [neg_succ_of_nat_eq, bit0_neg, zpow_neg]
    norm_cast

@[to_additive bit0_zsmul']
theorem zpow_bit0' (a : α) (n : ℤ) : a ^ bit0 n = (a * a) ^ n :=
  (zpow_bit0 a n).trans ((Commute.refl a).mul_zpow n).symm

@[simp]
theorem zpow_bit0_neg [HasDistribNeg α] (x : α) (n : ℤ) : -x ^ bit0 n = x ^ bit0 n := by
  rw [zpow_bit0', zpow_bit0', neg_mul_neg]

end DivisionMonoid

section Groupₓ

variable [Groupₓ G]

@[to_additive add_one_zsmul]
theorem zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by
    simp only [Int.coe_nat_succ, ← zpow_coe_nat, ← pow_succ'ₓ]
  | -[1+ 0] => by
    erw [zpow_zero, zpow_neg_succ_of_nat, pow_oneₓ, mul_left_invₓ]
  | -[1+ n + 1] => by
    rw [zpow_neg_succ_of_nat, pow_succₓ, mul_inv_rev, inv_mul_cancel_right]
    rw [Int.neg_succ_of_nat_eq, neg_add, add_assocₓ, neg_add_selfₓ, add_zeroₓ]
    exact zpow_neg_succ_of_nat _ _

@[to_additive zsmul_sub_one]
theorem zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_rightₓ _ _).symm
    _ = a ^ n * a⁻¹ := by
      rw [← zpow_add_one, sub_add_cancel]
    

@[to_additive add_zsmul]
theorem zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n using Int.induction_on with n ihn n ihn
  case hz =>
    simp
  · simp only [add_assocₓ, ← zpow_add_one, ← ihn, ← mul_assoc]
    
  · rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, add_sub_assoc]
    

@[to_additive add_zsmul_self]
theorem mul_self_zpow (b : G) (m : ℤ) : b * b ^ m = b ^ (m + 1) := by
  conv_lhs => congr rw [← zpow_one b]
  rw [← zpow_add, add_commₓ]

@[to_additive add_self_zsmul]
theorem mul_zpow_self (b : G) (m : ℤ) : b ^ m * b = b ^ (m + 1) := by
  conv_lhs => congr skip rw [← zpow_one b]
  rw [← zpow_add, add_commₓ]

@[to_additive sub_zsmul]
theorem zpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  rw [sub_eq_add_neg, zpow_add, zpow_neg]

@[to_additive one_add_zsmul]
theorem zpow_one_add (a : G) (i : ℤ) : a ^ (1 + i) = a * a ^ i := by
  rw [zpow_add, zpow_one]

@[to_additive]
theorem zpow_mul_comm (a : G) (i j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i :=
  (Commute.refl _).zpow_zpow _ _

@[to_additive bit1_zsmul]
theorem zpow_bit1 (a : G) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [bit1, zpow_add, zpow_bit0, zpow_one]

end Groupₓ

/-!
### `zpow`/`zsmul` and an order

Those lemmas are placed here (rather than in `algebra.group_power.order` with their friends) because
they require facts from `data.int.basic`.
-/


section OrderedAddCommGroup

variable [OrderedCommGroup α] {m n : ℤ} {a b : α}

@[to_additive zsmul_pos]
theorem one_lt_zpow' (ha : 1 < a) {k : ℤ} (hk : (0 : ℤ) < k) : 1 < a ^ k := by
  lift k to ℕ using Int.le_of_ltₓ hk
  rw [zpow_coe_nat]
  exact one_lt_pow' ha (coe_nat_pos.mp hk).ne'

@[to_additive zsmul_strict_mono_left]
theorem zpow_strict_mono_right (ha : 1 < a) : StrictMono fun n : ℤ => a ^ n := fun m n h =>
  calc
    a ^ m = a ^ m * 1 := (mul_oneₓ _).symm
    _ < a ^ m * a ^ (n - m) := mul_lt_mul_left' (one_lt_zpow' ha <| sub_pos_of_lt h) _
    _ = a ^ n := by
      rw [← zpow_add]
      simp
    

@[to_additive zsmul_mono_left]
theorem zpow_mono_right (ha : 1 ≤ a) : Monotone fun n : ℤ => a ^ n := fun m n h =>
  calc
    a ^ m = a ^ m * 1 := (mul_oneₓ _).symm
    _ ≤ a ^ m * a ^ (n - m) := mul_le_mul_left' (one_le_zpow ha <| sub_nonneg_of_le h) _
    _ = a ^ n := by
      rw [← zpow_add]
      simp
    

@[to_additive]
theorem zpow_le_zpow (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n :=
  zpow_mono_right ha h

@[to_additive]
theorem zpow_lt_zpow (ha : 1 < a) (h : m < n) : a ^ m < a ^ n :=
  zpow_strict_mono_right ha h

@[to_additive]
theorem zpow_le_zpow_iff (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_strict_mono_right ha).le_iff_le

@[to_additive]
theorem zpow_lt_zpow_iff (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_strict_mono_right ha).lt_iff_lt

variable (α)

@[to_additive zsmul_strict_mono_right]
theorem zpow_strict_mono_left (hn : 0 < n) : StrictMono ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_lt_div', ← div_zpow]
  exact one_lt_zpow' (one_lt_div'.2 hab) hn

@[to_additive zsmul_mono_right]
theorem zpow_mono_left (hn : 0 ≤ n) : Monotone ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_le_div', ← div_zpow]
  exact one_le_zpow (one_le_div'.2 hab) hn

variable {α}

@[to_additive]
theorem zpow_le_zpow' (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n :=
  zpow_mono_left α hn h

@[to_additive]
theorem zpow_lt_zpow' (hn : 0 < n) (h : a < b) : a ^ n < b ^ n :=
  zpow_strict_mono_left α hn h

end OrderedAddCommGroup

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {n : ℤ} {a b : α}

@[to_additive]
theorem zpow_le_zpow_iff' (hn : 0 < n) {a b : α} : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_strict_mono_left α hn).le_iff_le

@[to_additive]
theorem zpow_lt_zpow_iff' (hn : 0 < n) {a b : α} : a ^ n < b ^ n ↔ a < b :=
  (zpow_strict_mono_left α hn).lt_iff_lt

@[nolint to_additive_doc,
  to_additive zsmul_right_injective
      "See also `smul_right_injective`. TODO: provide a `no_zero_smul_divisors` instance. We can't do that\nhere because importing that definition would create import cycles."]
theorem zpow_left_injective (hn : n ≠ 0) : Function.Injective ((· ^ n) : α → α) := by
  cases hn.symm.lt_or_lt
  · exact (zpow_strict_mono_left α h).Injective
    
  · refine' fun a b (hab : a ^ n = b ^ n) => (zpow_strict_mono_left α (neg_pos.mpr h)).Injective _
    rw [zpow_neg, zpow_neg, hab]
    

@[to_additive zsmul_right_inj]
theorem zpow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  (zpow_left_injective hn).eq_iff

/-- Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
@[to_additive
      "Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and\n`zsmul_lt_zsmul_iff'`."]
theorem zpow_eq_zpow_iff' (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  zpow_left_inj hn

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {a b : α}

theorem abs_nsmul (n : ℕ) (a : α) : abs (n • a) = n • abs a := by
  cases' le_totalₓ a 0 with hneg hpos
  · rw [abs_of_nonpos hneg, ← abs_neg, ← neg_nsmul, abs_of_nonneg]
    exact nsmul_nonneg (neg_nonneg.mpr hneg) n
    
  · rw [abs_of_nonneg hpos, abs_of_nonneg]
    exact nsmul_nonneg hpos n
    

theorem abs_zsmul (n : ℤ) (a : α) : abs (n • a) = abs n • abs a := by
  obtain n0 | n0 := le_totalₓ 0 n
  · lift n to ℕ using n0
    simp only [← abs_nsmul, ← coe_nat_abs, ← coe_nat_zsmul]
    
  · lift -n to ℕ using neg_nonneg.2 n0 with m h
    rw [← abs_neg (n • a), ← neg_zsmul, ← abs_neg n, ← h, coe_nat_zsmul, coe_nat_abs, coe_nat_zsmul]
    exact abs_nsmul m _
    

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
theorem abs_add_eq_add_abs_le (hle : a ≤ b) : abs (a + b) = abs a + abs b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  obtain a0 | a0 := le_or_ltₓ 0 a <;> obtain b0 | b0 := le_or_ltₓ 0 b
  · simp [← a0, ← b0, ← abs_of_nonneg, ← add_nonneg a0 b0]
    
  · exact (lt_irreflₓ (0 : α) <| a0.trans_lt <| hle.trans_lt b0).elim
    
  any_goals {
  }
  have : (abs (a + b) = -a + b ↔ b ≤ 0) ↔ (abs (a + b) = abs a + abs b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) := by
    simp [← a0, ← a0.le, ← a0.not_le, ← b0, ← abs_of_neg, ← abs_of_nonneg]
  refine'
    this.mp
      ⟨fun h => _, fun h => by
        simp only [← le_antisymmₓ h b0, ← abs_of_neg a0, ← add_zeroₓ]⟩
  obtain ab | ab := le_or_ltₓ (a + b) 0
  · refine' le_of_eqₓ (eq_zero_of_neg_eq _)
    rwa [abs_of_nonpos ab, neg_add_rev, add_commₓ, add_right_injₓ] at h
    
  · refine' (lt_irreflₓ (0 : α) _).elim
    rw [abs_of_pos ab, add_left_injₓ] at h
    rwa [eq_zero_of_neg_eq h.symm] at a0
    

theorem abs_add_eq_add_abs_iff (a b : α) : abs (a + b) = abs a + abs b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  obtain ab | ab := le_totalₓ a b
  · exact abs_add_eq_add_abs_le ab
    
  · rw [add_commₓ a, add_commₓ (abs _), abs_add_eq_add_abs_le ab, And.comm, @And.comm (b ≤ 0)]
    

end LinearOrderedAddCommGroup

@[simp]
theorem WithBot.coe_nsmul [AddMonoidₓ A] (a : A) (n : ℕ) : ((n • a : A) : WithBot A) = n • a :=
  AddMonoidHom.map_nsmul ⟨(coe : A → WithBot A), WithBot.coe_zero, WithBot.coe_add⟩ a n

theorem nsmul_eq_mul' [NonAssocSemiringₓ R] (a : R) (n : ℕ) : n • a = a * n := by
  induction' n with n ih <;> [rw [zero_nsmul, Nat.cast_zeroₓ, mul_zero],
    rw [succ_nsmul', ih, Nat.cast_succₓ, mul_addₓ, mul_oneₓ]]

@[simp]
theorem nsmul_eq_mul [NonAssocSemiringₓ R] (n : ℕ) (a : R) : n • a = n * a := by
  rw [nsmul_eq_mul', (n.cast_commute a).Eq]

/-- Note that `add_comm_monoid.nat_smul_comm_class` requires stronger assumptions on `R`. -/
instance NonUnitalNonAssocSemiringₓ.nat_smul_comm_class [NonUnitalNonAssocSemiringₓ R] : SmulCommClass ℕ R R :=
  ⟨fun n x y =>
    match n with
    | 0 => by
      simp_rw [zero_nsmul, smul_eq_mul, mul_zero]
    | n + 1 => by
      simp_rw [succ_nsmul, smul_eq_mul, mul_addₓ, ← smul_eq_mul, _match n]⟩

/-- Note that `add_comm_monoid.nat_is_scalar_tower` requires stronger assumptions on `R`. -/
instance NonUnitalNonAssocSemiringₓ.nat_is_scalar_tower [NonUnitalNonAssocSemiringₓ R] : IsScalarTower ℕ R R :=
  ⟨fun n x y =>
    match n with
    | 0 => by
      simp_rw [zero_nsmul, smul_eq_mul, zero_mul]
    | n + 1 => by
      simp_rw [succ_nsmul, ← _match n, smul_eq_mul, add_mulₓ]⟩

@[simp, norm_cast]
theorem Nat.cast_powₓ [Semiringₓ R] (n m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m := by
  induction' m with m ih
  · rw [pow_zeroₓ, pow_zeroₓ]
    exact Nat.cast_oneₓ
    
  · rw [pow_succ'ₓ, pow_succ'ₓ, Nat.cast_mulₓ, ih]
    

@[simp, norm_cast]
theorem Int.coe_nat_pow (n m : ℕ) : ((n ^ m : ℕ) : ℤ) = n ^ m := by
  induction' m with m ih <;> [exact Int.coe_nat_one, rw [pow_succ'ₓ, pow_succ'ₓ, Int.coe_nat_mul, ih]]

theorem Int.nat_abs_pow (n : ℤ) (k : ℕ) : Int.natAbs (n ^ k) = Int.natAbs n ^ k := by
  induction' k with k ih <;> [rfl, rw [pow_succ'ₓ, Int.nat_abs_mul, pow_succ'ₓ, ih]]

-- The next four lemmas allow us to replace multiplication by a numeral with a `zsmul` expression.
-- They are used by the `noncomm_ring` tactic, to normalise expressions before passing to `abel`.
theorem bit0_mul [NonUnitalNonAssocRing R] {n r : R} : bit0 n * r = (2 : ℤ) • (n * r) := by
  dsimp' [← bit0]
  rw [add_mulₓ, add_zsmul, one_zsmul]

theorem mul_bit0 [NonUnitalNonAssocRing R] {n r : R} : r * bit0 n = (2 : ℤ) • (r * n) := by
  dsimp' [← bit0]
  rw [mul_addₓ, add_zsmul, one_zsmul]

theorem bit1_mul [NonAssocRing R] {n r : R} : bit1 n * r = (2 : ℤ) • (n * r) + r := by
  dsimp' [← bit1]
  rw [add_mulₓ, bit0_mul, one_mulₓ]

theorem mul_bit1 [NonAssocRing R] {n r : R} : r * bit1 n = (2 : ℤ) • (r * n) + r := by
  dsimp' [← bit1]
  rw [mul_addₓ, mul_bit0, mul_oneₓ]

@[simp]
theorem zsmul_eq_mul [Ringₓ R] (a : R) : ∀ n : ℤ, n • a = n * a
  | (n : ℕ) => by
    rw [coe_nat_zsmul, nsmul_eq_mul, Int.cast_coe_nat]
  | -[1+ n] => by
    simp [← Nat.cast_succₓ, ← neg_add_rev, ← Int.cast_neg_succ_of_nat, ← add_mulₓ]

theorem zsmul_eq_mul' [Ringₓ R] (a : R) (n : ℤ) : n • a = a * n := by
  rw [zsmul_eq_mul, (n.cast_commute a).Eq]

/-- Note that `add_comm_group.int_smul_comm_class` requires stronger assumptions on `R`. -/
instance NonUnitalNonAssocRing.int_smul_comm_class [NonUnitalNonAssocRing R] : SmulCommClass ℤ R R :=
  ⟨fun n x y =>
    match n with
    | (n : ℕ) => by
      simp_rw [coe_nat_zsmul, smul_comm]
    | -[1+ n] => by
      simp_rw [zsmul_neg_succ_of_nat, smul_eq_mul, mul_neg, mul_smul_comm]⟩

/-- Note that `add_comm_group.int_is_scalar_tower` requires stronger assumptions on `R`. -/
instance NonUnitalNonAssocRing.int_is_scalar_tower [NonUnitalNonAssocRing R] : IsScalarTower ℤ R R :=
  ⟨fun n x y =>
    match n with
    | (n : ℕ) => by
      simp_rw [coe_nat_zsmul, smul_assoc]
    | -[1+ n] => by
      simp_rw [zsmul_neg_succ_of_nat, smul_eq_mul, neg_mul, smul_mul_assoc]⟩

theorem zsmul_int_int (a b : ℤ) : a • b = a * b := by
  simp

theorem zsmul_int_one (n : ℤ) : n • 1 = n := by
  simp

@[simp, norm_cast]
theorem Int.cast_pow [Ringₓ R] (n : ℤ) (m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m := by
  induction' m with m ih
  · rw [pow_zeroₓ, pow_zeroₓ, Int.cast_oneₓ]
    
  · rw [pow_succₓ, pow_succₓ, Int.cast_mul, ih]
    

theorem neg_one_pow_eq_pow_mod_two [Ringₓ R] {n : ℕ} : (-1 : R) ^ n = -1 ^ (n % 2) := by
  rw [← Nat.mod_add_divₓ n 2, pow_addₓ, pow_mulₓ] <;> simp [← sq]

section OrderedSemiring

variable [OrderedSemiring R] {a : R}

/-- Bernoulli's inequality. This version works for semirings but requires
additional hypotheses `0 ≤ a * a` and `0 ≤ (1 + a) * (1 + a)`. -/
theorem one_add_mul_le_pow' (Hsq : 0 ≤ a * a) (Hsq' : 0 ≤ (1 + a) * (1 + a)) (H : 0 ≤ 2 + a) :
    ∀ n : ℕ, 1 + (n : R) * a ≤ (1 + a) ^ n
  | 0 => by
    simp
  | 1 => by
    simp
  | n + 2 =>
    have : 0 ≤ (n : R) * (a * a * (2 + a)) + a * a := add_nonneg (mul_nonneg n.cast_nonneg (mul_nonneg Hsq H)) Hsq
    calc
      1 + (↑(n + 2) : R) * a ≤ 1 + ↑(n + 2) * a + (n * (a * a * (2 + a)) + a * a) := (le_add_iff_nonneg_right _).2 this
      _ = (1 + a) * (1 + a) * (1 + n * a) := by
        simp [← add_mulₓ, ← mul_addₓ, ← bit0, ← mul_assoc, ← (n.cast_commute (_ : R)).left_comm]
        ac_rfl
      _ ≤ (1 + a) * (1 + a) * (1 + a) ^ n := mul_le_mul_of_nonneg_left (one_add_mul_le_pow' n) Hsq'
      _ = (1 + a) ^ (n + 2) := by
        simp only [← pow_succₓ, ← mul_assoc]
      

private theorem pow_le_pow_of_le_one_aux (h : 0 ≤ a) (ha : a ≤ 1) (i : ℕ) : ∀ k : ℕ, a ^ (i + k) ≤ a ^ i
  | 0 => by
    simp
  | k + 1 => by
    rw [← add_assocₓ, ← one_mulₓ (a ^ i), pow_succₓ]
    exact mul_le_mul ha (pow_le_pow_of_le_one_aux _) (pow_nonneg h _) zero_le_one

theorem pow_le_pow_of_le_one (h : 0 ≤ a) (ha : a ≤ 1) {i j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i := by
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  rw [hk] <;> exact pow_le_pow_of_le_one_aux h ha _ _

theorem pow_le_of_le_one (h₀ : 0 ≤ a) (h₁ : a ≤ 1) {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_oneₓ a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zeroₓ hn))

theorem sq_le (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a :=
  pow_le_of_le_one h₀ h₁ two_ne_zero

end OrderedSemiring

section LinearOrderedSemiring

variable [LinearOrderedSemiring R]

theorem sign_cases_of_C_mul_pow_nonneg {C r : R} (h : ∀ n : ℕ, 0 ≤ C * r ^ n) : C = 0 ∨ 0 < C ∧ 0 ≤ r := by
  have : 0 ≤ C := by
    simpa only [← pow_zeroₓ, ← mul_oneₓ] using h 0
  refine' this.eq_or_lt.elim (fun h => Or.inl h.symm) fun hC => Or.inr ⟨hC, _⟩
  refine' nonneg_of_mul_nonneg_right _ hC
  simpa only [← pow_oneₓ] using h 1

end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing R] {a : R} {n : ℕ}

@[simp]
theorem abs_pow (a : R) (n : ℕ) : abs (a ^ n) = abs a ^ n :=
  (pow_abs a n).symm

@[simp]
theorem pow_bit1_neg_iff : a ^ bit1 n < 0 ↔ a < 0 :=
  ⟨fun h => not_leₓ.1 fun h' => not_leₓ.2 h <| pow_nonneg h' _, fun ha => pow_bit1_neg ha n⟩

@[simp]
theorem pow_bit1_nonneg_iff : 0 ≤ a ^ bit1 n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 pow_bit1_neg_iff

@[simp]
theorem pow_bit1_nonpos_iff : a ^ bit1 n ≤ 0 ↔ a ≤ 0 := by
  simp only [← le_iff_lt_or_eqₓ, ← pow_bit1_neg_iff, ← pow_eq_zero_iff (bit1_pos (zero_le n))]

@[simp]
theorem pow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le pow_bit1_nonpos_iff

theorem strict_mono_pow_bit1 (n : ℕ) : StrictMono fun a : R => a ^ bit1 n := by
  intro a b hab
  cases' le_totalₓ a 0 with ha ha
  · cases' le_or_ltₓ b 0 with hb hb
    · rw [← neg_lt_neg_iff, ← neg_pow_bit1, ← neg_pow_bit1]
      exact pow_lt_pow_of_lt_left (neg_lt_neg hab) (neg_nonneg.2 hb) (bit1_pos (zero_le n))
      
    · exact (pow_bit1_nonpos_iff.2 ha).trans_lt (pow_bit1_pos_iff.2 hb)
      
    
  · exact pow_lt_pow_of_lt_left hab ha (bit1_pos (zero_le n))
    

/-- Bernoulli's inequality for `n : ℕ`, `-2 ≤ a`. -/
theorem one_add_mul_le_pow (H : -2 ≤ a) (n : ℕ) : 1 + (n : R) * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow' (mul_self_nonneg _) (mul_self_nonneg _) (neg_le_iff_add_nonneg'.1 H) _

/-- Bernoulli's inequality reformulated to estimate `a^n`. -/
theorem one_add_mul_sub_le_pow (H : -1 ≤ a) (n : ℕ) : 1 + (n : R) * (a - 1) ≤ a ^ n := by
  have : -2 ≤ a - 1 := by
    rwa [bit0, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right]
  simpa only [← add_sub_cancel'_right] using one_add_mul_le_pow this n

end LinearOrderedRing

namespace Int

alias units_sq ← units_pow_two

theorem units_pow_eq_pow_mod_two (u : ℤˣ) (n : ℕ) : u ^ n = u ^ (n % 2) := by
  conv => lhs rw [← Nat.mod_add_divₓ n 2] <;> rw [pow_addₓ, pow_mulₓ, units_sq, one_pow, mul_oneₓ]

@[simp]
theorem nat_abs_sq (x : ℤ) : (x.natAbs ^ 2 : ℤ) = x ^ 2 := by
  rw [sq, Int.nat_abs_mul_self', sq]

alias nat_abs_sq ← nat_abs_pow_two

theorem abs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by
  rw [← Int.nat_abs_sq a, sq]
  norm_cast
  apply Nat.le_mul_self

alias abs_le_self_sq ← abs_le_self_pow_two

theorem le_self_sq (b : ℤ) : b ≤ b ^ 2 :=
  le_transₓ le_nat_abs (abs_le_self_sq _)

alias le_self_sq ← le_self_pow_two

theorem pow_right_injective {x : ℤ} (h : 1 < x.natAbs) : Function.Injective ((· ^ ·) x : ℕ → ℤ) := by
  suffices Function.Injective (nat_abs ∘ ((· ^ ·) x : ℕ → ℤ)) by
    exact Function.Injective.of_comp this
  convert Nat.pow_right_injective h
  ext n
  rw [Function.comp_app, nat_abs_pow]

end Int

variable (M G A)

/-- Monoid homomorphisms from `multiplicative ℕ` are defined by the image
of `multiplicative.of_add 1`. -/
def powersHom [Monoidₓ M] : M ≃ (Multiplicative ℕ →* M) where
  toFun := fun x =>
    ⟨fun n => x ^ n.toAdd, by
      convert pow_zeroₓ x
      exact to_add_one, fun m n => pow_addₓ x m n⟩
  invFun := fun f => f (Multiplicative.ofAdd 1)
  left_inv := pow_oneₓ
  right_inv := fun f =>
    MonoidHom.ext fun n => by
      simp [f.map_pow, of_add_nsmul]

/-- Monoid homomorphisms from `multiplicative ℤ` are defined by the image
of `multiplicative.of_add 1`. -/
def zpowersHom [Groupₓ G] : G ≃ (Multiplicative ℤ →* G) where
  toFun := fun x => ⟨fun n => x ^ n.toAdd, zpow_zero x, fun m n => zpow_add x m n⟩
  invFun := fun f => f (Multiplicative.ofAdd 1)
  left_inv := zpow_one
  right_inv := fun f =>
    MonoidHom.ext fun n => by
      simp [f.map_zpow, of_add_zsmul]

/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
def multiplesHom [AddMonoidₓ A] : A ≃ (ℕ →+ A) where
  toFun := fun x => ⟨fun n => n • x, zero_nsmul x, fun m n => add_nsmul _ _ _⟩
  invFun := fun f => f 1
  left_inv := one_nsmul
  right_inv := fun f => AddMonoidHom.ext_nat <| one_nsmul (f 1)

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def zmultiplesHom [AddGroupₓ A] : A ≃ (ℤ →+ A) where
  toFun := fun x => ⟨fun n => n • x, zero_zsmul x, fun m n => add_zsmul _ _ _⟩
  invFun := fun f => f 1
  left_inv := one_zsmul
  right_inv := fun f => AddMonoidHom.ext_int <| one_zsmul (f 1)

attribute [to_additive multiplesHom] powersHom

attribute [to_additive zmultiplesHom] zpowersHom

variable {M G A}

@[simp]
theorem powers_hom_apply [Monoidₓ M] (x : M) (n : Multiplicative ℕ) : powersHom M x n = x ^ n.toAdd :=
  rfl

@[simp]
theorem powers_hom_symm_apply [Monoidₓ M] (f : Multiplicative ℕ →* M) :
    (powersHom M).symm f = f (Multiplicative.ofAdd 1) :=
  rfl

@[simp]
theorem zpowers_hom_apply [Groupₓ G] (x : G) (n : Multiplicative ℤ) : zpowersHom G x n = x ^ n.toAdd :=
  rfl

@[simp]
theorem zpowers_hom_symm_apply [Groupₓ G] (f : Multiplicative ℤ →* G) :
    (zpowersHom G).symm f = f (Multiplicative.ofAdd 1) :=
  rfl

@[simp]
theorem multiples_hom_apply [AddMonoidₓ A] (x : A) (n : ℕ) : multiplesHom A x n = n • x :=
  rfl

attribute [to_additive multiples_hom_apply] powers_hom_apply

@[simp]
theorem multiples_hom_symm_apply [AddMonoidₓ A] (f : ℕ →+ A) : (multiplesHom A).symm f = f 1 :=
  rfl

attribute [to_additive multiples_hom_symm_apply] powers_hom_symm_apply

@[simp]
theorem zmultiples_hom_apply [AddGroupₓ A] (x : A) (n : ℤ) : zmultiplesHom A x n = n • x :=
  rfl

attribute [to_additive zmultiples_hom_apply] zpowers_hom_apply

@[simp]
theorem zmultiples_hom_symm_apply [AddGroupₓ A] (f : ℤ →+ A) : (zmultiplesHom A).symm f = f 1 :=
  rfl

attribute [to_additive zmultiples_hom_symm_apply] zpowers_hom_symm_apply

-- TODO use to_additive in the rest of this file
theorem MonoidHom.apply_mnat [Monoidₓ M] (f : Multiplicative ℕ →* M) (n : Multiplicative ℕ) :
    f n = f (Multiplicative.ofAdd 1) ^ n.toAdd := by
  rw [← powers_hom_symm_apply, ← powers_hom_apply, Equivₓ.apply_symm_apply]

@[ext]
theorem MonoidHom.ext_mnat [Monoidₓ M] ⦃f g : Multiplicative ℕ →* M⦄
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g :=
  MonoidHom.ext fun n => by
    rw [f.apply_mnat, g.apply_mnat, h]

theorem MonoidHom.apply_mint [Groupₓ M] (f : Multiplicative ℤ →* M) (n : Multiplicative ℤ) :
    f n = f (Multiplicative.ofAdd 1) ^ n.toAdd := by
  rw [← zpowers_hom_symm_apply, ← zpowers_hom_apply, Equivₓ.apply_symm_apply]

/-! `monoid_hom.ext_mint` is defined in `data.int.cast` -/


theorem AddMonoidHom.apply_nat [AddMonoidₓ M] (f : ℕ →+ M) (n : ℕ) : f n = n • f 1 := by
  rw [← multiples_hom_symm_apply, ← multiples_hom_apply, Equivₓ.apply_symm_apply]

/-! `add_monoid_hom.ext_nat` is defined in `data.nat.cast` -/


theorem AddMonoidHom.apply_int [AddGroupₓ M] (f : ℤ →+ M) (n : ℤ) : f n = n • f 1 := by
  rw [← zmultiples_hom_symm_apply, ← zmultiples_hom_apply, Equivₓ.apply_symm_apply]

/-! `add_monoid_hom.ext_int` is defined in `data.int.cast` -/


variable (M G A)

/-- If `M` is commutative, `powers_hom` is a multiplicative equivalence. -/
def powersMulHom [CommMonoidₓ M] : M ≃* (Multiplicative ℕ →* M) :=
  { powersHom M with
    map_mul' := fun a b =>
      MonoidHom.ext <| by
        simp [← mul_powₓ] }

/-- If `M` is commutative, `zpowers_hom` is a multiplicative equivalence. -/
def zpowersMulHom [CommGroupₓ G] : G ≃* (Multiplicative ℤ →* G) :=
  { zpowersHom G with
    map_mul' := fun a b =>
      MonoidHom.ext <| by
        simp [← mul_zpow] }

/-- If `M` is commutative, `multiples_hom` is an additive equivalence. -/
def multiplesAddHom [AddCommMonoidₓ A] : A ≃+ (ℕ →+ A) :=
  { multiplesHom A with
    map_add' := fun a b =>
      AddMonoidHom.ext <| by
        simp [← nsmul_add] }

/-- If `M` is commutative, `zmultiples_hom` is an additive equivalence. -/
def zmultiplesAddHom [AddCommGroupₓ A] : A ≃+ (ℤ →+ A) :=
  { zmultiplesHom A with
    map_add' := fun a b =>
      AddMonoidHom.ext <| by
        simp [← zsmul_add] }

variable {M G A}

@[simp]
theorem powers_mul_hom_apply [CommMonoidₓ M] (x : M) (n : Multiplicative ℕ) : powersMulHom M x n = x ^ n.toAdd :=
  rfl

@[simp]
theorem powers_mul_hom_symm_apply [CommMonoidₓ M] (f : Multiplicative ℕ →* M) :
    (powersMulHom M).symm f = f (Multiplicative.ofAdd 1) :=
  rfl

@[simp]
theorem zpowers_mul_hom_apply [CommGroupₓ G] (x : G) (n : Multiplicative ℤ) : zpowersMulHom G x n = x ^ n.toAdd :=
  rfl

@[simp]
theorem zpowers_mul_hom_symm_apply [CommGroupₓ G] (f : Multiplicative ℤ →* G) :
    (zpowersMulHom G).symm f = f (Multiplicative.ofAdd 1) :=
  rfl

@[simp]
theorem multiples_add_hom_apply [AddCommMonoidₓ A] (x : A) (n : ℕ) : multiplesAddHom A x n = n • x :=
  rfl

@[simp]
theorem multiples_add_hom_symm_apply [AddCommMonoidₓ A] (f : ℕ →+ A) : (multiplesAddHom A).symm f = f 1 :=
  rfl

@[simp]
theorem zmultiples_add_hom_apply [AddCommGroupₓ A] (x : A) (n : ℤ) : zmultiplesAddHom A x n = n • x :=
  rfl

@[simp]
theorem zmultiples_add_hom_symm_apply [AddCommGroupₓ A] (f : ℤ →+ A) : (zmultiplesAddHom A).symm f = f 1 :=
  rfl

/-!
### Commutativity (again)

Facts about `semiconj_by` and `commute` that require `zpow` or `zsmul`, or the fact that integer
multiplication equals semiring multiplication.
-/


namespace SemiconjBy

section

variable [Semiringₓ R] {a x y : R}

@[simp]
theorem cast_nat_mul_right (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a ((n : R) * x) (n * y) :=
  SemiconjBy.mul_right (Nat.commute_cast _ _) h

@[simp]
theorem cast_nat_mul_left (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy ((n : R) * a) x y :=
  SemiconjBy.mul_left (Nat.cast_commute _ _) h

@[simp]
theorem cast_nat_mul_cast_nat_mul (h : SemiconjBy a x y) (m n : ℕ) : SemiconjBy ((m : R) * a) (n * x) (n * y) :=
  (h.cast_nat_mul_left m).cast_nat_mul_right n

end

variable [Monoidₓ M] [Groupₓ G] [Ringₓ R]

@[simp, to_additive]
theorem units_zpow_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : ∀ m : ℤ, SemiconjBy a ↑(x ^ m) ↑(y ^ m)
  | (n : ℕ) => by
    simp only [← zpow_coe_nat, ← Units.coe_pow, ← h, ← pow_right]
  | -[1+ n] => by
    simp only [← zpow_neg_succ_of_nat, ← Units.coe_pow, ← units_inv_right, ← h, ← pow_right]

variable {a b x y x' y' : R}

@[simp]
theorem cast_int_mul_right (h : SemiconjBy a x y) (m : ℤ) : SemiconjBy a ((m : ℤ) * x) (m * y) :=
  SemiconjBy.mul_right (Int.commute_cast _ _) h

@[simp]
theorem cast_int_mul_left (h : SemiconjBy a x y) (m : ℤ) : SemiconjBy ((m : R) * a) x y :=
  SemiconjBy.mul_left (Int.cast_commute _ _) h

@[simp]
theorem cast_int_mul_cast_int_mul (h : SemiconjBy a x y) (m n : ℤ) : SemiconjBy ((m : R) * a) (n * x) (n * y) :=
  (h.cast_int_mul_left m).cast_int_mul_right n

end SemiconjBy

namespace Commute

section

variable [Semiringₓ R] {a b : R}

@[simp]
theorem cast_nat_mul_right (h : Commute a b) (n : ℕ) : Commute a ((n : R) * b) :=
  h.cast_nat_mul_right n

@[simp]
theorem cast_nat_mul_left (h : Commute a b) (n : ℕ) : Commute ((n : R) * a) b :=
  h.cast_nat_mul_left n

@[simp]
theorem cast_nat_mul_cast_nat_mul (h : Commute a b) (m n : ℕ) : Commute (m * a : R) (n * b : R) :=
  h.cast_nat_mul_cast_nat_mul m n

@[simp]
theorem self_cast_nat_mul (n : ℕ) : Commute a (n * a : R) :=
  (Commute.refl a).cast_nat_mul_right n

@[simp]
theorem cast_nat_mul_self (n : ℕ) : Commute ((n : R) * a) a :=
  (Commute.refl a).cast_nat_mul_left n

@[simp]
theorem self_cast_nat_mul_cast_nat_mul (m n : ℕ) : Commute (m * a : R) (n * a : R) :=
  (Commute.refl a).cast_nat_mul_cast_nat_mul m n

end

variable [Monoidₓ M] [Groupₓ G] [Ringₓ R]

@[simp, to_additive]
theorem units_zpow_right {a : M} {u : Mˣ} (h : Commute a u) (m : ℤ) : Commute a ↑(u ^ m) :=
  h.units_zpow_right m

@[simp, to_additive]
theorem units_zpow_left {u : Mˣ} {a : M} (h : Commute (↑u) a) (m : ℤ) : Commute (↑(u ^ m)) a :=
  (h.symm.units_zpow_right m).symm

variable {a b : R}

@[simp]
theorem cast_int_mul_right (h : Commute a b) (m : ℤ) : Commute a (m * b : R) :=
  h.cast_int_mul_right m

@[simp]
theorem cast_int_mul_left (h : Commute a b) (m : ℤ) : Commute ((m : R) * a) b :=
  h.cast_int_mul_left m

theorem cast_int_mul_cast_int_mul (h : Commute a b) (m n : ℤ) : Commute (m * a : R) (n * b : R) :=
  h.cast_int_mul_cast_int_mul m n

variable (a) (m n : ℤ)

@[simp]
theorem cast_int_left : Commute (m : R) a := by
  rw [← mul_oneₓ (m : R)]
  exact (one_left a).cast_int_mul_left m

@[simp]
theorem cast_int_right : Commute a m := by
  rw [← mul_oneₓ (m : R)]
  exact (one_right a).cast_int_mul_right m

@[simp]
theorem self_cast_int_mul : Commute a (n * a : R) :=
  (Commute.refl a).cast_int_mul_right n

@[simp]
theorem cast_int_mul_self : Commute ((n : R) * a) a :=
  (Commute.refl a).cast_int_mul_left n

theorem self_cast_int_mul_cast_int_mul : Commute (m * a : R) (n * a : R) :=
  (Commute.refl a).cast_int_mul_cast_int_mul m n

end Commute

section Multiplicative

open Multiplicative

@[simp]
theorem Nat.to_add_pow (a : Multiplicative ℕ) (b : ℕ) : toAdd (a ^ b) = toAdd a * b := by
  induction' b with b ih
  · erw [pow_zeroₓ, to_add_one, mul_zero]
    
  · simp [*, ← pow_succₓ, ← add_commₓ, ← Nat.mul_succ]
    

@[simp]
theorem Nat.of_add_mul (a b : ℕ) : ofAdd (a * b) = ofAdd a ^ b :=
  (Nat.to_add_pow _ _).symm

@[simp]
theorem Int.to_add_pow (a : Multiplicative ℤ) (b : ℕ) : toAdd (a ^ b) = toAdd a * b := by
  induction b <;> simp [*, ← mul_addₓ, ← pow_succₓ, ← add_commₓ]

@[simp]
theorem Int.to_add_zpow (a : Multiplicative ℤ) (b : ℤ) : toAdd (a ^ b) = toAdd a * b :=
  Int.induction_on b
    (by
      simp )
    (by
      simp (config := { contextual := true })[← zpow_add, ← mul_addₓ])
    (by
      simp (config := { contextual := true })[← zpow_add, ← mul_addₓ, ← sub_eq_add_neg, -Int.add_neg_one])

@[simp]
theorem Int.of_add_mul (a b : ℤ) : ofAdd (a * b) = ofAdd a ^ b :=
  (Int.to_add_zpow _ _).symm

end Multiplicative

namespace Units

variable [Monoidₓ M]

theorem conj_pow (u : Mˣ) (x : M) (n : ℕ) : (↑u * x * ↑u⁻¹) ^ n = u * x ^ n * ↑u⁻¹ :=
  (divp_eq_iff_mul_eq.2 ((u.mk_semiconj_by x).pow_right n).Eq.symm).symm

theorem conj_pow' (u : Mˣ) (x : M) (n : ℕ) : (↑u⁻¹ * x * u) ^ n = ↑u⁻¹ * x ^ n * u :=
  u⁻¹.conj_pow x n

end Units

namespace MulOpposite

/-- Moving to the opposite monoid commutes with taking powers. -/
@[simp]
theorem op_pow [Monoidₓ M] (x : M) (n : ℕ) : op (x ^ n) = op x ^ n :=
  rfl

@[simp]
theorem unop_pow [Monoidₓ M] (x : Mᵐᵒᵖ) (n : ℕ) : unop (x ^ n) = unop x ^ n :=
  rfl

/-- Moving to the opposite group or group_with_zero commutes with taking powers. -/
@[simp]
theorem op_zpow [DivInvMonoidₓ M] (x : M) (z : ℤ) : op (x ^ z) = op x ^ z :=
  rfl

@[simp]
theorem unop_zpow [DivInvMonoidₓ M] (x : Mᵐᵒᵖ) (z : ℤ) : unop (x ^ z) = unop x ^ z :=
  rfl

end MulOpposite

