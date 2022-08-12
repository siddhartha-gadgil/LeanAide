/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Algebra.Ring.Basic
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.FieldPower
import Mathbin.Algebra.Opposites

/-!  # Squares, even and odd elements

This file proves some general facts about squares, even and odd elements of semirings.

In the implementation, we define `is_square` and we let `even` be the notion transported by
`to_additive`.  The definition are therefore as follows:
```lean
is_square a ↔ ∃ r, a = r * r
even a ↔ ∃ r, a = r + r
```

Odd elements are not unified with a multiplicative notion.

## Future work

* TODO: Try to generalize further the typeclass assumptions on `is_square/even`.
  For instance, in some cases, there are `semiring` assumptions that I (DT) am not convinced are
  necessary.
* TODO: Consider moving the definition and lemmas about `odd` to a separate file.
* TODO: The "old" definition of `even a` asked for the existence of an element `c` such that
  `a = 2 * c`.  For this reason, several fixes introduce an extra `two_mul` or `← two_mul`.
  It might be the case that by making a careful choice of `simp` lemma, this can be avoided.
 -/


open MulOpposite

variable {F α β R : Type _}

section Mul

variable [Mul α]

/-- An element `a` of a type `α` with multiplication satisfies `square a` if `a = r * r`,
for some `r : α`. -/
@[to_additive "An element `a` of a type `α` with addition satisfies `even a` if `a = r + r`,\nfor some `r : α`."]
def IsSquare (a : α) : Prop :=
  ∃ r, a = r * r

@[simp, to_additive]
theorem is_square_mul_self (m : α) : IsSquare (m * m) :=
  ⟨m, rfl⟩

@[to_additive]
theorem is_square_op_iff (a : α) : IsSquare (op a) ↔ IsSquare a :=
  ⟨fun ⟨c, hc⟩ =>
    ⟨unop c, by
      rw [← unop_mul, ← hc, unop_op]⟩,
    fun ⟨c, hc⟩ => by
    simp [← hc]⟩

/-- Create a decidability instance for `is_square` on `fintype`s. -/
instance isSquareDecidable [Fintype α] [DecidableEq α] : DecidablePred (IsSquare : α → Prop) := fun a =>
  Fintype.decidableExistsFintype

end Mul

@[simp, to_additive]
theorem is_square_one [MulOneClassₓ α] : IsSquare (1 : α) :=
  ⟨1, (mul_oneₓ _).symm⟩

@[to_additive]
theorem IsSquare.map [MulOneClassₓ α] [MulOneClassₓ β] [MonoidHomClass F α β] {m : α} (f : F) :
    IsSquare m → IsSquare (f m) := by
  rintro ⟨m, rfl⟩
  exact
    ⟨f m, by
      simp ⟩

section Monoidₓ

variable [Monoidₓ α]

@[to_additive even_iff_exists_two_nsmul]
theorem is_square_iff_exists_sq (m : α) : IsSquare m ↔ ∃ c, m = c ^ 2 := by
  simp [← IsSquare, ← pow_two]

alias is_square_iff_exists_sq ↔ IsSquare.exists_sq is_square_of_exists_sq

attribute [to_additive Even.exists_two_nsmul "Alias of the forwards direction of\n`even_iff_exists_two_nsmul`."]
  IsSquare.exists_sq

attribute [to_additive even_of_exists_two_nsmul "Alias of the backwards direction of\n`even_iff_exists_two_nsmul`."]
  is_square_of_exists_sq

@[simp, to_additive even_two_nsmul]
theorem is_square_sq (a : α) : IsSquare (a ^ 2) :=
  ⟨a, pow_two _⟩

variable [HasDistribNeg α] {n : ℕ}

theorem Even.neg_pow : Even n → ∀ a : α, -a ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  simp_rw [← two_mul, pow_mulₓ, neg_sq]

theorem Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1 := by
  rw [h.neg_pow, one_pow]

end Monoidₓ

/-- `0` is always a square (in a monoid with zero). -/
theorem is_square_zero (M : Type _) [MonoidWithZeroₓ M] : IsSquare (0 : M) := by
  use 0
  simp only [← mul_zero]

@[to_additive]
theorem IsSquare.mul [CommSemigroupₓ α] {a b : α} : IsSquare a → IsSquare b → IsSquare (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  exact ⟨a * b, mul_mul_mul_commₓ _ _ _ _⟩

section DivisionMonoid

variable [DivisionMonoid α] {a : α}

@[simp, to_additive]
theorem is_square_inv : IsSquare a⁻¹ ↔ IsSquare a := by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← is_square_op_iff, ← inv_invₓ a]
    exact h.map (MulEquiv.inv' α)
    
  · exact ((is_square_op_iff a).mpr h).map (MulEquiv.inv' α).symm
    

alias is_square_inv ↔ _ IsSquare.inv

attribute [to_additive] IsSquare.inv

variable [HasDistribNeg α] {n : ℤ}

theorem Even.neg_zpow : Even n → ∀ a : α, -a ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  exact zpow_bit0_neg _ _

theorem Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by
  rw [h.neg_zpow, one_zpow]

end DivisionMonoid

theorem even_abs [SubtractionMonoid α] [LinearOrderₓ α] {a : α} : Even (abs a) ↔ Even a := by
  cases abs_choice a <;> simp only [← h, ← even_neg]

@[to_additive]
theorem IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b) : IsSquare (a / b) := by
  rw [div_eq_mul_inv]
  exact ha.mul hb.inv

-- `odd.tsub` requires `canonically_linear_ordered_semiring`, which we don't have
theorem Even.tsub [CanonicallyLinearOrderedAddMonoid α] [Sub α] [HasOrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] {m n : α} (hm : Even m) (hn : Even n) : Even (m - n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine' ⟨a - b, _⟩
  obtain h | h := le_totalₓ a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zeroₓ]
    
  · exact (tsub_add_tsub_comm h h).symm
    

theorem even_iff_exists_bit0 [Add α] {a : α} : Even a ↔ ∃ b, a = bit0 b :=
  Iff.rfl

alias even_iff_exists_bit0 ↔ Even.exists_bit0 _

section Semiringₓ

variable [Semiringₓ α] [Semiringₓ β] {m n : α}

theorem even_iff_exists_two_mul (m : α) : Even m ↔ ∃ c, m = 2 * c := by
  simp [← even_iff_exists_two_nsmul]

theorem even_iff_two_dvd {a : α} : Even a ↔ 2 ∣ a := by
  simp [← Even, ← Dvd.Dvd, ← two_mul]

@[simp]
theorem range_two_mul (α : Type _) [Semiringₓ α] : (Set.Range fun x : α => 2 * x) = { a | Even a } := by
  ext x
  simp [← eq_comm, ← two_mul, ← Even]

@[simp]
theorem even_bit0 (a : α) : Even (bit0 a) :=
  ⟨a, rfl⟩

@[simp]
theorem even_two : Even (2 : α) :=
  ⟨1, rfl⟩

@[simp]
theorem Even.mul_left (hm : Even m) (n) : Even (n * m) :=
  hm.map (AddMonoidHom.mulLeft n)

@[simp]
theorem Even.mul_right (hm : Even m) (n) : Even (m * n) :=
  hm.map (AddMonoidHom.mulRight n)

theorem even_two_mul (m : α) : Even (2 * m) :=
  ⟨m, two_mul _⟩

theorem Even.pow_of_ne_zero (hm : Even m) : ∀ {a : ℕ}, a ≠ 0 → Even (m ^ a)
  | 0, a0 => (a0 rfl).elim
  | a + 1, _ => by
    rw [pow_succₓ]
    exact hm.mul_right _

section WithOdd

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def Odd (a : α) : Prop :=
  ∃ k, a = 2 * k + 1

theorem odd_iff_exists_bit1 {a : α} : Odd a ↔ ∃ b, a = bit1 b :=
  exists_congr fun b => by
    rw [two_mul]
    rfl

alias odd_iff_exists_bit1 ↔ Odd.exists_bit1 _

@[simp]
theorem odd_bit1 (a : α) : Odd (bit1 a) :=
  odd_iff_exists_bit1.2 ⟨a, rfl⟩

@[simp]
theorem range_two_mul_add_one (α : Type _) [Semiringₓ α] : (Set.Range fun x : α => 2 * x + 1) = { a | Odd a } := by
  ext x
  simp [← Odd, ← eq_comm]

theorem Even.add_odd : Even m → Odd n → Odd (m + n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  exact
    ⟨m + n, by
      rw [mul_addₓ, ← two_mul, add_assocₓ]⟩

theorem Odd.add_even (hm : Odd m) (hn : Even n) : Odd (m + n) := by
  rw [add_commₓ]
  exact hn.add_odd hm

theorem Odd.add_odd : Odd m → Odd n → Even (m + n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  refine' ⟨n + m + 1, _⟩
  rw [← two_mul, ← add_assocₓ, add_commₓ _ (2 * n), ← add_assocₓ, ← mul_addₓ, add_assocₓ, mul_addₓ _ (n + m), mul_oneₓ]
  rfl

@[simp]
theorem odd_one : Odd (1 : α) :=
  ⟨0, (zero_addₓ _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩

@[simp]
theorem odd_two_mul_add_one (m : α) : Odd (2 * m + 1) :=
  ⟨m, rfl⟩

theorem Odd.map [RingHomClass F α β] (f : F) : Odd m → Odd (f m) := by
  rintro ⟨m, rfl⟩
  exact
    ⟨f m, by
      simp [← two_mul]⟩

@[simp]
theorem Odd.mul : Odd m → Odd n → Odd (m * n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  refine' ⟨2 * m * n + n + m, _⟩
  rw [mul_addₓ, add_mulₓ, mul_oneₓ, ← add_assocₓ, one_mulₓ, mul_assoc, ← mul_addₓ, ← mul_addₓ, ← mul_assoc, ←
    Nat.cast_two, ← Nat.cast_comm]

theorem Odd.pow (hm : Odd m) : ∀ {a : ℕ}, Odd (m ^ a)
  | 0 => by
    rw [pow_zeroₓ]
    exact odd_one
  | a + 1 => by
    rw [pow_succₓ]
    exact hm.mul Odd.pow

end WithOdd

end Semiringₓ

section Monoidₓ

variable [Monoidₓ α] [HasDistribNeg α] {a : α} {n : ℕ}

theorem Odd.neg_pow : Odd n → ∀ a : α, -a ^ n = -(a ^ n) := by
  rintro ⟨c, rfl⟩ a
  simp_rw [pow_addₓ, pow_mulₓ, neg_sq, pow_oneₓ, mul_neg]

theorem Odd.neg_one_pow (h : Odd n) : (-1 : α) ^ n = -1 := by
  rw [h.neg_pow, one_pow]

end Monoidₓ

section CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring α]

-- this holds more generally in a `canonically_ordered_add_monoid` if we refactor `odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
theorem Odd.pos [Nontrivial α] {n : α} (hn : Odd n) : 0 < n := by
  obtain ⟨k, rfl⟩ := hn
  rw [pos_iff_ne_zero, Ne.def, add_eq_zero_iff, not_and']
  exact fun h => (one_ne_zero h).elim

end CanonicallyOrderedCommSemiring

section Ringₓ

variable [Ringₓ α] {a b : α} {n : ℕ}

@[simp]
theorem even_neg_two : Even (-2 : α) := by
  simp only [← even_neg, ← even_two]

theorem Odd.neg (hp : Odd a) : Odd (-a) := by
  obtain ⟨k, hk⟩ := hp
  use -(k + 1)
  rw [mul_neg, mul_addₓ, neg_add, add_assocₓ, two_mul (1 : α), neg_add, neg_add_cancel_right, ← neg_add, hk]

@[simp]
theorem odd_neg : Odd (-a) ↔ Odd a :=
  ⟨fun h => neg_negₓ a ▸ h.neg, Odd.neg⟩

@[simp]
theorem odd_neg_one : Odd (-1 : α) := by
  simp

theorem Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add_even hb.neg

theorem Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add_odd hb.neg

theorem Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add_odd hb.neg

theorem odd_abs [LinearOrderₓ α] : Odd (abs a) ↔ Odd a := by
  cases' abs_choice a with h h <;> simp only [← h, ← odd_neg]

end Ringₓ

section Powers

variable [LinearOrderedRing R] {a : R} {n : ℕ}

theorem Even.pow_nonneg (hn : Even n) (a : R) : 0 ≤ a ^ n := by
  cases' hn with k hk <;> simpa only [← hk, ← two_mul] using pow_bit0_nonneg a k

theorem Even.pow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n := by
  cases' hn with k hk <;> simpa only [← hk, ← two_mul] using pow_bit0_pos ha k

theorem Odd.pow_nonpos (hn : Odd n) (ha : a ≤ 0) : a ^ n ≤ 0 := by
  cases' hn with k hk <;> simpa only [← hk, ← two_mul] using pow_bit1_nonpos_iff.mpr ha

theorem Odd.pow_neg (hn : Odd n) (ha : a < 0) : a ^ n < 0 := by
  cases' hn with k hk <;> simpa only [← hk, ← two_mul] using pow_bit1_neg_iff.mpr ha

theorem Odd.pow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  ⟨fun h => le_of_not_ltₓ fun ha => h.not_lt <| hn.pow_neg ha, fun ha => pow_nonneg ha n⟩

theorem Odd.pow_nonpos_iff (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 :=
  ⟨fun h => le_of_not_ltₓ fun ha => h.not_lt <| pow_pos ha _, hn.pow_nonpos⟩

theorem Odd.pow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a :=
  ⟨fun h => lt_of_not_le fun ha => h.not_le <| hn.pow_nonpos ha, fun ha => pow_pos ha n⟩

theorem Odd.pow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 :=
  ⟨fun h => lt_of_not_le fun ha => h.not_le <| pow_nonneg ha _, hn.pow_neg⟩

theorem Even.pow_pos_iff (hn : Even n) (h₀ : 0 < n) : 0 < a ^ n ↔ a ≠ 0 :=
  ⟨fun h ha => by
    rw [ha, zero_pow h₀] at h
    exact lt_irreflₓ 0 h, hn.pow_pos⟩

theorem Even.pow_abs {p : ℕ} (hp : Even p) (a : R) : abs a ^ p = a ^ p := by
  rw [← abs_pow, abs_eq_self]
  exact hp.pow_nonneg _

@[simp]
theorem pow_bit0_abs (a : R) (p : ℕ) : abs a ^ bit0 p = a ^ bit0 p :=
  (even_bit0 _).pow_abs _

theorem Odd.strict_mono_pow (hn : Odd n) : StrictMono fun a : R => a ^ n := by
  cases' hn with k hk <;> simpa only [← hk, ← two_mul] using strict_mono_pow_bit1 _

end Powers

/-- The cardinality of `fin (bit0 k)` is even, `fact` version.
This `fact` is needed as an instance by `matrix.special_linear_group.has_neg`. -/
theorem Fintype.card_fin_even {k : ℕ} : Fact (Even (Fintype.card (Finₓ (bit0 k)))) :=
  ⟨by
    rw [Fintype.card_fin]
    exact even_bit0 k⟩

section FieldPower

variable {K : Type _}

section DivisionRing

variable [DivisionRing K] {n : ℤ}

theorem Odd.neg_zpow (h : Odd n) (a : K) : -a ^ n = -(a ^ n) := by
  obtain ⟨k, rfl⟩ := h.exists_bit1
  exact zpow_bit1_neg _ _

theorem Odd.neg_one_zpow (h : Odd n) : (-1 : K) ^ n = -1 := by
  rw [h.neg_zpow, one_zpow]

end DivisionRing

variable [LinearOrderedField K] {n : ℤ} {a : K}

protected theorem Even.zpow_nonneg (hn : Even n) (a : K) : 0 ≤ a ^ n := by
  cases' le_or_ltₓ 0 a with h h
  · exact zpow_nonneg h _
    
  · exact (hn.neg_zpow a).subst (zpow_nonneg (neg_nonneg_of_nonpos h.le) _)
    

theorem Even.zpow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n := by
  cases' hn with k hk <;> simpa only [← hk, ← two_mul] using zpow_bit0_pos ha k

protected theorem Odd.zpow_nonneg (hn : Odd n) (ha : 0 ≤ a) : 0 ≤ a ^ n := by
  cases' hn with k hk <;> simpa only [← hk, ← two_mul] using zpow_bit1_nonneg_iff.mpr ha

theorem Odd.zpow_pos (hn : Odd n) (ha : 0 < a) : 0 < a ^ n := by
  cases' hn with k hk <;> simpa only [← hk, ← two_mul] using zpow_bit1_pos_iff.mpr ha

theorem Odd.zpow_nonpos (hn : Odd n) (ha : a ≤ 0) : a ^ n ≤ 0 := by
  cases' hn with k hk <;> simpa only [← hk, ← two_mul] using zpow_bit1_nonpos_iff.mpr ha

theorem Odd.zpow_neg (hn : Odd n) (ha : a < 0) : a ^ n < 0 := by
  cases' hn with k hk <;> simpa only [← hk, ← two_mul] using zpow_bit1_neg_iff.mpr ha

theorem Even.zpow_abs {p : ℤ} (hp : Even p) (a : K) : abs a ^ p = a ^ p := by
  cases' abs_choice a with h h <;> simp only [← h, ← hp.neg_zpow _]

@[simp]
theorem zpow_bit0_abs (a : K) (p : ℤ) : abs a ^ bit0 p = a ^ bit0 p :=
  (even_bit0 _).zpow_abs _

theorem Even.abs_zpow {p : ℤ} (hp : Even p) (a : K) : abs (a ^ p) = a ^ p := by
  rw [abs_eq_self]
  exact hp.zpow_nonneg _

@[simp]
theorem abs_zpow_bit0 (a : K) (p : ℤ) : abs (a ^ bit0 p) = a ^ bit0 p :=
  (even_bit0 _).abs_zpow _

end FieldPower

