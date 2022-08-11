/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathbin.Algebra.Order.Ring
import Mathbin.Algebra.GroupPower.Ring

/-!
# Lemmas about the interaction of power operations with order

Note that some lemmas are in `algebra/group_power/lemmas.lean` as they import files which
depend on this file.
-/


variable {A G M R : Type _}

section Preorderₓ

variable [Monoidₓ M] [Preorderₓ M] [CovariantClass M M (· * ·) (· ≤ ·)]

@[to_additive nsmul_le_nsmul_of_le_right, mono]
theorem pow_le_pow_of_le_left' [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {a b : M} (hab : a ≤ b) :
    ∀ i : ℕ, a ^ i ≤ b ^ i
  | 0 => by
    simp
  | k + 1 => by
    rw [pow_succₓ, pow_succₓ]
    exact mul_le_mul' hab (pow_le_pow_of_le_left' k)

attribute [mono] nsmul_le_nsmul_of_le_right

@[to_additive nsmul_nonneg]
theorem one_le_pow_of_one_le' {a : M} (H : 1 ≤ a) : ∀ n : ℕ, 1 ≤ a ^ n
  | 0 => by
    simp
  | k + 1 => by
    rw [pow_succₓ]
    exact one_le_mul H (one_le_pow_of_one_le' k)

@[to_additive nsmul_nonpos]
theorem pow_le_one' {a : M} (H : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 :=
  @one_le_pow_of_one_le' Mᵒᵈ _ _ _ _ H n

@[to_additive nsmul_le_nsmul]
theorem pow_le_pow' {a : M} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
  let ⟨k, hk⟩ := Nat.Le.dest h
  calc
    a ^ n ≤ a ^ n * a ^ k := le_mul_of_one_le_right' (one_le_pow_of_one_le' ha _)
    _ = a ^ m := by
      rw [← hk, pow_addₓ]
    

@[to_additive nsmul_le_nsmul_of_nonpos]
theorem pow_le_pow_of_le_one' {a : M} {n m : ℕ} (ha : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n :=
  @pow_le_pow' Mᵒᵈ _ _ _ _ _ _ ha h

@[to_additive nsmul_pos]
theorem one_lt_pow' {a : M} (ha : 1 < a) {k : ℕ} (hk : k ≠ 0) : 1 < a ^ k := by
  rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨l, rfl⟩
  clear hk
  induction' l with l IH
  · simpa using ha
    
  · rw [pow_succₓ]
    exact one_lt_mul'' ha IH
    

@[to_additive nsmul_neg]
theorem pow_lt_one' {a : M} (ha : a < 1) {k : ℕ} (hk : k ≠ 0) : a ^ k < 1 :=
  @one_lt_pow' Mᵒᵈ _ _ _ _ ha k hk

@[to_additive nsmul_lt_nsmul]
theorem pow_lt_pow' [CovariantClass M M (· * ·) (· < ·)] {a : M} {n m : ℕ} (ha : 1 < a) (h : n < m) : a ^ n < a ^ m :=
  by
  rcases Nat.Le.dest h with ⟨k, rfl⟩
  clear h
  rw [pow_addₓ, pow_succ'ₓ, mul_assoc, ← pow_succₓ]
  exact lt_mul_of_one_lt_right' _ (one_lt_pow' ha k.succ_ne_zero)

@[to_additive nsmul_strict_mono_right]
theorem pow_strict_mono_left [CovariantClass M M (· * ·) (· < ·)] {a : M} (ha : 1 < a) :
    StrictMono ((· ^ ·) a : ℕ → M) := fun m n => pow_lt_pow' ha

end Preorderₓ

section LinearOrderₓ

variable [Monoidₓ M] [LinearOrderₓ M] [CovariantClass M M (· * ·) (· ≤ ·)]

@[to_additive nsmul_nonneg_iff]
theorem one_le_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 ≤ x ^ n ↔ 1 ≤ x :=
  ⟨le_imp_le_of_lt_imp_ltₓ fun h => pow_lt_one' h hn, fun h => one_le_pow_of_one_le' h n⟩

@[to_additive]
theorem pow_le_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n ≤ 1 ↔ x ≤ 1 :=
  @one_le_pow_iff Mᵒᵈ _ _ _ _ _ hn

@[to_additive nsmul_pos_iff]
theorem one_lt_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 < x ^ n ↔ 1 < x :=
  lt_iff_lt_of_le_iff_le (pow_le_one_iff hn)

@[to_additive]
theorem pow_lt_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n < 1 ↔ x < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff hn)

@[to_additive]
theorem pow_eq_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by
  simp only [← le_antisymm_iffₓ, ← pow_le_one_iff hn, ← one_le_pow_iff hn]

variable [CovariantClass M M (· * ·) (· < ·)] {a : M} {m n : ℕ}

@[to_additive nsmul_le_nsmul_iff]
theorem pow_le_pow_iff' (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (pow_strict_mono_left ha).le_iff_le

@[to_additive nsmul_lt_nsmul_iff]
theorem pow_lt_pow_iff' (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (pow_strict_mono_left ha).lt_iff_lt

end LinearOrderₓ

section DivInvMonoidₓ

variable [DivInvMonoidₓ G] [Preorderₓ G] [CovariantClass G G (· * ·) (· ≤ ·)]

@[to_additive zsmul_nonneg]
theorem one_le_zpow {x : G} (H : 1 ≤ x) {n : ℤ} (hn : 0 ≤ n) : 1 ≤ x ^ n := by
  lift n to ℕ using hn
  rw [zpow_coe_nat]
  apply one_le_pow_of_one_le' H

end DivInvMonoidₓ

namespace CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring R]

theorem pow_pos {a : R} (H : 0 < a) (n : ℕ) : 0 < a ^ n :=
  pos_iff_ne_zero.2 <| pow_ne_zero _ H.ne'

end CanonicallyOrderedCommSemiring

section OrderedSemiring

variable [OrderedSemiring R] {a x y : R} {n m : ℕ}

theorem zero_pow_le_one : ∀ n : ℕ, (0 : R) ^ n ≤ 1
  | 0 => (pow_zeroₓ _).le
  | n + 1 => by
    rw [zero_pow n.succ_pos]
    exact zero_le_one

theorem pow_add_pow_le (hx : 0 ≤ x) (hy : 0 ≤ y) (hn : n ≠ 0) : x ^ n + y ^ n ≤ (x + y) ^ n := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
  induction' k with k ih
  · simp only [← pow_oneₓ]
    
  let n := k.succ
  have h1 := add_nonneg (mul_nonneg hx (pow_nonneg hy n)) (mul_nonneg hy (pow_nonneg hx n))
  have h2 := add_nonneg hx hy
  calc x ^ n.succ + y ^ n.succ ≤ x * x ^ n + y * y ^ n + (x * y ^ n + y * x ^ n) := by
      rw [pow_succₓ _ n, pow_succₓ _ n]
      exact le_add_of_nonneg_right h1 _ = (x + y) * (x ^ n + y ^ n) := by
      rw [add_mulₓ, mul_addₓ, mul_addₓ, add_commₓ (y * x ^ n), ← add_assocₓ, ← add_assocₓ,
        add_assocₓ (x * x ^ n) (x * y ^ n), add_commₓ (x * y ^ n) (y * y ^ n), ← add_assocₓ]_ ≤ (x + y) ^ n.succ :=
      by
      rw [pow_succₓ _ n]
      exact mul_le_mul_of_nonneg_left (ih (Nat.succ_ne_zero k)) h2

theorem pow_lt_pow_of_lt_left (Hxy : x < y) (Hxpos : 0 ≤ x) (Hnpos : 0 < n) : x ^ n < y ^ n := by
  cases lt_or_eq_of_leₓ Hxpos
  · rw [← tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ Hnpos)]
    induction n - 1
    · simpa only [← pow_oneₓ]
      
    rw [pow_addₓ, pow_addₓ, Nat.succ_eq_add_one, pow_oneₓ, pow_oneₓ]
    apply mul_lt_mul ih (le_of_ltₓ Hxy) h (le_of_ltₓ (pow_pos (lt_transₓ h Hxy) _))
    
  · rw [← h, zero_pow Hnpos]
    apply
      pow_pos
        (by
          rwa [← h] at Hxy : 0 < y)
    

theorem pow_lt_one (h₀ : 0 ≤ a) (h₁ : a < 1) {n : ℕ} (hn : n ≠ 0) : a ^ n < 1 :=
  (one_pow n).subst (pow_lt_pow_of_lt_left h₁ h₀ (Nat.pos_of_ne_zeroₓ hn))

theorem strict_mono_on_pow (hn : 0 < n) : StrictMonoOn (fun x : R => x ^ n) (Set.Ici 0) := fun x hx y hy h =>
  pow_lt_pow_of_lt_left h hx hn

theorem one_le_pow_of_one_le (H : 1 ≤ a) : ∀ n : ℕ, 1 ≤ a ^ n
  | 0 => by
    rw [pow_zeroₓ]
  | n + 1 => by
    rw [pow_succₓ]
    simpa only [← mul_oneₓ] using mul_le_mul H (one_le_pow_of_one_le n) zero_le_one (le_transₓ zero_le_one H)

theorem pow_mono (h : 1 ≤ a) : Monotone fun n : ℕ => a ^ n :=
  monotone_nat_of_le_succ fun n => by
    rw [pow_succₓ]
    exact le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans h) _) h

theorem pow_le_pow (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
  pow_mono ha h

theorem le_self_pow (ha : 1 ≤ a) (h : 1 ≤ m) : a ≤ a ^ m :=
  Eq.trans_le (pow_oneₓ a).symm (pow_le_pow ha h)

theorem strict_mono_pow (h : 1 < a) : StrictMono fun n : ℕ => a ^ n :=
  have : 0 < a := zero_le_one.trans_lt h
  strict_mono_nat_of_lt_succ fun n => by
    simpa only [← one_mulₓ, ← pow_succₓ] using mul_lt_mul h (le_reflₓ (a ^ n)) (pow_pos this _) this.le

theorem pow_lt_pow (h : 1 < a) (h2 : n < m) : a ^ n < a ^ m :=
  strict_mono_pow h h2

theorem pow_lt_pow_iff (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
  (strict_mono_pow h).lt_iff_lt

theorem pow_le_pow_iff (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m :=
  (strict_mono_pow h).le_iff_le

theorem strict_anti_pow (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti fun n : ℕ => a ^ n :=
  strict_anti_nat_of_succ_lt fun n => by
    simpa only [← pow_succₓ, ← one_mulₓ] using mul_lt_mul h₁ le_rfl (pow_pos h₀ n) zero_le_one

theorem pow_lt_pow_iff_of_lt_one (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m :=
  (strict_anti_pow h₀ h₁).lt_iff_lt

theorem pow_lt_pow_of_lt_one (h : 0 < a) (ha : a < 1) {i j : ℕ} (hij : i < j) : a ^ j < a ^ i :=
  (pow_lt_pow_iff_of_lt_one h ha).2 hij

@[mono]
theorem pow_le_pow_of_le_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ i : ℕ, a ^ i ≤ b ^ i
  | 0 => by
    simp
  | k + 1 => by
    rw [pow_succₓ, pow_succₓ]
    exact mul_le_mul hab (pow_le_pow_of_le_left _) (pow_nonneg ha _) (le_transₓ ha hab)

theorem one_lt_pow (ha : 1 < a) {n : ℕ} (hn : n ≠ 0) : 1 < a ^ n :=
  pow_zeroₓ a ▸ pow_lt_pow ha (pos_iff_ne_zero.2 hn)

theorem pow_le_one : ∀ (n : ℕ) (h₀ : 0 ≤ a) (h₁ : a ≤ 1), a ^ n ≤ 1
  | 0, h₀, h₁ => (pow_zeroₓ a).le
  | n + 1, h₀, h₁ => (pow_succ'ₓ a n).le.trans (mul_le_one (pow_le_one n h₀ h₁) h₀ h₁)

theorem sq_pos_of_pos (ha : 0 < a) : 0 < a ^ 2 := by
  rw [sq]
  exact mul_pos ha ha

end OrderedSemiring

section OrderedRing

variable [OrderedRing R] {a : R}

theorem sq_pos_of_neg (ha : a < 0) : 0 < a ^ 2 := by
  rw [sq]
  exact mul_pos_of_neg_of_neg ha ha

theorem pow_bit0_pos_of_neg (ha : a < 0) (n : ℕ) : 0 < a ^ bit0 n := by
  rw [pow_bit0']
  exact pow_pos (mul_pos_of_neg_of_neg ha ha) _

theorem pow_bit1_neg (ha : a < 0) (n : ℕ) : a ^ bit1 n < 0 := by
  rw [bit1, pow_succₓ]
  exact mul_neg_of_neg_of_pos ha (pow_bit0_pos_of_neg ha n)

end OrderedRing

section LinearOrderedSemiring

variable [LinearOrderedSemiring R] {a b : R}

theorem pow_le_one_iff_of_nonneg {a : R} (ha : 0 ≤ a) {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 := by
  refine' ⟨_, pow_le_one n ha⟩
  rw [← not_ltₓ, ← not_ltₓ]
  exact mt fun h => one_lt_pow h hn

theorem one_le_pow_iff_of_nonneg {a : R} (ha : 0 ≤ a) {n : ℕ} (hn : n ≠ 0) : 1 ≤ a ^ n ↔ 1 ≤ a := by
  refine' ⟨_, fun h => one_le_pow_of_one_le h n⟩
  rw [← not_ltₓ, ← not_ltₓ]
  exact mt fun h => pow_lt_one ha h hn

theorem one_lt_pow_iff_of_nonneg {a : R} (ha : 0 ≤ a) {n : ℕ} (hn : n ≠ 0) : 1 < a ^ n ↔ 1 < a :=
  lt_iff_lt_of_le_iff_le (pow_le_one_iff_of_nonneg ha hn)

theorem pow_lt_one_iff_of_nonneg {a : R} (ha : 0 ≤ a) {n : ℕ} (hn : n ≠ 0) : a ^ n < 1 ↔ a < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)

theorem sq_le_one_iff {a : R} (ha : 0 ≤ a) : a ^ 2 ≤ 1 ↔ a ≤ 1 :=
  pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

theorem sq_lt_one_iff {a : R} (ha : 0 ≤ a) : a ^ 2 < 1 ↔ a < 1 :=
  pow_lt_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

theorem one_le_sq_iff {a : R} (ha : 0 ≤ a) : 1 ≤ a ^ 2 ↔ 1 ≤ a :=
  one_le_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

theorem one_lt_sq_iff {a : R} (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a :=
  one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

@[simp]
theorem pow_left_inj {x y : R} {n : ℕ} (Hxpos : 0 ≤ x) (Hypos : 0 ≤ y) (Hnpos : 0 < n) : x ^ n = y ^ n ↔ x = y :=
  (@strict_mono_on_pow R _ _ Hnpos).InjOn.eq_iff Hxpos Hypos

theorem lt_of_pow_lt_pow {a b : R} (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
  lt_of_not_geₓ fun hn => not_lt_of_geₓ (pow_le_pow_of_le_left hb hn _) h

theorem le_of_pow_le_pow {a b : R} (n : ℕ) (hb : 0 ≤ b) (hn : 0 < n) (h : a ^ n ≤ b ^ n) : a ≤ b :=
  le_of_not_ltₓ fun h1 => not_le_of_lt (pow_lt_pow_of_lt_left h1 hb hn) h

@[simp]
theorem sq_eq_sq {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b :=
  pow_left_inj ha hb
    (by
      decide)

theorem lt_of_mul_self_lt_mul_self (hb : 0 ≤ b) : a * a < b * b → a < b := by
  simp_rw [← sq]
  exact lt_of_pow_lt_pow _ hb

end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing R]

theorem pow_abs (a : R) (n : ℕ) : abs a ^ n = abs (a ^ n) :=
  ((absHom.toMonoidHom : R →* R).map_pow a n).symm

theorem abs_neg_one_pow (n : ℕ) : abs ((-1 : R) ^ n) = 1 := by
  rw [← pow_abs, abs_neg, abs_one, one_pow]

theorem pow_bit0_nonneg (a : R) (n : ℕ) : 0 ≤ a ^ bit0 n := by
  rw [pow_bit0]
  exact mul_self_nonneg _

theorem sq_nonneg (a : R) : 0 ≤ a ^ 2 :=
  pow_bit0_nonneg a 1

alias sq_nonneg ← pow_two_nonneg

theorem pow_bit0_pos {a : R} (h : a ≠ 0) (n : ℕ) : 0 < a ^ bit0 n :=
  (pow_bit0_nonneg a n).lt_of_ne (pow_ne_zero _ h).symm

theorem sq_pos_of_ne_zero (a : R) (h : a ≠ 0) : 0 < a ^ 2 :=
  pow_bit0_pos h 1

alias sq_pos_of_ne_zero ← pow_two_pos_of_ne_zero

theorem pow_bit0_pos_iff (a : R) {n : ℕ} (hn : n ≠ 0) : 0 < a ^ bit0 n ↔ a ≠ 0 := by
  refine' ⟨fun h => _, fun h => pow_bit0_pos h n⟩
  rintro rfl
  rw [zero_pow (Nat.zero_lt_bit0 hn)] at h
  exact lt_irreflₓ _ h

theorem sq_pos_iff (a : R) : 0 < a ^ 2 ↔ a ≠ 0 :=
  pow_bit0_pos_iff a one_ne_zero

variable {x y : R}

theorem sq_abs (x : R) : abs x ^ 2 = x ^ 2 := by
  simpa only [← sq] using abs_mul_abs_self x

theorem abs_sq (x : R) : abs (x ^ 2) = x ^ 2 := by
  simpa only [← sq] using abs_mul_self x

theorem sq_lt_sq : x ^ 2 < y ^ 2 ↔ abs x < abs y := by
  simpa only [← sq_abs] using (@strict_mono_on_pow R _ _ two_pos).lt_iff_lt (abs_nonneg x) (abs_nonneg y)

theorem sq_lt_sq' (h1 : -y < x) (h2 : x < y) : x ^ 2 < y ^ 2 :=
  sq_lt_sq.2 (lt_of_lt_of_leₓ (abs_lt.2 ⟨h1, h2⟩) (le_abs_self _))

theorem sq_le_sq : x ^ 2 ≤ y ^ 2 ↔ abs x ≤ abs y := by
  simpa only [← sq_abs] using (@strict_mono_on_pow R _ _ two_pos).le_iff_le (abs_nonneg x) (abs_nonneg y)

theorem sq_le_sq' (h1 : -y ≤ x) (h2 : x ≤ y) : x ^ 2 ≤ y ^ 2 :=
  sq_le_sq.2 (le_transₓ (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))

theorem abs_lt_of_sq_lt_sq (h : x ^ 2 < y ^ 2) (hy : 0 ≤ y) : abs x < y := by
  rwa [← abs_of_nonneg hy, ← sq_lt_sq]

theorem abs_lt_of_sq_lt_sq' (h : x ^ 2 < y ^ 2) (hy : 0 ≤ y) : -y < x ∧ x < y :=
  abs_lt.mp <| abs_lt_of_sq_lt_sq h hy

theorem abs_le_of_sq_le_sq (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : abs x ≤ y := by
  rwa [← abs_of_nonneg hy, ← sq_le_sq]

theorem abs_le_of_sq_le_sq' (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y :=
  abs_le.mp <| abs_le_of_sq_le_sq h hy

theorem sq_eq_sq_iff_abs_eq_abs (x y : R) : x ^ 2 = y ^ 2 ↔ abs x = abs y := by
  simp only [← le_antisymm_iffₓ, ← sq_le_sq]

@[simp]
theorem sq_le_one_iff_abs_le_one (x : R) : x ^ 2 ≤ 1 ↔ abs x ≤ 1 := by
  simpa only [← one_pow, ← abs_one] using @sq_le_sq _ _ x 1

@[simp]
theorem sq_lt_one_iff_abs_lt_one (x : R) : x ^ 2 < 1 ↔ abs x < 1 := by
  simpa only [← one_pow, ← abs_one] using @sq_lt_sq _ _ x 1

@[simp]
theorem one_le_sq_iff_one_le_abs (x : R) : 1 ≤ x ^ 2 ↔ 1 ≤ abs x := by
  simpa only [← one_pow, ← abs_one] using @sq_le_sq _ _ 1 x

@[simp]
theorem one_lt_sq_iff_one_lt_abs (x : R) : 1 < x ^ 2 ↔ 1 < abs x := by
  simpa only [← one_pow, ← abs_one] using @sq_lt_sq _ _ 1 x

theorem pow_four_le_pow_two_of_pow_two_le {x y : R} (h : x ^ 2 ≤ y) : x ^ 4 ≤ y ^ 2 :=
  (pow_mulₓ x 2 2).symm ▸ pow_le_pow_of_le_left (sq_nonneg x) h 2

end LinearOrderedRing

section LinearOrderedCommRing

variable [LinearOrderedCommRing R]

/-- Arithmetic mean-geometric mean (AM-GM) inequality for linearly ordered commutative rings. -/
theorem two_mul_le_add_sq (a b : R) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
  sub_nonneg.mp ((sub_add_eq_add_sub _ _ _).subst ((sub_sq a b).subst (sq_nonneg _)))

alias two_mul_le_add_sq ← two_mul_le_add_pow_two

end LinearOrderedCommRing

