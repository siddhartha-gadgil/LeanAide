/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes, Floris van Doorn, Yaël Dillies
-/
import Mathbin.Data.Nat.Basic
import Mathbin.Data.Nat.Pow

/-!
# Factorial and variants

This file defines the factorial, along with the ascending and descending variants.

## Main declarations

* `nat.factorial`: The factorial.
* `nat.asc_factorial`: The ascending factorial. Note that it runs from `n + 1` to `n + k`
  and *not* from `n` to `n + k - 1`. We might want to change that in the future.
* `nat.desc_factorial`: The descending factorial. It runs from `n - k` to `n`.
-/


namespace Nat

/-- `nat.factorial n` is the factorial of `n`. -/
@[simp]
def factorial : ℕ → ℕ
  | 0 => 1
  | succ n => succ n * factorial n

-- mathport name: «expr !»
localized [Nat] notation:10000 n "!" => Nat.factorial n

section Factorial

variable {m n : ℕ}

@[simp]
theorem factorial_zero : 0! = 1 :=
  rfl

@[simp]
theorem factorial_succ (n : ℕ) : n.succ ! = (n + 1) * n ! :=
  rfl

@[simp]
theorem factorial_one : 1! = 1 :=
  rfl

@[simp]
theorem factorial_two : 2! = 2 :=
  rfl

theorem mul_factorial_pred (hn : 0 < n) : n * (n - 1)! = n ! :=
  tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ hn) ▸ rfl

theorem factorial_pos : ∀ n, 0 < n !
  | 0 => zero_lt_one
  | succ n => mul_pos (succ_posₓ _) (factorial_pos n)

theorem factorial_ne_zero (n : ℕ) : n ! ≠ 0 :=
  ne_of_gtₓ (factorial_pos _)

theorem factorial_dvd_factorial {m n} (h : m ≤ n) : m ! ∣ n ! := by
  induction' n with n IH
  · simp [← Nat.eq_zero_of_le_zeroₓ h]
    
  obtain rfl | hl := h.eq_or_lt
  · simp
    
  exact (IH (le_of_lt_succ hl)).mul_left _

theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ n !
  | succ m, n, _, h => dvd_of_mul_right_dvd (factorial_dvd_factorial h)

@[mono]
theorem factorial_le {m n} (h : m ≤ n) : m ! ≤ n ! :=
  le_of_dvdₓ (factorial_pos _) (factorial_dvd_factorial h)

theorem factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, m ! * m.succ ^ n ≤ (m + n)!
  | m, 0 => by
    simp
  | m, n + 1 => by
    rw [← add_assocₓ, Nat.factorial_succ, mul_comm (Nat.succ _), pow_succ'ₓ, ← mul_assoc] <;>
      exact
        mul_le_mul factorial_mul_pow_le_factorial (Nat.succ_le_succₓ (Nat.le_add_rightₓ _ _)) (Nat.zero_leₓ _)
          (Nat.zero_leₓ _)

theorem monotone_factorial : Monotone factorial := fun n m => factorial_le

theorem factorial_lt (hn : 0 < n) : n ! < m ! ↔ n < m := by
  refine' ⟨fun h => not_le.mp fun hmn => not_le_of_lt h (factorial_le hmn), fun h => _⟩
  have : ∀ {n}, 0 < n → n ! < n.succ ! := by
    intro k hk
    rw [factorial_succ, succ_mul, lt_add_iff_pos_left]
    exact mul_pos hk k.factorial_pos
  induction' h with k hnk ih generalizing hn
  · exact this hn
    
  · exact (ih hn).trans (this <| hn.trans <| lt_of_succ_le hnk)
    

theorem one_lt_factorial : 1 < n ! ↔ 1 < n :=
  factorial_lt one_posₓ

theorem factorial_eq_one : n ! = 1 ↔ n ≤ 1 := by
  refine'
    ⟨fun h => _, by
      rintro (_ | ⟨_, _ | _⟩) <;> rfl⟩
  rw [← not_ltₓ, ← one_lt_factorial, h]
  apply lt_irreflₓ

theorem factorial_inj (hn : 1 < n !) : n ! = m ! ↔ n = m := by
  refine' ⟨fun h => _, congr_arg _⟩
  obtain hnm | rfl | hnm := lt_trichotomyₓ n m
  · rw [← factorial_lt <| pos_of_gt <| one_lt_factorial.mp hn, h] at hnm
    cases lt_irreflₓ _ hnm
    
  · rfl
    
  rw [h, one_lt_factorial] at hn
  rw [← factorial_lt (lt_transₓ one_pos hn), h] at hnm
  cases lt_irreflₓ _ hnm

theorem self_le_factorial : ∀ n : ℕ, n ≤ n !
  | 0 => zero_le_one
  | k + 1 => le_mul_of_one_le_right k.zero_lt_succ.le (Nat.one_le_of_lt <| Nat.factorial_pos _)

theorem lt_factorial_self {n : ℕ} (hi : 3 ≤ n) : n < n ! := by
  rw [← succ_pred_eq_of_pos ((zero_lt_two.trans (lt.base 2)).trans_le hi), factorial_succ]
  exact
    lt_mul_of_one_lt_right (pred n).succ_pos
      ((one_lt_two.trans_le (le_pred_of_lt (succ_le_iff.mp hi))).trans_le (self_le_factorial _))

theorem add_factorial_succ_lt_factorial_add_succ {i : ℕ} (n : ℕ) (hi : 2 ≤ i) : i + (n + 1)! < (i + n + 1)! := by
  rw [factorial_succ (i + _), add_mulₓ, one_mulₓ]
  have : i ≤ i + n := le.intro rfl
  exact
    add_lt_add_of_lt_of_le
      (this.trans_lt
        ((lt_mul_iff_one_lt_right (zero_lt_two.trans_le (hi.trans this))).mpr
          (lt_iff_le_and_ne.mpr
            ⟨(i + n).factorial_pos, fun g =>
              Nat.not_succ_le_selfₓ 1 ((hi.trans this).trans (factorial_eq_one.mp g.symm))⟩)))
      (factorial_le ((le_of_eqₓ (add_commₓ n 1)).trans ((add_le_add_iff_right n).mpr (one_le_two.trans hi))))

theorem add_factorial_lt_factorial_add {i n : ℕ} (hi : 2 ≤ i) (hn : 1 ≤ n) : i + n ! < (i + n)! := by
  cases hn
  · rw [factorial_one]
    exact lt_factorial_self (succ_le_succ hi)
    
  exact add_factorial_succ_lt_factorial_add_succ _ hi

theorem add_factorial_succ_le_factorial_add_succ (i : ℕ) (n : ℕ) : i + (n + 1)! ≤ (i + (n + 1))! := by
  obtain i2 | (_ | ⟨_, i0⟩) := le_or_ltₓ 2 i
  · exact (n.add_factorial_succ_lt_factorial_add_succ i2).le
    
  · rw [← add_assocₓ, factorial_succ (1 + n), add_mulₓ, one_mulₓ, add_commₓ 1 n]
    exact (add_le_add_iff_right _).mpr (one_le_mul (Nat.le_add_leftₓ 1 n) (n + 1).factorial_pos)
    
  rw [nat.le_zero_iff.mp (nat.succ_le_succ_iff.mp i0), zero_addₓ, zero_addₓ]

theorem add_factorial_le_factorial_add (i : ℕ) {n : ℕ} (n1 : 1 ≤ n) : i + n ! ≤ (i + n)! := by
  cases' n1 with h
  · exact self_le_factorial _
    
  exact add_factorial_succ_le_factorial_add_succ i h

theorem factorial_mul_pow_sub_le_factorial {n m : ℕ} (hnm : n ≤ m) : n ! * n ^ (m - n) ≤ m ! := by
  suffices n ! * (n + 1) ^ (m - n) ≤ m ! by
    apply trans _ this
    rw [mul_le_mul_left]
    apply pow_le_pow_of_le_left (zero_le n) (le_succ n)
    exact factorial_pos n
  convert Nat.factorial_mul_pow_le_factorial
  exact (add_tsub_cancel_of_le hnm).symm

end Factorial

/-! ### Ascending and descending factorials -/


section AscFactorial

/-- `n.asc_factorial k = (n + k)! / n!` (as seen in `nat.asc_factorial_eq_div`), but implemented
recursively to allow for "quick" computation when using `norm_num`. This is closely related to
`pochhammer`, but much less general. -/
def ascFactorial (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (n + k + 1) * asc_factorial k

@[simp]
theorem asc_factorial_zero (n : ℕ) : n.ascFactorial 0 = 1 :=
  rfl

@[simp]
theorem zero_asc_factorial (k : ℕ) : (0 : ℕ).ascFactorial k = k ! := by
  induction' k with t ht
  · rfl
    
  rw [asc_factorial, ht, zero_addₓ, Nat.factorial_succ]

theorem asc_factorial_succ {n k : ℕ} : n.ascFactorial k.succ = (n + k + 1) * n.ascFactorial k :=
  rfl

theorem succ_asc_factorial (n : ℕ) : ∀ k, (n + 1) * n.succ.ascFactorial k = (n + k + 1) * n.ascFactorial k
  | 0 => by
    rw [add_zeroₓ, asc_factorial_zero, asc_factorial_zero]
  | k + 1 => by
    rw [asc_factorial, mul_left_commₓ, succ_asc_factorial, asc_factorial, succ_add, ← add_assocₓ]

/-- `n.asc_factorial k = (n + k)! / n!` but without ℕ-division. See `nat.asc_factorial_eq_div` for
the version with ℕ-division. -/
theorem factorial_mul_asc_factorial (n : ℕ) : ∀ k, n ! * n.ascFactorial k = (n + k)!
  | 0 => by
    rw [asc_factorial, add_zeroₓ, mul_oneₓ]
  | k + 1 => by
    rw [asc_factorial_succ, mul_left_commₓ, factorial_mul_asc_factorial, ← add_assocₓ, factorial]

/-- Avoid in favor of `nat.factorial_mul_asc_factorial` if you can. ℕ-division isn't worth it. -/
theorem asc_factorial_eq_div (n k : ℕ) : n.ascFactorial k = (n + k)! / n ! := by
  apply mul_left_cancel₀ n.factorial_ne_zero
  rw [factorial_mul_asc_factorial]
  exact (Nat.mul_div_cancel'ₓ <| factorial_dvd_factorial <| le.intro rfl).symm

theorem asc_factorial_of_sub {n k : ℕ} (h : k < n) :
    (n - k) * (n - k).ascFactorial k = (n - (k + 1)).ascFactorial (k + 1) := by
  set t := n - k.succ with ht
  suffices h' : n - k = t.succ
  · rw [← ht, h', succ_asc_factorial, asc_factorial_succ]
    
  rw [ht, succ_eq_add_one, ← tsub_tsub_assoc (succ_le_of_lt h) (succ_pos _), succ_sub_one]

theorem pow_succ_le_asc_factorial (n : ℕ) : ∀ k : ℕ, (n + 1) ^ k ≤ n.ascFactorial k
  | 0 => by
    rw [asc_factorial_zero, pow_zeroₓ]
  | k + 1 => by
    rw [pow_succₓ]
    exact Nat.mul_le_mulₓ (Nat.add_le_add_rightₓ le_self_add _) (pow_succ_le_asc_factorial k)

theorem pow_lt_asc_factorial' (n k : ℕ) : (n + 1) ^ (k + 2) < n.ascFactorial (k + 2) := by
  rw [pow_succₓ]
  exact
    Nat.mul_lt_mulₓ (Nat.add_lt_add_rightₓ (Nat.lt_add_of_pos_rightₓ succ_pos') 1) (pow_succ_le_asc_factorial n _)
      (pow_pos succ_pos' _)

theorem pow_lt_asc_factorial (n : ℕ) : ∀ {k : ℕ}, 2 ≤ k → (n + 1) ^ k < n.ascFactorial k
  | 0 => by
    rintro ⟨⟩
  | 1 => by
    rintro (_ | ⟨_, ⟨⟩⟩)
  | k + 2 => fun _ => pow_lt_asc_factorial' n k

theorem asc_factorial_le_pow_add (n : ℕ) : ∀ k : ℕ, n.ascFactorial k ≤ (n + k) ^ k
  | 0 => by
    rw [asc_factorial_zero, pow_zeroₓ]
  | k + 1 => by
    rw [asc_factorial_succ, pow_succₓ]
    exact Nat.mul_le_mul_of_nonneg_leftₓ ((asc_factorial_le_pow_add k).trans (Nat.pow_le_pow_of_le_leftₓ (le_succ _) _))

theorem asc_factorial_lt_pow_add (n : ℕ) : ∀ {k : ℕ}, 2 ≤ k → n.ascFactorial k < (n + k) ^ k
  | 0 => by
    rintro ⟨⟩
  | 1 => by
    rintro (_ | ⟨_, ⟨⟩⟩)
  | k + 2 => fun _ => by
    rw [asc_factorial_succ, pow_succₓ]
    refine'
      Nat.mul_lt_mul'ₓ le_rfl
        ((asc_factorial_le_pow_add n _).trans_lt (pow_lt_pow_of_lt_left (lt_add_one _) (succ_pos _))) (succ_pos _)

theorem asc_factorial_pos (n k : ℕ) : 0 < n.ascFactorial k :=
  (pow_pos (succ_posₓ n) k).trans_le (pow_succ_le_asc_factorial n k)

end AscFactorial

section DescFactorial

/-- `n.desc_factorial k = n! / (n - k)!` (as seen in `nat.desc_factorial_eq_div`), but
implemented recursively to allow for "quick" computation when using `norm_num`. This is closely
related to `pochhammer`, but much less general. -/
def descFactorial (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (n - k) * desc_factorial k

@[simp]
theorem desc_factorial_zero (n : ℕ) : n.descFactorial 0 = 1 :=
  rfl

@[simp]
theorem desc_factorial_succ (n k : ℕ) : n.descFactorial k.succ = (n - k) * n.descFactorial k :=
  rfl

theorem zero_desc_factorial_succ (k : ℕ) : (0 : ℕ).descFactorial k.succ = 0 := by
  rw [desc_factorial_succ, zero_tsub, zero_mul]

@[simp]
theorem desc_factorial_one (n : ℕ) : n.descFactorial 1 = n := by
  rw [desc_factorial_succ, desc_factorial_zero, mul_oneₓ, tsub_zero]

@[simp]
theorem succ_desc_factorial_succ (n : ℕ) : ∀ k : ℕ, (n + 1).descFactorial (k + 1) = (n + 1) * n.descFactorial k
  | 0 => by
    rw [desc_factorial_zero, desc_factorial_one, mul_oneₓ]
  | succ k => by
    rw [desc_factorial_succ, succ_desc_factorial_succ, desc_factorial_succ, succ_sub_succ, mul_left_commₓ]

theorem succ_desc_factorial (n : ℕ) : ∀ k, (n + 1 - k) * (n + 1).descFactorial k = (n + 1) * n.descFactorial k
  | 0 => by
    rw [tsub_zero, desc_factorial_zero, desc_factorial_zero]
  | k + 1 => by
    rw [desc_factorial, succ_desc_factorial, desc_factorial_succ, succ_sub_succ, mul_left_commₓ]

theorem desc_factorial_self : ∀ n : ℕ, n.descFactorial n = n !
  | 0 => by
    rw [desc_factorial_zero, factorial_zero]
  | succ n => by
    rw [succ_desc_factorial_succ, desc_factorial_self, factorial_succ]

@[simp]
theorem desc_factorial_eq_zero_iff_lt {n : ℕ} : ∀ {k : ℕ}, n.descFactorial k = 0 ↔ n < k
  | 0 => by
    simp only [← desc_factorial_zero, ← Nat.one_ne_zero, ← Nat.not_lt_zeroₓ]
  | succ k => by
    rw [desc_factorial_succ, mul_eq_zero, desc_factorial_eq_zero_iff_lt, lt_succ_iff, tsub_eq_zero_iff_le,
      lt_iff_le_and_ne, or_iff_left_iff_imp, and_imp]
    exact fun h _ => h

alias desc_factorial_eq_zero_iff_lt ↔ _ desc_factorial_of_lt

theorem add_desc_factorial_eq_asc_factorial (n : ℕ) : ∀ k : ℕ, (n + k).descFactorial k = n.ascFactorial k
  | 0 => by
    rw [asc_factorial_zero, desc_factorial_zero]
  | succ k => by
    rw [Nat.add_succ, succ_desc_factorial_succ, asc_factorial_succ, add_desc_factorial_eq_asc_factorial]

/-- `n.desc_factorial k = n! / (n - k)!` but without ℕ-division. See `nat.desc_factorial_eq_div`
for the version using ℕ-division. -/
theorem factorial_mul_desc_factorial : ∀ {n k : ℕ}, k ≤ n → (n - k)! * n.descFactorial k = n !
  | n, 0 => fun _ => by
    rw [desc_factorial_zero, mul_oneₓ, tsub_zero]
  | 0, succ k => fun h => by
    exfalso
    exact not_succ_le_zero k h
  | succ n, succ k => fun h => by
    rw [succ_desc_factorial_succ, succ_sub_succ, ← mul_assoc, mul_comm (n - k)!, mul_assoc,
      factorial_mul_desc_factorial (Nat.succ_le_succ_iff.1 h), factorial_succ]

/-- Avoid in favor of `nat.factorial_mul_desc_factorial` if you can. ℕ-division isn't worth it. -/
theorem desc_factorial_eq_div {n k : ℕ} (h : k ≤ n) : n.descFactorial k = n ! / (n - k)! := by
  apply mul_left_cancel₀ (factorial_ne_zero (n - k))
  rw [factorial_mul_desc_factorial h]
  exact (Nat.mul_div_cancel'ₓ <| factorial_dvd_factorial <| Nat.sub_leₓ n k).symm

theorem pow_sub_le_desc_factorial (n : ℕ) : ∀ k : ℕ, (n + 1 - k) ^ k ≤ n.descFactorial k
  | 0 => by
    rw [desc_factorial_zero, pow_zeroₓ]
  | k + 1 => by
    rw [desc_factorial_succ, pow_succₓ, succ_sub_succ]
    exact
      Nat.mul_le_mul_of_nonneg_leftₓ
        (le_transₓ (Nat.pow_le_pow_of_le_leftₓ (tsub_le_tsub_right (le_succ _) _) k) (pow_sub_le_desc_factorial k))

theorem pow_sub_lt_desc_factorial' {n : ℕ} : ∀ {k : ℕ}, k + 2 ≤ n → (n - (k + 1)) ^ (k + 2) < n.descFactorial (k + 2)
  | 0 => fun h => by
    rw [desc_factorial_succ, pow_succₓ, pow_oneₓ, desc_factorial_one]
    exact Nat.mul_lt_mul_of_pos_leftₓ (tsub_lt_self (lt_of_lt_of_leₓ zero_lt_two h) zero_lt_one) (tsub_pos_of_lt h)
  | k + 1 => fun h => by
    rw [desc_factorial_succ, pow_succₓ]
    refine'
      Nat.mul_lt_mul_of_pos_leftₓ ((Nat.pow_le_pow_of_le_leftₓ (tsub_le_tsub_right (le_succ n) _) _).trans_lt _)
        (tsub_pos_of_lt h)
    rw [succ_sub_succ]
    exact pow_sub_lt_desc_factorial' ((le_succ _).trans h)

theorem pow_sub_lt_desc_factorial {n : ℕ} : ∀ {k : ℕ}, 2 ≤ k → k ≤ n → (n + 1 - k) ^ k < n.descFactorial k
  | 0 => by
    rintro ⟨⟩
  | 1 => by
    rintro (_ | ⟨_, ⟨⟩⟩)
  | k + 2 => fun _ h => by
    rw [succ_sub_succ]
    exact pow_sub_lt_desc_factorial' h

theorem desc_factorial_le_pow (n : ℕ) : ∀ k : ℕ, n.descFactorial k ≤ n ^ k
  | 0 => by
    rw [desc_factorial_zero, pow_zeroₓ]
  | k + 1 => by
    rw [desc_factorial_succ, pow_succₓ]
    exact Nat.mul_le_mulₓ (Nat.sub_leₓ _ _) (desc_factorial_le_pow k)

theorem desc_factorial_lt_pow {n : ℕ} (hn : 1 ≤ n) : ∀ {k : ℕ}, 2 ≤ k → n.descFactorial k < n ^ k
  | 0 => by
    rintro ⟨⟩
  | 1 => by
    rintro (_ | ⟨_, ⟨⟩⟩)
  | k + 2 => fun _ => by
    rw [desc_factorial_succ, pow_succ'ₓ, mul_comm]
    exact Nat.mul_lt_mul'ₓ (desc_factorial_le_pow _ _) (tsub_lt_self hn k.zero_lt_succ) (pow_pos hn _)

end DescFactorial

end Nat

