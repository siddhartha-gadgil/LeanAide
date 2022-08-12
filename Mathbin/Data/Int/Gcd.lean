/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Nat.Prime
import Mathbin.Data.Int.Order

/-!
# Extended GCD and divisibility over ℤ

## Main definitions

* Given `x y : ℕ`, `xgcd x y` computes the pair of integers `(a, b)` such that
  `gcd x y = x * a + y * b`. `gcd_a x y` and `gcd_b x y` are defined to be `a` and `b`,
  respectively.

## Main statements

* `gcd_eq_gcd_ab`: Bézout's lemma, given `x y : ℕ`, `gcd x y = x * gcd_a x y + y * gcd_b x y`.

## Tags

Bézout's lemma, Bezout's lemma
-/


/-! ### Extended Euclidean algorithm -/


namespace Nat

/-- Helper function for the extended GCD algorithm (`nat.xgcd`). -/
def xgcdAux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ
  | 0, s, t, r', s', t' => (r', s', t')
  | r@(succ _), s, t, r', s', t' =>
    have : r' % r < r := mod_ltₓ _ <| succ_posₓ _
    let q := r' / r
    xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t

@[simp]
theorem xgcd_zero_left {s t r' s' t'} : xgcdAux 0 s t r' s' t' = (r', s', t') := by
  simp [← xgcd_aux]

theorem xgcd_aux_rec {r s t r' s' t'} (h : 0 < r) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  cases r <;> [exact absurd h (lt_irreflₓ _),
    · simp only [← xgcd_aux]
      rfl
      ]

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : ℕ) : ℤ × ℤ :=
  (xgcdAux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA (x y : ℕ) : ℤ :=
  (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB (x y : ℕ) : ℤ :=
  (xgcd x y).2

@[simp]
theorem gcd_a_zero_left {s : ℕ} : gcdA 0 s = 0 := by
  unfold gcd_a
  rw [xgcd, xgcd_zero_left]

@[simp]
theorem gcd_b_zero_left {s : ℕ} : gcdB 0 s = 1 := by
  unfold gcd_b
  rw [xgcd, xgcd_zero_left]

@[simp]
theorem gcd_a_zero_right {s : ℕ} (h : s ≠ 0) : gcdA s 0 = 1 := by
  unfold gcd_a xgcd
  induction s
  · exact absurd rfl h
    
  · simp [← xgcd_aux]
    

@[simp]
theorem gcd_b_zero_right {s : ℕ} (h : s ≠ 0) : gcdB s 0 = 0 := by
  unfold gcd_b xgcd
  induction s
  · exact absurd rfl h
    
  · simp [← xgcd_aux]
    

@[simp]
theorem xgcd_aux_fst (x y) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcdₓ x y :=
  gcdₓ.induction x y
    (by
      simp )
    fun x y h IH s t s' t' => by
    simp [← xgcd_aux_rec, ← h, ← IH] <;> rw [← gcd_rec]

theorem xgcd_aux_val (x y) : xgcdAux x 1 0 y 0 1 = (gcdₓ x y, xgcd x y) := by
  rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1] <;> cases xgcd_aux x 1 0 y 0 1 <;> rfl

theorem xgcd_val (x y) : xgcd x y = (gcdA x y, gcdB x y) := by
  unfold gcd_a gcd_b <;> cases xgcd x y <;> rfl

section

parameter (x y : ℕ)

private def P : ℕ × ℤ × ℤ → Prop
  | (r, s, t) => (r : ℤ) = x * s + y * t

theorem xgcd_aux_P {r r'} : ∀ {s t s' t'}, P (r, s, t) → P (r', s', t') → P (xgcdAux r s t r' s' t') :=
  (gcdₓ.induction r r'
      (by
        simp ))
    fun a b h IH s t s' t' p p' => by
    rw [xgcd_aux_rec h]
    refine' IH _ p
    dsimp' [← P]  at *
    rw [Int.mod_def]
    generalize (b / a : ℤ) = k
    rw [p, p']
    simp [← mul_addₓ, ← mul_comm, ← mul_left_commₓ, ← add_commₓ, ← add_left_commₓ, ← sub_eq_neg_add, ← mul_assoc]

/-- **Bézout's lemma**: given `x y : ℕ`, `gcd x y = x * a + y * b`, where `a = gcd_a x y` and
`b = gcd_b x y` are computed by the extended Euclidean algorithm.
-/
theorem gcd_eq_gcd_ab : (gcdₓ x y : ℤ) = x * gcdA x y + y * gcdB x y := by
  have :=
      @xgcd_aux_P x y x y 1 0 0 1
        (by
          simp [← P])
        (by
          simp [← P]) <;>
    rwa [xgcd_aux_val, xgcd_val] at this

end

theorem exists_mul_mod_eq_gcd {k n : ℕ} (hk : gcdₓ n k < k) : ∃ m, n * m % k = gcdₓ n k := by
  have hk' := int.coe_nat_ne_zero.mpr (ne_of_gtₓ (lt_of_le_of_ltₓ (zero_le (gcd n k)) hk))
  have key := congr_arg (fun m => Int.natModₓ m k) (gcd_eq_gcd_ab n k)
  simp_rw [Int.natModₓ] at key
  rw [Int.add_mul_mod_self_left, ← Int.coe_nat_mod, Int.to_nat_coe_nat, mod_eq_of_lt hk] at key
  refine' ⟨(n.gcd_a k % k).toNat, Eq.trans (Int.coe_nat_inj _) key.symm⟩
  rw [Int.coe_nat_mod, Int.coe_nat_mul, Int.to_nat_of_nonneg (Int.mod_nonneg _ hk'),
    Int.to_nat_of_nonneg (Int.mod_nonneg _ hk'), Int.mul_mod, Int.mod_mod, ← Int.mul_mod]

theorem exists_mul_mod_eq_one_of_coprime {k n : ℕ} (hkn : Coprime n k) (hk : 1 < k) : ∃ m, n * m % k = 1 :=
  Exists.cases_on (exists_mul_mod_eq_gcd (lt_of_le_of_ltₓ (le_of_eqₓ hkn) hk)) fun m hm => ⟨m, hm.trans hkn⟩

end Nat

/-! ### Divisibility over ℤ -/


namespace Int

protected theorem coe_nat_gcd (m n : ℕ) : Int.gcdₓ ↑m ↑n = Nat.gcdₓ m n :=
  rfl

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA : ℤ → ℤ → ℤ
  | of_nat m, n => m.gcdA n.natAbs
  | -[1+ m], n => -m.succ.gcdA n.natAbs

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB : ℤ → ℤ → ℤ
  | m, of_nat n => m.natAbs.gcdB n
  | m, -[1+ n] => -m.natAbs.gcdB n.succ

/-- **Bézout's lemma** -/
theorem gcd_eq_gcd_ab : ∀ x y : ℤ, (gcdₓ x y : ℤ) = x * gcdA x y + y * gcdB x y
  | (m : ℕ), (n : ℕ) => Nat.gcd_eq_gcd_ab _ _
  | (m : ℕ), -[1+ n] =>
    show (_ : ℤ) = _ + -(n + 1) * -_ by
      rw [neg_mul_neg] <;> apply Nat.gcd_eq_gcd_ab
  | -[1+ m], (n : ℕ) =>
    show (_ : ℤ) = -(m + 1) * -_ + _ by
      rw [neg_mul_neg] <;> apply Nat.gcd_eq_gcd_ab
  | -[1+ m], -[1+ n] =>
    show (_ : ℤ) = -(m + 1) * -_ + -(n + 1) * -_ by
      rw [neg_mul_neg, neg_mul_neg]
      apply Nat.gcd_eq_gcd_ab

theorem nat_abs_div (a b : ℤ) (H : b ∣ a) : natAbs (a / b) = natAbs a / natAbs b := by
  cases Nat.eq_zero_or_posₓ (nat_abs b)
  · rw [eq_zero_of_nat_abs_eq_zero h]
    simp [← Int.div_zero]
    
  calc nat_abs (a / b) = nat_abs (a / b) * 1 := by
      rw [mul_oneₓ]_ = nat_abs (a / b) * (nat_abs b / nat_abs b) := by
      rw [Nat.div_selfₓ h]_ = nat_abs (a / b) * nat_abs b / nat_abs b := by
      rw [Nat.mul_div_assocₓ _ dvd_rfl]_ = nat_abs (a / b * b) / nat_abs b := by
      rw [nat_abs_mul (a / b) b]_ = nat_abs a / nat_abs b := by
      rw [Int.div_mul_cancel H]

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : Nat.Prime p) {m n : ℤ} {k l : ℕ}
    (hpm : ↑(p ^ k) ∣ m) (hpn : ↑(p ^ l) ∣ n) (hpmn : ↑(p ^ (k + l + 1)) ∣ m * n) :
    ↑(p ^ (k + 1)) ∣ m ∨ ↑(p ^ (l + 1)) ∣ n :=
  have hpm' : p ^ k ∣ m.natAbs := Int.coe_nat_dvd.1 <| Int.dvd_nat_abs.2 hpm
  have hpn' : p ^ l ∣ n.natAbs := Int.coe_nat_dvd.1 <| Int.dvd_nat_abs.2 hpn
  have hpmn' : p ^ (k + l + 1) ∣ m.natAbs * n.natAbs := by
    rw [← Int.nat_abs_mul] <;> apply Int.coe_nat_dvd.1 <| Int.dvd_nat_abs.2 hpmn
  let hsd := Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul p_prime hpm' hpn' hpmn'
  hsd.elim
    (fun hsd1 =>
      Or.inl
        (by
          apply Int.dvd_nat_abs.1
          apply Int.coe_nat_dvd.2 hsd1))
    fun hsd2 =>
    Or.inr
      (by
        apply Int.dvd_nat_abs.1
        apply Int.coe_nat_dvd.2 hsd2)

theorem dvd_of_mul_dvd_mul_left {i j k : ℤ} (k_non_zero : k ≠ 0) (H : k * i ∣ k * j) : i ∣ j :=
  Dvd.elim H fun l H1 => by
    rw [mul_assoc] at H1 <;> exact ⟨_, mul_left_cancel₀ k_non_zero H1⟩

theorem dvd_of_mul_dvd_mul_right {i j k : ℤ} (k_non_zero : k ≠ 0) (H : i * k ∣ j * k) : i ∣ j := by
  rw [mul_comm i k, mul_comm j k] at H <;> exact dvd_of_mul_dvd_mul_left k_non_zero H

theorem Prime.dvd_nat_abs_of_coe_dvd_sq {p : ℕ} (hp : p.Prime) (k : ℤ) (h : ↑p ∣ k ^ 2) : p ∣ k.natAbs := by
  apply @Nat.Prime.dvd_of_dvd_pow _ _ 2 hp
  rwa [sq, ← nat_abs_mul, ← coe_nat_dvd_left, ← sq]

/-- ℤ specific version of least common multiple. -/
def lcm (i j : ℤ) : ℕ :=
  Nat.lcmₓ (natAbs i) (natAbs j)

theorem lcm_def (i j : ℤ) : lcm i j = Nat.lcmₓ (natAbs i) (natAbs j) :=
  rfl

protected theorem coe_nat_lcm (m n : ℕ) : Int.lcm ↑m ↑n = Nat.lcmₓ m n :=
  rfl

theorem gcd_dvd_left (i j : ℤ) : (gcdₓ i j : ℤ) ∣ i :=
  dvd_nat_abs.mp <| coe_nat_dvd.mpr <| Nat.gcd_dvd_leftₓ _ _

theorem gcd_dvd_right (i j : ℤ) : (gcdₓ i j : ℤ) ∣ j :=
  dvd_nat_abs.mp <| coe_nat_dvd.mpr <| Nat.gcd_dvd_rightₓ _ _

theorem dvd_gcd {i j k : ℤ} (h1 : k ∣ i) (h2 : k ∣ j) : k ∣ gcdₓ i j :=
  nat_abs_dvd.1 <| coe_nat_dvd.2 <| Nat.dvd_gcdₓ (nat_abs_dvd_iff_dvd.2 h1) (nat_abs_dvd_iff_dvd.2 h2)

theorem gcd_mul_lcm (i j : ℤ) : gcdₓ i j * lcm i j = natAbs (i * j) := by
  rw [Int.gcdₓ, Int.lcm, Nat.gcd_mul_lcmₓ, nat_abs_mul]

theorem gcd_comm (i j : ℤ) : gcdₓ i j = gcdₓ j i :=
  Nat.gcd_commₓ _ _

theorem gcd_assoc (i j k : ℤ) : gcdₓ (gcdₓ i j) k = gcdₓ i (gcdₓ j k) :=
  Nat.gcd_assocₓ _ _ _

@[simp]
theorem gcd_self (i : ℤ) : gcdₓ i i = natAbs i := by
  simp [← gcd]

@[simp]
theorem gcd_zero_left (i : ℤ) : gcdₓ 0 i = natAbs i := by
  simp [← gcd]

@[simp]
theorem gcd_zero_right (i : ℤ) : gcdₓ i 0 = natAbs i := by
  simp [← gcd]

@[simp]
theorem gcd_one_left (i : ℤ) : gcdₓ 1 i = 1 :=
  Nat.gcd_one_leftₓ _

@[simp]
theorem gcd_one_right (i : ℤ) : gcdₓ i 1 = 1 :=
  Nat.gcd_one_rightₓ _

theorem gcd_mul_left (i j k : ℤ) : gcdₓ (i * j) (i * k) = natAbs i * gcdₓ j k := by
  rw [Int.gcdₓ, Int.gcdₓ, nat_abs_mul, nat_abs_mul]
  apply Nat.gcd_mul_leftₓ

theorem gcd_mul_right (i j k : ℤ) : gcdₓ (i * j) (k * j) = gcdₓ i k * natAbs j := by
  rw [Int.gcdₓ, Int.gcdₓ, nat_abs_mul, nat_abs_mul]
  apply Nat.gcd_mul_rightₓ

theorem gcd_pos_of_non_zero_left {i : ℤ} (j : ℤ) (i_non_zero : i ≠ 0) : 0 < gcdₓ i j :=
  Nat.gcd_pos_of_pos_leftₓ (natAbs j) (nat_abs_pos_of_ne_zero i_non_zero)

theorem gcd_pos_of_non_zero_right (i : ℤ) {j : ℤ} (j_non_zero : j ≠ 0) : 0 < gcdₓ i j :=
  Nat.gcd_pos_of_pos_rightₓ (natAbs i) (nat_abs_pos_of_ne_zero j_non_zero)

theorem gcd_eq_zero_iff {i j : ℤ} : gcdₓ i j = 0 ↔ i = 0 ∧ j = 0 := by
  rw [Int.gcdₓ]
  constructor
  · intro h
    exact
      ⟨nat_abs_eq_zero.mp (Nat.eq_zero_of_gcd_eq_zero_leftₓ h),
        nat_abs_eq_zero.mp (Nat.eq_zero_of_gcd_eq_zero_rightₓ h)⟩
    
  · intro h
    rw [nat_abs_eq_zero.mpr h.left, nat_abs_eq_zero.mpr h.right]
    apply Nat.gcd_zero_leftₓ
    

theorem gcd_pos_iff {i j : ℤ} : 0 < gcdₓ i j ↔ i ≠ 0 ∨ j ≠ 0 :=
  pos_iff_ne_zero.trans <| gcd_eq_zero_iff.Not.trans not_and_distrib

theorem gcd_div {i j k : ℤ} (H1 : k ∣ i) (H2 : k ∣ j) : gcdₓ (i / k) (j / k) = gcdₓ i j / natAbs k := by
  rw [gcd, nat_abs_div i k H1, nat_abs_div j k H2] <;>
    exact Nat.gcd_divₓ (nat_abs_dvd_iff_dvd.mpr H1) (nat_abs_dvd_iff_dvd.mpr H2)

theorem gcd_div_gcd_div_gcd {i j : ℤ} (H : 0 < gcdₓ i j) : gcdₓ (i / gcdₓ i j) (j / gcdₓ i j) = 1 := by
  rw [gcd_div (gcd_dvd_left i j) (gcd_dvd_right i j)]
  rw [nat_abs_of_nat, Nat.div_selfₓ H]

theorem gcd_dvd_gcd_of_dvd_left {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcdₓ i j ∣ gcdₓ k j :=
  Int.coe_nat_dvd.1 <| dvd_gcd ((gcd_dvd_left i j).trans H) (gcd_dvd_right i j)

theorem gcd_dvd_gcd_of_dvd_right {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcdₓ j i ∣ gcdₓ j k :=
  Int.coe_nat_dvd.1 <| dvd_gcd (gcd_dvd_left j i) ((gcd_dvd_right j i).trans H)

theorem gcd_dvd_gcd_mul_left (i j k : ℤ) : gcdₓ i j ∣ gcdₓ (k * i) j :=
  gcd_dvd_gcd_of_dvd_left _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right (i j k : ℤ) : gcdₓ i j ∣ gcdₓ (i * k) j :=
  gcd_dvd_gcd_of_dvd_left _ (dvd_mul_right _ _)

theorem gcd_dvd_gcd_mul_left_right (i j k : ℤ) : gcdₓ i j ∣ gcdₓ i (k * j) :=
  gcd_dvd_gcd_of_dvd_right _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (i j k : ℤ) : gcdₓ i j ∣ gcdₓ i (j * k) :=
  gcd_dvd_gcd_of_dvd_right _ (dvd_mul_right _ _)

theorem gcd_eq_left {i j : ℤ} (H : i ∣ j) : gcdₓ i j = natAbs i :=
  Nat.dvd_antisymm
    (by
      unfold gcd <;> exact Nat.gcd_dvd_leftₓ _ _)
    (by
      unfold gcd <;> exact Nat.dvd_gcdₓ dvd_rfl (nat_abs_dvd_iff_dvd.mpr H))

theorem gcd_eq_right {i j : ℤ} (H : j ∣ i) : gcdₓ i j = natAbs j := by
  rw [gcd_comm, gcd_eq_left H]

theorem ne_zero_of_gcd {x y : ℤ} (hc : gcdₓ x y ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by
  contrapose! hc
  rw [hc.left, hc.right, gcd_zero_right, nat_abs_zero]

theorem exists_gcd_one {m n : ℤ} (H : 0 < gcdₓ m n) :
    ∃ m' n' : ℤ, gcdₓ m' n' = 1 ∧ m = m' * gcdₓ m n ∧ n = n' * gcdₓ m n :=
  ⟨_, _, gcd_div_gcd_div_gcd H, (Int.div_mul_cancel (gcd_dvd_left m n)).symm,
    (Int.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_gcd_one' {m n : ℤ} (H : 0 < gcdₓ m n) :
    ∃ (g : ℕ)(m' n' : ℤ), 0 < g ∧ gcdₓ m' n' = 1 ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_gcd_one H
  ⟨_, m', n', H, h⟩

theorem pow_dvd_pow_iff {m n : ℤ} {k : ℕ} (k0 : 0 < k) : m ^ k ∣ n ^ k ↔ m ∣ n := by
  refine' ⟨fun h => _, fun h => pow_dvd_pow_of_dvd h _⟩
  apply int.nat_abs_dvd_iff_dvd.mp
  apply (Nat.pow_dvd_pow_iff k0).mp
  rw [← Int.nat_abs_pow, ← Int.nat_abs_pow]
  exact int.nat_abs_dvd_iff_dvd.mpr h

theorem gcd_dvd_iff {a b : ℤ} {n : ℕ} : gcdₓ a b ∣ n ↔ ∃ x y : ℤ, ↑n = a * x + b * y := by
  constructor
  · intro h
    rw [← Nat.mul_div_cancel'ₓ h, Int.coe_nat_mul, gcd_eq_gcd_ab, add_mulₓ, mul_assoc, mul_assoc]
    refine' ⟨_, _, rfl⟩
    
  · rintro ⟨x, y, h⟩
    rw [← Int.coe_nat_dvd, h]
    exact dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left a b) _) (dvd_mul_of_dvd_left (gcd_dvd_right a b) y)
    

theorem gcd_greatest {a b d : ℤ} (hd_pos : 0 ≤ d) (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : ℤ, e ∣ a → e ∣ b → e ∣ d) :
    d = gcdₓ a b :=
  dvd_antisymm hd_pos (coe_zero_le (gcdₓ a b)) (dvd_gcd hda hdb) (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b))

/-- Euclid's lemma: if `a ∣ b * c` and `gcd a c = 1` then `a ∣ b`.
Compare with `is_coprime.dvd_of_dvd_mul_left` and
`unique_factorization_monoid.dvd_of_dvd_mul_left_of_no_prime_factors` -/
theorem dvd_of_dvd_mul_left_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c) (hab : gcdₓ a c = 1) : a ∣ b := by
  have := gcd_eq_gcd_ab a c
  simp only [← hab, ← Int.coe_nat_zero, ← Int.coe_nat_succ, ← zero_addₓ] at this
  have : b * a * gcd_a a c + b * c * gcd_b a c = b := by
    simp [← mul_assoc, mul_addₓ, this]
  rw [← this]
  exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_left a b) _) (dvd_mul_of_dvd_left habc _)

/-- Euclid's lemma: if `a ∣ b * c` and `gcd a b = 1` then `a ∣ c`.
Compare with `is_coprime.dvd_of_dvd_mul_right` and
`unique_factorization_monoid.dvd_of_dvd_mul_right_of_no_prime_factors` -/
theorem dvd_of_dvd_mul_right_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c) (hab : gcdₓ a b = 1) : a ∣ c := by
  rw [mul_comm] at habc
  exact dvd_of_dvd_mul_left_of_gcd_one habc hab

/-- For nonzero integers `a` and `b`, `gcd a b` is the smallest positive natural number that can be
written in the form `a * x + b * y` for some pair of integers `x` and `y` -/
theorem gcd_least_linear {a b : ℤ} (ha : a ≠ 0) : IsLeast { n : ℕ | 0 < n ∧ ∃ x y : ℤ, ↑n = a * x + b * y } (a.gcd b) :=
  by
  simp_rw [← gcd_dvd_iff]
  constructor
  · simpa [← and_trueₓ, ← dvd_refl, ← Set.mem_set_of_eq] using gcd_pos_of_non_zero_left b ha
    
  · simp only [← LowerBounds, ← and_imp, ← Set.mem_set_of_eq]
    exact fun n hn_pos hn => Nat.le_of_dvdₓ hn_pos hn
    

/-! ### lcm -/


theorem lcm_comm (i j : ℤ) : lcm i j = lcm j i := by
  rw [Int.lcm, Int.lcm]
  exact Nat.lcm_commₓ _ _

theorem lcm_assoc (i j k : ℤ) : lcm (lcm i j) k = lcm i (lcm j k) := by
  rw [Int.lcm, Int.lcm, Int.lcm, Int.lcm, nat_abs_of_nat, nat_abs_of_nat]
  apply Nat.lcm_assocₓ

@[simp]
theorem lcm_zero_left (i : ℤ) : lcm 0 i = 0 := by
  rw [Int.lcm]
  apply Nat.lcm_zero_leftₓ

@[simp]
theorem lcm_zero_right (i : ℤ) : lcm i 0 = 0 := by
  rw [Int.lcm]
  apply Nat.lcm_zero_rightₓ

@[simp]
theorem lcm_one_left (i : ℤ) : lcm 1 i = natAbs i := by
  rw [Int.lcm]
  apply Nat.lcm_one_leftₓ

@[simp]
theorem lcm_one_right (i : ℤ) : lcm i 1 = natAbs i := by
  rw [Int.lcm]
  apply Nat.lcm_one_rightₓ

@[simp]
theorem lcm_self (i : ℤ) : lcm i i = natAbs i := by
  rw [Int.lcm]
  apply Nat.lcm_selfₓ

theorem dvd_lcm_left (i j : ℤ) : i ∣ lcm i j := by
  rw [Int.lcm]
  apply coe_nat_dvd_right.mpr
  apply Nat.dvd_lcm_leftₓ

theorem dvd_lcm_right (i j : ℤ) : j ∣ lcm i j := by
  rw [Int.lcm]
  apply coe_nat_dvd_right.mpr
  apply Nat.dvd_lcm_rightₓ

theorem lcm_dvd {i j k : ℤ} : i ∣ k → j ∣ k → (lcm i j : ℤ) ∣ k := by
  rw [Int.lcm]
  intro hi hj
  exact coe_nat_dvd_left.mpr (Nat.lcm_dvdₓ (nat_abs_dvd_iff_dvd.mpr hi) (nat_abs_dvd_iff_dvd.mpr hj))

end Int

theorem pow_gcd_eq_one {M : Type _} [Monoidₓ M] (x : M) {m n : ℕ} (hm : x ^ m = 1) (hn : x ^ n = 1) : x ^ m.gcd n = 1 :=
  by
  cases m
  · simp only [← hn, ← Nat.gcd_zero_leftₓ]
    
  obtain ⟨x, rfl⟩ : IsUnit x := by
    apply is_unit_of_pow_eq_one _ _ hm m.succ_pos
  simp only [Units.coe_pow] at *
  rw [← Units.coe_one, ← zpow_coe_nat, ← Units.ext_iff] at *
  simp only [← Nat.gcd_eq_gcd_ab, ← zpow_add, ← zpow_mul, ← hm, ← hn, ← one_zpow, ← one_mulₓ]

theorem gcd_nsmul_eq_zero {M : Type _} [AddMonoidₓ M] (x : M) {m n : ℕ} (hm : m • x = 0) (hn : n • x = 0) :
    m.gcd n • x = 0 := by
  apply multiplicative.of_add.injective
  rw [of_add_nsmul, of_add_zero, pow_gcd_eq_one] <;> rwa [← of_add_nsmul, ← of_add_zero, Equivₓ.apply_eq_iff_eq]

attribute [to_additive gcd_nsmul_eq_zero] pow_gcd_eq_one

/-! ### GCD prover -/


open NormNum

namespace Tactic

namespace NormNum

theorem int_gcd_helper' {d : ℕ} {x y a b : ℤ} (h₁ : (d : ℤ) ∣ x) (h₂ : (d : ℤ) ∣ y) (h₃ : x * a + y * b = d) :
    Int.gcdₓ x y = d := by
  refine' Nat.dvd_antisymm _ (Int.coe_nat_dvd.1 (Int.dvd_gcd h₁ h₂))
  rw [← Int.coe_nat_dvd, ← h₃]
  apply dvd_add
  · exact (Int.gcd_dvd_left _ _).mul_right _
    
  · exact (Int.gcd_dvd_right _ _).mul_right _
    

theorem nat_gcd_helper_dvd_left (x y a : ℕ) (h : x * a = y) : Nat.gcdₓ x y = x :=
  Nat.gcd_eq_leftₓ ⟨a, h.symm⟩

theorem nat_gcd_helper_dvd_right (x y a : ℕ) (h : y * a = x) : Nat.gcdₓ x y = y :=
  Nat.gcd_eq_rightₓ ⟨a, h.symm⟩

theorem nat_gcd_helper_2 (d x y a b u v tx ty : ℕ) (hu : d * u = x) (hv : d * v = y) (hx : x * a = tx) (hy : y * b = ty)
    (h : ty + d = tx) : Nat.gcdₓ x y = d := by
  rw [← Int.coe_nat_gcd]
  apply @int_gcd_helper' _ _ _ a (-b) (Int.coe_nat_dvd.2 ⟨_, hu.symm⟩) (Int.coe_nat_dvd.2 ⟨_, hv.symm⟩)
  rw [mul_neg, ← sub_eq_add_neg, sub_eq_iff_eq_add']
  norm_cast
  rw [hx, hy, h]

theorem nat_gcd_helper_1 (d x y a b u v tx ty : ℕ) (hu : d * u = x) (hv : d * v = y) (hx : x * a = tx) (hy : y * b = ty)
    (h : tx + d = ty) : Nat.gcdₓ x y = d :=
  (Nat.gcd_commₓ _ _).trans <| nat_gcd_helper_2 _ _ _ _ _ _ _ _ _ hv hu hy hx h

theorem nat_lcm_helper (x y d m n : ℕ) (hd : Nat.gcdₓ x y = d) (d0 : 0 < d) (xy : x * y = n) (dm : d * m = n) :
    Nat.lcmₓ x y = m :=
  (Nat.mul_right_inj d0).1 <| by
    rw [dm, ← xy, ← hd, Nat.gcd_mul_lcmₓ]

theorem nat_coprime_helper_zero_left (x : ℕ) (h : 1 < x) : ¬Nat.Coprime 0 x :=
  mt (Nat.coprime_zero_leftₓ _).1 <| ne_of_gtₓ h

theorem nat_coprime_helper_zero_right (x : ℕ) (h : 1 < x) : ¬Nat.Coprime x 0 :=
  mt (Nat.coprime_zero_rightₓ _).1 <| ne_of_gtₓ h

theorem nat_coprime_helper_1 (x y a b tx ty : ℕ) (hx : x * a = tx) (hy : y * b = ty) (h : tx + 1 = ty) :
    Nat.Coprime x y :=
  nat_gcd_helper_1 _ _ _ _ _ _ _ _ _ (one_mulₓ _) (one_mulₓ _) hx hy h

theorem nat_coprime_helper_2 (x y a b tx ty : ℕ) (hx : x * a = tx) (hy : y * b = ty) (h : ty + 1 = tx) :
    Nat.Coprime x y :=
  nat_gcd_helper_2 _ _ _ _ _ _ _ _ _ (one_mulₓ _) (one_mulₓ _) hx hy h

theorem nat_not_coprime_helper (d x y u v : ℕ) (hu : d * u = x) (hv : d * v = y) (h : 1 < d) : ¬Nat.Coprime x y :=
  Nat.not_coprime_of_dvd_of_dvdₓ h ⟨_, hu.symm⟩ ⟨_, hv.symm⟩

theorem int_gcd_helper (x y : ℤ) (nx ny d : ℕ) (hx : (nx : ℤ) = x) (hy : (ny : ℤ) = y) (h : Nat.gcdₓ nx ny = d) :
    Int.gcdₓ x y = d := by
  rwa [← hx, ← hy, Int.coe_nat_gcd]

theorem int_gcd_helper_neg_left (x y : ℤ) (d : ℕ) (h : Int.gcdₓ x y = d) : Int.gcdₓ (-x) y = d := by
  rw [Int.gcdₓ] at h⊢ <;> rwa [Int.nat_abs_neg]

theorem int_gcd_helper_neg_right (x y : ℤ) (d : ℕ) (h : Int.gcdₓ x y = d) : Int.gcdₓ x (-y) = d := by
  rw [Int.gcdₓ] at h⊢ <;> rwa [Int.nat_abs_neg]

theorem int_lcm_helper (x y : ℤ) (nx ny d : ℕ) (hx : (nx : ℤ) = x) (hy : (ny : ℤ) = y) (h : Nat.lcmₓ nx ny = d) :
    Int.lcm x y = d := by
  rwa [← hx, ← hy, Int.coe_nat_lcm]

theorem int_lcm_helper_neg_left (x y : ℤ) (d : ℕ) (h : Int.lcm x y = d) : Int.lcm (-x) y = d := by
  rw [Int.lcm] at h⊢ <;> rwa [Int.nat_abs_neg]

theorem int_lcm_helper_neg_right (x y : ℤ) (d : ℕ) (h : Int.lcm x y = d) : Int.lcm x (-y) = d := by
  rw [Int.lcm] at h⊢ <;> rwa [Int.nat_abs_neg]

/-- Evaluates the `nat.gcd` function. -/
unsafe def prove_gcd_nat (c : instance_cache) (ex ey : expr) : tactic (instance_cache × expr × expr) := do
  let x ← ex.toNat
  let y ← ey.toNat
  match x, y with
    | 0, _ => pure (c, ey, (quote.1 Nat.gcd_zero_leftₓ).mk_app [ey])
    | _, 0 => pure (c, ex, (quote.1 Nat.gcd_zero_rightₓ).mk_app [ex])
    | 1, _ => pure (c, quote.1 (1 : ℕ), (quote.1 Nat.gcd_one_leftₓ).mk_app [ey])
    | _, 1 => pure (c, quote.1 (1 : ℕ), (quote.1 Nat.gcd_one_rightₓ).mk_app [ex])
    | _, _ => do
      let (d, a, b) := Nat.xgcdAux x 1 0 y 0 1
      if d = x then do
          let (c, ea) ← c (y / x)
          let (c, _, p) ← prove_mul_nat c ex ea
          pure (c, ex, (quote.1 nat_gcd_helper_dvd_left).mk_app [ex, ey, ea, p])
        else
          if d = y then do
            let (c, ea) ← c (x / y)
            let (c, _, p) ← prove_mul_nat c ey ea
            pure (c, ey, (quote.1 nat_gcd_helper_dvd_right).mk_app [ex, ey, ea, p])
          else do
            let (c, ed) ← c d
            let (c, ea) ← c a
            let (c, eb) ← c b
            let (c, eu) ← c (x / d)
            let (c, ev) ← c (y / d)
            let (c, _, pu) ← prove_mul_nat c ed eu
            let (c, _, pv) ← prove_mul_nat c ed ev
            let (c, etx, px) ← prove_mul_nat c ex ea
            let (c, ety, py) ← prove_mul_nat c ey eb
            let (c, p) ← if a ≥ 0 then prove_add_nat c ety ed etx else prove_add_nat c etx ed ety
            let pf : expr := if a ≥ 0 then quote.1 nat_gcd_helper_2 else quote.1 nat_gcd_helper_1
            pure (c, ed, pf [ed, ex, ey, ea, eb, eu, ev, etx, ety, pu, pv, px, py, p])

/-- Evaluates the `nat.lcm` function. -/
unsafe def prove_lcm_nat (c : instance_cache) (ex ey : expr) : tactic (instance_cache × expr × expr) := do
  let x ← ex.toNat
  let y ← ey.toNat
  match x, y with
    | 0, _ => pure (c, quote.1 (0 : ℕ), (quote.1 Nat.lcm_zero_leftₓ).mk_app [ey])
    | _, 0 => pure (c, quote.1 (0 : ℕ), (quote.1 Nat.lcm_zero_rightₓ).mk_app [ex])
    | 1, _ => pure (c, ey, (quote.1 Nat.lcm_one_leftₓ).mk_app [ey])
    | _, 1 => pure (c, ex, (quote.1 Nat.lcm_one_rightₓ).mk_app [ex])
    | _, _ => do
      let (c, ed, pd) ← prove_gcd_nat c ex ey
      let (c, p0) ← prove_pos c ed
      let (c, en, xy) ← prove_mul_nat c ex ey
      let d ← ed
      let (c, em) ← c (x * y / d)
      let (c, _, dm) ← prove_mul_nat c ed em
      pure (c, em, (quote.1 nat_lcm_helper).mk_app [ex, ey, ed, em, en, pd, p0, xy, dm])

/-- Evaluates the `int.gcd` function. -/
unsafe def prove_gcd_int (zc nc : instance_cache) : expr → expr → tactic (instance_cache × instance_cache × expr × expr)
  | x, y =>
    match match_neg x with
    | some x => do
      let (zc, nc, d, p) ← prove_gcd_int x y
      pure (zc, nc, d, (quote.1 int_gcd_helper_neg_left).mk_app [x, y, d, p])
    | none =>
      match match_neg y with
      | some y => do
        let (zc, nc, d, p) ← prove_gcd_int x y
        pure (zc, nc, d, (quote.1 int_gcd_helper_neg_right).mk_app [x, y, d, p])
      | none => do
        let (zc, nc, nx, px) ← prove_nat_uncast zc nc x
        let (zc, nc, ny, py) ← prove_nat_uncast zc nc y
        let (nc, d, p) ← prove_gcd_nat nc nx ny
        pure (zc, nc, d, (quote.1 int_gcd_helper).mk_app [x, y, nx, ny, d, px, py, p])

/-- Evaluates the `int.lcm` function. -/
unsafe def prove_lcm_int (zc nc : instance_cache) : expr → expr → tactic (instance_cache × instance_cache × expr × expr)
  | x, y =>
    match match_neg x with
    | some x => do
      let (zc, nc, d, p) ← prove_lcm_int x y
      pure (zc, nc, d, (quote.1 int_lcm_helper_neg_left).mk_app [x, y, d, p])
    | none =>
      match match_neg y with
      | some y => do
        let (zc, nc, d, p) ← prove_lcm_int x y
        pure (zc, nc, d, (quote.1 int_lcm_helper_neg_right).mk_app [x, y, d, p])
      | none => do
        let (zc, nc, nx, px) ← prove_nat_uncast zc nc x
        let (zc, nc, ny, py) ← prove_nat_uncast zc nc y
        let (nc, d, p) ← prove_lcm_nat nc nx ny
        pure (zc, nc, d, (quote.1 int_lcm_helper).mk_app [x, y, nx, ny, d, px, py, p])

/-- Evaluates the `nat.coprime` function. -/
unsafe def prove_coprime_nat (c : instance_cache) (ex ey : expr) : tactic (instance_cache × Sum expr expr) := do
  let x ← ex.toNat
  let y ← ey.toNat
  match x, y with
    | 1, _ => pure (c, Sum.inl <| (quote.1 Nat.coprime_one_leftₓ).mk_app [ey])
    | _, 1 => pure (c, Sum.inl <| (quote.1 Nat.coprime_one_rightₓ).mk_app [ex])
    | 0, 0 => pure (c, Sum.inr (quote.1 Nat.not_coprime_zero_zero))
    | 0, _ => do
      let c ← mk_instance_cache (quote.1 ℕ)
      let (c, p) ← prove_lt_nat c (quote.1 1) ey
      pure (c, Sum.inr <| (quote.1 nat_coprime_helper_zero_left).mk_app [ey, p])
    | _, 0 => do
      let c ← mk_instance_cache (quote.1 ℕ)
      let (c, p) ← prove_lt_nat c (quote.1 1) ex
      pure (c, Sum.inr <| (quote.1 nat_coprime_helper_zero_right).mk_app [ex, p])
    | _, _ => do
      let c ← mk_instance_cache (quote.1 ℕ)
      let (d, a, b) := Nat.xgcdAux x 1 0 y 0 1
      if d = 1 then do
          let (c, ea) ← c a
          let (c, eb) ← c b
          let (c, etx, px) ← prove_mul_nat c ex ea
          let (c, ety, py) ← prove_mul_nat c ey eb
          let (c, p) ← if a ≥ 0 then prove_add_nat c ety (quote.1 1) etx else prove_add_nat c etx (quote.1 1) ety
          let pf : expr := if a ≥ 0 then quote.1 nat_coprime_helper_2 else quote.1 nat_coprime_helper_1
          pure (c, Sum.inl <| pf [ex, ey, ea, eb, etx, ety, px, py, p])
        else do
          let (c, ed) ← c d
          let (c, eu) ← c (x / d)
          let (c, ev) ← c (y / d)
          let (c, _, pu) ← prove_mul_nat c ed eu
          let (c, _, pv) ← prove_mul_nat c ed ev
          let (c, p) ← prove_lt_nat c (quote.1 1) ed
          pure (c, Sum.inr <| (quote.1 nat_not_coprime_helper).mk_app [ed, ex, ey, eu, ev, pu, pv, p])

/-- Evaluates the `gcd`, `lcm`, and `coprime` functions. -/
@[norm_num]
unsafe def eval_gcd : expr → tactic (expr × expr)
  | quote.1 (Nat.gcdₓ (%%ₓex) (%%ₓey)) => do
    let c ← mk_instance_cache (quote.1 ℕ)
    Prod.snd <$> prove_gcd_nat c ex ey
  | quote.1 (Nat.lcmₓ (%%ₓex) (%%ₓey)) => do
    let c ← mk_instance_cache (quote.1 ℕ)
    Prod.snd <$> prove_lcm_nat c ex ey
  | quote.1 (Nat.Coprime (%%ₓex) (%%ₓey)) => do
    let c ← mk_instance_cache (quote.1 ℕ)
    prove_coprime_nat c ex ey >>= Sum.elim true_intro false_intro ∘ Prod.snd
  | quote.1 (Int.gcdₓ (%%ₓex) (%%ₓey)) => do
    let zc ← mk_instance_cache (quote.1 ℤ)
    let nc ← mk_instance_cache (quote.1 ℕ)
    (Prod.snd ∘ Prod.snd) <$> prove_gcd_int zc nc ex ey
  | quote.1 (Int.lcm (%%ₓex) (%%ₓey)) => do
    let zc ← mk_instance_cache (quote.1 ℤ)
    let nc ← mk_instance_cache (quote.1 ℕ)
    (Prod.snd ∘ Prod.snd) <$> prove_lcm_int zc nc ex ey
  | _ => failed

end NormNum

end Tactic

