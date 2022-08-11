/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathbin.Algebra.GroupPower.Order
import Mathbin.Algebra.BigOperators.Basic

/-!
# Definitions and properties of `gcd`, `lcm`, and `coprime`

-/


namespace Nat

/-! ### `gcd` -/


theorem gcd_dvdₓ (m n : ℕ) : gcdₓ m n ∣ m ∧ gcdₓ m n ∣ n :=
  gcdₓ.induction m n
    (fun n => by
      rw [gcd_zero_left] <;> exact ⟨dvd_zero n, dvd_refl n⟩)
    fun m n npos => by
    rw [← gcd_rec] <;> exact fun ⟨IH₁, IH₂⟩ => ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩

theorem gcd_dvd_leftₓ (m n : ℕ) : gcdₓ m n ∣ m :=
  (gcd_dvdₓ m n).left

theorem gcd_dvd_rightₓ (m n : ℕ) : gcdₓ m n ∣ n :=
  (gcd_dvdₓ m n).right

theorem gcd_le_leftₓ {m} (n) (h : 0 < m) : gcdₓ m n ≤ m :=
  le_of_dvdₓ h <| gcd_dvd_leftₓ m n

theorem gcd_le_rightₓ (m) {n} (h : 0 < n) : gcdₓ m n ≤ n :=
  le_of_dvdₓ h <| gcd_dvd_rightₓ m n

theorem dvd_gcdₓ {m n k : ℕ} : k ∣ m → k ∣ n → k ∣ gcdₓ m n :=
  gcdₓ.induction m n
    (fun n _ kn => by
      rw [gcd_zero_left] <;> exact kn)
    fun n m mpos IH H1 H2 => by
    rw [gcd_rec] <;> exact IH ((dvd_mod_iff H1).2 H2) H1

theorem dvd_gcd_iffₓ {m n k : ℕ} : k ∣ gcdₓ m n ↔ k ∣ m ∧ k ∣ n :=
  Iff.intro (fun h => ⟨h.trans (gcd_dvdₓ m n).left, h.trans (gcd_dvdₓ m n).right⟩) fun h => dvd_gcdₓ h.left h.right

theorem gcd_commₓ (m n : ℕ) : gcdₓ m n = gcdₓ n m :=
  dvd_antisymm (dvd_gcdₓ (gcd_dvd_rightₓ m n) (gcd_dvd_leftₓ m n)) (dvd_gcdₓ (gcd_dvd_rightₓ n m) (gcd_dvd_leftₓ n m))

theorem gcd_eq_left_iff_dvdₓ {m n : ℕ} : m ∣ n ↔ gcdₓ m n = m :=
  ⟨fun h => by
    rw [gcd_rec, mod_eq_zero_of_dvd h, gcd_zero_left], fun h => h ▸ gcd_dvd_rightₓ m n⟩

theorem gcd_eq_right_iff_dvdₓ {m n : ℕ} : m ∣ n ↔ gcdₓ n m = m := by
  rw [gcd_comm] <;> apply gcd_eq_left_iff_dvd

theorem gcd_assocₓ (m n k : ℕ) : gcdₓ (gcdₓ m n) k = gcdₓ m (gcdₓ n k) :=
  dvd_antisymm
    (dvd_gcdₓ ((gcd_dvd_leftₓ (gcdₓ m n) k).trans (gcd_dvd_leftₓ m n))
      (dvd_gcdₓ ((gcd_dvd_leftₓ (gcdₓ m n) k).trans (gcd_dvd_rightₓ m n)) (gcd_dvd_rightₓ (gcdₓ m n) k)))
    (dvd_gcdₓ (dvd_gcdₓ (gcd_dvd_leftₓ m (gcdₓ n k)) ((gcd_dvd_rightₓ m (gcdₓ n k)).trans (gcd_dvd_leftₓ n k)))
      ((gcd_dvd_rightₓ m (gcdₓ n k)).trans (gcd_dvd_rightₓ n k)))

@[simp]
theorem gcd_one_rightₓ (n : ℕ) : gcdₓ n 1 = 1 :=
  Eq.trans (gcd_commₓ n 1) <| gcd_one_leftₓ n

theorem gcd_mul_leftₓ (m n k : ℕ) : gcdₓ (m * n) (m * k) = m * gcdₓ n k :=
  gcdₓ.induction n k
    (fun k => by
      repeat'
        first |
          rw [mul_zero]|
          rw [gcd_zero_left])
    fun k n H IH => by
    rwa [← mul_mod_mul_left, ← gcd_rec, ← gcd_rec] at IH

theorem gcd_mul_rightₓ (m n k : ℕ) : gcdₓ (m * n) (k * n) = gcdₓ m k * n := by
  rw [mul_comm m n, mul_comm k n, mul_comm (gcd m k) n, gcd_mul_left]

theorem gcd_pos_of_pos_leftₓ {m : ℕ} (n : ℕ) (mpos : 0 < m) : 0 < gcdₓ m n :=
  pos_of_dvd_of_posₓ (gcd_dvd_leftₓ m n) mpos

theorem gcd_pos_of_pos_rightₓ (m : ℕ) {n : ℕ} (npos : 0 < n) : 0 < gcdₓ m n :=
  pos_of_dvd_of_posₓ (gcd_dvd_rightₓ m n) npos

theorem eq_zero_of_gcd_eq_zero_leftₓ {m n : ℕ} (H : gcdₓ m n = 0) : m = 0 :=
  Or.elim (Nat.eq_zero_or_posₓ m) id fun H1 : 0 < m => absurd (Eq.symm H) (ne_of_ltₓ (gcd_pos_of_pos_leftₓ _ H1))

theorem eq_zero_of_gcd_eq_zero_rightₓ {m n : ℕ} (H : gcdₓ m n = 0) : n = 0 := by
  rw [gcd_comm] at H <;> exact eq_zero_of_gcd_eq_zero_left H

@[simp]
theorem gcd_eq_zero_iffₓ {i j : ℕ} : gcdₓ i j = 0 ↔ i = 0 ∧ j = 0 := by
  constructor
  · intro h
    exact ⟨eq_zero_of_gcd_eq_zero_left h, eq_zero_of_gcd_eq_zero_right h⟩
    
  · rintro ⟨rfl, rfl⟩
    exact Nat.gcd_zero_rightₓ 0
    

theorem gcd_divₓ {m n k : ℕ} (H1 : k ∣ m) (H2 : k ∣ n) : gcdₓ (m / k) (n / k) = gcdₓ m n / k :=
  Or.elim (Nat.eq_zero_or_posₓ k)
    (fun k0 => by
      rw [k0, Nat.div_zeroₓ, Nat.div_zeroₓ, Nat.div_zeroₓ, gcd_zero_right])
    fun H3 =>
    Nat.eq_of_mul_eq_mul_rightₓ H3 <| by
      rw [Nat.div_mul_cancelₓ (dvd_gcd H1 H2), ← gcd_mul_right, Nat.div_mul_cancelₓ H1, Nat.div_mul_cancelₓ H2]

theorem gcd_greatest {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : ℕ, e ∣ a → e ∣ b → e ∣ d) : d = a.gcd b :=
  (dvd_antisymm (hd _ (gcd_dvd_leftₓ a b) (gcd_dvd_rightₓ a b)) (dvd_gcdₓ hda hdb)).symm

theorem gcd_dvd_gcd_of_dvd_leftₓ {m k : ℕ} (n : ℕ) (H : m ∣ k) : gcdₓ m n ∣ gcdₓ k n :=
  dvd_gcdₓ ((gcd_dvd_leftₓ m n).trans H) (gcd_dvd_rightₓ m n)

theorem gcd_dvd_gcd_of_dvd_rightₓ {m k : ℕ} (n : ℕ) (H : m ∣ k) : gcdₓ n m ∣ gcdₓ n k :=
  dvd_gcdₓ (gcd_dvd_leftₓ n m) ((gcd_dvd_rightₓ n m).trans H)

theorem gcd_dvd_gcd_mul_leftₓ (m n k : ℕ) : gcdₓ m n ∣ gcdₓ (k * m) n :=
  gcd_dvd_gcd_of_dvd_leftₓ _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_rightₓ (m n k : ℕ) : gcdₓ m n ∣ gcdₓ (m * k) n :=
  gcd_dvd_gcd_of_dvd_leftₓ _ (dvd_mul_right _ _)

theorem gcd_dvd_gcd_mul_left_rightₓ (m n k : ℕ) : gcdₓ m n ∣ gcdₓ m (k * n) :=
  gcd_dvd_gcd_of_dvd_rightₓ _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_rightₓ (m n k : ℕ) : gcdₓ m n ∣ gcdₓ m (n * k) :=
  gcd_dvd_gcd_of_dvd_rightₓ _ (dvd_mul_right _ _)

theorem gcd_eq_leftₓ {m n : ℕ} (H : m ∣ n) : gcdₓ m n = m :=
  dvd_antisymm (gcd_dvd_leftₓ _ _) (dvd_gcdₓ dvd_rfl H)

theorem gcd_eq_rightₓ {m n : ℕ} (H : n ∣ m) : gcdₓ m n = n := by
  rw [gcd_comm, gcd_eq_left H]

-- Lemmas where one argument is a multiple of the other
@[simp]
theorem gcd_mul_left_leftₓ (m n : ℕ) : gcdₓ (m * n) n = n :=
  dvd_antisymm (gcd_dvd_rightₓ _ _) (dvd_gcdₓ (dvd_mul_left _ _) dvd_rfl)

@[simp]
theorem gcd_mul_left_rightₓ (m n : ℕ) : gcdₓ n (m * n) = n := by
  rw [gcd_comm, gcd_mul_left_left]

@[simp]
theorem gcd_mul_right_leftₓ (m n : ℕ) : gcdₓ (n * m) n = n := by
  rw [mul_comm, gcd_mul_left_left]

@[simp]
theorem gcd_mul_right_rightₓ (m n : ℕ) : gcdₓ n (n * m) = n := by
  rw [gcd_comm, gcd_mul_right_left]

-- Lemmas for repeated application of `gcd`
@[simp]
theorem gcd_gcd_self_right_leftₓ (m n : ℕ) : gcdₓ m (gcdₓ m n) = gcdₓ m n :=
  dvd_antisymm (gcd_dvd_rightₓ _ _) (dvd_gcdₓ (gcd_dvd_leftₓ _ _) dvd_rfl)

@[simp]
theorem gcd_gcd_self_right_rightₓ (m n : ℕ) : gcdₓ m (gcdₓ n m) = gcdₓ n m := by
  rw [gcd_comm n m, gcd_gcd_self_right_left]

@[simp]
theorem gcd_gcd_self_left_rightₓ (m n : ℕ) : gcdₓ (gcdₓ n m) m = gcdₓ n m := by
  rw [gcd_comm, gcd_gcd_self_right_right]

@[simp]
theorem gcd_gcd_self_left_leftₓ (m n : ℕ) : gcdₓ (gcdₓ m n) m = gcdₓ m n := by
  rw [gcd_comm m n, gcd_gcd_self_left_right]

-- Lemmas where one argument consists of addition of a multiple of the other
@[simp]
theorem gcd_add_mul_right_right (m n k : ℕ) : gcdₓ m (n + k * m) = gcdₓ m n := by
  simp [← gcd_rec m (n + k * m), ← gcd_rec m n]

@[simp]
theorem gcd_add_mul_left_right (m n k : ℕ) : gcdₓ m (n + m * k) = gcdₓ m n := by
  simp [← gcd_rec m (n + m * k), ← gcd_rec m n]

@[simp]
theorem gcd_mul_right_add_right (m n k : ℕ) : gcdₓ m (k * m + n) = gcdₓ m n := by
  simp [← add_commₓ _ n]

@[simp]
theorem gcd_mul_left_add_right (m n k : ℕ) : gcdₓ m (m * k + n) = gcdₓ m n := by
  simp [← add_commₓ _ n]

@[simp]
theorem gcd_add_mul_right_left (m n k : ℕ) : gcdₓ (m + k * n) n = gcdₓ m n := by
  rw [gcd_comm, gcd_add_mul_right_right, gcd_comm]

@[simp]
theorem gcd_add_mul_left_left (m n k : ℕ) : gcdₓ (m + n * k) n = gcdₓ m n := by
  rw [gcd_comm, gcd_add_mul_left_right, gcd_comm]

@[simp]
theorem gcd_mul_right_add_left (m n k : ℕ) : gcdₓ (k * n + m) n = gcdₓ m n := by
  rw [gcd_comm, gcd_mul_right_add_right, gcd_comm]

@[simp]
theorem gcd_mul_left_add_left (m n k : ℕ) : gcdₓ (n * k + m) n = gcdₓ m n := by
  rw [gcd_comm, gcd_mul_left_add_right, gcd_comm]

-- Lemmas where one argument consists of an addition of the other
@[simp]
theorem gcd_add_self_right (m n : ℕ) : gcdₓ m (n + m) = gcdₓ m n :=
  Eq.trans
    (by
      rw [one_mulₓ])
    (gcd_add_mul_right_right m n 1)

@[simp]
theorem gcd_add_self_left (m n : ℕ) : gcdₓ (m + n) n = gcdₓ m n := by
  rw [gcd_comm, gcd_add_self_right, gcd_comm]

@[simp]
theorem gcd_self_add_left (m n : ℕ) : gcdₓ (m + n) m = gcdₓ n m := by
  rw [add_commₓ, gcd_add_self_left]

@[simp]
theorem gcd_self_add_right (m n : ℕ) : gcdₓ m (m + n) = gcdₓ m n := by
  rw [add_commₓ, gcd_add_self_right]

/-! ### `lcm` -/


theorem lcm_commₓ (m n : ℕ) : lcmₓ m n = lcmₓ n m := by
  delta' lcm <;> rw [mul_comm, gcd_comm]

@[simp]
theorem lcm_zero_leftₓ (m : ℕ) : lcmₓ 0 m = 0 := by
  delta' lcm <;> rw [zero_mul, Nat.zero_divₓ]

@[simp]
theorem lcm_zero_rightₓ (m : ℕ) : lcmₓ m 0 = 0 :=
  lcm_commₓ 0 m ▸ lcm_zero_leftₓ m

@[simp]
theorem lcm_one_leftₓ (m : ℕ) : lcmₓ 1 m = m := by
  delta' lcm <;> rw [one_mulₓ, gcd_one_left, Nat.div_oneₓ]

@[simp]
theorem lcm_one_rightₓ (m : ℕ) : lcmₓ m 1 = m :=
  lcm_commₓ 1 m ▸ lcm_one_leftₓ m

@[simp]
theorem lcm_selfₓ (m : ℕ) : lcmₓ m m = m :=
  Or.elim (Nat.eq_zero_or_posₓ m)
    (fun h => by
      rw [h, lcm_zero_left])
    fun h => by
    delta' lcm <;> rw [gcd_self, Nat.mul_div_cancelₓ _ h]

theorem dvd_lcm_leftₓ (m n : ℕ) : m ∣ lcmₓ m n :=
  Dvd.intro (n / gcdₓ m n) (Nat.mul_div_assocₓ _ <| gcd_dvd_rightₓ m n).symm

theorem dvd_lcm_rightₓ (m n : ℕ) : n ∣ lcmₓ m n :=
  lcm_commₓ n m ▸ dvd_lcm_leftₓ n m

theorem gcd_mul_lcmₓ (m n : ℕ) : gcdₓ m n * lcmₓ m n = m * n := by
  delta' lcm <;> rw [Nat.mul_div_cancel'ₓ ((gcd_dvd_left m n).trans (dvd_mul_right m n))]

theorem lcm_dvdₓ {m n k : ℕ} (H1 : m ∣ k) (H2 : n ∣ k) : lcmₓ m n ∣ k :=
  Or.elim (Nat.eq_zero_or_posₓ k)
    (fun h => by
      rw [h] <;> exact dvd_zero _)
    fun kpos =>
    dvd_of_mul_dvd_mul_leftₓ (gcd_pos_of_pos_leftₓ n (pos_of_dvd_of_posₓ H1 kpos)) <| by
      rw [gcd_mul_lcm, ← gcd_mul_right, mul_comm n k] <;> exact dvd_gcd (mul_dvd_mul_left _ H2) (mul_dvd_mul_right H1 _)

theorem lcm_dvd_mul (m n : ℕ) : lcmₓ m n ∣ m * n :=
  lcm_dvdₓ (dvd_mul_right _ _) (dvd_mul_left _ _)

theorem lcm_dvd_iff {m n k : ℕ} : lcmₓ m n ∣ k ↔ m ∣ k ∧ n ∣ k :=
  ⟨fun h => ⟨(dvd_lcm_leftₓ _ _).trans h, (dvd_lcm_rightₓ _ _).trans h⟩, and_imp.2 lcm_dvdₓ⟩

theorem lcm_assocₓ (m n k : ℕ) : lcmₓ (lcmₓ m n) k = lcmₓ m (lcmₓ n k) :=
  dvd_antisymm
    (lcm_dvdₓ (lcm_dvdₓ (dvd_lcm_leftₓ m (lcmₓ n k)) ((dvd_lcm_leftₓ n k).trans (dvd_lcm_rightₓ m (lcmₓ n k))))
      ((dvd_lcm_rightₓ n k).trans (dvd_lcm_rightₓ m (lcmₓ n k))))
    (lcm_dvdₓ ((dvd_lcm_leftₓ m n).trans (dvd_lcm_leftₓ (lcmₓ m n) k))
      (lcm_dvdₓ ((dvd_lcm_rightₓ m n).trans (dvd_lcm_leftₓ (lcmₓ m n) k)) (dvd_lcm_rightₓ (lcmₓ m n) k)))

theorem lcm_ne_zeroₓ {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : lcmₓ m n ≠ 0 := by
  intro h
  simpa [← h, ← hm, ← hn] using gcd_mul_lcm m n

/-!
### `coprime`

See also `nat.coprime_of_dvd` and `nat.coprime_of_dvd'` to prove `nat.coprime m n`.
-/


instance (m n : ℕ) : Decidable (Coprime m n) := by
  unfold coprime <;> infer_instance

theorem coprime_iff_gcd_eq_oneₓ {m n : ℕ} : Coprime m n ↔ gcdₓ m n = 1 :=
  Iff.rfl

theorem Coprime.gcd_eq_one {m n : ℕ} (h : Coprime m n) : gcdₓ m n = 1 :=
  h

theorem Coprime.lcm_eq_mul {m n : ℕ} (h : Coprime m n) : lcmₓ m n = m * n := by
  rw [← one_mulₓ (lcm m n), ← h.gcd_eq_one, gcd_mul_lcm]

theorem Coprime.symm {m n : ℕ} : Coprime n m → Coprime m n :=
  (gcd_commₓ m n).trans

theorem coprime_commₓ {m n : ℕ} : Coprime n m ↔ Coprime m n :=
  ⟨Coprime.symm, Coprime.symm⟩

theorem Coprime.symmetric : Symmetric Coprime := fun m n => Coprime.symm

theorem Coprime.dvd_of_dvd_mul_right {m n k : ℕ} (H1 : Coprime k n) (H2 : k ∣ m * n) : k ∣ m := by
  let t := dvd_gcdₓ (dvd_mul_left k m) H2
  rwa [gcd_mul_left, H1.gcd_eq_one, mul_oneₓ] at t

theorem Coprime.dvd_of_dvd_mul_left {m n k : ℕ} (H1 : Coprime k m) (H2 : k ∣ m * n) : k ∣ n := by
  rw [mul_comm] at H2 <;> exact H1.dvd_of_dvd_mul_right H2

theorem Coprime.dvd_mul_right {m n k : ℕ} (H : Coprime k n) : k ∣ m * n ↔ k ∣ m :=
  ⟨H.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h n⟩

theorem Coprime.dvd_mul_left {m n k : ℕ} (H : Coprime k m) : k ∣ m * n ↔ k ∣ n :=
  ⟨H.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h m⟩

theorem Coprime.gcd_mul_left_cancel {k : ℕ} (m : ℕ) {n : ℕ} (H : Coprime k n) : gcdₓ (k * m) n = gcdₓ m n :=
  have H1 : Coprime (gcdₓ (k * m) n) k := by
    rw [coprime, gcd_assoc, H.symm.gcd_eq_one, gcd_one_right]
  dvd_antisymm (dvd_gcdₓ (H1.dvd_of_dvd_mul_left (gcd_dvd_leftₓ _ _)) (gcd_dvd_rightₓ _ _))
    (gcd_dvd_gcd_mul_leftₓ _ _ _)

theorem Coprime.gcd_mul_right_cancel (m : ℕ) {k n : ℕ} (H : Coprime k n) : gcdₓ (m * k) n = gcdₓ m n := by
  rw [mul_comm m k, H.gcd_mul_left_cancel m]

theorem Coprime.gcd_mul_left_cancel_right {k m : ℕ} (n : ℕ) (H : Coprime k m) : gcdₓ m (k * n) = gcdₓ m n := by
  rw [gcd_comm m n, gcd_comm m (k * n), H.gcd_mul_left_cancel n]

theorem Coprime.gcd_mul_right_cancel_right {k m : ℕ} (n : ℕ) (H : Coprime k m) : gcdₓ m (n * k) = gcdₓ m n := by
  rw [mul_comm n k, H.gcd_mul_left_cancel_right n]

theorem coprime_div_gcd_div_gcdₓ {m n : ℕ} (H : 0 < gcdₓ m n) : Coprime (m / gcdₓ m n) (n / gcdₓ m n) := by
  rw [coprime_iff_gcd_eq_one, gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), Nat.div_selfₓ H]

theorem not_coprime_of_dvd_of_dvdₓ {m n d : ℕ} (dgt1 : 1 < d) (Hm : d ∣ m) (Hn : d ∣ n) : ¬Coprime m n := fun co =>
  not_lt_of_geₓ
    (le_of_dvdₓ zero_lt_one <| by
      rw [← co.gcd_eq_one] <;> exact dvd_gcd Hm Hn)
    dgt1

theorem exists_coprimeₓ {m n : ℕ} (H : 0 < gcdₓ m n) : ∃ m' n', Coprime m' n' ∧ m = m' * gcdₓ m n ∧ n = n' * gcdₓ m n :=
  ⟨_, _, coprime_div_gcd_div_gcdₓ H, (Nat.div_mul_cancelₓ (gcd_dvd_leftₓ m n)).symm,
    (Nat.div_mul_cancelₓ (gcd_dvd_rightₓ m n)).symm⟩

theorem exists_coprime'ₓ {m n : ℕ} (H : 0 < gcdₓ m n) : ∃ g m' n', 0 < g ∧ Coprime m' n' ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_coprimeₓ H
  ⟨_, m', n', H, h⟩

@[simp]
theorem coprime_add_self_right {m n : ℕ} : Coprime m (n + m) ↔ Coprime m n := by
  rw [coprime, coprime, gcd_add_self_right]

@[simp]
theorem coprime_self_add_right {m n : ℕ} : Coprime m (m + n) ↔ Coprime m n := by
  rw [add_commₓ, coprime_add_self_right]

@[simp]
theorem coprime_add_self_left {m n : ℕ} : Coprime (m + n) n ↔ Coprime m n := by
  rw [coprime, coprime, gcd_add_self_left]

@[simp]
theorem coprime_self_add_left {m n : ℕ} : Coprime (m + n) m ↔ Coprime n m := by
  rw [coprime, coprime, gcd_self_add_left]

@[simp]
theorem coprime_add_mul_right_right (m n k : ℕ) : Coprime m (n + k * m) ↔ Coprime m n := by
  rw [coprime, coprime, gcd_add_mul_right_right]

@[simp]
theorem coprime_add_mul_left_right (m n k : ℕ) : Coprime m (n + m * k) ↔ Coprime m n := by
  rw [coprime, coprime, gcd_add_mul_left_right]

@[simp]
theorem coprime_mul_right_add_right (m n k : ℕ) : Coprime m (k * m + n) ↔ Coprime m n := by
  rw [coprime, coprime, gcd_mul_right_add_right]

@[simp]
theorem coprime_mul_left_add_right (m n k : ℕ) : Coprime m (m * k + n) ↔ Coprime m n := by
  rw [coprime, coprime, gcd_mul_left_add_right]

@[simp]
theorem coprime_add_mul_right_left (m n k : ℕ) : Coprime (m + k * n) n ↔ Coprime m n := by
  rw [coprime, coprime, gcd_add_mul_right_left]

@[simp]
theorem coprime_add_mul_left_left (m n k : ℕ) : Coprime (m + n * k) n ↔ Coprime m n := by
  rw [coprime, coprime, gcd_add_mul_left_left]

@[simp]
theorem coprime_mul_right_add_left (m n k : ℕ) : Coprime (k * n + m) n ↔ Coprime m n := by
  rw [coprime, coprime, gcd_mul_right_add_left]

@[simp]
theorem coprime_mul_left_add_left (m n k : ℕ) : Coprime (n * k + m) n ↔ Coprime m n := by
  rw [coprime, coprime, gcd_mul_left_add_left]

theorem Coprime.mul {m n k : ℕ} (H1 : Coprime m k) (H2 : Coprime n k) : Coprime (m * n) k :=
  (H1.gcd_mul_left_cancel n).trans H2

theorem Coprime.mul_right {k m n : ℕ} (H1 : Coprime k m) (H2 : Coprime k n) : Coprime k (m * n) :=
  (H1.symm.mul H2.symm).symm

theorem Coprime.coprime_dvd_left {m k n : ℕ} (H1 : m ∣ k) (H2 : Coprime k n) : Coprime m n :=
  eq_one_of_dvd_one
    (by
      delta' coprime  at H2 <;> rw [← H2] <;> exact gcd_dvd_gcd_of_dvd_left _ H1)

theorem Coprime.coprime_dvd_right {m k n : ℕ} (H1 : n ∣ m) (H2 : Coprime k m) : Coprime k n :=
  (H2.symm.coprime_dvd_left H1).symm

theorem Coprime.coprime_mul_left {k m n : ℕ} (H : Coprime (k * m) n) : Coprime m n :=
  H.coprime_dvd_left (dvd_mul_left _ _)

theorem Coprime.coprime_mul_right {k m n : ℕ} (H : Coprime (m * k) n) : Coprime m n :=
  H.coprime_dvd_left (dvd_mul_right _ _)

theorem Coprime.coprime_mul_left_right {k m n : ℕ} (H : Coprime m (k * n)) : Coprime m n :=
  H.coprime_dvd_right (dvd_mul_left _ _)

theorem Coprime.coprime_mul_right_right {k m n : ℕ} (H : Coprime m (n * k)) : Coprime m n :=
  H.coprime_dvd_right (dvd_mul_right _ _)

theorem Coprime.coprime_div_left {m n a : ℕ} (cmn : Coprime m n) (dvd : a ∣ m) : Coprime (m / a) n := by
  by_cases' a_split : a = 0
  · subst a_split
    rw [zero_dvd_iff] at dvd
    simpa [← dvd] using cmn
    
  · rcases dvd with ⟨k, rfl⟩
    rw [Nat.mul_div_cancel_leftₓ _ (Nat.pos_of_ne_zeroₓ a_split)]
    exact coprime.coprime_mul_left cmn
    

theorem Coprime.coprime_div_right {m n a : ℕ} (cmn : Coprime m n) (dvd : a ∣ n) : Coprime m (n / a) :=
  (Coprime.coprime_div_left cmn.symm dvd).symm

theorem coprime_mul_iff_leftₓ {k m n : ℕ} : Coprime (m * n) k ↔ Coprime m k ∧ Coprime n k :=
  ⟨fun h => ⟨Coprime.coprime_mul_right h, Coprime.coprime_mul_left h⟩, fun ⟨h, _⟩ => by
    rwa [coprime_iff_gcd_eq_one, coprime.gcd_mul_left_cancel n h]⟩

theorem coprime_mul_iff_rightₓ {k m n : ℕ} : Coprime k (m * n) ↔ Coprime k m ∧ Coprime k n := by
  simpa only [← coprime_comm] using coprime_mul_iff_left

theorem Coprime.gcd_left (k : ℕ) {m n : ℕ} (hmn : Coprime m n) : Coprime (gcdₓ k m) n :=
  hmn.coprime_dvd_left <| gcd_dvd_rightₓ k m

theorem Coprime.gcd_right (k : ℕ) {m n : ℕ} (hmn : Coprime m n) : Coprime m (gcdₓ k n) :=
  hmn.coprime_dvd_right <| gcd_dvd_rightₓ k n

theorem Coprime.gcd_both (k l : ℕ) {m n : ℕ} (hmn : Coprime m n) : Coprime (gcdₓ k m) (gcdₓ l n) :=
  (hmn.gcd_left k).gcd_right l

theorem Coprime.mul_dvd_of_dvd_of_dvd {a n m : ℕ} (hmn : Coprime m n) (hm : m ∣ a) (hn : n ∣ a) : m * n ∣ a :=
  let ⟨k, hk⟩ := hm
  hk.symm ▸ mul_dvd_mul_left _ (hmn.symm.dvd_of_dvd_mul_left (hk ▸ hn))

theorem coprime_one_leftₓ : ∀ n, Coprime 1 n :=
  gcd_one_left

theorem coprime_one_rightₓ : ∀ n, Coprime n 1 :=
  gcd_one_right

theorem Coprime.pow_left {m k : ℕ} (n : ℕ) (H1 : Coprime m k) : Coprime (m ^ n) k :=
  Nat.recOn n (coprime_one_leftₓ _) fun n IH => H1.mul IH

theorem Coprime.pow_right {m k : ℕ} (n : ℕ) (H1 : Coprime k m) : Coprime k (m ^ n) :=
  (H1.symm.pow_left n).symm

theorem Coprime.pow {k l : ℕ} (m n : ℕ) (H1 : Coprime k l) : Coprime (k ^ m) (l ^ n) :=
  (H1.pow_left _).pow_right _

@[simp]
theorem coprime_pow_left_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) : Nat.Coprime (a ^ n) b ↔ Nat.Coprime a b := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero hn.ne'
  rw [pow_succₓ, Nat.coprime_mul_iff_leftₓ]
  exact ⟨And.left, fun hab => ⟨hab, hab.pow_left _⟩⟩

@[simp]
theorem coprime_pow_right_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) : Nat.Coprime a (b ^ n) ↔ Nat.Coprime a b := by
  rw [Nat.coprime_commₓ, coprime_pow_left_iff hn, Nat.coprime_commₓ]

theorem Coprime.eq_one_of_dvd {k m : ℕ} (H : Coprime k m) (d : k ∣ m) : k = 1 := by
  rw [← H.gcd_eq_one, gcd_eq_left d]

@[simp]
theorem coprime_zero_leftₓ (n : ℕ) : Coprime 0 n ↔ n = 1 := by
  simp [← coprime]

@[simp]
theorem coprime_zero_rightₓ (n : ℕ) : Coprime n 0 ↔ n = 1 := by
  simp [← coprime]

theorem not_coprime_zero_zero : ¬Coprime 0 0 := by
  simp

@[simp]
theorem coprime_one_left_iffₓ (n : ℕ) : Coprime 1 n ↔ True := by
  simp [← coprime]

@[simp]
theorem coprime_one_right_iffₓ (n : ℕ) : Coprime n 1 ↔ True := by
  simp [← coprime]

@[simp]
theorem coprime_selfₓ (n : ℕ) : Coprime n n ↔ n = 1 := by
  simp [← coprime]

theorem gcd_mul_of_coprime_of_dvd {a b c : ℕ} (hac : Coprime a c) (b_dvd_c : b ∣ c) : gcdₓ (a * b) c = b := by
  rcases exists_eq_mul_left_of_dvd b_dvd_c with ⟨d, rfl⟩
  rw [gcd_mul_right]
  convert one_mulₓ b
  exact coprime.coprime_mul_right_right hac

section BigOperators

open BigOperators

/-- See `is_coprime.prod_left` for the corresponding lemma about `is_coprime` -/
theorem coprime_prod_left {ι : Type _} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → Coprime (s i) x) → Coprime (∏ i : ι in t, s i) x :=
  Finset.prod_induction s (fun y => y.Coprime x) (fun a b => Coprime.mul)
    (by
      simp )

/-- See `is_coprime.prod_right` for the corresponding lemma about `is_coprime` -/
theorem coprime_prod_right {ι : Type _} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → Coprime x (s i)) → Coprime x (∏ i : ι in t, s i) :=
  Finset.prod_induction s (fun y => x.Coprime y) (fun a b => Coprime.mul_right)
    (by
      simp )

end BigOperators

theorem Coprime.eq_of_mul_eq_zero {m n : ℕ} (h : m.Coprime n) (hmn : m * n = 0) : m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 :=
  (Nat.eq_zero_of_mul_eq_zero hmn).imp (fun hm => ⟨hm, n.coprime_zero_left.mp <| hm ▸ h⟩) fun hn =>
    ⟨m.coprime_zero_left.mp <| hn ▸ h.symm, hn⟩

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`. -/
def prodDvdAndDvdOfDvdProd {m n k : ℕ} (H : k ∣ m * n) : { d : { m' // m' ∣ m } × { n' // n' ∣ n } // k = d.1 * d.2 } :=
  by
  cases h0 : gcd k m
  case nat.zero =>
    obtain rfl : k = 0 := eq_zero_of_gcd_eq_zero_left h0
    obtain rfl : m = 0 := eq_zero_of_gcd_eq_zero_right h0
    exact ⟨⟨⟨0, dvd_refl 0⟩, ⟨n, dvd_refl n⟩⟩, (zero_mul n).symm⟩
  case nat.succ tmp =>
    have hpos : 0 < gcd k m := h0.symm ▸ Nat.zero_lt_succₓ _ <;> clear h0 tmp
    have hd : gcd k m * (k / gcd k m) = k := Nat.mul_div_cancel'ₓ (gcd_dvd_left k m)
    refine' ⟨⟨⟨gcd k m, gcd_dvd_right k m⟩, ⟨k / gcd k m, _⟩⟩, hd.symm⟩
    apply dvd_of_mul_dvd_mul_left hpos
    rw [hd, ← gcd_mul_right]
    exact dvd_gcd (dvd_mul_right _ _) H

theorem gcd_mul_dvd_mul_gcdₓ (k m n : ℕ) : gcdₓ k (m * n) ∣ gcdₓ k m * gcdₓ k n := by
  rcases prod_dvd_and_dvd_of_dvd_prod <| gcd_dvd_right k (m * n) with ⟨⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩, h⟩
  replace h : gcd k (m * n) = m' * n' := h
  rw [h]
  have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _
  apply mul_dvd_mul
  · have hm'k : m' ∣ k := (dvd_mul_right m' n').trans hm'n'
    exact dvd_gcd hm'k hm'
    
  · have hn'k : n' ∣ k := (dvd_mul_left n' m').trans hm'n'
    exact dvd_gcd hn'k hn'
    

theorem Coprime.gcd_mul (k : ℕ) {m n : ℕ} (h : Coprime m n) : gcdₓ k (m * n) = gcdₓ k m * gcdₓ k n :=
  dvd_antisymm (gcd_mul_dvd_mul_gcdₓ k m n)
    ((h.gcd_both k k).mul_dvd_of_dvd_of_dvd (gcd_dvd_gcd_mul_right_rightₓ _ _ _) (gcd_dvd_gcd_mul_left_rightₓ _ _ _))

theorem pow_dvd_pow_iff {a b n : ℕ} (n0 : 0 < n) : a ^ n ∣ b ^ n ↔ a ∣ b := by
  refine' ⟨fun h => _, fun h => pow_dvd_pow_of_dvd h _⟩
  cases' Nat.eq_zero_or_posₓ (gcd a b) with g0 g0
  · simp [← eq_zero_of_gcd_eq_zero_right g0]
    
  rcases exists_coprime' g0 with ⟨g, a', b', g0', co, rfl, rfl⟩
  rw [mul_powₓ, mul_powₓ] at h
  replace h := dvd_of_mul_dvd_mul_right (pow_pos g0' _) h
  have := pow_dvd_pow a' n0
  rw [pow_oneₓ, (co.pow n n).eq_one_of_dvd h] at this
  simp [← eq_one_of_dvd_one this]

theorem gcd_mul_gcd_of_coprime_of_mul_eq_mulₓ {a b c d : ℕ} (cop : c.Coprime d) (h : a * b = c * d) :
    a.gcd c * b.gcd c = c := by
  apply dvd_antisymm
  · apply Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.mul (cop.gcd_left _) (cop.gcd_left _))
    rw [← h]
    apply mul_dvd_mul (gcd_dvd _ _).1 (gcd_dvd _ _).1
    
  · rw [gcd_comm a _, gcd_comm b _]
    trans c.gcd (a * b)
    rw [h, gcd_mul_right_right d c]
    apply gcd_mul_dvd_mul_gcd
    

/-- If `k:ℕ` divides coprime `a` and `b` then `k = 1` -/
theorem eq_one_of_dvd_coprimes {a b k : ℕ} (h_ab_coprime : Coprime a b) (hka : k ∣ a) (hkb : k ∣ b) : k = 1 := by
  rw [coprime_iff_gcd_eq_one] at h_ab_coprime
  have h1 := dvd_gcd hka hkb
  rw [h_ab_coprime] at h1
  exact nat.dvd_one.mp h1

theorem Coprime.mul_add_mul_ne_mul {m n a b : ℕ} (cop : Coprime m n) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * m + b * n ≠ m * n := by
  intro h
  obtain ⟨x, rfl⟩ : n ∣ a :=
    cop.symm.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_left (dvd_mul_left n b)).mpr ((congr_arg _ h).mpr (dvd_mul_left n m)))
  obtain ⟨y, rfl⟩ : m ∣ b :=
    cop.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_right (dvd_mul_left m (n * x))).mpr ((congr_arg _ h).mpr (dvd_mul_right m n)))
  rw [mul_comm, mul_ne_zero_iff, ← one_le_iff_ne_zero] at ha hb
  refine' mul_ne_zero hb.2 ha.2 (eq_zero_of_mul_eq_self_left (ne_of_gtₓ (add_le_add ha.1 hb.1)) _)
  rw [← mul_assoc, ← h, add_mulₓ, add_mulₓ, mul_comm _ n, ← mul_assoc, mul_comm y]

end Nat

