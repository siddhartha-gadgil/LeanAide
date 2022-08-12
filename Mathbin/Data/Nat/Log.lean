/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies
-/
import Mathbin.Data.Nat.Pow
import Mathbin.Tactic.ByContra

/-!
# Natural number logarithms

This file defines two `ℕ`-valued analogs of the logarithm of `n` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `b^k ≤ n`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ b^k`.

These are interesting because, for `1 < b`, `nat.log b` and `nat.clog b` are respectively right and
left adjoints of `nat.pow b`. See `pow_le_iff_le_log` and `le_pow_iff_clog_le`.
-/


namespace Nat

/-! ### Floor logarithm -/


/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
def log (b : ℕ) : ℕ → ℕ
  | n =>
    if h : b ≤ n ∧ 1 < b then
      have : n / b < n := div_lt_selfₓ ((zero_lt_one.trans h.2).trans_le h.1) h.2
      log (n / b) + 1
    else 0

private theorem log_eq_zero_aux {b n : ℕ} (hnb : n < b ∨ b ≤ 1) : log b n = 0 := by
  rw [or_iff_not_and_not, not_ltₓ, not_leₓ] at hnb
  rw [log, ← ite_not, if_pos hnb]

theorem log_of_lt {b n : ℕ} (hb : n < b) : log b n = 0 :=
  log_eq_zero_aux (Or.inl hb)

theorem log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n) : log b n = 0 :=
  log_eq_zero_aux (Or.inr hb)

theorem log_of_one_lt_of_le {b n : ℕ} (h : 1 < b) (hn : b ≤ n) : log b n = log b (n / b) + 1 := by
  rw [log]
  exact if_pos ⟨hn, h⟩

theorem log_eq_zero_iff {b n : ℕ} : log b n = 0 ↔ n < b ∨ b ≤ 1 :=
  ⟨fun h_log => by
    by_contra' h
    have := log_of_one_lt_of_le h.2 h.1
    rw [h_log] at this
    exact succ_ne_zero _ this.symm, log_eq_zero_aux⟩

theorem log_eq_one_iff {b n : ℕ} : log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b ≤ n := by
  -- This is best possible: if b = 2, n = 5, then 1 < b and b ≤ n but n > b * b.
  refine' ⟨fun h_log => _, _⟩
  · have bound : 1 < b ∧ b ≤ n := by
      contrapose h_log
      rw [not_and_distrib, not_ltₓ, not_leₓ, or_comm, ← log_eq_zero_iff] at h_log
      rw [h_log]
      exact Nat.zero_ne_one
    cases' bound with one_lt_b b_le_n
    refine' ⟨_, one_lt_b, b_le_n⟩
    rw [log_of_one_lt_of_le one_lt_b b_le_n, succ_inj', log_eq_zero_iff,
      Nat.div_lt_iff_lt_mulₓ (lt_transₓ zero_lt_one one_lt_b)] at h_log
    exact h_log.resolve_right fun b_small => lt_irreflₓ _ (lt_of_lt_of_leₓ one_lt_b b_small)
    
  · rintro ⟨h, one_lt_b, b_le_n⟩
    rw [log_of_one_lt_of_le one_lt_b b_le_n, succ_inj', log_eq_zero_iff,
      Nat.div_lt_iff_lt_mulₓ (lt_transₓ zero_lt_one one_lt_b)]
    exact Or.inl h
    

@[simp]
theorem log_zero_left : ∀ n, log 0 n = 0 :=
  log_of_left_le_one zero_le_one

@[simp]
theorem log_zero_right (b : ℕ) : log b 0 = 0 := by
  rw [log]
  cases b <;> rfl

@[simp]
theorem log_one_left : ∀ n, log 1 n = 0 :=
  log_of_left_le_one le_rfl

@[simp]
theorem log_one_right (b : ℕ) : log b 1 = 0 :=
  if h : b ≤ 1 then log_of_left_le_one h 1 else log_of_lt (not_leₓ.mp h)

/-- `pow b` and `log b` (almost) form a Galois connection. -/
theorem pow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : 0 < y) : b ^ x ≤ y ↔ x ≤ log b y := by
  induction' y using Nat.strong_induction_onₓ with y ih generalizing x
  cases x
  · exact iff_of_true hy (zero_le _)
    
  rw [log]
  split_ifs
  · have b_pos : 0 < b := zero_le_one.trans_lt hb
    rw [succ_eq_add_one, add_le_add_iff_right, ← ih (y / b) (div_lt_self hy hb) (Nat.div_pos h.1 b_pos),
      le_div_iff_mul_le b_pos, pow_succ'ₓ]
    
  · refine' iff_of_false (fun hby => h ⟨le_transₓ _ hby, hb⟩) (not_succ_le_zero _)
    convert pow_mono hb.le (zero_lt_succ x)
    exact (pow_oneₓ b).symm
    

theorem lt_pow_iff_log_lt {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : 0 < y) : y < b ^ x ↔ log b y < x :=
  lt_iff_lt_of_le_iff_le (pow_le_iff_le_log hb hy)

theorem log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) : log b (b ^ x) = x :=
  eq_of_forall_le_iff fun z => by
    rw [← pow_le_iff_le_log hb (pow_pos (zero_lt_one.trans hb) _)]
    exact (pow_right_strict_mono hb).le_iff_le

theorem log_pos {b n : ℕ} (hb : 1 < b) (hn : b ≤ n) : 0 < log b n := by
  rwa [← succ_le_iff, ← pow_le_iff_le_log hb (hb.le.trans hn), pow_oneₓ]

theorem log_mul_base (b n : ℕ) (hb : 1 < b) (hn : 0 < n) : log b (n * b) = log b n + 1 :=
  eq_of_forall_le_iff fun z => by
    cases z
    · simp
      
    have : 0 < b := zero_lt_one.trans hb
    rw [← pow_le_iff_le_log hb, pow_succ'ₓ, (strict_mono_mul_right_of_pos this).le_iff_le, pow_le_iff_le_log hb hn,
      Nat.succ_le_succ_iff]
    simp [← hn, ← this]

theorem lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) (x : ℕ) : x < b ^ (log b x).succ := by
  cases' x.eq_zero_or_pos with hx hx
  · simp only [← hx, ← log_zero_right, ← pow_oneₓ]
    exact pos_of_gt hb
    
  rw [← not_leₓ, pow_le_iff_le_log hb hx, not_leₓ]
  exact lt_succ_self _

theorem pow_log_le_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 0 < x) : b ^ log b x ≤ x :=
  (pow_le_iff_le_log hb hx).2 le_rfl

@[mono]
theorem log_mono_right {b n m : ℕ} (h : n ≤ m) : log b n ≤ log b m := by
  cases' le_or_ltₓ b 1 with hb hb
  · rw [log_of_left_le_one hb]
    exact zero_le _
    
  · cases' Nat.eq_zero_or_posₓ n with hn hn
    · rw [hn, log_zero_right]
      exact zero_le _
      
    · rw [← pow_le_iff_le_log hb (hn.trans_le h)]
      exact (pow_log_le_self hb hn).trans h
      
    

@[mono]
theorem log_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : log b n ≤ log c n := by
  cases n
  · rw [log_zero_right, log_zero_right]
    
  rw [← pow_le_iff_le_log hc (zero_lt_succ n)]
  calc c ^ log b n.succ ≤ b ^ log b n.succ := pow_le_pow_of_le_left (zero_lt_one.trans hc).le hb _ _ ≤ n.succ :=
      pow_log_le_self (hc.trans_le hb) (zero_lt_succ n)

theorem log_monotone {b : ℕ} : Monotone (log b) := fun x y => log_mono_right

theorem log_antitone_left {n : ℕ} : AntitoneOn (fun b => log b n) (Set.Ioi 1) := fun _ hc _ _ hb =>
  log_anti_left (Set.mem_Iio.1 hc) hb

@[simp]
theorem log_div_mul_self (b n : ℕ) : log b (n / b * b) = log b n :=
  eq_of_forall_le_iff fun z =>
    ⟨fun h => h.trans (log_monotone (div_mul_le_selfₓ _ _)), fun h => by
      rcases b with (_ | _ | b)
      · rwa [log_zero_left] at *
        
      · rwa [log_one_left] at *
        
      rcases n.zero_le.eq_or_lt with (rfl | hn)
      · rwa [Nat.zero_divₓ, zero_mul]
        
      cases' le_or_ltₓ b.succ.succ n with hb hb
      · cases z
        · apply zero_le
          
        rw [← pow_le_iff_le_log, pow_succ'ₓ] at h⊢
        · rwa [(strict_mono_mul_right_of_pos Nat.succ_pos').le_iff_le, Nat.le_div_iff_mul_leₓ Nat.succ_pos']
          
        all_goals
          simp [← hn, ← Nat.div_pos hb Nat.succ_pos']
        
      · simpa [← div_eq_of_lt, ← hb, ← log_of_lt] using h
        ⟩

@[simp]
theorem log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 := by
  cases' lt_or_leₓ n b with h h
  · rw [div_eq_of_lt h, log_of_lt h, log_zero_right]
    
  rcases n.zero_le.eq_or_lt with (rfl | hn)
  · rw [Nat.zero_divₓ, log_zero_right]
    
  rcases b with (_ | _ | b)
  · rw [log_zero_left, log_zero_left]
    
  · rw [log_one_left, log_one_left]
    
  rw [← succ_inj', ← succ_inj']
  simp_rw [succ_eq_add_one]
  rw [Nat.sub_add_cancelₓ, ← log_mul_base] <;>
    · simp [← succ_le_iff, ← log_pos, ← h, ← Nat.div_pos]
      

private theorem add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1) / b < n := by
  rw [div_lt_iff_lt_mul (zero_lt_one.trans hb), ← succ_le_iff, ← pred_eq_sub_one,
    succ_pred_eq_of_pos (add_pos (zero_lt_one.trans hn) (zero_lt_one.trans hb))]
  exact add_le_mul hn hb

/-! ### Ceil logarithm -/


/-- `clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
def clog (b : ℕ) : ℕ → ℕ
  | n =>
    if h : 1 < b ∧ 1 < n then
      have : (n + b - 1) / b < n := add_pred_div_lt h.1 h.2
      clog ((n + b - 1) / b) + 1
    else 0

theorem clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : ℕ) : clog b n = 0 := by
  rw [clog, if_neg fun h : 1 < b ∧ 1 < n => h.1.not_le hb]

theorem clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 := by
  rw [clog, if_neg fun h : 1 < b ∧ 1 < n => h.2.not_le hn]

@[simp]
theorem clog_zero_left (n : ℕ) : clog 0 n = 0 :=
  clog_of_left_le_one zero_le_one _

@[simp]
theorem clog_zero_right (b : ℕ) : clog b 0 = 0 :=
  clog_of_right_le_one zero_le_one _

@[simp]
theorem clog_one_left (n : ℕ) : clog 1 n = 0 :=
  clog_of_left_le_one le_rfl _

@[simp]
theorem clog_one_right (b : ℕ) : clog b 1 = 0 :=
  clog_of_right_le_one le_rfl _

theorem clog_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : clog b n = clog b ((n + b - 1) / b) + 1 := by
  rw [clog, if_pos (⟨hb, hn⟩ : 1 < b ∧ 1 < n)]

theorem clog_pos {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : 0 < clog b n := by
  rw [clog_of_two_le hb hn]
  exact zero_lt_succ _

theorem clog_eq_one {b n : ℕ} (hn : 2 ≤ n) (h : n ≤ b) : clog b n = 1 := by
  rw [clog_of_two_le (hn.trans h) hn, clog_of_right_le_one]
  have n_pos : 0 < n := zero_lt_two.trans_le hn
  rw [← lt_succ_iff, Nat.div_lt_iff_lt_mulₓ (n_pos.trans_le h), ← succ_le_iff, ← pred_eq_sub_one,
    succ_pred_eq_of_pos (add_pos n_pos (n_pos.trans_le h)), succ_mul, one_mulₓ]
  exact add_le_add_right h _

/-- `clog b` and `pow b` form a Galois connection. -/
theorem le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x y : ℕ} : x ≤ b ^ y ↔ clog b x ≤ y := by
  induction' x using Nat.strong_induction_onₓ with x ih generalizing y
  cases y
  · rw [pow_zeroₓ]
    refine' ⟨fun h => (clog_of_right_le_one h b).le, _⟩
    simp_rw [← not_ltₓ]
    contrapose!
    exact clog_pos hb
    
  have b_pos : 0 < b := zero_lt_two.trans_le hb
  rw [clog]
  split_ifs
  · rw [succ_eq_add_one, add_le_add_iff_right, ← ih ((x + b - 1) / b) (add_pred_div_lt hb h.2),
      Nat.div_le_iff_le_mul_add_pred b_pos, ← pow_succₓ, add_tsub_assoc_of_le (Nat.succ_le_of_ltₓ b_pos),
      add_le_add_iff_right]
    
  · exact iff_of_true ((not_ltₓ.1 (not_and.1 h hb)).trans <| succ_le_of_lt <| pow_pos b_pos _) (zero_le _)
    

theorem pow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x y : ℕ} : b ^ y < x ↔ y < clog b x :=
  lt_iff_lt_of_le_iff_le (le_pow_iff_clog_le hb)

theorem clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
  eq_of_forall_ge_iff fun z => by
    rw [← le_pow_iff_clog_le hb]
    exact (pow_right_strict_mono hb).le_iff_le

theorem pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 1 < x) : b ^ (clog b x).pred < x := by
  rw [← not_leₓ, le_pow_iff_clog_le hb, not_leₓ]
  exact pred_lt (clog_pos hb hx).ne'

theorem le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x :=
  (le_pow_iff_clog_le hb).2 le_rfl

@[mono]
theorem clog_mono_right (b : ℕ) {n m : ℕ} (h : n ≤ m) : clog b n ≤ clog b m := by
  cases' le_or_ltₓ b 1 with hb hb
  · rw [clog_of_left_le_one hb]
    exact zero_le _
    
  · rw [← le_pow_iff_clog_le hb]
    exact h.trans (le_pow_clog hb _)
    

@[mono]
theorem clog_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n := by
  rw [← le_pow_iff_clog_le (lt_of_lt_of_leₓ hc hb)]
  calc n ≤ c ^ clog c n := le_pow_clog hc _ _ ≤ b ^ clog c n := pow_le_pow_of_le_left (zero_lt_one.trans hc).le hb _

theorem clog_monotone (b : ℕ) : Monotone (clog b) := fun x y => clog_mono_right _

theorem clog_antitone_left {n : ℕ} : AntitoneOn (fun b : ℕ => clog b n) (Set.Ioi 1) := fun _ hc _ _ hb =>
  clog_anti_left (Set.mem_Iio.1 hc) hb

theorem log_le_clog (b n : ℕ) : log b n ≤ clog b n := by
  obtain hb | hb := le_or_ltₓ b 1
  · rw [log_of_left_le_one hb]
    exact zero_le _
    
  cases n
  · rw [log_zero_right]
    exact zero_le _
    
  exact (pow_right_strict_mono hb).le_iff_le.1 ((pow_log_le_self hb <| succ_pos _).trans <| le_pow_clog hb _)

end Nat

