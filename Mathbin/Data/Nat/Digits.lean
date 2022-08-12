/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam, Mario Carneiro
-/
import Mathbin.Data.Int.Modeq
import Mathbin.Data.Nat.Log
import Mathbin.Data.Nat.Parity
import Mathbin.Data.List.Indexes
import Mathbin.Data.List.Palindrome
import Mathbin.Tactic.IntervalCases
import Mathbin.Tactic.Linarith.Default

/-!
# Digits of a natural number

This provides a basic API for extracting the digits of a natural number in a given base,
and reconstructing numbers from their digits.

We also prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

A basic `norm_digits` tactic is also provided for proving goals of the form
`nat.digits a b = l` where `a` and `b` are numerals.
-/


namespace Nat

variable {n : ℕ}

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digitsAux0 : ℕ → List ℕ
  | 0 => []
  | n + 1 => [n + 1]

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digitsAux1 (n : ℕ) : List ℕ :=
  List.repeat 1 n

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digitsAux (b : ℕ) (h : 2 ≤ b) : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    have : (n + 1) / b < n + 1 := Nat.div_lt_selfₓ (Nat.succ_posₓ _) h
    (n + 1) % b :: digits_aux ((n + 1) / b)

@[simp]
theorem digits_aux_zero (b : ℕ) (h : 2 ≤ b) : digitsAux b h 0 = [] := by
  rw [digits_aux]

theorem digits_aux_def (b : ℕ) (h : 2 ≤ b) (n : ℕ) (w : 0 < n) : digitsAux b h n = n % b :: digitsAux b h (n / b) := by
  cases n
  · cases w
    
  · rw [digits_aux]
    

/-- `digits b n` gives the digits, in little-endian order,
of a natural number `n` in a specified base `b`.

In any base, we have `of_digits b L = L.foldr (λ x y, x + b * y) 0`.
* For any `2 ≤ b`, we have `l < b` for any `l ∈ digits b n`,
  and the last digit is not zero.
  This uniquely specifies the behaviour of `digits b`.
* For `b = 1`, we define `digits 1 n = list.repeat 1 n`.
* For `b = 0`, we define `digits 0 n = [n]`, except `digits 0 0 = []`.

Note this differs from the existing `nat.to_digits` in core, which is used for printing numerals.
In particular, `nat.to_digits b 0 = [0]`, while `digits b 0 = []`.
-/
def digits : ℕ → ℕ → List ℕ
  | 0 => digitsAux0
  | 1 => digitsAux1
  | b + 2 =>
    digitsAux (b + 2)
      (by
        norm_num)

@[simp]
theorem digits_zero (b : ℕ) : digits b 0 = [] := by
  rcases b with (_ | ⟨_ | ⟨_⟩⟩) <;> simp [← digits, ← digits_aux_0, ← digits_aux_1]

@[simp]
theorem digits_zero_zero : digits 0 0 = [] :=
  rfl

@[simp]
theorem digits_zero_succ (n : ℕ) : digits 0 n.succ = [n + 1] :=
  rfl

theorem digits_zero_succ' : ∀ {n : ℕ} (w : 0 < n), digits 0 n = [n]
  | 0, h =>
    absurd h
      (by
        decide)
  | n + 1, _ => rfl

@[simp]
theorem digits_one (n : ℕ) : digits 1 n = List.repeat 1 n :=
  rfl

@[simp]
theorem digits_one_succ (n : ℕ) : digits 1 (n + 1) = 1 :: digits 1 n :=
  rfl

@[simp]
theorem digits_add_two_add_one (b n : ℕ) :
    digits (b + 2) (n + 1) = (n + 1) % (b + 2) :: digits (b + 2) ((n + 1) / (b + 2)) := by
  rw [digits, digits_aux_def]
  exact succ_pos n

theorem digits_def' : ∀ {b : ℕ} (h : 2 ≤ b) {n : ℕ} (w : 0 < n), digits b n = n % b :: digits b (n / b)
  | 0, h =>
    absurd h
      (by
        decide)
  | 1, h =>
    absurd h
      (by
        decide)
  | b + 2, h => digits_aux_def _ _

@[simp]
theorem digits_of_lt (b x : ℕ) (w₁ : 0 < x) (w₂ : x < b) : digits b x = [x] := by
  cases b
  · cases w₂
    
  · cases b
    · interval_cases x
      
    · cases x
      · cases w₁
        
      · rw [digits_add_two_add_one, Nat.div_eq_of_ltₓ w₂, digits_zero, Nat.mod_eq_of_ltₓ w₂]
        
      
    

theorem digits_add (b : ℕ) (h : 2 ≤ b) (x y : ℕ) (w : x < b) (w' : 0 < x ∨ 0 < y) :
    digits b (x + b * y) = x :: digits b y := by
  cases b
  · cases h
    
  · cases b
    · norm_num  at h
      
    · cases y
      · norm_num  at w'
        simp [← w, ← w']
        
      dsimp' [← digits]
      rw [digits_aux_def]
      · congr
        · simp [← Nat.add_modₓ, ← Nat.mod_eq_of_ltₓ w]
          
        · simp [← mul_comm (b + 2), ← Nat.add_mul_div_rightₓ, ← Nat.div_eq_of_ltₓ w]
          
        
      · apply Nat.succ_posₓ
        
      
    

/-- `of_digits b L` takes a list `L` of natural numbers, and interprets them
as a number in semiring, as the little-endian digits in base `b`.
-/
-- If we had a function converting a list into a polynomial,
-- and appropriate lemmas about that function,
-- we could rewrite this in terms of that.
def ofDigits {α : Type _} [Semiringₓ α] (b : α) : List ℕ → α
  | [] => 0
  | h :: t => h + b * of_digits t

theorem of_digits_eq_foldr {α : Type _} [Semiringₓ α] (b : α) (L : List ℕ) :
    ofDigits b L = L.foldr (fun x y => x + b * y) 0 := by
  induction' L with d L ih
  · rfl
    
  · dsimp' [← of_digits]
    rw [ih]
    

theorem of_digits_eq_sum_map_with_index_aux (b : ℕ) (l : List ℕ) :
    ((List.range l.length).zipWith ((fun i a : ℕ => a * b ^ i) ∘ succ) l).Sum =
      b * ((List.range l.length).zipWith (fun i a => a * b ^ i) l).Sum :=
  by
  suffices
    (List.range l.length).zipWith ((fun i a : ℕ => a * b ^ i) ∘ succ) l =
      (List.range l.length).zipWith (fun i a => b * (a * b ^ i)) l
    by
    simp [← this]
  congr
  ext
  simp [← pow_succₓ]
  ring

theorem of_digits_eq_sum_map_with_index (b : ℕ) (L : List ℕ) :
    ofDigits b L = (L.mapWithIndex fun i a => a * b ^ i).Sum := by
  rw [List.map_with_index_eq_enum_map, List.enum_eq_zip_range, List.map_uncurry_zip_eq_zip_with, of_digits_eq_foldr]
  induction' L with hd tl hl
  · simp
    
  · simpa [← List.range_succ_eq_map, ← List.zip_with_map_left, ← of_digits_eq_sum_map_with_index_aux] using Or.inl hl
    

@[simp]
theorem of_digits_singleton {b n : ℕ} : ofDigits b [n] = n := by
  simp [← of_digits]

@[simp]
theorem of_digits_one_cons {α : Type _} [Semiringₓ α] (h : ℕ) (L : List ℕ) :
    ofDigits (1 : α) (h :: L) = h + ofDigits 1 L := by
  simp [← of_digits]

theorem of_digits_append {b : ℕ} {l1 l2 : List ℕ} :
    ofDigits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2 := by
  induction' l1 with hd tl IH
  · simp [← of_digits]
    
  · rw [of_digits, List.cons_append, of_digits, IH, List.length_cons, pow_succ'ₓ]
    ring
    

@[norm_cast]
theorem coe_of_digits (α : Type _) [Semiringₓ α] (b : ℕ) (L : List ℕ) : ((ofDigits b L : ℕ) : α) = ofDigits (b : α) L :=
  by
  induction' L with d L ih
  · simp [← of_digits]
    
  · dsimp' [← of_digits]
    push_cast
    rw [ih]
    

@[norm_cast]
theorem coe_int_of_digits (b : ℕ) (L : List ℕ) : ((ofDigits b L : ℕ) : ℤ) = ofDigits (b : ℤ) L := by
  induction' L with d L ih
  · rfl
    
  · dsimp' [← of_digits]
    push_cast
    

theorem digits_zero_of_eq_zero {b : ℕ} (h : 1 ≤ b) {L : List ℕ} (w : ofDigits b L = 0) : ∀, ∀ l ∈ L, ∀, l = 0 := by
  induction' L with d L ih
  · intro l m
    cases m
    
  · intro l m
    dsimp' [← of_digits]  at w
    rcases m with ⟨rfl⟩
    · apply Nat.eq_zero_of_add_eq_zero_right w
      
    · exact ih ((Nat.mul_right_inj h).mp (Nat.eq_zero_of_add_eq_zero_left w)) _ m
      
    

theorem digits_of_digits (b : ℕ) (h : 2 ≤ b) (L : List ℕ) (w₁ : ∀, ∀ l ∈ L, ∀, l < b)
    (w₂ : ∀ h : L ≠ [], L.last h ≠ 0) : digits b (ofDigits b L) = L := by
  induction' L with d L ih
  · dsimp' [← of_digits]
    simp
    
  · dsimp' [← of_digits]
    replace w₂ :=
      w₂
        (by
          simp )
    rw [digits_add b h]
    · rw [ih]
      · intro l m
        apply w₁
        exact List.mem_cons_of_memₓ _ m
        
      · intro h
        · rw [List.last_cons h] at w₂
          convert w₂
          
        
      
    · exact w₁ d (List.mem_cons_selfₓ _ _)
      
    · by_cases' h' : L = []
      · rcases h' with rfl
        simp at w₂
        left
        apply Nat.pos_of_ne_zeroₓ
        exact w₂
        
      · right
        apply Nat.pos_of_ne_zeroₓ
        contrapose! w₂
        apply digits_zero_of_eq_zero _ w₂
        · rw [List.last_cons h']
          exact List.last_mem h'
          
        · exact le_of_ltₓ h
          
        
      
    

theorem of_digits_digits (b n : ℕ) : ofDigits b (digits b n) = n := by
  cases' b with b
  · cases' n with n
    · rfl
      
    · change of_digits 0 [n + 1] = n + 1
      dsimp' [← of_digits]
      simp
      
    
  · cases' b with b
    · induction' n with n ih
      · rfl
        
      · simp only [← ih, ← add_commₓ 1, ← of_digits_one_cons, ← Nat.cast_id, ← digits_one_succ]
        
      
    · apply Nat.strong_induction_onₓ n _
      clear n
      intro n h
      cases n
      · rw [digits_zero]
        rfl
        
      · simp only [← Nat.succ_eq_add_one, ← digits_add_two_add_one]
        dsimp' [← of_digits]
        rw [h _ (Nat.div_lt_self' n b)]
        rw [Nat.mod_add_divₓ]
        
      
    

theorem of_digits_one (L : List ℕ) : ofDigits 1 L = L.Sum := by
  induction' L with d L ih
  · rfl
    
  · simp [← of_digits, ← List.sum_cons, ← ih]
    

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `of_digits`.
-/


theorem digits_eq_nil_iff_eq_zero {b n : ℕ} : digits b n = [] ↔ n = 0 := by
  constructor
  · intro h
    have : of_digits b (digits b n) = of_digits b [] := by
      rw [h]
    convert this
    rw [of_digits_digits]
    
  · rintro rfl
    simp
    

theorem digits_ne_nil_iff_ne_zero {b n : ℕ} : digits b n ≠ [] ↔ n ≠ 0 :=
  not_congr digits_eq_nil_iff_eq_zero

theorem digits_eq_cons_digits_div {b n : ℕ} (h : 2 ≤ b) (w : 0 < n) : digits b n = n % b :: digits b (n / b) := by
  rcases b with (_ | _ | b)
  · rw [digits_zero_succ' w, Nat.mod_zeroₓ, Nat.div_zeroₓ, Nat.digits_zero_zero]
    
  · norm_num  at h
    
  rcases n with (_ | n)
  · norm_num  at w
    
  simp

theorem digits_last {b : ℕ} (m : ℕ) (h : 2 ≤ b) (p q) : (digits b m).last p = (digits b (m / b)).last q := by
  by_cases' hm : m = 0
  · simp [← hm]
    
  simp only [← digits_eq_cons_digits_div h (Nat.pos_of_ne_zeroₓ hm)]
  rw [List.last_cons]

theorem digits.injective (b : ℕ) : Function.Injective b.digits :=
  Function.LeftInverse.injective (of_digits_digits b)

@[simp]
theorem digits_inj_iff {b n m : ℕ} : b.digits n = b.digits m ↔ n = m :=
  (digits.injective b).eq_iff

theorem digits_len (b n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) : (b.digits n).length = b.log n + 1 := by
  induction' n using Nat.strong_induction_onₓ with n IH
  rw [digits_eq_cons_digits_div hb hn, List.length]
  cases' (n / b).eq_zero_or_pos with h h
  · have posb : 0 < b := zero_lt_two.trans_le hb
    simp [← h, ← log_eq_zero_iff, Nat.div_eq_zero_iff posb]
    
  · have hb' : 1 < b := one_lt_two.trans_le hb
    have : n / b < n := div_lt_self hn hb'
    rw [IH _ this h, log_div_base, tsub_add_cancel_of_le]
    rw [succ_le_iff]
    refine' log_pos hb' _
    contrapose! h
    rw [div_eq_of_lt h]
    

theorem last_digit_ne_zero (b : ℕ) {m : ℕ} (hm : m ≠ 0) : (digits b m).last (digits_ne_nil_iff_ne_zero.mpr hm) ≠ 0 := by
  rcases b with (_ | _ | b)
  · cases m
    · cases hm rfl
      
    · simp
      
    
  · cases m
    · cases hm rfl
      
    simp_rw [digits_one, List.last_repeat_succ 1 m]
    norm_num
    
  revert hm
  apply Nat.strong_induction_onₓ m
  intro n IH hn
  have hnpos : 0 < n := Nat.pos_of_ne_zeroₓ hn
  by_cases' hnb : n < b + 2
  · simp_rw [digits_of_lt b.succ.succ n hnpos hnb]
    exact pos_iff_ne_zero.mp hnpos
    
  · rw
      [digits_last n
        (show 2 ≤ b + 2 by
          decide)]
    refine'
      IH _
        (Nat.div_lt_selfₓ hnpos
          (by
            decide))
        _
    · rw [← pos_iff_ne_zero]
      exact
        Nat.div_pos (le_of_not_ltₓ hnb)
          (by
            decide)
      
    

/-- The digits in the base b+2 expansion of n are all less than b+2 -/
theorem digits_lt_base' {b m : ℕ} : ∀ {d}, d ∈ digits (b + 2) m → d < b + 2 := by
  apply Nat.strong_induction_onₓ m
  intro n IH d hd
  cases' n with n
  · rw [digits_zero] at hd
    cases hd
    
  -- base b+2 expansion of 0 has no digits
  rw [digits_add_two_add_one] at hd
  cases hd
  · rw [hd]
    exact
      n.succ.mod_lt
        (by
          linarith)
    
  · exact
      IH _
        (Nat.div_lt_selfₓ (Nat.succ_posₓ _)
          (by
            linarith))
        hd
    

/-- The digits in the base b expansion of n are all less than b, if b ≥ 2 -/
theorem digits_lt_base {b m d : ℕ} (hb : 2 ≤ b) (hd : d ∈ digits b m) : d < b := by
  rcases b with (_ | _ | b) <;>
    try
      linarith
  exact digits_lt_base' hd

/-- an n-digit number in base b + 2 is less than (b + 2)^n -/
theorem of_digits_lt_base_pow_length' {b : ℕ} {l : List ℕ} (hl : ∀, ∀ x ∈ l, ∀, x < b + 2) :
    ofDigits (b + 2) l < (b + 2) ^ l.length := by
  induction' l with hd tl IH
  · simp [← of_digits]
    
  · rw [of_digits, List.length_cons, pow_succₓ]
    have : (of_digits (b + 2) tl + 1) * (b + 2) ≤ (b + 2) ^ tl.length * (b + 2) :=
      mul_le_mul (IH fun x hx => hl _ (List.mem_cons_of_memₓ _ hx))
        (by
          rfl)
        (by
          decide)
        (Nat.zero_leₓ _)
    suffices ↑hd < b + 2 by
      linarith
    norm_cast
    exact hl hd (List.mem_cons_selfₓ _ _)
    

/-- an n-digit number in base b is less than b^n if b ≥ 2 -/
theorem of_digits_lt_base_pow_length {b : ℕ} {l : List ℕ} (hb : 2 ≤ b) (hl : ∀, ∀ x ∈ l, ∀, x < b) :
    ofDigits b l < b ^ l.length := by
  rcases b with (_ | _ | b) <;>
    try
      linarith
  exact of_digits_lt_base_pow_length' hl

/-- Any number m is less than (b+2)^(number of digits in the base b + 2 representation of m) -/
theorem lt_base_pow_length_digits' {b m : ℕ} : m < (b + 2) ^ (digits (b + 2) m).length := by
  convert of_digits_lt_base_pow_length' fun _ => digits_lt_base'
  rw [of_digits_digits (b + 2) m]

/-- Any number m is less than b^(number of digits in the base b representation of m) -/
theorem lt_base_pow_length_digits {b m : ℕ} (hb : 2 ≤ b) : m < b ^ (digits b m).length := by
  rcases b with (_ | _ | b) <;>
    try
      linarith
  exact lt_base_pow_length_digits'

theorem of_digits_digits_append_digits {b m n : ℕ} :
    ofDigits b (digits b n ++ digits b m) = n + b ^ (digits b n).length * m := by
  rw [of_digits_append, of_digits_digits, of_digits_digits]

theorem digits_len_le_digits_len_succ (b n : ℕ) : (digits b n).length ≤ (digits b (n + 1)).length := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
    
  cases' lt_or_leₓ b 2 with hb hb
  · rcases b with (_ | _ | b)
    · simp [← digits_zero_succ', ← hn]
      
    · simp
      
    · simpa [← succ_lt_succ_iff] using hb
      
    
  simpa [← digits_len, ← hb, ← hn] using log_mono_right (le_succ _)

theorem le_digits_len_le (b n m : ℕ) (h : n ≤ m) : (digits b n).length ≤ (digits b m).length :=
  monotone_nat_of_le_succ (digits_len_le_digits_len_succ b) h

theorem pow_length_le_mul_of_digits {b : ℕ} {l : List ℕ} (hl : l ≠ []) (hl2 : l.last hl ≠ 0) :
    (b + 2) ^ l.length ≤ (b + 2) * ofDigits (b + 2) l := by
  rw [← List.init_append_last hl]
  simp only [← List.length_append, ← List.length, ← zero_addₓ, ← List.length_init, ← of_digits_append, ←
    List.length_init, ← of_digits_singleton, ← add_commₓ (l.length - 1), ← pow_addₓ, ← pow_oneₓ]
  apply Nat.mul_le_mul_leftₓ
  refine' le_transₓ _ (Nat.le_add_leftₓ _ _)
  have : 0 < l.last hl := by
    rwa [pos_iff_ne_zero]
  convert Nat.mul_le_mul_leftₓ _ this
  rw [mul_oneₓ]

/-- Any non-zero natural number `m` is greater than
(b+2)^((number of digits in the base (b+2) representation of m) - 1)
-/
theorem base_pow_length_digits_le' (b m : ℕ) (hm : m ≠ 0) : (b + 2) ^ (digits (b + 2) m).length ≤ (b + 2) * m := by
  have : digits (b + 2) m ≠ [] := digits_ne_nil_iff_ne_zero.mpr hm
  convert pow_length_le_mul_of_digits this (last_digit_ne_zero _ hm)
  rwa [of_digits_digits]

/-- Any non-zero natural number `m` is greater than
b^((number of digits in the base b representation of m) - 1)
-/
theorem base_pow_length_digits_le (b m : ℕ) (hb : 2 ≤ b) : m ≠ 0 → b ^ (digits b m).length ≤ b * m := by
  rcases b with (_ | _ | b) <;>
    try
      linarith
  exact base_pow_length_digits_le' b m

/-! ### Modular Arithmetic -/


-- This is really a theorem about polynomials.
theorem dvd_of_digits_sub_of_digits {α : Type _} [CommRingₓ α] {a b k : α} (h : k ∣ a - b) (L : List ℕ) :
    k ∣ ofDigits a L - ofDigits b L := by
  induction' L with d L ih
  · change k ∣ 0 - 0
    simp
    
  · simp only [← of_digits, ← add_sub_add_left_eq_sub]
    exact dvd_mul_sub_mul h ih
    

theorem of_digits_modeq' (b b' : ℕ) (k : ℕ) (h : b ≡ b' [MOD k]) (L : List ℕ) : ofDigits b L ≡ ofDigits b' L [MOD k] :=
  by
  induction' L with d L ih
  · rfl
    
  · dsimp' [← of_digits]
    dsimp' [← Nat.Modeq]  at *
    conv_lhs => rw [Nat.add_modₓ, Nat.mul_modₓ, h, ih]
    conv_rhs => rw [Nat.add_modₓ, Nat.mul_modₓ]
    

theorem of_digits_modeq (b k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [MOD k] :=
  of_digits_modeq' b (b % k) k (b.mod_modeq k).symm L

theorem of_digits_mod (b k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  of_digits_modeq b k L

theorem of_digits_zmodeq' (b b' : ℤ) (k : ℕ) (h : b ≡ b' [ZMOD k]) (L : List ℕ) :
    ofDigits b L ≡ ofDigits b' L [ZMOD k] := by
  induction' L with d L ih
  · rfl
    
  · dsimp' [← of_digits]
    dsimp' [← Int.Modeq]  at *
    conv_lhs => rw [Int.add_mod, Int.mul_mod, h, ih]
    conv_rhs => rw [Int.add_mod, Int.mul_mod]
    

theorem of_digits_zmodeq (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [ZMOD k] :=
  of_digits_zmodeq' b (b % k) k (b.mod_modeq ↑k).symm L

theorem of_digits_zmod (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  of_digits_zmodeq b k L

theorem modeq_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) : n ≡ (digits b' n).Sum [MOD b] := by
  rw [← of_digits_one]
  conv => congr skip rw [← of_digits_digits b' n]
  convert of_digits_modeq _ _ _
  exact h.symm

theorem modeq_three_digits_sum (n : ℕ) : n ≡ (digits 10 n).Sum [MOD 3] :=
  modeq_digits_sum 3 10
    (by
      norm_num)
    n

theorem modeq_nine_digits_sum (n : ℕ) : n ≡ (digits 10 n).Sum [MOD 9] :=
  modeq_digits_sum 9 10
    (by
      norm_num)
    n

theorem zmodeq_of_digits_digits (b b' : ℕ) (c : ℤ) (h : b' ≡ c [ZMOD b]) (n : ℕ) :
    n ≡ ofDigits c (digits b' n) [ZMOD b] := by
  conv => congr skip rw [← of_digits_digits b' n]
  rw [coe_int_of_digits]
  apply of_digits_zmodeq' _ _ _ h

theorem of_digits_neg_one : ∀ L : List ℕ, ofDigits (-1 : ℤ) L = (L.map fun n : ℕ => (n : ℤ)).alternatingSum
  | [] => rfl
  | [n] => by
    simp [← of_digits, ← List.alternatingSum]
  | a :: b :: t => by
    simp only [← of_digits, ← List.alternatingSum, ← List.map_cons, ← of_digits_neg_one t]
    ring

theorem modeq_eleven_digits_sum (n : ℕ) : n ≡ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum [ZMOD 11] := by
  have t :=
    zmodeq_of_digits_digits 11 10 (-1 : ℤ)
      (by
        unfold Int.Modeq <;> norm_num)
      n
  rwa [of_digits_neg_one] at t

/-! ## Divisibility  -/


theorem dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) : b ∣ n ↔ b ∣ (digits b' n).Sum := by
  rw [← of_digits_one]
  conv_lhs => rw [← of_digits_digits b' n]
  rw [Nat.dvd_iff_mod_eq_zeroₓ, Nat.dvd_iff_mod_eq_zeroₓ, of_digits_mod, h]

/-- **Divisibility by 3 Rule** -/
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).Sum :=
  dvd_iff_dvd_digits_sum 3 10
    (by
      norm_num)
    n

theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ (digits 10 n).Sum :=
  dvd_iff_dvd_digits_sum 9 10
    (by
      norm_num)
    n

theorem dvd_iff_dvd_of_digits (b b' : ℕ) (c : ℤ) (h : (b : ℤ) ∣ (b' : ℤ) - c) (n : ℕ) :
    b ∣ n ↔ (b : ℤ) ∣ ofDigits c (digits b' n) := by
  rw [← Int.coe_nat_dvd]
  exact dvd_iff_dvd_of_dvd_sub (zmodeq_of_digits_digits b b' c (Int.modeq_iff_dvd.2 h).symm _).symm.Dvd

theorem eleven_dvd_iff : 11 ∣ n ↔ (11 : ℤ) ∣ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum := by
  have t :=
    dvd_iff_dvd_of_digits 11 10 (-1 : ℤ)
      (by
        norm_num)
      n
  rw [of_digits_neg_one] at t
  exact t

theorem eleven_dvd_of_palindrome (p : (digits 10 n).Palindrome) (h : Even (digits 10 n).length) : 11 ∣ n := by
  let dig := (digits 10 n).map (coe : ℕ → ℤ)
  replace h : Even dig.length := by
    rwa [List.length_mapₓ]
  refine' eleven_dvd_iff.2 ⟨0, (_ : dig.alternating_sum = 0)⟩
  have := dig.alternating_sum_reverse
  rw [(p.map _).reverse_eq, pow_succₓ, h.neg_one_pow, mul_oneₓ, neg_one_zsmul] at this
  exact eq_zero_of_neg_eq this.symm

/-! ### `norm_digits` tactic -/


namespace NormDigits

theorem digits_succ (b n m r l) (e : r + b * m = n) (hr : r < b) (h : Nat.digits b m = l ∧ 2 ≤ b ∧ 0 < m) :
    Nat.digits b n = r :: l ∧ 2 ≤ b ∧ 0 < n := by
  rcases h with ⟨h, b2, m0⟩
  have b0 : 0 < b := by
    linarith
  have n0 : 0 < n := by
    linarith [mul_pos b0 m0]
  refine' ⟨_, b2, n0⟩
  obtain ⟨rfl, rfl⟩ := (Nat.div_mod_unique b0).2 ⟨e, hr⟩
  subst h
  exact Nat.digits_def' b2 n0

theorem digits_one (b n) (n0 : 0 < n) (nb : n < b) : Nat.digits b n = [n] ∧ 2 ≤ b ∧ 0 < n := by
  have b2 : 2 ≤ b := by
    linarith
  refine' ⟨_, b2, n0⟩
  rw [Nat.digits_def' b2 n0, Nat.mod_eq_of_ltₓ nb,
    (Nat.div_eq_zero_iff
          (by
            linarith : 0 < b)).2
      nb,
    Nat.digits_zero]

open Tactic

/-- Helper function for the `norm_digits` tactic. -/
unsafe def eval_aux (eb : expr) (b : ℕ) : expr → ℕ → instance_cache → tactic (instance_cache × expr × expr)
  | en, n, ic => do
    let m := n / b
    let r := n % b
    let (ic, er) ← ic.ofNat r
    let (ic, pr) ← norm_num.prove_lt_nat ic er eb
    if m = 0 then do
        let (_, pn0) ← norm_num.prove_pos ic en
        return (ic, quote.1 ([%%ₓen] : List Nat), quote.1 (digits_one (%%ₓeb) (%%ₓen) (%%ₓpn0) (%%ₓpr)))
      else do
        let em ← expr.of_nat (quote.1 ℕ) m
        let (_, pe) ← norm_num.derive (quote.1 ((%%ₓer) + (%%ₓeb) * %%ₓem : ℕ))
        let (ic, el, p) ← eval_aux em m ic
        return
            (ic, quote.1 (@List.cons ℕ (%%ₓer) (%%ₓel)),
              quote.1 (digits_succ (%%ₓeb) (%%ₓen) (%%ₓem) (%%ₓer) (%%ₓel) (%%ₓpe) (%%ₓpr) (%%ₓp)))

/-- A tactic for normalizing expressions of the form `nat.digits a b = l` where
`a` and `b` are numerals.

```
example : nat.digits 10 123 = [3,2,1] := by norm_num
```
-/
@[norm_num]
unsafe def eval : expr → tactic (expr × expr)
  | quote.1 (Nat.digits (%%ₓeb) (%%ₓen)) => do
    let b ← expr.to_nat eb
    let n ← expr.to_nat en
    if n = 0 then return (quote.1 ([] : List ℕ), quote.1 (Nat.digits_zero (%%ₓeb)))
      else
        if b = 0 then do
          let ic ← mk_instance_cache (quote.1 ℕ)
          let (_, pn0) ← norm_num.prove_pos ic en
          return (quote.1 ([%%ₓen] : List ℕ), quote.1 (@Nat.digits_zero_succ' (%%ₓen) (%%ₓpn0)))
        else
          if b = 1 then do
            let ic ← mk_instance_cache (quote.1 ℕ)
            let (_, pn0) ← norm_num.prove_pos ic en
            let s ← simp_lemmas.add_simp simp_lemmas.mk `list.repeat
            let (rhs, p2, _) ← simplify s [] (quote.1 (List.repeat 1 (%%ₓen)))
            let p ← mk_eq_trans (quote.1 (Nat.digits_one (%%ₓen))) p2
            return (rhs, p)
          else do
            let ic ← mk_instance_cache (quote.1 ℕ)
            let (_, l, p) ← eval_aux eb b en n ic
            let p ← mk_app `` And.left [p]
            return (l, p)
  | _ => failed

end NormDigits

end Nat

