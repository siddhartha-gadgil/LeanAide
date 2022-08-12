/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Data.List.Func
import Mathbin.Tactic.Ring
import Mathbin.Tactic.Omega.Misc

/-
Non-constant terms of linear constraints are represented
by storing their coefficients in integer lists.
-/
namespace Omega

namespace Coeffs

open List.Func

variable {v : Nat → Int}

/-- `val_between v as l o` is the value (under valuation `v`) of the term
    obtained taking the term represented by `(0, as)` and dropping all
    subterms that include variables outside the range `[l,l+o)` -/
@[simp]
def valBetween (v : Nat → Int) (as : List Int) (l : Nat) : Nat → Int
  | 0 => 0
  | o + 1 => val_between o + get (l + o) as * v (l + o)

@[simp]
theorem val_between_nil {l : Nat} : ∀ m, valBetween v [] l m = 0
  | 0 => by
    simp only [← val_between]
  | m + 1 => by
    simp only [← val_between_nil m, ← Omega.Coeffs.valBetween, ← get_nil, ← zero_addₓ, ← zero_mul, ←
      Int.default_eq_zero]

/-- Evaluation of the nonconstant component of a normalized linear arithmetic term. -/
def val (v : Nat → Int) (as : List Int) : Int :=
  valBetween v as 0 as.length

@[simp]
theorem val_nil : val v [] = 0 :=
  rfl

theorem val_between_eq_of_le {as : List Int} {l : Nat} :
    ∀ m, as.length ≤ l + m → valBetween v as l m = valBetween v as l (as.length - l)
  | 0, h1 => by
    rw [add_zeroₓ] at h1
    rw [tsub_eq_zero_iff_le.mpr h1]
  | m + 1, h1 => by
    rw [le_iff_eq_or_lt] at h1
    cases h1
    · rw [h1, add_commₓ l, add_tsub_cancel_right]
      
    have h2 : List.length as ≤ l + m := by
      rw [← Nat.lt_succ_iffₓ]
      apply h1
    simpa [← get_eq_default_of_le _ h2, ← zero_mul, ← add_zeroₓ, ← val_between] using val_between_eq_of_le _ h2

theorem val_eq_of_le {as : List Int} {k : Nat} : as.length ≤ k → val v as = valBetween v as 0 k := by
  intro h1
  unfold val
  rw [val_between_eq_of_le k _]
  rfl
  rw [zero_addₓ]
  exact h1

theorem val_between_eq_val_between {v w : Nat → Int} {as bs : List Int} {l : Nat} :
    ∀ {m},
      (∀ x, l ≤ x → x < l + m → v x = w x) →
        (∀ x, l ≤ x → x < l + m → get x as = get x bs) → valBetween v as l m = valBetween w bs l m
  | 0, h1, h2 => rfl
  | m + 1, h1, h2 => by
    unfold val_between
    have h3 : l + m < l + (m + 1) := by
      rw [← add_assocₓ]
      apply lt_add_one
    apply fun_mono_2
    apply val_between_eq_val_between <;> intro x h4 h5
    · apply h1 _ h4 (lt_transₓ h5 h3)
      
    · apply h2 _ h4 (lt_transₓ h5 h3)
      
    rw [h1 _ _ h3, h2 _ _ h3] <;> apply Nat.le_add_rightₓ

open List.Func

theorem val_between_set {a : Int} {l n : Nat} : ∀ {m}, l ≤ n → n < l + m → valBetween v ([] {n ↦ a}) l m = a * v n
  | 0, h1, h2 => by
    exfalso
    apply lt_irreflₓ l (lt_of_le_of_ltₓ h1 h2)
  | m + 1, h1, h2 => by
    rw [← add_assocₓ, Nat.lt_succ_iffₓ, le_iff_eq_or_lt] at h2
    cases h2 <;> unfold val_between
    · have h3 : val_between v ([] {l + m ↦ a}) l m = 0 := by
        apply @Eq.trans _ _ (val_between v [] l m)
        · apply val_between_eq_val_between
          · intros
            rfl
            
          · intro x h4 h5
            rw [get_nil, get_set_eq_of_ne, get_nil]
            apply ne_of_ltₓ h5
            
          
        apply val_between_nil
      rw [h2]
      simp only [← h3, ← zero_addₓ, ← List.Func.get_set]
      
    · have h3 : l + m ≠ n := by
        apply ne_of_gtₓ h2
      rw [@val_between_set m h1 h2, get_set_eq_of_ne _ _ h3]
      simp only [← h3, ← get_nil, ← add_zeroₓ, ← zero_mul, ← Int.default_eq_zero]
      

@[simp]
theorem val_set {m : Nat} {a : Int} : val v ([] {m ↦ a}) = a * v m := by
  apply val_between_set
  apply zero_le
  apply lt_of_lt_of_leₓ (lt_add_one _)
  simp only [← length_set, ← zero_addₓ, ← le_max_rightₓ]
  infer_instance

theorem val_between_neg {as : List Int} {l : Nat} : ∀ {o}, valBetween v (neg as) l o = -valBetween v as l o
  | 0 => rfl
  | o + 1 => by
    unfold val_between
    rw [neg_add, neg_mul_eq_neg_mulₓ]
    apply fun_mono_2
    apply val_between_neg
    apply fun_mono_2 _ rfl
    apply get_neg

@[simp]
theorem val_neg {as : List Int} : val v (neg as) = -val v as := by
  simpa only [← val, ← length_neg] using val_between_neg

theorem val_between_add {is js : List Int} {l : Nat} :
    ∀ m, valBetween v (add is js) l m = valBetween v is l m + valBetween v js l m
  | 0 => rfl
  | m + 1 => by
    simp only [← val_between, ← val_between_add m, ← List.Func.get, ← get_add]
    ring

@[simp]
theorem val_add {is js : List Int} : val v (add is js) = val v is + val v js := by
  unfold val
  rw [val_between_add]
  apply fun_mono_2 <;> apply val_between_eq_of_le <;> rw [zero_addₓ, length_add]
  apply le_max_leftₓ
  apply le_max_rightₓ

theorem val_between_sub {is js : List Int} {l : Nat} :
    ∀ m, valBetween v (sub is js) l m = valBetween v is l m - valBetween v js l m
  | 0 => rfl
  | m + 1 => by
    simp only [← val_between, ← val_between_sub m, ← List.Func.get, ← get_sub]
    ring

@[simp]
theorem val_sub {is js : List Int} : val v (sub is js) = val v is - val v js := by
  unfold val
  rw [val_between_sub]
  apply fun_mono_2 <;> apply val_between_eq_of_le <;> rw [zero_addₓ, length_sub]
  apply le_max_leftₓ
  apply le_max_rightₓ

/-- `val_except k v as` is the value (under valuation `v`) of the term
    obtained taking the term represented by `(0, as)` and dropping the
    subterm that includes the `k`th variable. -/
def valExcept (k : Nat) (v : Nat → Int) (as) :=
  valBetween v as 0 k + valBetween v as (k + 1) (as.length - (k + 1))

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ≠ » k)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ≠ » k)
theorem val_except_eq_val_except {k : Nat} {is js : List Int} {v w : Nat → Int} :
    (∀ (x) (_ : x ≠ k), v x = w x) → (∀ (x) (_ : x ≠ k), get x is = get x js) → valExcept k v is = valExcept k w js :=
  by
  intro h1 h2
  unfold val_except
  apply fun_mono_2
  · apply val_between_eq_val_between <;>
      intro x h3 h4 <;>
          [· apply h1
            ,
          · apply h2
            ] <;>
        apply ne_of_ltₓ <;> rw [zero_addₓ] at h4 <;> apply h4
    
  · repeat'
      rw [← val_between_eq_of_le (max is.length js.length - (k + 1))]
    · apply val_between_eq_val_between <;>
        intro x h3 h4 <;>
            [· apply h1
              ,
            · apply h2
              ] <;>
          apply Ne.symm <;> apply ne_of_ltₓ <;> rw [Nat.lt_iff_add_one_le] <;> exact h3
      
    · refine' le_transₓ (le_max_rightₓ _ _) le_add_tsub
      
    · refine' le_transₓ (le_max_leftₓ _ _) le_add_tsub
      
    

open Omega

theorem val_except_update_set {n : Nat} {as : List Int} {i j : Int} :
    valExcept n (v ⟨n ↦ i⟩) (as {n ↦ j}) = valExcept n v as := by
  apply val_except_eq_val_except update_eq_of_ne (get_set_eq_of_ne _)

theorem val_between_add_val_between {as : List Int} {l m : Nat} :
    ∀ {n}, valBetween v as l m + valBetween v as (l + m) n = valBetween v as l (m + n)
  | 0 => by
    simp only [← val_between, ← add_zeroₓ]
  | n + 1 => by
    rw [← add_assocₓ]
    unfold val_between
    rw [add_assocₓ]
    rw [← @val_between_add_val_between n]
    ring

theorem val_except_add_eq (n : Nat) {as : List Int} : valExcept n v as + get n as * v n = val v as := by
  unfold val_except
  unfold val
  cases' le_totalₓ (n + 1) as.length with h1 h1
  · have h4 := @val_between_add_val_between v as 0 (n + 1) (as.length - (n + 1))
    have h5 : n + 1 + (as.length - (n + 1)) = as.length := by
      rw [add_commₓ, tsub_add_cancel_of_le h1]
    rw [h5] at h4
    apply Eq.trans _ h4
    simp only [← val_between, ← zero_addₓ]
    ring
    
  have h2 : List.length as - (n + 1) = 0 := tsub_eq_zero_iff_le.mpr h1
  have h3 : val_between v as 0 (List.length as) = val_between v as 0 (n + 1) := by
    simpa only [← val] using @val_eq_of_le v as (n + 1) h1
  simp only [← add_zeroₓ, ← val_between, ← zero_addₓ, ← h2, ← h3]

@[simp]
theorem val_between_map_mul {i : Int} {as : List Int} {l : Nat} :
    ∀ {m}, valBetween v (List.map ((· * ·) i) as) l m = i * valBetween v as l m
  | 0 => by
    simp only [← val_between, ← mul_zero, ← List.map]
  | m + 1 => by
    unfold val_between
    rw [@val_between_map_mul m, mul_addₓ]
    apply fun_mono_2 rfl
    by_cases' h1 : l + m < as.length
    · rw [get_map h1, mul_assoc]
      
    rw [not_ltₓ] at h1
    rw [get_eq_default_of_le, get_eq_default_of_le] <;>
      try
          simp <;>
        apply h1

theorem forall_val_dvd_of_forall_mem_dvd {i : Int} {as : List Int} : (∀, ∀ x ∈ as, ∀, i ∣ x) → ∀ n, i ∣ get n as
  | h1, n => by
    apply forall_val_of_forall_mem _ h1
    apply dvd_zero

theorem dvd_val_between {i} {as : List Int} {l : Nat} : ∀ {m}, (∀, ∀ x ∈ as, ∀, i ∣ x) → i ∣ valBetween v as l m
  | 0, h1 => dvd_zero _
  | m + 1, h1 => by
    unfold val_between
    apply dvd_add
    apply dvd_val_between h1
    apply dvd_mul_of_dvd_left
    by_cases' h2 : get (l + m) as = 0
    · rw [h2]
      apply dvd_zero
      
    apply h1
    apply mem_get_of_ne_zero h2

theorem dvd_val {as : List Int} {i : Int} : (∀, ∀ x ∈ as, ∀, i ∣ x) → i ∣ val v as := by
  apply dvd_val_between

@[simp]
theorem val_between_map_div {as : List Int} {i : Int} {l : Nat} (h1 : ∀, ∀ x ∈ as, ∀, i ∣ x) :
    ∀ {m}, valBetween v (List.map (fun x => x / i) as) l m = valBetween v as l m / i
  | 0 => by
    simp only [← Int.zero_div, ← val_between, ← List.map]
  | m + 1 => by
    unfold val_between
    rw [@val_between_map_div m, Int.add_div_of_dvd_right]
    apply fun_mono_2 rfl
    · apply
        calc
          get (l + m) (List.map (fun x : ℤ => x / i) as) * v (l + m) = get (l + m) as / i * v (l + m) := by
            apply fun_mono_2 _ rfl
            rw [get_map']
            apply Int.zero_div
          _ = get (l + m) as * v (l + m) / i := by
            repeat'
              rw [mul_comm _ (v (l + m))]
            rw [Int.mul_div_assoc]
            apply forall_val_dvd_of_forall_mem_dvd h1
          
      
    apply dvd_mul_of_dvd_left
    apply forall_val_dvd_of_forall_mem_dvd h1

@[simp]
theorem val_map_div {as : List Int} {i : Int} :
    (∀, ∀ x ∈ as, ∀, i ∣ x) → val v (List.map (fun x => x / i) as) = val v as / i := by
  intro h1
  simpa only [← val, ← List.length_mapₓ] using val_between_map_div h1

theorem val_between_eq_zero {is : List Int} {l : Nat} : ∀ {m}, (∀ x : Int, x ∈ is → x = 0) → valBetween v is l m = 0
  | 0, h1 => rfl
  | m + 1, h1 => by
    have h2 := @forall_val_of_forall_mem _ _ is (fun x => x = 0) rfl h1
    simpa only [← val_between, ← h2 (l + m), ← zero_mul, ← add_zeroₓ] using @val_between_eq_zero m h1

theorem val_eq_zero {is : List Int} : (∀ x : Int, x ∈ is → x = 0) → val v is = 0 := by
  apply val_between_eq_zero

end Coeffs

end Omega

