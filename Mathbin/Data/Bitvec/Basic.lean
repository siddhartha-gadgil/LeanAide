/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Data.Bitvec.Core
import Mathbin.Data.Fin.Basic
import Mathbin.Tactic.NormNum
import Mathbin.Tactic.Monotonicity.Default

namespace Bitvec

instance (n : ℕ) : Preorderₓ (Bitvec n) :=
  Preorderₓ.lift Bitvec.toNat

/-- convert `fin` to `bitvec` -/
def ofFin {n : ℕ} (i : Finₓ <| 2 ^ n) : Bitvec n :=
  Bitvec.ofNat _ i.val

theorem of_fin_val {n : ℕ} (i : Finₓ <| 2 ^ n) : (ofFin i).toNat = i.val := by
  rw [of_fin, to_nat_of_nat, Nat.mod_eq_of_ltₓ] <;> apply i.is_lt

/-- convert `bitvec` to `fin` -/
def toFin {n : ℕ} (i : Bitvec n) : Finₓ <| 2 ^ n :=
  @Finₓ.ofNat' _
    ⟨pow_pos
        (by
          norm_num)
        _⟩
    i.toNat

theorem add_lsb_eq_twice_add_one {x b} : addLsb x b = 2 * x + cond b 1 0 := by
  simp [← add_lsb, ← two_mul]

theorem to_nat_eq_foldr_reverse {n : ℕ} (v : Bitvec n) : v.toNat = v.toList.reverse.foldr (flip addLsb) 0 := by
  rw [List.foldr_reverse, flip] <;> rfl

theorem to_nat_lt {n : ℕ} (v : Bitvec n) : v.toNat < 2 ^ n := by
  suffices v.to_nat + 1 ≤ 2 ^ n by
    simpa
  rw [to_nat_eq_foldr_reverse]
  cases' v with xs h
  dsimp' [← Bitvec.toNat, ← bits_to_nat]
  rw [← List.length_reverse] at h
  generalize xs.reverse = ys  at h⊢
  clear xs
  induction ys generalizing n
  · simp [h]
    
  · simp only [h, ← pow_addₓ, ← flip, ← List.length, ← List.foldr, ← pow_oneₓ]
    rw [add_lsb_eq_twice_add_one]
    trans 2 * List.foldr (fun (x : Bool) (y : ℕ) => add_lsb y x) 0 ys_tl + 2 * 1
    · ac_mono
      rw [two_mul]
      mono
      cases ys_hd <;> simp
      
    · rw [← left_distrib]
      ac_mono
      norm_num
      apply ys_ih
      rfl
      
    

theorem add_lsb_div_two {x b} : addLsb x b / 2 = x := by
  cases b <;>
    simp only [← Nat.add_mul_div_leftₓ, ← add_lsb, two_mul, ← add_commₓ, ← Nat.succ_pos', ← Nat.mul_div_rightₓ, ←
        gt_iff_lt, ← zero_addₓ, ← cond] <;>
      norm_num

theorem to_bool_add_lsb_mod_two {x b} : toBool (addLsb x b % 2 = 1) = b := by
  cases b <;>
    simp only [← to_bool_iff, ← Nat.add_mul_mod_self_leftₓ, ← add_lsb, two_mul, ← add_commₓ, ← Bool.to_bool_false, ←
        Nat.mul_mod_rightₓ, ← zero_addₓ, ← cond, ← zero_ne_one] <;>
      norm_num

theorem of_nat_to_nat {n : ℕ} (v : Bitvec n) : Bitvec.ofNat _ v.toNat = v := by
  cases' v with xs h
  ext1
  change Vector.toList _ = xs
  dsimp' [← Bitvec.toNat, ← bits_to_nat]
  rw [← List.length_reverse] at h
  rw [← List.reverse_reverse xs, List.foldl_reverse]
  generalize xs.reverse = ys  at h⊢
  clear xs
  induction ys generalizing n
  · cases h
    simp [← Bitvec.ofNat]
    
  · simp only [Nat.succ_eq_add_one, ← List.length] at h
    subst n
    simp only [← Bitvec.ofNat, ← Vector.to_list_cons, ← Vector.to_list_nil, ← List.reverse_cons, ←
      Vector.to_list_append, ← List.foldr]
    erw [add_lsb_div_two, to_bool_add_lsb_mod_two]
    congr
    apply ys_ih
    rfl
    

theorem to_fin_val {n : ℕ} (v : Bitvec n) : (toFin v : ℕ) = v.toNat := by
  rw [to_fin, Finₓ.coe_of_nat_eq_mod', Nat.mod_eq_of_ltₓ] <;> apply to_nat_lt

theorem to_fin_le_to_fin_of_le {n} {v₀ v₁ : Bitvec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by
    rw [to_fin_val, to_fin_val] <;> exact h

theorem of_fin_le_of_fin_of_le {n : ℕ} {i j : Finₓ (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j :=
  show (Bitvec.ofNat n i).toNat ≤ (Bitvec.ofNat n j).toNat by
    simp only [← to_nat_of_nat, ← Nat.mod_eq_of_ltₓ, ← Finₓ.is_lt]
    exact h

theorem to_fin_of_fin {n} (i : Finₓ <| 2 ^ n) : (ofFin i).toFin = i :=
  Finₓ.eq_of_veq
    (by
      simp [← to_fin_val, ← of_fin, ← to_nat_of_nat, ← Nat.mod_eq_of_ltₓ, ← i.is_lt])

theorem of_fin_to_fin {n} (v : Bitvec n) : ofFin (toFin v) = v := by
  dsimp' [← of_fin] <;> rw [to_fin_val, of_nat_to_nat]

end Bitvec

