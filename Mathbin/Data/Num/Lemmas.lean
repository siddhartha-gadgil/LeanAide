/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Num.Bitwise
import Mathbin.Data.Int.CharZero
import Mathbin.Data.Nat.Gcd
import Mathbin.Data.Nat.Psub

/-!
# Properties of the binary representation of integers
-/


attribute [local simp] add_assocₓ

namespace PosNum

variable {α : Type _}

@[simp, norm_cast]
theorem cast_one [One α] [Add α] : ((1 : PosNum) : α) = 1 :=
  rfl

@[simp]
theorem cast_one' [One α] [Add α] : (PosNum.one : α) = 1 :=
  rfl

@[simp, norm_cast]
theorem cast_bit0 [One α] [Add α] (n : PosNum) : (n.bit0 : α) = bit0 n :=
  rfl

@[simp, norm_cast]
theorem cast_bit1 [One α] [Add α] (n : PosNum) : (n.bit1 : α) = bit1 n :=
  rfl

@[simp, norm_cast]
theorem cast_to_nat [AddMonoidWithOneₓ α] : ∀ n : PosNum, ((n : ℕ) : α) = n
  | 1 => Nat.cast_oneₓ
  | bit0 p => (Nat.cast_bit0 _).trans <| congr_arg bit0 p.cast_to_nat
  | bit1 p => (Nat.cast_bit1 _).trans <| congr_arg bit1 p.cast_to_nat

@[simp, norm_cast]
theorem to_nat_to_int (n : PosNum) : ((n : ℕ) : ℤ) = n :=
  cast_to_nat _

@[simp, norm_cast]
theorem cast_to_int [AddGroupWithOneₓ α] (n : PosNum) : ((n : ℤ) : α) = n := by
  rw [← to_nat_to_int, Int.cast_coe_nat, cast_to_nat]

theorem succ_to_nat : ∀ n, (succ n : ℕ) = n + 1
  | 1 => rfl
  | bit0 p => rfl
  | bit1 p =>
    (congr_arg bit0 (succ_to_nat p)).trans <|
      show ↑p + 1 + ↑p + 1 = ↑p + ↑p + 1 + 1 by
        simp [← add_left_commₓ]

theorem one_add (n : PosNum) : 1 + n = succ n := by
  cases n <;> rfl

theorem add_one (n : PosNum) : n + 1 = succ n := by
  cases n <;> rfl

@[norm_cast]
theorem add_to_nat : ∀ m n, ((m + n : PosNum) : ℕ) = m + n
  | 1, b => by
    rw [one_add b, succ_to_nat, add_commₓ] <;> rfl
  | a, 1 => by
    rw [add_one a, succ_to_nat] <;> rfl
  | bit0 a, bit0 b => (congr_arg bit0 (add_to_nat a b)).trans <| add_add_add_commₓ _ _ _ _
  | bit0 a, bit1 b =>
    (congr_arg bit1 (add_to_nat a b)).trans <|
      show (a + b + (a + b) + 1 : ℕ) = a + a + (b + b + 1) by
        simp [← add_left_commₓ]
  | bit1 a, bit0 b =>
    (congr_arg bit1 (add_to_nat a b)).trans <|
      show (a + b + (a + b) + 1 : ℕ) = a + a + 1 + (b + b) by
        simp [← add_commₓ, ← add_left_commₓ]
  | bit1 a, bit1 b =>
    show (succ (a + b) + succ (a + b) : ℕ) = a + a + 1 + (b + b + 1) by
      rw [succ_to_nat, add_to_nat] <;> simp [← add_left_commₓ]

theorem add_succ : ∀ m n : PosNum, m + succ n = succ (m + n)
  | 1, b => by
    simp [← one_add]
  | bit0 a, 1 => congr_arg bit0 (add_one a)
  | bit1 a, 1 => congr_arg bit1 (add_one a)
  | bit0 a, bit0 b => rfl
  | bit0 a, bit1 b => congr_arg bit0 (add_succ a b)
  | bit1 a, bit0 b => rfl
  | bit1 a, bit1 b => congr_arg bit1 (add_succ a b)

theorem bit0_of_bit0 : ∀ n, bit0 n = bit0 n
  | 1 => rfl
  | bit0 p => congr_arg bit0 (bit0_of_bit0 p)
  | bit1 p =>
    show bit0 (succ (bit0 p)) = _ by
      rw [bit0_of_bit0] <;> rfl

theorem bit1_of_bit1 (n : PosNum) : bit1 n = bit1 n :=
  show bit0 n + 1 = bit1 n by
    rw [add_one, bit0_of_bit0] <;> rfl

@[norm_cast]
theorem mul_to_nat (m) : ∀ n, ((m * n : PosNum) : ℕ) = m * n
  | 1 => (mul_oneₓ _).symm
  | bit0 p =>
    show (↑(m * p) + ↑(m * p) : ℕ) = ↑m * (p + p) by
      rw [mul_to_nat, left_distrib]
  | bit1 p =>
    (add_to_nat (bit0 (m * p)) m).trans <|
      show (↑(m * p) + ↑(m * p) + ↑m : ℕ) = ↑m * (p + p) + m by
        rw [mul_to_nat, left_distrib]

theorem to_nat_pos : ∀ n : PosNum, 0 < (n : ℕ)
  | 1 => zero_lt_one
  | bit0 p =>
    let h := to_nat_pos p
    add_pos h h
  | bit1 p => Nat.succ_posₓ _

theorem cmp_to_nat_lemma {m n : PosNum} : (m : ℕ) < n → (bit1 m : ℕ) < bit0 n :=
  show (m : ℕ) < n → (m + m + 1 + 1 : ℕ) ≤ n + n by
    intro h <;> rw [Nat.add_right_comm m m 1, add_assocₓ] <;> exact add_le_add h h

theorem cmp_swap (m) : ∀ n, (cmp m n).swap = cmp n m := by
  induction' m with m IH m IH <;>
    intro n <;>
      cases' n with n n <;>
        try
            unfold cmp <;>
          try
              rfl <;>
            rw [← IH] <;> cases cmp m n <;> rfl

theorem cmp_to_nat : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℕ) < n) (m = n) ((n : ℕ) < m) : Prop)
  | 1, 1 => rfl
  | bit0 a, 1 =>
    let h : (1 : ℕ) ≤ a := to_nat_pos a
    add_le_add h h
  | bit1 a, 1 => Nat.succ_lt_succₓ <| to_nat_pos <| bit0 a
  | 1, bit0 b =>
    let h : (1 : ℕ) ≤ b := to_nat_pos b
    add_le_add h h
  | 1, bit1 b => Nat.succ_lt_succₓ <| to_nat_pos <| bit0 b
  | bit0 a, bit0 b => by
    have := cmp_to_nat a b
    revert this
    cases cmp a b <;> dsimp' <;> intro
    · exact add_lt_add this this
      
    · rw [this]
      
    · exact add_lt_add this this
      
  | bit0 a, bit1 b => by
    dsimp' [← cmp]
    have := cmp_to_nat a b
    revert this
    cases cmp a b <;> dsimp' <;> intro
    · exact Nat.le_succ_of_leₓ (add_lt_add this this)
      
    · rw [this]
      apply Nat.lt_succ_selfₓ
      
    · exact cmp_to_nat_lemma this
      
  | bit1 a, bit0 b => by
    dsimp' [← cmp]
    have := cmp_to_nat a b
    revert this
    cases cmp a b <;> dsimp' <;> intro
    · exact cmp_to_nat_lemma this
      
    · rw [this]
      apply Nat.lt_succ_selfₓ
      
    · exact Nat.le_succ_of_leₓ (add_lt_add this this)
      
  | bit1 a, bit1 b => by
    have := cmp_to_nat a b
    revert this
    cases cmp a b <;> dsimp' <;> intro
    · exact Nat.succ_lt_succₓ (add_lt_add this this)
      
    · rw [this]
      
    · exact Nat.succ_lt_succₓ (add_lt_add this this)
      

@[norm_cast]
theorem lt_to_nat {m n : PosNum} : (m : ℕ) < n ↔ m < n :=
  show (m : ℕ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by
      simp at h <;> simp [← h]
    | Ordering.eq, h => by
      simp at h <;>
        simp [← h, ← lt_irreflₓ] <;>
          exact by
            decide
    | Ordering.gt, h => by
      simp [← not_lt_of_gtₓ h] <;>
        exact by
          decide

@[norm_cast]
theorem le_to_nat {m n : PosNum} : (m : ℕ) ≤ n ↔ m ≤ n := by
  rw [← not_ltₓ] <;> exact not_congr lt_to_nat

end PosNum

namespace Num

variable {α : Type _}

open PosNum

theorem add_zero (n : Num) : n + 0 = n := by
  cases n <;> rfl

theorem zero_add (n : Num) : 0 + n = n := by
  cases n <;> rfl

theorem add_one : ∀ n : Num, n + 1 = succ n
  | 0 => rfl
  | Pos p => by
    cases p <;> rfl

theorem add_succ : ∀ m n : Num, m + succ n = succ (m + n)
  | 0, n => by
    simp [← zero_addₓ]
  | Pos p, 0 =>
    show pos (p + 1) = succ (pos p + 0) by
      rw [PosNum.add_one, add_zeroₓ] <;> rfl
  | Pos p, Pos q => congr_arg pos (PosNum.add_succ _ _)

theorem bit0_of_bit0 : ∀ n : Num, bit0 n = n.bit0
  | 0 => rfl
  | Pos p => congr_arg pos p.bit0_of_bit0

theorem bit1_of_bit1 : ∀ n : Num, bit1 n = n.bit1
  | 0 => rfl
  | Pos p => congr_arg pos p.bit1_of_bit1

@[simp]
theorem of_nat'_zero : Num.ofNat' 0 = 0 := by
  simp [← Num.ofNat']

theorem of_nat'_bit (b n) : ofNat' (Nat.bit b n) = cond b Num.bit1 Num.bit0 (ofNat' n) :=
  Nat.binary_rec_eq rfl _ _

@[simp]
theorem of_nat'_one : Num.ofNat' 1 = 1 := by
  erw [of_nat'_bit tt 0, cond, of_nat'_zero] <;> rfl

theorem bit1_succ : ∀ n : Num, n.bit1.succ = n.succ.bit0
  | 0 => rfl
  | Pos n => rfl

theorem of_nat'_succ : ∀ {n}, ofNat' (n + 1) = ofNat' n + 1 :=
  (Nat.binaryRec
      (by
        simp <;> rfl))
    fun b n ih => by
    cases b
    · erw [of_nat'_bit tt n, of_nat'_bit]
      simp only [bit1_of_bit1, bit0_of_bit0, ← cond, ← _root_.bit1]
      
    · erw
        [show n.bit tt + 1 = (n + 1).bit ff by
          simp [← Nat.bit, ← _root_.bit1, ← _root_.bit0] <;> cc,
        of_nat'_bit, of_nat'_bit, ih]
      simp only [← cond, ← add_one, ← bit1_succ]
      

@[simp]
theorem add_of_nat' (m n) : Num.ofNat' (m + n) = Num.ofNat' m + Num.ofNat' n := by
  induction n <;> simp [← Nat.add_zero, ← of_nat'_succ, ← add_zeroₓ, ← Nat.add_succ, ← add_one, ← add_succ, *]

@[simp, norm_cast]
theorem cast_zero [Zero α] [One α] [Add α] : ((0 : Num) : α) = 0 :=
  rfl

@[simp]
theorem cast_zero' [Zero α] [One α] [Add α] : (Num.zero : α) = 0 :=
  rfl

@[simp, norm_cast]
theorem cast_one [Zero α] [One α] [Add α] : ((1 : Num) : α) = 1 :=
  rfl

@[simp]
theorem cast_pos [Zero α] [One α] [Add α] (n : PosNum) : (Num.pos n : α) = n :=
  rfl

theorem succ'_to_nat : ∀ n, (succ' n : ℕ) = n + 1
  | 0 => (zero_addₓ _).symm
  | Pos p => PosNum.succ_to_nat _

theorem succ_to_nat (n) : (succ n : ℕ) = n + 1 :=
  succ'_to_nat n

@[simp, norm_cast]
theorem cast_to_nat [AddMonoidWithOneₓ α] : ∀ n : Num, ((n : ℕ) : α) = n
  | 0 => Nat.cast_zeroₓ
  | Pos p => p.cast_to_nat

@[norm_cast]
theorem add_to_nat : ∀ m n, ((m + n : Num) : ℕ) = m + n
  | 0, 0 => rfl
  | 0, Pos q => (zero_addₓ _).symm
  | Pos p, 0 => rfl
  | Pos p, Pos q => PosNum.add_to_nat _ _

@[norm_cast]
theorem mul_to_nat : ∀ m n, ((m * n : Num) : ℕ) = m * n
  | 0, 0 => rfl
  | 0, Pos q => (zero_mul _).symm
  | Pos p, 0 => rfl
  | Pos p, Pos q => PosNum.mul_to_nat _ _

theorem cmp_to_nat : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℕ) < n) (m = n) ((n : ℕ) < m) : Prop)
  | 0, 0 => rfl
  | 0, Pos b => to_nat_pos _
  | Pos a, 0 => to_nat_pos _
  | Pos a, Pos b => by
    have := PosNum.cmp_to_nat a b <;> revert this <;> dsimp' [← cmp] <;> cases PosNum.cmp a b
    exacts[id, congr_arg Pos, id]

@[norm_cast]
theorem lt_to_nat {m n : Num} : (m : ℕ) < n ↔ m < n :=
  show (m : ℕ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by
      simp at h <;> simp [← h]
    | Ordering.eq, h => by
      simp at h <;>
        simp [← h, ← lt_irreflₓ] <;>
          exact by
            decide
    | Ordering.gt, h => by
      simp [← not_lt_of_gtₓ h] <;>
        exact by
          decide

@[norm_cast]
theorem le_to_nat {m n : Num} : (m : ℕ) ≤ n ↔ m ≤ n := by
  rw [← not_ltₓ] <;> exact not_congr lt_to_nat

end Num

namespace PosNum

@[simp]
theorem of_to_nat' : ∀ n : PosNum, Num.ofNat' (n : ℕ) = Num.pos n
  | 1 => by
    erw [@Num.of_nat'_bit tt 0, Num.of_nat'_zero] <;> rfl
  | bit0 p => by
    erw [@Num.of_nat'_bit ff, of_to_nat'] <;> rfl
  | bit1 p => by
    erw [@Num.of_nat'_bit tt, of_to_nat'] <;> rfl

end PosNum

namespace Num

@[simp, norm_cast]
theorem of_to_nat' : ∀ n : Num, Num.ofNat' (n : ℕ) = n
  | 0 => of_nat'_zero
  | Pos p => p.of_to_nat'

@[norm_cast]
theorem to_nat_inj {m n : Num} : (m : ℕ) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective of_to_nat' h, congr_arg _⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- This tactic tries to turn an (in)equality about `num`s to one about `nat`s by rewriting.
```lean
example (n : num) (m : num) : n ≤ n + m :=
begin
  num.transfer_rw,
  exact nat.le_add_right _ _
end
```
-/
unsafe def transfer_rw : tactic Unit :=
  sorry

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- This tactic tries to prove (in)equalities about `num`s by transfering them to the `nat` world and
then trying to call `simp`.
```lean
example (n : num) (m : num) : n ≤ n + m := by num.transfer
```
-/
unsafe def transfer : tactic Unit :=
  sorry

instance : AddMonoidₓ Num where
  add := (· + ·)
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  add_assoc := by
    run_tac
      transfer

instance : AddMonoidWithOneₓ Num :=
  { Num.addMonoid with natCast := Num.ofNat', one := 1, nat_cast_zero := of_nat'_zero,
    nat_cast_succ := fun _ => of_nat'_succ }

instance : CommSemiringₓ Num := by
  refine_struct
      { Num.addMonoid, Num.addMonoidWithOne with mul := (· * ·), one := 1, add := (· + ·), zero := 0,
        npow := @npowRec Num ⟨1⟩ ⟨(· * ·)⟩ } <;>
    try
        intros
        rfl <;>
      try
          run_tac
            transfer <;>
        simp [← add_commₓ, ← mul_addₓ, ← add_mulₓ, ← mul_assoc, ← mul_comm, ← mul_left_commₓ]

instance : OrderedCancelAddCommMonoid Num :=
  { Num.commSemiring with
    add_left_cancel := by
      intro a b c
      run_tac
        transfer_rw
      apply add_left_cancelₓ,
    lt := (· < ·),
    lt_iff_le_not_le := by
      intro a b
      run_tac
        transfer_rw
      apply lt_iff_le_not_leₓ,
    le := (· ≤ ·),
    le_refl := by
      run_tac
        transfer,
    le_trans := by
      intro a b c
      run_tac
        transfer_rw
      apply le_transₓ,
    le_antisymm := by
      intro a b
      run_tac
        transfer_rw
      apply le_antisymmₓ,
    add_le_add_left := by
      intro a b h c
      revert h
      run_tac
        transfer_rw
      exact fun h => add_le_add_left h c,
    le_of_add_le_add_left := by
      intro a b c
      run_tac
        transfer_rw
      apply le_of_add_le_add_left }

instance : LinearOrderedSemiring Num :=
  { Num.commSemiring, Num.orderedCancelAddCommMonoid with
    le_total := by
      intro a b
      run_tac
        transfer_rw
      apply le_totalₓ,
    zero_le_one := by
      decide,
    mul_lt_mul_of_pos_left := by
      intro a b c
      run_tac
        transfer_rw
      apply mul_lt_mul_of_pos_left,
    mul_lt_mul_of_pos_right := by
      intro a b c
      run_tac
        transfer_rw
      apply mul_lt_mul_of_pos_right,
    decidableLt := Num.decidableLt, decidableLe := Num.decidableLe, DecidableEq := Num.decidableEq,
    exists_pair_ne :=
      ⟨0, 1, by
        decide⟩ }

@[simp, norm_cast]
theorem add_of_nat (m n) : ((m + n : ℕ) : Num) = m + n :=
  add_of_nat' _ _

@[simp, norm_cast]
theorem to_nat_to_int (n : Num) : ((n : ℕ) : ℤ) = n :=
  cast_to_nat _

@[simp, norm_cast]
theorem cast_to_int {α} [AddGroupWithOneₓ α] (n : Num) : ((n : ℤ) : α) = n := by
  rw [← to_nat_to_int, Int.cast_coe_nat, cast_to_nat]

theorem to_of_nat : ∀ n : ℕ, ((n : Num) : ℕ) = n
  | 0 => by
    rw [Nat.cast_zeroₓ, cast_zero]
  | n + 1 => by
    rw [Nat.cast_succₓ, add_one, succ_to_nat, to_of_nat]

@[simp, norm_cast]
theorem of_nat_cast {α} [AddMonoidWithOneₓ α] (n : ℕ) : ((n : Num) : α) = n := by
  rw [← cast_to_nat, to_of_nat]

@[simp, norm_cast]
theorem of_nat_inj {m n : ℕ} : (m : Num) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective to_of_nat h, congr_arg _⟩

@[simp, norm_cast]
theorem of_to_nat : ∀ n : Num, ((n : ℕ) : Num) = n :=
  of_to_nat'

@[norm_cast]
theorem dvd_to_nat (m n : Num) : (m : ℕ) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ =>
    ⟨k, by
      rw [← of_to_nat n, e] <;> simp ⟩,
    fun ⟨k, e⟩ =>
    ⟨k, by
      simp [← e, ← mul_to_nat]⟩⟩

end Num

namespace PosNum

variable {α : Type _}

open Num

@[simp, norm_cast]
theorem of_to_nat : ∀ n : PosNum, ((n : ℕ) : Num) = Num.pos n :=
  of_to_nat'

@[norm_cast]
theorem to_nat_inj {m n : PosNum} : (m : ℕ) = n ↔ m = n :=
  ⟨fun h =>
    Num.pos.inj <| by
      rw [← PosNum.of_to_nat, ← PosNum.of_to_nat, h],
    congr_arg _⟩

theorem pred'_to_nat : ∀ n, (pred' n : ℕ) = Nat.pred n
  | 1 => rfl
  | bit0 n =>
    have : Nat.succ ↑(pred' n) = ↑n := by
      rw [pred'_to_nat n, Nat.succ_pred_eq_of_posₓ (to_nat_pos n)]
    match pred' n, this with
    | 0, (h : ((1 : Num) : ℕ) = n) => by
      rw [← to_nat_inj.1 h] <;> rfl
    | Num.pos p, (h : Nat.succ ↑p = n) => by
      rw [← h] <;> exact (Nat.succ_add p p).symm
  | bit1 n => rfl

@[simp]
theorem pred'_succ' (n) : pred' (succ' n) = n :=
  Num.to_nat_inj.1 <| by
    rw [pred'_to_nat, succ'_to_nat, Nat.add_one, Nat.pred_succ]

@[simp]
theorem succ'_pred' (n) : succ' (pred' n) = n :=
  to_nat_inj.1 <| by
    rw [succ'_to_nat, pred'_to_nat, Nat.add_one, Nat.succ_pred_eq_of_posₓ (to_nat_pos _)]

instance : Dvd PosNum :=
  ⟨fun m n => Pos m ∣ Pos n⟩

@[norm_cast]
theorem dvd_to_nat {m n : PosNum} : (m : ℕ) ∣ n ↔ m ∣ n :=
  Num.dvd_to_nat (Pos m) (Pos n)

theorem size_to_nat : ∀ n, (size n : ℕ) = Nat.size n
  | 1 => Nat.size_one.symm
  | bit0 n => by
    rw [size, succ_to_nat, size_to_nat, cast_bit0, Nat.size_bit0 <| ne_of_gtₓ <| to_nat_pos n]
  | bit1 n => by
    rw [size, succ_to_nat, size_to_nat, cast_bit1, Nat.size_bit1]

theorem size_eq_nat_size : ∀ n, (size n : ℕ) = natSize n
  | 1 => rfl
  | bit0 n => by
    rw [size, succ_to_nat, nat_size, size_eq_nat_size]
  | bit1 n => by
    rw [size, succ_to_nat, nat_size, size_eq_nat_size]

theorem nat_size_to_nat (n) : natSize n = Nat.size n := by
  rw [← size_eq_nat_size, size_to_nat]

theorem nat_size_pos (n) : 0 < natSize n := by
  cases n <;> apply Nat.succ_posₓ

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- This tactic tries to turn an (in)equality about `pos_num`s to one about `nat`s by rewriting.
```lean
example (n : pos_num) (m : pos_num) : n ≤ n + m :=
begin
  pos_num.transfer_rw,
  exact nat.le_add_right _ _
end
```
-/
unsafe def transfer_rw : tactic Unit :=
  sorry

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- This tactic tries to prove (in)equalities about `pos_num`s by transferring them to the `nat` world
and then trying to call `simp`.
```lean
example (n : pos_num) (m : pos_num) : n ≤ n + m := by pos_num.transfer
```
-/
unsafe def transfer : tactic Unit :=
  sorry

instance : AddCommSemigroupₓ PosNum := by
  refine' { add := (· + ·).. } <;>
    run_tac
      transfer

instance : CommMonoidₓ PosNum := by
  refine_struct { mul := (· * ·), one := (1 : PosNum), npow := @npowRec PosNum ⟨1⟩ ⟨(· * ·)⟩ } <;>
    try
        intros
        rfl <;>
      run_tac
        transfer

instance : Distribₓ PosNum := by
  refine' { add := (· + ·), mul := (· * ·).. } <;>
    · run_tac
        transfer
      simp [← mul_addₓ, ← mul_comm]
      

instance : LinearOrderₓ PosNum where
  lt := (· < ·)
  lt_iff_le_not_le := by
    intro a b
    run_tac
      transfer_rw
    apply lt_iff_le_not_leₓ
  le := (· ≤ ·)
  le_refl := by
    run_tac
      transfer
  le_trans := by
    intro a b c
    run_tac
      transfer_rw
    apply le_transₓ
  le_antisymm := by
    intro a b
    run_tac
      transfer_rw
    apply le_antisymmₓ
  le_total := by
    intro a b
    run_tac
      transfer_rw
    apply le_totalₓ
  decidableLt := by
    infer_instance
  decidableLe := by
    infer_instance
  DecidableEq := by
    infer_instance

@[simp]
theorem cast_to_num (n : PosNum) : ↑n = Num.pos n := by
  rw [← cast_to_nat, ← of_to_nat n]

@[simp, norm_cast]
theorem bit_to_nat (b n) : (bit b n : ℕ) = Nat.bit b n := by
  cases b <;> rfl

@[simp, norm_cast]
theorem cast_add [AddMonoidWithOneₓ α] (m n) : ((m + n : PosNum) : α) = m + n := by
  rw [← cast_to_nat, add_to_nat, Nat.cast_addₓ, cast_to_nat, cast_to_nat]

@[simp, norm_cast]
theorem cast_succ [AddMonoidWithOneₓ α] (n : PosNum) : (succ n : α) = n + 1 := by
  rw [← add_one, cast_add, cast_one]

@[simp, norm_cast]
theorem cast_inj [AddMonoidWithOneₓ α] [CharZero α] {m n : PosNum} : (m : α) = n ↔ m = n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_inj, to_nat_inj]

@[simp]
theorem one_le_cast [LinearOrderedSemiring α] (n : PosNum) : (1 : α) ≤ n := by
  rw [← cast_to_nat, ← Nat.cast_oneₓ, Nat.cast_le] <;> apply to_nat_pos

@[simp]
theorem cast_pos [LinearOrderedSemiring α] (n : PosNum) : 0 < (n : α) :=
  lt_of_lt_of_leₓ zero_lt_one (one_le_cast n)

@[simp, norm_cast]
theorem cast_mul [Semiringₓ α] (m n) : ((m * n : PosNum) : α) = m * n := by
  rw [← cast_to_nat, mul_to_nat, Nat.cast_mulₓ, cast_to_nat, cast_to_nat]

@[simp]
theorem cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n := by
  have := cmp_to_nat m n
  cases cmp m n <;>
    simp at this⊢ <;>
      try
          exact this <;>
        · simp [←
            show m ≠ n from fun e => by
              rw [e] at this <;> exact lt_irreflₓ _ this]
          

@[simp, norm_cast]
theorem cast_lt [LinearOrderedSemiring α] {m n : PosNum} : (m : α) < n ↔ m < n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_lt, lt_to_nat]

@[simp, norm_cast]
theorem cast_le [LinearOrderedSemiring α] {m n : PosNum} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_ltₓ] <;> exact not_congr cast_lt

end PosNum

namespace Num

variable {α : Type _}

open PosNum

theorem bit_to_nat (b n) : (bit b n : ℕ) = Nat.bit b n := by
  cases b <;> cases n <;> rfl

theorem cast_succ' [AddMonoidWithOneₓ α] (n) : (succ' n : α) = n + 1 := by
  rw [← PosNum.cast_to_nat, succ'_to_nat, Nat.cast_add_one, cast_to_nat]

theorem cast_succ [AddMonoidWithOneₓ α] (n) : (succ n : α) = n + 1 :=
  cast_succ' n

@[simp, norm_cast]
theorem cast_add [Semiringₓ α] (m n) : ((m + n : Num) : α) = m + n := by
  rw [← cast_to_nat, add_to_nat, Nat.cast_addₓ, cast_to_nat, cast_to_nat]

@[simp, norm_cast]
theorem cast_bit0 [Semiringₓ α] (n : Num) : (n.bit0 : α) = bit0 n := by
  rw [← bit0_of_bit0, _root_.bit0, cast_add] <;> rfl

@[simp, norm_cast]
theorem cast_bit1 [Semiringₓ α] (n : Num) : (n.bit1 : α) = bit1 n := by
  rw [← bit1_of_bit1, _root_.bit1, bit0_of_bit0, cast_add, cast_bit0] <;> rfl

@[simp, norm_cast]
theorem cast_mul [Semiringₓ α] : ∀ m n, ((m * n : Num) : α) = m * n
  | 0, 0 => (zero_mul _).symm
  | 0, Pos q => (zero_mul _).symm
  | Pos p, 0 => (mul_zero _).symm
  | Pos p, Pos q => PosNum.cast_mul _ _

theorem size_to_nat : ∀ n, (size n : ℕ) = Nat.size n
  | 0 => Nat.size_zero.symm
  | Pos p => p.size_to_nat

theorem size_eq_nat_size : ∀ n, (size n : ℕ) = natSize n
  | 0 => rfl
  | Pos p => p.size_eq_nat_size

theorem nat_size_to_nat (n) : natSize n = Nat.size n := by
  rw [← size_eq_nat_size, size_to_nat]

@[simp]
theorem of_nat'_eq : ∀ n, Num.ofNat' n = n :=
  (Nat.binaryRec
      (by
        simp ))
    fun b n IH => by
    rw [of_nat'] at IH⊢
    rw [Nat.binary_rec_eq, IH]
    · cases b <;> simp [← Nat.bit, ← bit0_of_bit0, ← bit1_of_bit1]
      
    · rfl
      

theorem zneg_to_znum (n : Num) : -n.toZnum = n.toZnumNeg := by
  cases n <;> rfl

theorem zneg_to_znum_neg (n : Num) : -n.toZnumNeg = n.toZnum := by
  cases n <;> rfl

theorem to_znum_inj {m n : Num} : m.toZnum = n.toZnum ↔ m = n :=
  ⟨fun h => by
    cases m <;> cases n <;> cases h <;> rfl, congr_arg _⟩

@[simp, norm_cast squash]
theorem cast_to_znum [Zero α] [One α] [Add α] [Neg α] : ∀ n : Num, (n.toZnum : α) = n
  | 0 => rfl
  | Num.pos p => rfl

@[simp]
theorem cast_to_znum_neg [AddGroupₓ α] [One α] : ∀ n : Num, (n.toZnumNeg : α) = -n
  | 0 => neg_zero.symm
  | Num.pos p => rfl

@[simp]
theorem add_to_znum (m n : Num) : Num.toZnum (m + n) = m.toZnum + n.toZnum := by
  cases m <;> cases n <;> rfl

end Num

namespace PosNum

open Num

theorem pred_to_nat {n : PosNum} (h : 1 < n) : (pred n : ℕ) = Nat.pred n := by
  unfold pred
  have := pred'_to_nat n
  cases e : pred' n
  · have : (1 : ℕ) ≤ Nat.pred n := Nat.pred_le_predₓ ((@cast_lt ℕ _ _ _).2 h)
    rw [← pred'_to_nat, e] at this
    exact
      absurd this
        (by
          decide)
    
  · rw [← pred'_to_nat, e]
    rfl
    

theorem sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZnum := by
  cases a <;> rfl

theorem one_sub' (a : PosNum) : sub' 1 a = (pred' a).toZnumNeg := by
  cases a <;> rfl

theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl

theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ Ordering.gt :=
  not_congr <|
    lt_iff_cmp.trans <| by
      rw [← cmp_swap] <;>
        cases cmp m n <;>
          exact by
            decide

end PosNum

namespace Num

variable {α : Type _}

open PosNum

theorem pred_to_nat : ∀ n : Num, (pred n : ℕ) = Nat.pred n
  | 0 => rfl
  | Pos p => by
    rw [pred, PosNum.pred'_to_nat] <;> rfl

theorem ppred_to_nat : ∀ n : Num, coe <$> ppred n = Nat.ppred n
  | 0 => rfl
  | Pos p => by
    rw [ppred, Option.map_some, Nat.ppred_eq_some.2] <;>
      rw [PosNum.pred'_to_nat, Nat.succ_pred_eq_of_posₓ (PosNum.to_nat_pos _)] <;> rfl

theorem cmp_swap (m n) : (cmp m n).swap = cmp n m := by
  cases m <;>
    cases n <;>
      try
          unfold cmp <;>
        try
            rfl <;>
          apply PosNum.cmp_swap

theorem cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n := by
  have := cmp_to_nat m n
  cases cmp m n <;>
    simp at this⊢ <;>
      try
          exact this <;>
        · simp [←
            show m ≠ n from fun e => by
              rw [e] at this <;> exact lt_irreflₓ _ this]
          

@[simp, norm_cast]
theorem cast_lt [LinearOrderedSemiring α] {m n : Num} : (m : α) < n ↔ m < n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_lt, lt_to_nat]

@[simp, norm_cast]
theorem cast_le [LinearOrderedSemiring α] {m n : Num} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_ltₓ] <;> exact not_congr cast_lt

@[simp, norm_cast]
theorem cast_inj [LinearOrderedSemiring α] {m n : Num} : (m : α) = n ↔ m = n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_inj, to_nat_inj]

theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl

theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ Ordering.gt :=
  not_congr <|
    lt_iff_cmp.trans <| by
      rw [← cmp_swap] <;>
        cases cmp m n <;>
          exact by
            decide

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
theorem bitwise_to_nat {f : Num → Num → Num} {g : Bool → Bool → Bool} (p : PosNum → PosNum → Num)
    (gff : g false false = ff) (f00 : f 0 0 = 0) (f0n : ∀ n, f 0 (pos n) = cond (g false true) (pos n) 0)
    (fn0 : ∀ n, f (pos n) 0 = cond (g true false) (pos n) 0) (fnn : ∀ m n, f (pos m) (pos n) = p m n)
    (p11 : p 1 1 = cond (g true true) 1 0)
    (p1b : ∀ b n, p 1 (PosNum.bit b n) = bit (g true b) (cond (g false true) (pos n) 0))
    (pb1 : ∀ a m, p (PosNum.bit a m) 1 = bit (g a true) (cond (g true false) (pos m) 0))
    (pbb : ∀ a b m n, p (PosNum.bit a m) (PosNum.bit b n) = bit (g a b) (p m n)) :
    ∀ m n : Num, (f m n : ℕ) = Nat.bitwiseₓ g m n := by
  intros
  cases' m with m <;>
    cases' n with n <;>
      try
          change zero with 0 <;>
        try
          change ((0 : Num) : ℕ) with 0
  · rw [f00, Nat.bitwise_zero] <;> rfl
    
  · unfold Nat.bitwiseₓ
    rw [f0n, Nat.binary_rec_zero]
    cases g ff tt <;> rfl
    
  · unfold Nat.bitwiseₓ
    generalize h : (Pos m : ℕ) = m'
    revert h
    apply Nat.bitCasesOn m' _
    intro b m' h
    rw [fn0, Nat.binary_rec_eq, Nat.binary_rec_zero, ← h]
    cases g tt ff <;> rfl
    apply Nat.bitwise_bit_aux gff
    
  · rw [fnn]
    have : ∀ (b) (n : PosNum), (cond b (↑n) 0 : ℕ) = ↑(cond b (Pos n) 0 : Num) := by
      intros <;> cases b <;> rfl
    induction' m with m IH m IH generalizing n <;> cases' n with n n
    any_goals {
    }
    any_goals {
    }
    any_goals {
    }
    any_goals {
    }
    any_goals {
    }
    all_goals
      repeat'
        rw
          [show ∀ b n, (Pos (PosNum.bit b n) : ℕ) = Nat.bit b ↑n by
            intros <;> cases b <;> rfl]
      rw [Nat.bitwise_bit]
    any_goals {
    }
    any_goals {
    }
    any_goals {
    }
    any_goals {
    }
    all_goals
      rw [← show ∀ n, ↑(p m n) = Nat.bitwiseₓ g ↑m ↑n from IH]
      rw [← bit_to_nat, pbb]
    

@[simp, norm_cast]
theorem lor_to_nat : ∀ m n, (lor m n : ℕ) = Nat.lorₓ m n := by
  apply bitwise_to_nat fun x y => Pos (PosNum.lor x y) <;>
    intros <;>
      try
          cases a <;>
        try
            cases b <;>
          rfl

@[simp, norm_cast]
theorem land_to_nat : ∀ m n, (land m n : ℕ) = Nat.landₓ m n := by
  apply bitwise_to_nat PosNum.land <;>
    intros <;>
      try
          cases a <;>
        try
            cases b <;>
          rfl

@[simp, norm_cast]
theorem ldiff_to_nat : ∀ m n, (ldiff m n : ℕ) = Nat.ldiff m n := by
  apply bitwise_to_nat PosNum.ldiff <;>
    intros <;>
      try
          cases a <;>
        try
            cases b <;>
          rfl

@[simp, norm_cast]
theorem lxor_to_nat : ∀ m n, (lxor m n : ℕ) = Nat.lxor m n := by
  apply bitwise_to_nat PosNum.lxor <;>
    intros <;>
      try
          cases a <;>
        try
            cases b <;>
          rfl

@[simp, norm_cast]
theorem shiftl_to_nat (m n) : (shiftl m n : ℕ) = Nat.shiftl m n := by
  cases m <;> dunfold shiftl
  · symm
    apply Nat.zero_shiftl
    
  simp
  induction' n with n IH
  · rfl
    
  simp [← PosNum.shiftl, ← Nat.shiftl_succ]
  rw [← IH]

@[simp, norm_cast]
theorem shiftr_to_nat (m n) : (shiftr m n : ℕ) = Nat.shiftr m n := by
  cases' m with m <;> dunfold shiftr
  · symm
    apply Nat.zero_shiftr
    
  induction' n with n IH generalizing m
  · cases m <;> rfl
    
  cases' m with m m <;> dunfold PosNum.shiftr
  · rw [Nat.shiftr_eq_div_pow]
    symm
    apply Nat.div_eq_of_ltₓ
    exact
      @Nat.pow_lt_pow_of_lt_right 2
        (by
          decide)
        0 (n + 1) (Nat.succ_posₓ _)
    
  · trans
    apply IH
    change Nat.shiftr m n = Nat.shiftr (bit1 m) (n + 1)
    rw [add_commₓ n 1, Nat.shiftr_add]
    apply congr_arg fun x => Nat.shiftr x n
    unfold Nat.shiftr
    change (bit1 ↑m : ℕ) with Nat.bit tt m
    rw [Nat.div2_bit]
    
  · trans
    apply IH
    change Nat.shiftr m n = Nat.shiftr (bit0 m) (n + 1)
    rw [add_commₓ n 1, Nat.shiftr_add]
    apply congr_arg fun x => Nat.shiftr x n
    unfold Nat.shiftr
    change (bit0 ↑m : ℕ) with Nat.bit ff m
    rw [Nat.div2_bit]
    

@[simp]
theorem test_bit_to_nat (m n) : testBit m n = Nat.testBit m n := by
  cases' m with m <;> unfold test_bit Nat.testBit
  · change (zero : Nat) with 0
    rw [Nat.zero_shiftr]
    rfl
    
  induction' n with n IH generalizing m <;> cases m <;> dunfold PosNum.testBit
  · rfl
    
  · exact (Nat.bodd_bit _ _).symm
    
  · exact (Nat.bodd_bit _ _).symm
    
  · change ff = Nat.bodd (Nat.shiftr 1 (n + 1))
    rw [add_commₓ, Nat.shiftr_add]
    change Nat.shiftr 1 1 with 0
    rw [Nat.zero_shiftr] <;> rfl
    
  · change PosNum.testBit m n = Nat.bodd (Nat.shiftr (Nat.bit tt m) (n + 1))
    rw [add_commₓ, Nat.shiftr_add]
    unfold Nat.shiftr
    rw [Nat.div2_bit]
    apply IH
    
  · change PosNum.testBit m n = Nat.bodd (Nat.shiftr (Nat.bit ff m) (n + 1))
    rw [add_commₓ, Nat.shiftr_add]
    unfold Nat.shiftr
    rw [Nat.div2_bit]
    apply IH
    

end Num

namespace Znum

variable {α : Type _}

open PosNum

@[simp, norm_cast]
theorem cast_zero [Zero α] [One α] [Add α] [Neg α] : ((0 : Znum) : α) = 0 :=
  rfl

@[simp]
theorem cast_zero' [Zero α] [One α] [Add α] [Neg α] : (Znum.zero : α) = 0 :=
  rfl

@[simp, norm_cast]
theorem cast_one [Zero α] [One α] [Add α] [Neg α] : ((1 : Znum) : α) = 1 :=
  rfl

@[simp]
theorem cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (pos n : α) = n :=
  rfl

@[simp]
theorem cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (neg n : α) = -n :=
  rfl

@[simp, norm_cast]
theorem cast_zneg [AddGroupₓ α] [One α] : ∀ n, ((-n : Znum) : α) = -n
  | 0 => neg_zero.symm
  | Pos p => rfl
  | neg p => (neg_negₓ _).symm

theorem neg_zero : (-0 : Znum) = 0 :=
  rfl

theorem zneg_pos (n : PosNum) : -pos n = neg n :=
  rfl

theorem zneg_neg (n : PosNum) : -neg n = pos n :=
  rfl

theorem zneg_zneg (n : Znum) : - -n = n := by
  cases n <;> rfl

theorem zneg_bit1 (n : Znum) : -n.bit1 = (-n).bitm1 := by
  cases n <;> rfl

theorem zneg_bitm1 (n : Znum) : -n.bitm1 = (-n).bit1 := by
  cases n <;> rfl

theorem zneg_succ (n : Znum) : -n.succ = (-n).pred := by
  cases n <;>
    try
        rfl <;>
      rw [succ, Num.zneg_to_znum_neg] <;> rfl

theorem zneg_pred (n : Znum) : -n.pred = (-n).succ := by
  rw [← zneg_zneg (succ (-n)), zneg_succ, zneg_zneg]

@[simp]
theorem abs_to_nat : ∀ n, (abs n : ℕ) = Int.natAbs n
  | 0 => rfl
  | Pos p => congr_arg Int.natAbs p.to_nat_to_int
  | neg p =>
    show Int.natAbs ((p : ℕ) : ℤ) = Int.natAbs (-p) by
      rw [p.to_nat_to_int, Int.nat_abs_neg]

@[simp]
theorem abs_to_znum : ∀ n : Num, abs n.toZnum = n
  | 0 => rfl
  | Num.pos p => rfl

@[simp, norm_cast]
theorem cast_to_int [AddGroupWithOneₓ α] : ∀ n : Znum, ((n : ℤ) : α) = n
  | 0 => by
    rw [cast_zero, cast_zero, Int.cast_zeroₓ]
  | Pos p => by
    rw [cast_pos, cast_pos, PosNum.cast_to_int]
  | neg p => by
    rw [cast_neg, cast_neg, Int.cast_neg, PosNum.cast_to_int]

theorem bit0_of_bit0 : ∀ n : Znum, bit0 n = n.bit0
  | 0 => rfl
  | Pos a => congr_arg pos a.bit0_of_bit0
  | neg a => congr_arg neg a.bit0_of_bit0

theorem bit1_of_bit1 : ∀ n : Znum, bit1 n = n.bit1
  | 0 => rfl
  | Pos a => congr_arg pos a.bit1_of_bit1
  | neg a =>
    show PosNum.sub' 1 (bit0 a) = _ by
      rw [PosNum.one_sub', a.bit0_of_bit0] <;> rfl

@[simp, norm_cast]
theorem cast_bit0 [AddGroupWithOneₓ α] : ∀ n : Znum, (n.bit0 : α) = bit0 n
  | 0 => (add_zeroₓ _).symm
  | Pos p => by
    rw [Znum.bit0, cast_pos, cast_pos] <;> rfl
  | neg p => by
    rw [Znum.bit0, cast_neg, cast_neg, PosNum.cast_bit0, _root_.bit0, _root_.bit0, neg_add_rev]

@[simp, norm_cast]
theorem cast_bit1 [AddGroupWithOneₓ α] : ∀ n : Znum, (n.bit1 : α) = bit1 n
  | 0 => by
    simp [← Znum.bit1, ← _root_.bit1, ← _root_.bit0]
  | Pos p => by
    rw [Znum.bit1, cast_pos, cast_pos] <;> rfl
  | neg p => by
    rw [Znum.bit1, cast_neg, cast_neg]
    cases' e : pred' p with a <;> have : p = _ := (succ'_pred' p).symm.trans (congr_arg Num.succ' e)
    · change p = 1 at this
      subst p
      simp [← _root_.bit1, ← _root_.bit0]
      
    · rw [Num.succ'] at this
      subst p
      have : (↑(-↑a : ℤ) : α) = -1 + ↑(-↑a + 1 : ℤ) := by
        simp [← add_commₓ]
      simpa [← _root_.bit1, ← _root_.bit0, -add_commₓ]
      

@[simp]
theorem cast_bitm1 [AddGroupWithOneₓ α] (n : Znum) : (n.bitm1 : α) = bit0 n - 1 := by
  conv => lhs rw [← zneg_zneg n]
  rw [← zneg_bit1, cast_zneg, cast_bit1]
  have : ((-1 + n + n : ℤ) : α) = (n + n + -1 : ℤ) := by
    simp [← add_commₓ, ← add_left_commₓ]
  simpa [← _root_.bit1, ← _root_.bit0, ← sub_eq_add_neg, -Int.add_neg_one]

theorem add_zero (n : Znum) : n + 0 = n := by
  cases n <;> rfl

theorem zero_add (n : Znum) : 0 + n = n := by
  cases n <;> rfl

theorem add_one : ∀ n : Znum, n + 1 = succ n
  | 0 => rfl
  | Pos p => congr_arg pos p.add_one
  | neg p => by
    cases p <;> rfl

end Znum

namespace PosNum

variable {α : Type _}

theorem cast_to_znum : ∀ n : PosNum, (n : Znum) = Znum.pos n
  | 1 => rfl
  | bit0 p => (Znum.bit0_of_bit0 p).trans <| congr_arg _ (cast_to_znum p)
  | bit1 p => (Znum.bit1_of_bit1 p).trans <| congr_arg _ (cast_to_znum p)

attribute [-simp] Int.add_neg_one

theorem cast_sub' [AddGroupWithOneₓ α] : ∀ m n : PosNum, (sub' m n : α) = m - n
  | a, 1 => by
    rw [sub'_one, Num.cast_to_znum, ← Num.cast_to_nat, pred'_to_nat, ← Nat.sub_one] <;> simp [← PosNum.cast_pos]
  | 1, b => by
    rw [one_sub', Num.cast_to_znum_neg, ← neg_sub, neg_inj, ← Num.cast_to_nat, pred'_to_nat, ← Nat.sub_one] <;>
      simp [← PosNum.cast_pos]
  | bit0 a, bit0 b => by
    rw [sub', Znum.cast_bit0, cast_sub']
    have : ((a + -b + (a + -b) : ℤ) : α) = a + a + (-b + -b) := by
      simp [← add_left_commₓ]
    simpa [← _root_.bit0, ← sub_eq_add_neg]
  | bit0 a, bit1 b => by
    rw [sub', Znum.cast_bitm1, cast_sub']
    have : ((-b + (a + (-b + -1)) : ℤ) : α) = (a + -1 + (-b + -b) : ℤ) := by
      simp [← add_commₓ, ← add_left_commₓ]
    simpa [← _root_.bit1, ← _root_.bit0, ← sub_eq_add_neg]
  | bit1 a, bit0 b => by
    rw [sub', Znum.cast_bit1, cast_sub']
    have : ((-b + (a + (-b + 1)) : ℤ) : α) = (a + 1 + (-b + -b) : ℤ) := by
      simp [← add_commₓ, ← add_left_commₓ]
    simpa [← _root_.bit1, ← _root_.bit0, ← sub_eq_add_neg]
  | bit1 a, bit1 b => by
    rw [sub', Znum.cast_bit0, cast_sub']
    have : ((-b + (a + -b) : ℤ) : α) = a + (-b + -b) := by
      simp [← add_left_commₓ]
    simpa [← _root_.bit1, ← _root_.bit0, ← sub_eq_add_neg]

theorem to_nat_eq_succ_pred (n : PosNum) : (n : ℕ) = n.pred' + 1 := by
  rw [← Num.succ'_to_nat, n.succ'_pred']

theorem to_int_eq_succ_pred (n : PosNum) : (n : ℤ) = (n.pred' : ℕ) + 1 := by
  rw [← n.to_nat_to_int, to_nat_eq_succ_pred] <;> rfl

end PosNum

namespace Num

variable {α : Type _}

@[simp]
theorem cast_sub' [AddGroupWithOneₓ α] : ∀ m n : Num, (sub' m n : α) = m - n
  | 0, 0 => (sub_zero _).symm
  | Pos a, 0 => (sub_zero _).symm
  | 0, Pos b => (zero_sub _).symm
  | Pos a, Pos b => PosNum.cast_sub' _ _

theorem to_znum_succ : ∀ n : Num, n.succ.toZnum = n.toZnum.succ
  | 0 => rfl
  | Pos n => rfl

theorem to_znum_neg_succ : ∀ n : Num, n.succ.toZnumNeg = n.toZnumNeg.pred
  | 0 => rfl
  | Pos n => rfl

@[simp]
theorem pred_succ : ∀ n : Znum, n.pred.succ = n
  | 0 => rfl
  | Znum.neg p =>
    show toZnumNeg (pos p).succ'.pred' = _ by
      rw [PosNum.pred'_succ'] <;> rfl
  | Znum.pos p => by
    rw [Znum.pred, ← to_znum_succ, Num.succ, PosNum.succ'_pred', to_znum]

theorem succ_of_int' : ∀ n, Znum.ofInt' (n + 1) = Znum.ofInt' n + 1
  | (n : ℕ) => by
    erw [Znum.ofInt', Znum.ofInt', Num.of_nat'_succ, Num.add_one, to_znum_succ, Znum.add_one]
  | -[1+ 0] => by
    erw [Znum.ofInt', Znum.ofInt', of_nat'_succ, of_nat'_zero] <;> rfl
  | -[1+ n + 1] => by
    erw [Znum.ofInt', Znum.ofInt', @Num.of_nat'_succ (n + 1), Num.add_one, to_znum_neg_succ, @of_nat'_succ n,
      Num.add_one, Znum.add_one, pred_succ]

theorem of_int'_to_znum : ∀ n : ℕ, toZnum n = Znum.ofInt' n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.cast_succₓ, Num.add_one, to_znum_succ, of_int'_to_znum, Nat.cast_succₓ, succ_of_int', Znum.add_one]

theorem mem_of_znum' : ∀ {m : Num} {n : Znum}, m ∈ ofZnum' n ↔ n = toZnum m
  | 0, 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | Pos m, 0 =>
    ⟨fun h => by
      cases h, fun h => by
      cases h⟩
  | m, Znum.pos p =>
    Option.some_inj.trans <| by
      cases m <;>
        constructor <;>
          intro h <;>
            try
                cases h <;>
              rfl
  | m, Znum.neg p =>
    ⟨fun h => by
      cases h, fun h => by
      cases m <;> cases h⟩

theorem of_znum'_to_nat : ∀ n : Znum, coe <$> ofZnum' n = Int.toNat' n
  | 0 => rfl
  | Znum.pos p =>
    show _ = Int.toNat' p by
      rw [← PosNum.to_nat_to_int p] <;> rfl
  | Znum.neg p =>
    (congr_arg fun x => Int.toNat' (-x)) <|
      show ((p.pred' + 1 : ℕ) : ℤ) = p by
        rw [← succ'_to_nat] <;> simp

@[simp]
theorem of_znum_to_nat : ∀ n : Znum, (ofZnum n : ℕ) = Int.toNat n
  | 0 => rfl
  | Znum.pos p =>
    show _ = Int.toNat p by
      rw [← PosNum.to_nat_to_int p] <;> rfl
  | Znum.neg p =>
    (congr_arg fun x => Int.toNat (-x)) <|
      show ((p.pred' + 1 : ℕ) : ℤ) = p by
        rw [← succ'_to_nat] <;> simp

@[simp]
theorem cast_of_znum [AddGroupWithOneₓ α] (n : Znum) : (ofZnum n : α) = Int.toNat n := by
  rw [← cast_to_nat, of_znum_to_nat]

@[simp, norm_cast]
theorem sub_to_nat (m n) : ((m - n : Num) : ℕ) = m - n :=
  show (ofZnum _ : ℕ) = _ by
    rw [of_znum_to_nat, cast_sub', ← to_nat_to_int, ← to_nat_to_int, Int.to_nat_sub]

end Num

namespace Znum

variable {α : Type _}

@[simp, norm_cast]
theorem cast_add [AddGroupWithOneₓ α] : ∀ m n, ((m + n : Znum) : α) = m + n
  | 0, a => by
    cases a <;> exact (_root_.zero_add _).symm
  | b, 0 => by
    cases b <;> exact (_root_.add_zero _).symm
  | Pos a, Pos b => PosNum.cast_add _ _
  | Pos a, neg b => by
    simpa only [← sub_eq_add_neg] using PosNum.cast_sub' _ _
  | neg a, Pos b =>
    have : (↑b + -↑a : α) = -↑a + ↑b := by
      rw [← PosNum.cast_to_int a, ← PosNum.cast_to_int b, ← Int.cast_neg, ← Int.cast_add (-a)] <;> simp [← add_commₓ]
    (PosNum.cast_sub' _ _).trans <| (sub_eq_add_neg _ _).trans this
  | neg a, neg b =>
    show -(↑(a + b) : α) = -a + -b by
      rw [PosNum.cast_add, neg_eq_iff_neg_eq, neg_add_rev, neg_negₓ, neg_negₓ, ← PosNum.cast_to_int a, ←
          PosNum.cast_to_int b, ← Int.cast_add] <;>
        simp [← add_commₓ]

@[simp]
theorem cast_succ [AddGroupWithOneₓ α] (n) : ((succ n : Znum) : α) = n + 1 := by
  rw [← add_one, cast_add, cast_one]

@[simp, norm_cast]
theorem mul_to_int : ∀ m n, ((m * n : Znum) : ℤ) = m * n
  | 0, a => by
    cases a <;> exact (_root_.zero_mul _).symm
  | b, 0 => by
    cases b <;> exact (_root_.mul_zero _).symm
  | Pos a, Pos b => PosNum.cast_mul a b
  | Pos a, neg b =>
    show -↑(a * b) = ↑a * -↑b by
      rw [PosNum.cast_mul, neg_mul_eq_mul_neg]
  | neg a, Pos b =>
    show -↑(a * b) = -↑a * ↑b by
      rw [PosNum.cast_mul, neg_mul_eq_neg_mulₓ]
  | neg a, neg b =>
    show ↑(a * b) = -↑a * -↑b by
      rw [PosNum.cast_mul, neg_mul_neg]

theorem cast_mul [Ringₓ α] (m n) : ((m * n : Znum) : α) = m * n := by
  rw [← cast_to_int, mul_to_int, Int.cast_mul, cast_to_int, cast_to_int]

theorem of_int'_neg : ∀ n : ℤ, ofInt' (-n) = -ofInt' n
  | -[1+ n] =>
    show ofInt' (n + 1 : ℕ) = _ by
      simp only [← of_int', ← Num.zneg_to_znum_neg]
  | 0 =>
    show Num.toZnum _ = -Num.toZnum _ by
      rw [Num.of_nat'_zero] <;> rfl
  | (n + 1 : ℕ) =>
    show Num.toZnumNeg _ = -Num.toZnum _ by
      rw [Num.zneg_to_znum] <;> rfl

theorem of_to_int' : ∀ n : Znum, Znum.ofInt' n = n
  | 0 => by
    erw [of_int', Num.of_nat'_zero, Num.toZnum]
  | Pos a => by
    rw [cast_pos, ← PosNum.cast_to_nat, ← Num.of_int'_to_znum, PosNum.of_to_nat] <;> rfl
  | neg a => by
    rw [cast_neg, of_int'_neg, ← PosNum.cast_to_nat, ← Num.of_int'_to_znum, PosNum.of_to_nat] <;> rfl

theorem to_int_inj {m n : Znum} : (m : ℤ) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective of_to_int' h, congr_arg _⟩

theorem cmp_to_int : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℤ) < n) (m = n) ((n : ℤ) < m) : Prop)
  | 0, 0 => rfl
  | Pos a, Pos b => by
    have := PosNum.cmp_to_nat a b <;>
      revert this <;> dsimp' [← cmp] <;> cases PosNum.cmp a b <;> dsimp' <;> [simp , exact congr_arg Pos, simp [← Gt]]
  | neg a, neg b => by
    have := PosNum.cmp_to_nat b a <;>
      revert this <;>
        dsimp' [← cmp] <;>
          cases PosNum.cmp b a <;> dsimp' <;> [simp , simp (config := { contextual := true }), simp [← Gt]]
  | Pos a, 0 => PosNum.cast_pos _
  | Pos a, neg b => lt_transₓ (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, neg b => neg_lt_zero.2 <| PosNum.cast_pos _
  | neg a, 0 => neg_lt_zero.2 <| PosNum.cast_pos _
  | neg a, Pos b => lt_transₓ (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, Pos b => PosNum.cast_pos _

@[norm_cast]
theorem lt_to_int {m n : Znum} : (m : ℤ) < n ↔ m < n :=
  show (m : ℤ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_int m n with
    | Ordering.lt, h => by
      simp at h <;> simp [← h]
    | Ordering.eq, h => by
      simp at h <;>
        simp [← h, ← lt_irreflₓ] <;>
          exact by
            decide
    | Ordering.gt, h => by
      simp [← not_lt_of_gtₓ h] <;>
        exact by
          decide

theorem le_to_int {m n : Znum} : (m : ℤ) ≤ n ↔ m ≤ n := by
  rw [← not_ltₓ] <;> exact not_congr lt_to_int

@[simp, norm_cast]
theorem cast_lt [LinearOrderedRing α] {m n : Znum} : (m : α) < n ↔ m < n := by
  rw [← cast_to_int m, ← cast_to_int n, Int.cast_lt, lt_to_int]

@[simp, norm_cast]
theorem cast_le [LinearOrderedRing α] {m n : Znum} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_ltₓ] <;> exact not_congr cast_lt

@[simp, norm_cast]
theorem cast_inj [LinearOrderedRing α] {m n : Znum} : (m : α) = n ↔ m = n := by
  rw [← cast_to_int m, ← cast_to_int n, Int.cast_inj, to_int_inj]

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- This tactic tries to turn an (in)equality about `znum`s to one about `int`s by rewriting.
```lean
example (n : znum) (m : znum) : n ≤ n + m * m :=
begin
  znum.transfer_rw,
  exact le_add_of_nonneg_right (mul_self_nonneg _)
end
```
-/
unsafe def transfer_rw : tactic Unit :=
  sorry

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- This tactic tries to prove (in)equalities about `znum`s by transfering them to the `int` world and
then trying to call `simp`.
```lean
example (n : znum) (m : znum) : n ≤ n + m * m :=
begin
  znum.transfer,
  exact mul_self_nonneg _
end
```
-/
unsafe def transfer : tactic Unit :=
  sorry

instance : LinearOrderₓ Znum where
  lt := (· < ·)
  lt_iff_le_not_le := by
    intro a b
    run_tac
      transfer_rw
    apply lt_iff_le_not_leₓ
  le := (· ≤ ·)
  le_refl := by
    run_tac
      transfer
  le_trans := by
    intro a b c
    run_tac
      transfer_rw
    apply le_transₓ
  le_antisymm := by
    intro a b
    run_tac
      transfer_rw
    apply le_antisymmₓ
  le_total := by
    intro a b
    run_tac
      transfer_rw
    apply le_totalₓ
  DecidableEq := Znum.decidableEq
  decidableLe := Znum.decidableLe
  decidableLt := Znum.decidableLt

instance : AddCommGroupₓ Znum where
  add := (· + ·)
  add_assoc := by
    run_tac
      transfer
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  add_comm := by
    run_tac
      transfer
  neg := Neg.neg
  add_left_neg := by
    run_tac
      transfer

instance : AddMonoidWithOneₓ Znum :=
  { Znum.addCommGroup with one := 1, natCast := fun n => Znum.ofInt' n,
    nat_cast_zero :=
      show (Num.ofNat' 0).toZnum = 0 by
        rw [Num.of_nat'_zero] <;> rfl,
    nat_cast_succ := fun n =>
      show (Num.ofNat' (n + 1)).toZnum = (Num.ofNat' n).toZnum + 1 by
        rw [Num.of_nat'_succ, Num.add_one, Num.to_znum_succ, Znum.add_one] }

instance : LinearOrderedCommRing Znum :=
  { Znum.linearOrder, Znum.addCommGroup, Znum.addMonoidWithOne with mul := (· * ·),
    mul_assoc := by
      run_tac
        transfer,
    one := 1,
    one_mul := by
      run_tac
        transfer,
    mul_one := by
      run_tac
        transfer,
    left_distrib := by
      run_tac
        transfer
      simp [← mul_addₓ],
    right_distrib := by
      run_tac
        transfer
      simp [← mul_addₓ, ← mul_comm],
    mul_comm := by
      run_tac
        transfer,
    exists_pair_ne :=
      ⟨0, 1, by
        decide⟩,
    add_le_add_left := by
      intro a b h c
      revert h
      run_tac
        transfer_rw
      exact fun h => add_le_add_left h c,
    mul_pos := fun a b =>
      show 0 < a → 0 < b → 0 < a * b by
        run_tac
          transfer_rw
        apply mul_pos,
    zero_le_one := by
      decide }

@[simp, norm_cast]
theorem cast_sub [Ringₓ α] (m n) : ((m - n : Znum) : α) = m - n := by
  simp [← sub_eq_neg_add]

@[simp, norm_cast]
theorem neg_of_int : ∀ n, ((-n : ℤ) : Znum) = -n
  | (n + 1 : ℕ) => rfl
  | 0 => by
    rw [Int.cast_neg, Int.cast_zeroₓ]
  | -[1+ n] => (zneg_zneg _).symm

@[simp]
theorem of_int'_eq : ∀ n : ℤ, Znum.ofInt' n = n
  | (n : ℕ) => rfl
  | -[1+ n] => by
    show Num.toZnumNeg (n + 1 : ℕ) = -(n + 1 : ℕ)
    rw [← neg_inj, neg_negₓ, Nat.cast_succₓ, Num.add_one, Num.zneg_to_znum_neg, Num.to_znum_succ, Nat.cast_succₓ,
      Znum.add_one]
    rfl

@[simp]
theorem of_nat_to_znum (n : ℕ) : Num.toZnum n = n :=
  rfl

@[simp, norm_cast]
theorem of_to_int (n : Znum) : ((n : ℤ) : Znum) = n := by
  rw [← of_int'_eq, of_to_int']

theorem to_of_int (n : ℤ) : ((n : Znum) : ℤ) = n :=
  Int.inductionOn' n 0
    (by
      simp )
    (by
      simp )
    (by
      simp )

@[simp]
theorem of_nat_to_znum_neg (n : ℕ) : Num.toZnumNeg n = -n := by
  rw [← of_nat_to_znum, Num.zneg_to_znum]

@[simp, norm_cast]
theorem of_int_cast [AddGroupWithOneₓ α] (n : ℤ) : ((n : Znum) : α) = n := by
  rw [← cast_to_int, to_of_int]

@[simp, norm_cast]
theorem of_nat_cast [AddGroupWithOneₓ α] (n : ℕ) : ((n : Znum) : α) = n := by
  rw [← Int.cast_coe_nat, of_int_cast, Int.cast_coe_nat]

@[simp, norm_cast]
theorem dvd_to_int (m n : Znum) : (m : ℤ) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ =>
    ⟨k, by
      rw [← of_to_int n, e] <;> simp ⟩,
    fun ⟨k, e⟩ =>
    ⟨k, by
      simp [← e]⟩⟩

end Znum

namespace PosNum

theorem divmod_to_nat_aux {n d : PosNum} {q r : Num} (h₁ : (r : ℕ) + d * bit0 q = n) (h₂ : (r : ℕ) < 2 * d) :
    ((divmodAux d q r).2 + d * (divmodAux d q r).1 : ℕ) = ↑n ∧ ((divmodAux d q r).2 : ℕ) < d := by
  unfold divmod_aux
  have : ∀ {r₂}, Num.ofZnum' (Num.sub' r (Num.pos d)) = some r₂ ↔ (r : ℕ) = r₂ + d := by
    intro r₂
    apply num.mem_of_znum'.trans
    rw [← Znum.to_int_inj, Num.cast_to_znum, Num.cast_sub', sub_eq_iff_eq_add, ← Int.coe_nat_inj']
    simp
  cases' e : Num.ofZnum' (Num.sub' r (Num.pos d)) with r₂ <;> simp [← divmod_aux]
  · refine' ⟨h₁, lt_of_not_geₓ fun h => _⟩
    cases' Nat.Le.dest h with r₂ e'
    rw [← Num.to_of_nat r₂, add_commₓ] at e'
    cases e.symm.trans (this.2 e'.symm)
    
  · have := this.1 e
    constructor
    · rwa [_root_.bit1, add_commₓ _ 1, mul_addₓ, mul_oneₓ, ← add_assocₓ, ← this]
      
    · rwa [this, two_mul, add_lt_add_iff_right] at h₂
      
    

theorem divmod_to_nat (d n : PosNum) : (n / d : ℕ) = (divmod d n).1 ∧ (n % d : ℕ) = (divmod d n).2 := by
  rw [Nat.div_mod_unique (PosNum.cast_pos _)]
  induction' n with n IH n IH
  · exact
      divmod_to_nat_aux
        (by
          simp <;> rfl)
        (Nat.mul_le_mul_leftₓ 2 (PosNum.cast_pos d : (0 : ℕ) < d))
    
  · unfold divmod
    cases' divmod d n with q r
    simp only [← divmod] at IH⊢
    apply divmod_to_nat_aux <;> simp
    · rw [_root_.bit1, _root_.bit1, add_right_commₓ, bit0_eq_two_mul (n : ℕ), ← IH.1, mul_addₓ, ← bit0_eq_two_mul,
        mul_left_commₓ, ← bit0_eq_two_mul]
      
    · rw [← bit0_eq_two_mul]
      exact Nat.bit1_lt_bit0 IH.2
      
    
  · unfold divmod
    cases' divmod d n with q r
    simp only [← divmod] at IH⊢
    apply divmod_to_nat_aux <;> simp
    · rw [bit0_eq_two_mul (n : ℕ), ← IH.1, mul_addₓ, ← bit0_eq_two_mul, mul_left_commₓ, ← bit0_eq_two_mul]
      
    · rw [← bit0_eq_two_mul]
      exact Nat.bit0_lt IH.2
      
    

@[simp]
theorem div'_to_nat (n d) : (div' n d : ℕ) = n / d :=
  (divmod_to_nat _ _).1.symm

@[simp]
theorem mod'_to_nat (n d) : (mod' n d : ℕ) = n % d :=
  (divmod_to_nat _ _).2.symm

end PosNum

namespace Num

@[simp]
protected theorem div_zero (n : Num) : n / 0 = 0 :=
  show n.div 0 = 0 by
    cases n
    rfl
    simp [← Num.div]

@[simp, norm_cast]
theorem div_to_nat : ∀ n d, ((n / d : Num) : ℕ) = n / d
  | 0, 0 => by
    simp
  | 0, Pos d => (Nat.zero_divₓ _).symm
  | Pos n, 0 => (Nat.div_zeroₓ _).symm
  | Pos n, Pos d => PosNum.div'_to_nat _ _

@[simp]
protected theorem mod_zero (n : Num) : n % 0 = n :=
  show n.mod 0 = n by
    cases n
    rfl
    simp [← Num.mod]

@[simp, norm_cast]
theorem mod_to_nat : ∀ n d, ((n % d : Num) : ℕ) = n % d
  | 0, 0 => by
    simp
  | 0, Pos d => (Nat.zero_modₓ _).symm
  | Pos n, 0 => (Nat.mod_zeroₓ _).symm
  | Pos n, Pos d => PosNum.mod'_to_nat _ _

theorem gcd_to_nat_aux : ∀ {n} {a b : Num}, a ≤ b → (a * b).natSize ≤ n → (gcdAux n a b : ℕ) = Nat.gcdₓ a b
  | 0, 0, b, ab, h => (Nat.gcd_zero_leftₓ _).symm
  | 0, Pos a, 0, ab, h => (not_lt_of_geₓ ab).elim rfl
  | 0, Pos a, Pos b, ab, h => (not_lt_of_le h).elim <| PosNum.nat_size_pos _
  | Nat.succ n, 0, b, ab, h => (Nat.gcd_zero_leftₓ _).symm
  | Nat.succ n, Pos a, b, ab, h => by
    simp [← gcd_aux]
    rw [Nat.gcd_recₓ, gcd_to_nat_aux, mod_to_nat]
    · rfl
      
    · rw [← le_to_nat, mod_to_nat]
      exact le_of_ltₓ (Nat.mod_ltₓ _ (PosNum.cast_pos _))
      
    rw [nat_size_to_nat, mul_to_nat, Nat.size_le] at h⊢
    rw [mod_to_nat, mul_comm]
    rw [pow_succ'ₓ, ← Nat.mod_add_divₓ b (Pos a)] at h
    refine' lt_of_mul_lt_mul_right (lt_of_le_of_ltₓ _ h) (Nat.zero_leₓ 2)
    rw [mul_two, mul_addₓ]
    refine' add_le_add_left (Nat.mul_le_mul_leftₓ _ (le_transₓ (le_of_ltₓ (Nat.mod_ltₓ _ (PosNum.cast_pos _))) _)) _
    suffices : 1 ≤ _
    simpa using Nat.mul_le_mul_leftₓ (Pos a) this
    rw [Nat.le_div_iff_mul_leₓ a.cast_pos, one_mulₓ]
    exact le_to_nat.2 ab

@[simp]
theorem gcd_to_nat : ∀ a b, (gcd a b : ℕ) = Nat.gcdₓ a b := by
  have : ∀ a b : Num, (a * b).natSize ≤ a.natSize + b.natSize := by
    intros
    simp [← nat_size_to_nat]
    rw [Nat.size_le, pow_addₓ]
    exact mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _) (Nat.zero_leₓ _) (Nat.zero_leₓ _)
  intros
  unfold gcd
  split_ifs
  · exact gcd_to_nat_aux h (this _ _)
    
  · rw [Nat.gcd_commₓ]
    exact gcd_to_nat_aux (le_of_not_leₓ h) (this _ _)
    

theorem dvd_iff_mod_eq_zero {m n : Num} : m ∣ n ↔ n % m = 0 := by
  rw [← dvd_to_nat, Nat.dvd_iff_mod_eq_zeroₓ, ← to_nat_inj, mod_to_nat] <;> rfl

instance decidableDvd : DecidableRel ((· ∣ ·) : Num → Num → Prop)
  | a, b => decidableOfIff' _ dvd_iff_mod_eq_zero

end Num

instance PosNum.decidableDvd : DecidableRel ((· ∣ ·) : PosNum → PosNum → Prop)
  | a, b => Num.decidableDvd _ _

namespace Znum

@[simp]
protected theorem div_zero (n : Znum) : n / 0 = 0 :=
  show n.div 0 = 0 by
    cases n <;>
      first |
        rfl|
        simp [← Znum.div]

@[simp, norm_cast]
theorem div_to_int : ∀ n d, ((n / d : Znum) : ℤ) = n / d
  | 0, 0 => by
    simp [← Int.div_zero]
  | 0, Pos d => (Int.zero_div _).symm
  | 0, neg d => (Int.zero_div _).symm
  | Pos n, 0 => (Int.div_zero _).symm
  | neg n, 0 => (Int.div_zero _).symm
  | Pos n, Pos d =>
    (Num.cast_to_znum _).trans <| by
      rw [← Num.to_nat_to_int] <;> simp
  | Pos n, neg d =>
    (Num.cast_to_znum_neg _).trans <| by
      rw [← Num.to_nat_to_int] <;> simp
  | neg n, Pos d =>
    show -_ = -_ / ↑d by
      rw [n.to_int_eq_succ_pred, d.to_int_eq_succ_pred, ← PosNum.to_nat_to_int, Num.succ'_to_nat, Num.div_to_nat]
      change -[1+ n.pred' / ↑d] = -[1+ n.pred' / (d.pred' + 1)]
      rw [d.to_nat_eq_succ_pred]
  | neg n, neg d =>
    show ↑(PosNum.pred' n / Num.pos d).succ' = -_ / -↑d by
      rw [n.to_int_eq_succ_pred, d.to_int_eq_succ_pred, ← PosNum.to_nat_to_int, Num.succ'_to_nat, Num.div_to_nat]
      change (Nat.succ (_ / d) : ℤ) = Nat.succ (n.pred' / (d.pred' + 1))
      rw [d.to_nat_eq_succ_pred]

@[simp, norm_cast]
theorem mod_to_int : ∀ n d, ((n % d : Znum) : ℤ) = n % d
  | 0, d => (Int.zero_mod _).symm
  | Pos n, d =>
    (Num.cast_to_znum _).trans <| by
      rw [← Num.to_nat_to_int, cast_pos, Num.mod_to_nat, ← PosNum.to_nat_to_int, abs_to_nat] <;> rfl
  | neg n, d =>
    (Num.cast_sub' _ _).trans <| by
      rw [← Num.to_nat_to_int, cast_neg, ← Num.to_nat_to_int, Num.succ_to_nat, Num.mod_to_nat, abs_to_nat, ←
          Int.sub_nat_nat_eq_coe, n.to_int_eq_succ_pred] <;>
        rfl

@[simp]
theorem gcd_to_nat (a b) : (gcd a b : ℕ) = Int.gcdₓ a b :=
  (Num.gcd_to_nat _ _).trans <| by
    simpa

theorem dvd_iff_mod_eq_zero {m n : Znum} : m ∣ n ↔ n % m = 0 := by
  rw [← dvd_to_int, Int.dvd_iff_mod_eq_zero, ← to_int_inj, mod_to_int] <;> rfl

instance : DecidableRel ((· ∣ ·) : Znum → Znum → Prop)
  | a, b => decidableOfIff' _ dvd_iff_mod_eq_zero

end Znum

namespace Int

/-- Cast a `snum` to the corresponding integer. -/
def ofSnum : Snum → ℤ :=
  Snum.rec' (fun a => cond a (-1) 0) fun a p IH => cond a (bit1 IH) (bit0 IH)

instance snumCoe : Coe Snum ℤ :=
  ⟨ofSnum⟩

end Int

instance : LT Snum :=
  ⟨fun a b => (a : ℤ) < b⟩

instance : LE Snum :=
  ⟨fun a b => (a : ℤ) ≤ b⟩

