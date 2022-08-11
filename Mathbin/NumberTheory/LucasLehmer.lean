/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison, Ainsley Pahljina
-/
import Mathbin.Data.Nat.Parity
import Mathbin.Data.Pnat.Interval
import Mathbin.Data.Zmod.Basic
import Mathbin.GroupTheory.OrderOfElement
import Mathbin.RingTheory.Fintype
import Mathbin.Tactic.IntervalCases
import Mathbin.Tactic.RingExp

/-!
# The Lucas-Lehmer test for Mersenne primes.

We define `lucas_lehmer_residue : Π p : ℕ, zmod (2^p - 1)`, and
prove `lucas_lehmer_residue p = 0 → prime (mersenne p)`.

We construct a tactic `lucas_lehmer.run_test`, which iteratively certifies the arithmetic
required to calculate the residue, and enables us to prove

```
example : prime (mersenne 127) :=
lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test)
```

## TODO

- Show reverse implication.
- Speed up the calculations using `n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]`.
- Find some bigger primes!

## History

This development began as a student project by Ainsley Pahljina,
and was then cleaned up for mathlib by Scott Morrison.
The tactic for certified computation of Lucas-Lehmer residues was provided by Mario Carneiro.
-/


/-- The Mersenne numbers, 2^p - 1. -/
def mersenne (p : ℕ) : ℕ :=
  2 ^ p - 1

theorem mersenne_pos {p : ℕ} (h : 0 < p) : 0 < mersenne p := by
  dsimp' [← mersenne]
  calc 0 < 2 ^ 1 - 1 := by
      norm_num _ ≤ 2 ^ p - 1 := Nat.pred_le_predₓ (Nat.pow_le_pow_of_le_rightₓ (Nat.succ_posₓ 1) h)

@[simp]
theorem succ_mersenne (k : ℕ) : mersenne k + 1 = 2 ^ k := by
  rw [mersenne, tsub_add_cancel_of_le]
  exact
    one_le_pow_of_one_le
      (by
        norm_num)
      k

namespace LucasLehmer

open Nat

/-!
We now define three(!) different versions of the recurrence
`s (i+1) = (s i)^2 - 2`.

These versions take values either in `ℤ`, in `zmod (2^p - 1)`, or
in `ℤ` but applying `% (2^p - 1)` at each step.

They are each useful at different points in the proof,
so we take a moment setting up the lemmas relating them.
-/


/-- The recurrence `s (i+1) = (s i)^2 - 2` in `ℤ`. -/
def s : ℕ → ℤ
  | 0 => 4
  | i + 1 => s i ^ 2 - 2

/-- The recurrence `s (i+1) = (s i)^2 - 2` in `zmod (2^p - 1)`. -/
def sZmod (p : ℕ) : ℕ → Zmod (2 ^ p - 1)
  | 0 => 4
  | i + 1 => s_zmod i ^ 2 - 2

/-- The recurrence `s (i+1) = ((s i)^2 - 2) % (2^p - 1)` in `ℤ`. -/
def sMod (p : ℕ) : ℕ → ℤ
  | 0 => 4 % (2 ^ p - 1)
  | i + 1 => (s_mod i ^ 2 - 2) % (2 ^ p - 1)

theorem mersenne_int_ne_zero (p : ℕ) (w : 0 < p) : (2 ^ p - 1 : ℤ) ≠ 0 := by
  apply ne_of_gtₓ
  simp only [← gt_iff_lt, ← sub_pos]
  exact_mod_cast Nat.one_lt_two_pow p w

theorem s_mod_nonneg (p : ℕ) (w : 0 < p) (i : ℕ) : 0 ≤ sMod p i := by
  cases i <;> dsimp' [← s_mod]
  · exact sup_eq_left.mp rfl
    
  · apply Int.mod_nonneg
    exact mersenne_int_ne_zero p w
    

theorem s_mod_mod (p i : ℕ) : sMod p i % (2 ^ p - 1) = sMod p i := by
  cases i <;> simp [← s_mod]

theorem s_mod_lt (p : ℕ) (w : 0 < p) (i : ℕ) : sMod p i < 2 ^ p - 1 := by
  rw [← s_mod_mod]
  convert Int.mod_lt _ _
  · refine' (abs_of_nonneg _).symm
    simp only [← sub_nonneg, ← ge_iff_le]
    exact_mod_cast Nat.one_le_two_pow p
    
  · exact mersenne_int_ne_zero p w
    

theorem s_zmod_eq_s (p' : ℕ) (i : ℕ) : sZmod (p' + 2) i = (s i : Zmod (2 ^ (p' + 2) - 1)) := by
  induction' i with i ih
  · dsimp' [← s, ← s_zmod]
    norm_num
    
  · push_cast [← s, ← s_zmod, ← ih]
    

-- These next two don't make good `norm_cast` lemmas.
theorem Int.coe_nat_pow_pred (b p : ℕ) (w : 0 < b) : ((b ^ p - 1 : ℕ) : ℤ) = (b ^ p - 1 : ℤ) := by
  have : 1 ≤ b ^ p := Nat.one_le_pow p b w
  norm_cast

theorem Int.coe_nat_two_pow_pred (p : ℕ) : ((2 ^ p - 1 : ℕ) : ℤ) = (2 ^ p - 1 : ℤ) :=
  Int.coe_nat_pow_pred 2 p
    (by
      decide)

theorem s_zmod_eq_s_mod (p : ℕ) (i : ℕ) : sZmod p i = (sMod p i : Zmod (2 ^ p - 1)) := by
  induction i <;> push_cast [int.coe_nat_two_pow_pred p, ← s_mod, ← s_zmod, *]

/-- The Lucas-Lehmer residue is `s p (p-2)` in `zmod (2^p - 1)`. -/
def lucasLehmerResidue (p : ℕ) : Zmod (2 ^ p - 1) :=
  sZmod p (p - 2)

theorem residue_eq_zero_iff_s_mod_eq_zero (p : ℕ) (w : 1 < p) : lucasLehmerResidue p = 0 ↔ sMod p (p - 2) = 0 := by
  dsimp' [← lucas_lehmer_residue]
  rw [s_zmod_eq_s_mod p]
  constructor
  · -- We want to use that fact that `0 ≤ s_mod p (p-2) < 2^p - 1`
    -- and `lucas_lehmer_residue p = 0 → 2^p - 1 ∣ s_mod p (p-2)`.
    intro h
    simp [← Zmod.int_coe_zmod_eq_zero_iff_dvd] at h
    apply Int.eq_zero_of_dvd_of_nonneg_of_lt _ _ h <;> clear h
    apply s_mod_nonneg _ (Nat.lt_of_succ_ltₓ w)
    exact s_mod_lt _ (Nat.lt_of_succ_ltₓ w) (p - 2)
    
  · intro h
    rw [h]
    simp
    

/-- A Mersenne number `2^p-1` is prime if and only if
the Lucas-Lehmer residue `s p (p-2) % (2^p - 1)` is zero.
-/
def LucasLehmerTest (p : ℕ) : Prop :=
  lucasLehmerResidue p = 0deriving DecidablePred

/-- `q` is defined as the minimum factor of `mersenne p`, bundled as an `ℕ+`. -/
def q (p : ℕ) : ℕ+ :=
  ⟨Nat.minFac (mersenne p), Nat.min_fac_pos (mersenne p)⟩

@[local instance]
theorem fact_pnat_pos (q : ℕ+) : Fact (0 < (q : ℕ)) :=
  ⟨q.2⟩

/-- We construct the ring `X q` as ℤ/qℤ + √3 ℤ/qℤ. -/
-- It would be nice to define this as (ℤ/qℤ)[x] / (x^2 - 3),
-- obtaining the ring structure for free,
-- but that seems to be more trouble than it's worth;
-- if it were easy to make the definition,
-- cardinality calculations would be somewhat more involved, too.
def X (q : ℕ+) : Type :=
  Zmod q × Zmod q deriving AddCommGroupₓ, DecidableEq, Fintype, Inhabited

namespace X

variable {q : ℕ+}

@[ext]
theorem ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  cases x
  cases y
  congr <;> assumption

@[simp]
theorem add_fst (x y : X q) : (x + y).1 = x.1 + y.1 :=
  rfl

@[simp]
theorem add_snd (x y : X q) : (x + y).2 = x.2 + y.2 :=
  rfl

@[simp]
theorem neg_fst (x : X q) : (-x).1 = -x.1 :=
  rfl

@[simp]
theorem neg_snd (x : X q) : (-x).2 = -x.2 :=
  rfl

instance : Mul (X q) where mul := fun x y => (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[simp]
theorem mul_fst (x y : X q) : (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2 :=
  rfl

@[simp]
theorem mul_snd (x y : X q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 :=
  rfl

instance : One (X q) where one := ⟨1, 0⟩

@[simp]
theorem one_fst : (1 : X q).1 = 1 :=
  rfl

@[simp]
theorem one_snd : (1 : X q).2 = 0 :=
  rfl

@[simp]
theorem bit0_fst (x : X q) : (bit0 x).1 = bit0 x.1 :=
  rfl

@[simp]
theorem bit0_snd (x : X q) : (bit0 x).2 = bit0 x.2 :=
  rfl

@[simp]
theorem bit1_fst (x : X q) : (bit1 x).1 = bit1 x.1 :=
  rfl

@[simp]
theorem bit1_snd (x : X q) : (bit1 x).2 = bit0 x.2 := by
  dsimp' [← bit1]
  simp

instance : Monoidₓ (X q) :=
  { (inferInstance : Mul (X q)) with
    mul_assoc := fun x y z => by
      ext <;>
        · dsimp'
          ring
          ,
    one := ⟨1, 0⟩,
    one_mul := fun x => by
      ext <;> simp ,
    mul_one := fun x => by
      ext <;> simp }

instance : AddGroupWithOneₓ (X q) :=
  { X.monoid, X.addCommGroup _ with natCast := fun n => ⟨n, 0⟩,
    nat_cast_zero := by
      simp ,
    nat_cast_succ := by
      simp [← Nat.castₓ, ← Monoidₓ.one],
    intCast := fun n => ⟨n, 0⟩,
    int_cast_of_nat := fun n => by
      simp <;> rfl,
    int_cast_neg_succ_of_nat := fun n => by
      ext <;> simp <;> rfl }

theorem left_distrib (x y z : X q) : x * (y + z) = x * y + x * z := by
  ext <;>
    · dsimp'
      ring
      

theorem right_distrib (x y z : X q) : (x + y) * z = x * z + y * z := by
  ext <;>
    · dsimp'
      ring
      

instance : Ringₓ (X q) :=
  { X.addGroupWithOne, (inferInstance : AddCommGroupₓ (X q)), (inferInstance : Monoidₓ (X q)) with
    left_distrib := left_distrib, right_distrib := right_distrib }

instance : CommRingₓ (X q) :=
  { (inferInstance : Ringₓ (X q)) with
    mul_comm := fun x y => by
      ext <;>
        · dsimp'
          ring
           }

instance [Fact (1 < (q : ℕ))] : Nontrivial (X q) :=
  ⟨⟨0, 1, fun h => by
      injection h with h1 _
      exact zero_ne_one h1⟩⟩

@[simp]
theorem nat_coe_fst (n : ℕ) : (n : X q).fst = (n : Zmod q) :=
  rfl

@[simp]
theorem nat_coe_snd (n : ℕ) : (n : X q).snd = (0 : Zmod q) :=
  rfl

@[simp]
theorem int_coe_fst (n : ℤ) : (n : X q).fst = (n : Zmod q) :=
  rfl

@[simp]
theorem int_coe_snd (n : ℤ) : (n : X q).snd = (0 : Zmod q) :=
  rfl

@[norm_cast]
theorem coe_mul (n m : ℤ) : ((n * m : ℤ) : X q) = (n : X q) * (m : X q) := by
  ext <;> simp <;> ring

@[norm_cast]
theorem coe_nat (n : ℕ) : ((n : ℤ) : X q) = (n : X q) := by
  ext <;> simp

/-- The cardinality of `X` is `q^2`. -/
theorem X_card : Fintype.card (X q) = q ^ 2 := by
  dsimp' [← X]
  rw [Fintype.card_prod, Zmod.card q]
  ring

/-- There are strictly fewer than `q^2` units, since `0` is not a unit. -/
theorem units_card (w : 1 < q) : Fintype.card (X q)ˣ < q ^ 2 := by
  have : Fact (1 < (q : ℕ)) := ⟨w⟩
  convert card_units_lt (X q)
  rw [X_card]

/-- We define `ω = 2 + √3`. -/
def ω : X q :=
  (2, 1)

/-- We define `ωb = 2 - √3`, which is the inverse of `ω`. -/
def ωb : X q :=
  (2, -1)

theorem ω_mul_ωb (q : ℕ+) : (ω : X q) * ωb = 1 := by
  dsimp' [← ω, ← ωb]
  ext <;> simp <;> ring

theorem ωb_mul_ω (q : ℕ+) : (ωb : X q) * ω = 1 := by
  dsimp' [← ω, ← ωb]
  ext <;> simp <;> ring

/-- A closed form for the recurrence relation. -/
theorem closed_form (i : ℕ) : (s i : X q) = (ω : X q) ^ 2 ^ i + (ωb : X q) ^ 2 ^ i := by
  induction' i with i ih
  · dsimp' [← s, ← ω, ← ωb]
    ext <;>
      · simp <;> rfl
        
    
  · calc (s (i + 1) : X q) = (s i ^ 2 - 2 : ℤ) := rfl _ = (s i : X q) ^ 2 - 2 := by
        push_cast _ = (ω ^ 2 ^ i + ωb ^ 2 ^ i) ^ 2 - 2 := by
        rw [ih]_ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 + 2 * (ωb ^ 2 ^ i * ω ^ 2 ^ i) - 2 := by
        ring _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 := by
        rw [← mul_powₓ ωb ω, ωb_mul_ω, one_pow, mul_oneₓ, add_sub_cancel]_ = ω ^ 2 ^ (i + 1) + ωb ^ 2 ^ (i + 1) := by
        rw [← pow_mulₓ, ← pow_mulₓ, pow_succ'ₓ]
    

end X

open X

/-!
Here and below, we introduce `p' = p - 2`, in order to avoid using subtraction in `ℕ`.
-/


/-- If `1 < p`, then `q p`, the smallest prime factor of `mersenne p`, is more than 2. -/
theorem two_lt_q (p' : ℕ) : 2 < q (p' + 2) := by
  by_contra H
  simp at H
  interval_cases q (p' + 2) <;> clear H
  · -- If q = 1, we get a contradiction from 2^p = 2
    dsimp' [← q]  at h
    injection h with h'
    clear h
    simp [← mersenne] at h'
    exact
      lt_irreflₓ 2
        (calc
          2 ≤ p' + 2 := Nat.le_add_leftₓ _ _
          _ < 2 ^ (p' + 2) := Nat.lt_two_pow _
          _ = 2 :=
            Nat.pred_injₓ (Nat.one_le_two_pow _)
              (by
                decide)
              h'
          )
    
  · -- If q = 2, we get a contradiction from 2 ∣ 2^p - 1
    dsimp' [← q]  at h
    injection h with h'
    clear h
    rw [mersenne, Pnat.one_coe, Nat.min_fac_eq_two_iff, pow_succₓ] at h'
    exact Nat.two_not_dvd_two_mul_sub_one (Nat.one_le_two_pow _) h'
    

theorem ω_pow_formula (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    ∃ k : ℤ, (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) = k * mersenne (p' + 2) * (ω : X (q (p' + 2))) ^ 2 ^ p' - 1 := by
  dsimp' [← lucas_lehmer_residue]  at h
  rw [s_zmod_eq_s p'] at h
  simp [← Zmod.int_coe_zmod_eq_zero_iff_dvd] at h
  cases' h with k h
  use k
  replace h := congr_arg (fun n : ℤ => (n : X (q (p' + 2)))) h
  -- coercion from ℤ to X q
  dsimp'  at h
  rw [closed_form] at h
  replace h := congr_arg (fun x => ω ^ 2 ^ p' * x) h
  dsimp'  at h
  have t : 2 ^ p' + 2 ^ p' = 2 ^ (p' + 1) := by
    ring_exp
  rw [mul_addₓ, ← pow_addₓ ω, t, ← mul_powₓ ω ωb (2 ^ p'), ω_mul_ωb, one_pow] at h
  rw [mul_comm, coe_mul] at h
  rw [mul_comm _ (k : X (q (p' + 2)))] at h
  replace h := eq_sub_of_add_eq h
  have : 1 ≤ 2 ^ (p' + 2) :=
    Nat.one_le_pow _ _
      (by
        decide)
  exact_mod_cast h

/-- `q` is the minimum factor of `mersenne p`, so `M p = 0` in `X q`. -/
theorem mersenne_coe_X (p : ℕ) : (mersenne p : X (q p)) = 0 := by
  ext <;> simp [← mersenne, ← q, ← Zmod.nat_coe_zmod_eq_zero_iff_dvd, -pow_pos]
  apply Nat.min_fac_dvd

theorem ω_pow_eq_neg_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) : (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) = -1 := by
  cases' ω_pow_formula p' h with k w
  rw [mersenne_coe_X] at w
  simpa using w

theorem ω_pow_eq_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) : (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = 1 :=
  calc
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = (ω ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mulₓ, ← pow_succ'ₓ]
    _ = -1 ^ 2 := by
      rw [ω_pow_eq_neg_one p' h]
    _ = 1 := by
      simp
    

/-- `ω` as an element of the group of units. -/
def ωUnit (p : ℕ) : Units (X (q p)) where
  val := ω
  inv := ωb
  val_inv := by
    simp [← ω_mul_ωb]
  inv_val := by
    simp [← ωb_mul_ω]

@[simp]
theorem ω_unit_coe (p : ℕ) : (ωUnit p : X (q p)) = ω :=
  rfl

/-- The order of `ω` in the unit group is exactly `2^p`. -/
theorem order_ω (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) : orderOf (ωUnit (p' + 2)) = 2 ^ (p' + 2) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow
  -- the order of ω divides 2^p
  · norm_num
    
  · intro o
    have ω_pow := order_of_dvd_iff_pow_eq_one.1 o
    replace ω_pow := congr_arg (Units.coeHom (X (q (p' + 2))) : Units (X (q (p' + 2))) → X (q (p' + 2))) ω_pow
    simp at ω_pow
    have h : (1 : Zmod (q (p' + 2))) = -1 := congr_arg Prod.fst (ω_pow.symm.trans (ω_pow_eq_neg_one p' h))
    have : Fact (2 < (q (p' + 2) : ℕ)) := ⟨two_lt_q _⟩
    apply Zmod.neg_one_ne_one h.symm
    
  · apply order_of_dvd_iff_pow_eq_one.2
    apply Units.ext
    push_cast
    exact ω_pow_eq_one p' h
    

theorem order_ineq (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) : 2 ^ (p' + 2) < (q (p' + 2) : ℕ) ^ 2 :=
  calc
    2 ^ (p' + 2) = orderOf (ωUnit (p' + 2)) := (order_ω p' h).symm
    _ ≤ Fintype.card (X _)ˣ := order_of_le_card_univ
    _ < (q (p' + 2) : ℕ) ^ 2 := units_card (Nat.lt_of_succ_ltₓ (two_lt_q _))
    

end LucasLehmer

export LucasLehmer (LucasLehmerTest lucasLehmerResidue)

open LucasLehmer

theorem lucas_lehmer_sufficiency (p : ℕ) (w : 1 < p) : LucasLehmerTest p → (mersenne p).Prime := by
  let p' := p - 2
  have z : p = p' + 2 := (tsub_eq_iff_eq_add_of_le w.nat_succ_le).mp rfl
  have w : 1 < p' + 2 := Nat.lt_of_sub_eq_succₓ rfl
  contrapose
  intro a t
  rw [z] at a
  rw [z] at t
  have h₁ := order_ineq p' t
  have h₂ := Nat.min_fac_sq_le_self (mersenne_pos (Nat.lt_of_succ_ltₓ w)) a
  have h := lt_of_lt_of_leₓ h₁ h₂
  exact not_lt_of_geₓ (Nat.sub_leₓ _ _) h

-- Here we calculate the residue, very inefficiently, using `dec_trivial`. We can do much better.
example : (mersenne 5).Prime :=
  lucas_lehmer_sufficiency 5
    (by
      norm_num)
    (by
      decide)

-- Next we use `norm_num` to calculate each `s p i`.
namespace LucasLehmer

open Tactic

theorem s_mod_succ {p a i b c} (h1 : (2 ^ p - 1 : ℤ) = a) (h2 : sMod p i = b) (h3 : (b * b - 2) % a = c) :
    sMod p (i + 1) = c := by
  dsimp' [← s_mod, ← mersenne]
  rw [h1, h2, sq, h3]

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Given a goal of the form `lucas_lehmer_test p`,
attempt to do the calculation using `norm_num` to certify each step.
-/
unsafe def run_test : tactic Unit := do
  let quote.1 (LucasLehmerTest (%%ₓp)) ← target
  sorry
  sorry
  let p ← eval_expr ℕ p
  let-- Calculate the candidate Mersenne prime
  M : ℤ := 2 ^ p - 1
  let t ← to_expr (pquote.1 ((2 ^ %%ₓquote.1 p) - 1 = %%ₓquote.1 M))
  let v ←
    to_expr
        (pquote.1
          (by
            norm_num : (2 ^ %%ₓquote.1 p) - 1 = %%ₓquote.1 M))
  let w ← assertv `w t v
  let t
    ←-- base case
        to_expr
        (pquote.1 (sMod (%%ₓquote.1 p) 0 = 4))
  let v ←
    to_expr
        (pquote.1
          (by
            norm_num [← LucasLehmer.sMod] : sMod (%%ₓquote.1 p) 0 = 4))
  let h ← assertv `h t v
  -- step case, repeated p-2 times
      iterate_exactly
      (p - 2) sorry
  let h
    ←-- now close the goal
        get_local
        `h
  exact h

end LucasLehmer

/-- We verify that the tactic works to prove `127.prime`. -/
example : (mersenne 7).Prime :=
  lucas_lehmer_sufficiency _
    (by
      norm_num)
    (by
      run_tac
        lucas_lehmer.run_test)

/-!
This implementation works successfully to prove `(2^127 - 1).prime`,
and all the Mersenne primes up to this point appear in [archive/examples/mersenne_primes.lean].

`(2^127 - 1).prime` takes about 5 minutes to run (depending on your CPU!),
and unfortunately the next Mersenne prime `(2^521 - 1)`,
which was the first "computer era" prime,
is out of reach with the current implementation.

There's still low hanging fruit available to do faster computations
based on the formula
```
n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]
```
and the fact that `% 2^p` and `/ 2^p` can be very efficient on the binary representation.
Someone should do this, too!
-/


theorem modeq_mersenne (n k : ℕ) : k ≡ k / 2 ^ n + k % 2 ^ n [MOD 2 ^ n - 1] := by
  -- See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/help.20finding.20a.20lemma/near/177698446
  conv in k => rw [← Nat.div_add_modₓ k (2 ^ n)]
  refine' Nat.Modeq.add_right _ _
  conv => congr skip skip rw [← one_mulₓ (k / 2 ^ n)]
  exact (Nat.modeq_sub <| Nat.succ_le_of_ltₓ <| pow_pos zero_lt_two _).mul_right _

-- It's hard to know what the limiting factor for large Mersenne primes would be.
-- In the purely computational world, I think it's the squaring operation in `s`.
