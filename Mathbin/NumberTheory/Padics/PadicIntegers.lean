/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
import Mathbin.Data.Int.Modeq
import Mathbin.NumberTheory.Padics.PadicNumbers
import Mathbin.RingTheory.DiscreteValuationRing
import Mathbin.Topology.MetricSpace.CauSeqFilter

/-!
# p-adic integers

This file defines the p-adic integers `ℤ_p` as the subtype of `ℚ_p` with norm `≤ 1`.
We show that `ℤ_p`
* is complete
* is nonarchimedean
* is a normed ring
* is a local ring
* is a discrete valuation ring

The relation between `ℤ_[p]` and `zmod p` is established in another file.

## Important definitions

* `padic_int` : the type of p-adic numbers

## Notation

We introduce the notation `ℤ_[p]` for the p-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (nat.prime p)] as a type class argument.

Coercions into `ℤ_p` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/


open Padic Metric LocalRing

noncomputable section

open Classical

/-- The p-adic integers ℤ_p are the p-adic numbers with norm ≤ 1. -/
def PadicInt (p : ℕ) [Fact p.Prime] :=
  { x : ℚ_[p] // ∥x∥ ≤ 1 }

-- mathport name: «exprℤ_[ ]»
notation "ℤ_[" p "]" => PadicInt p

namespace PadicInt

/-! ### Ring structure and coercion to `ℚ_[p]` -/


variable {p : ℕ} [Fact p.Prime]

instance : Coe ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val⟩

theorem ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y :=
  Subtype.ext_iff_val.2

/-- Addition on ℤ_p is inherited from ℚ_p. -/
instance : Add ℤ_[p] :=
  ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, le_transₓ (padicNormE.nonarchimedean _ _) (max_le_iff.2 ⟨hx, hy⟩)⟩⟩

/-- Multiplication on ℤ_p is inherited from ℚ_p. -/
instance : Mul ℤ_[p] :=
  ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ =>
    ⟨x * y, by
      rw [padicNormE.mul]
      apply mul_le_one <;>
        · first |
            assumption|
            apply norm_nonneg
          ⟩⟩

/-- Negation on ℤ_p is inherited from ℚ_p. -/
instance : Neg ℤ_[p] :=
  ⟨fun ⟨x, hx⟩ =>
    ⟨-x, by
      simpa⟩⟩

/-- Subtraction on ℤ_p is inherited from ℚ_p. -/
instance : Sub ℤ_[p] :=
  ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ =>
    ⟨x - y, by
      rw [sub_eq_add_neg]
      rw [← norm_neg] at hy
      exact le_transₓ (padicNormE.nonarchimedean _ _) (max_le_iff.2 ⟨hx, hy⟩)⟩⟩

/-- Zero on ℤ_p is inherited from ℚ_p. -/
instance : Zero ℤ_[p] :=
  ⟨⟨0, by
      norm_num⟩⟩

instance : Inhabited ℤ_[p] :=
  ⟨0⟩

/-- One on ℤ_p is inherited from ℚ_p. -/
instance : One ℤ_[p] :=
  ⟨⟨1, by
      norm_num⟩⟩

@[simp]
theorem mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) :=
  rfl

@[simp]
theorem val_eq_coe (z : ℤ_[p]) : z.val = z :=
  rfl

@[simp, norm_cast]
theorem coe_add : ∀ z1 z2 : ℤ_[p], ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

@[simp, norm_cast]
theorem coe_mul : ∀ z1 z2 : ℤ_[p], ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

@[simp, norm_cast]
theorem coe_neg : ∀ z1 : ℤ_[p], ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1
  | ⟨_, _⟩ => rfl

@[simp, norm_cast]
theorem coe_sub : ∀ z1 z2 : ℤ_[p], ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 :=
  rfl

instance : AddCommGroupₓ ℤ_[p] := by
  refine_struct
      { add := (· + ·), neg := Neg.neg, zero := (0 : ℤ_[p]), sub := Sub.sub,
        nsmul := @nsmulRec _ ⟨(0 : ℤ_[p])⟩ ⟨(· + ·)⟩, zsmul := @zsmulRec _ ⟨(0 : ℤ_[p])⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ } <;>
    intros <;>
      try
          rfl <;>
        ext <;> simp <;> ring

instance : AddGroupWithOneₓ ℤ_[p] :=
  { -- TODO: define nat_cast/int_cast so that coe_coe and coe_coe_int are rfl
    PadicInt.addCommGroup with
    one := 1 }

instance : Ringₓ ℤ_[p] := by
  refine_struct
      { PadicInt.addGroupWithOne with add := (· + ·), mul := (· * ·), neg := Neg.neg, zero := (0 : ℤ_[p]), one := 1,
        sub := Sub.sub, npow := @npowRec _ ⟨(1 : ℤ_[p])⟩ ⟨(· * ·)⟩ } <;>
    intros <;>
      try
          rfl <;>
        ext <;> simp <;> ring

@[simp, norm_cast]
theorem coe_coe : ∀ n : ℕ, ((n : ℤ_[p]) : ℚ_[p]) = n
  | 0 => rfl
  | k + 1 => by
    simp [← coe_coe]

@[simp, norm_cast]
theorem coe_coe_int : ∀ z : ℤ, ((z : ℤ_[p]) : ℚ_[p]) = z
  | Int.ofNat n => by
    simp
  | -[1+ n] => by
    simp

/-- The coercion from ℤ[p] to ℚ[p] as a ring homomorphism. -/
def Coe.ringHom : ℤ_[p] →+* ℚ_[p] where
  toFun := (coe : ℤ_[p] → ℚ_[p])
  map_zero' := rfl
  map_one' := rfl
  map_mul' := coe_mul
  map_add' := coe_add

@[simp, norm_cast]
theorem coe_pow (x : ℤ_[p]) (n : ℕ) : (↑(x ^ n) : ℚ_[p]) = (↑x : ℚ_[p]) ^ n :=
  (Coe.ringHom : ℤ_[p] →+* ℚ_[p]).map_pow x n

@[simp]
theorem mk_coe : ∀ k : ℤ_[p], (⟨k, k.2⟩ : ℤ_[p]) = k
  | ⟨_, _⟩ => rfl

/-- The inverse of a p-adic integer with norm equal to 1 is also a p-adic integer. Otherwise, the
inverse is defined to be 0. -/
def inv : ℤ_[p] → ℤ_[p]
  | ⟨k, _⟩ =>
    if h : ∥k∥ = 1 then
      ⟨1 / k, by
        simp [← h]⟩
    else 0

instance :
    CharZero ℤ_[p] where cast_injective := fun m n h =>
    Nat.cast_injective <|
      show (m : ℚ_[p]) = n by
        rw [Subtype.ext_iff] at h
        norm_cast  at h
        exact h

@[simp, norm_cast]
theorem coe_int_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 := by
  suffices (z1 : ℚ_[p]) = z2 ↔ z1 = z2 from
    Iff.trans
      (by
        norm_cast)
      this
  norm_cast

/-- A sequence of integers that is Cauchy with respect to the `p`-adic norm
converges to a `p`-adic integer.
-/
def ofIntSeq (seq : ℕ → ℤ) (h : IsCauSeq (padicNorm p) fun n => seq n) : ℤ_[p] :=
  ⟨⟦⟨_, h⟩⟧,
    show ↑(PadicSeq.norm _) ≤ (1 : ℝ) by
      rw [PadicSeq.norm]
      split_ifs with hne <;> norm_cast
      · exact zero_le_one
        
      · apply padicNorm.of_int
        ⟩

end PadicInt

namespace PadicInt

/-!
### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/


variable (p : ℕ) [Fact p.Prime]

instance : MetricSpace ℤ_[p] :=
  Subtype.metricSpace

instance complete_space : CompleteSpace ℤ_[p] :=
  have : IsClosed { x : ℚ_[p] | ∥x∥ ≤ 1 } := is_closed_le continuous_norm continuous_const
  this.complete_space_coe

instance : HasNorm ℤ_[p] :=
  ⟨fun z => ∥(z : ℚ_[p])∥⟩

variable {p}

protected theorem mul_comm : ∀ z1 z2 : ℤ_[p], z1 * z2 = z2 * z1
  | ⟨q1, h1⟩, ⟨q2, h2⟩ =>
    show (⟨q1 * q2, _⟩ : ℤ_[p]) = ⟨q2 * q1, _⟩ by
      simp [← _root_.mul_comm]

protected theorem zero_ne_one : (0 : ℤ_[p]) ≠ 1 :=
  show (⟨(0 : ℚ_[p]), _⟩ : ℤ_[p]) ≠ ⟨(1 : ℚ_[p]), _⟩ from mt Subtype.ext_iff_val.1 zero_ne_one

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : ℤ_[p], a * b = 0 → a = 0 ∨ b = 0
  | ⟨a, ha⟩, ⟨b, hb⟩ => fun h : (⟨a * b, _⟩ : ℤ_[p]) = ⟨0, _⟩ =>
    have : a * b = 0 := Subtype.ext_iff_val.1 h
    (mul_eq_zero.1 this).elim
      (fun h1 =>
        Or.inl
          (by
            simp [← h1] <;> rfl))
      fun h2 =>
      Or.inr
        (by
          simp [← h2] <;> rfl)

theorem norm_def {z : ℤ_[p]} : ∥z∥ = ∥(z : ℚ_[p])∥ :=
  rfl

variable (p)

instance : NormedCommRing ℤ_[p] :=
  { PadicInt.ring, PadicInt.metricSpace p with dist_eq := fun ⟨_, _⟩ ⟨_, _⟩ => rfl,
    norm_mul := by
      simp [← norm_def],
    mul_comm := PadicInt.mul_comm, norm := norm }

instance : NormOneClass ℤ_[p] :=
  ⟨norm_def.trans norm_one⟩

instance is_absolute_value : IsAbsoluteValue fun z : ℤ_[p] => ∥z∥ where
  abv_nonneg := norm_nonneg
  abv_eq_zero := fun ⟨_, _⟩ => by
    simp [← norm_eq_zero]
  abv_add := fun ⟨_, _⟩ ⟨_, _⟩ => norm_add_le _ _
  abv_mul := fun _ _ => by
    simp only [← norm_def, ← padicNormE.mul, ← PadicInt.coe_mul]

variable {p}

instance : IsDomain ℤ_[p] :=
  { PadicInt.normedCommRing p with
    eq_zero_or_eq_zero_of_mul_eq_zero := fun x y => PadicInt.eq_zero_or_eq_zero_of_mul_eq_zero x y,
    exists_pair_ne := ⟨0, 1, PadicInt.zero_ne_one⟩ }

end PadicInt

namespace PadicInt

/-! ### Norm -/


variable {p : ℕ} [Fact p.Prime]

theorem norm_le_one : ∀ z : ℤ_[p], ∥z∥ ≤ 1
  | ⟨_, h⟩ => h

@[simp]
theorem norm_mul (z1 z2 : ℤ_[p]) : ∥z1 * z2∥ = ∥z1∥ * ∥z2∥ := by
  simp [← norm_def]

@[simp]
theorem norm_pow (z : ℤ_[p]) : ∀ n : ℕ, ∥z ^ n∥ = ∥z∥ ^ n
  | 0 => by
    simp
  | k + 1 => by
    rw [pow_succₓ, pow_succₓ, norm_mul]
    congr
    apply norm_pow

theorem nonarchimedean : ∀ q r : ℤ_[p], ∥q + r∥ ≤ max ∥q∥ ∥r∥
  | ⟨_, _⟩, ⟨_, _⟩ => padicNormE.nonarchimedean _ _

theorem norm_add_eq_max_of_ne : ∀ {q r : ℤ_[p]}, ∥q∥ ≠ ∥r∥ → ∥q + r∥ = max ∥q∥ ∥r∥
  | ⟨_, _⟩, ⟨_, _⟩ => padicNormE.add_eq_max_of_ne

theorem norm_eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]} (h : ∥z1 + z2∥ < ∥z2∥) : ∥z1∥ = ∥z2∥ :=
  by_contradiction fun hne =>
    not_lt_of_geₓ
      (by
        rw [norm_add_eq_max_of_ne hne] <;> apply le_max_rightₓ)
      h

theorem norm_eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]} (h : ∥z1 + z2∥ < ∥z1∥) : ∥z1∥ = ∥z2∥ :=
  by_contradiction fun hne =>
    not_lt_of_geₓ
      (by
        rw [norm_add_eq_max_of_ne hne] <;> apply le_max_leftₓ)
      h

@[simp]
theorem padic_norm_e_of_padic_int (z : ℤ_[p]) : ∥(↑z : ℚ_[p])∥ = ∥z∥ := by
  simp [← norm_def]

theorem norm_int_cast_eq_padic_norm (z : ℤ) : ∥(z : ℤ_[p])∥ = ∥(z : ℚ_[p])∥ := by
  simp [← norm_def]

@[simp]
theorem norm_eq_padic_norm {q : ℚ_[p]} (hq : ∥q∥ ≤ 1) : @norm ℤ_[p] _ ⟨q, hq⟩ = ∥q∥ :=
  rfl

@[simp]
theorem norm_p : ∥(p : ℤ_[p])∥ = p⁻¹ :=
  show ∥((p : ℤ_[p]) : ℚ_[p])∥ = p⁻¹ by
    exact_mod_cast padicNormE.norm_p

@[simp]
theorem norm_p_pow (n : ℕ) : ∥(p : ℤ_[p]) ^ n∥ = p ^ (-n : ℤ) :=
  show ∥((p ^ n : ℤ_[p]) : ℚ_[p])∥ = p ^ (-n : ℤ) by
    convert padicNormE.norm_p_pow n
    simp

private def cau_seq_to_rat_cau_seq (f : CauSeq ℤ_[p] norm) : CauSeq ℚ_[p] fun a => ∥a∥ :=
  ⟨fun n => f n, fun _ hε => by
    simpa [← norm, ← norm_def] using f.cauchy hε⟩

variable (p)

instance complete : CauSeq.IsComplete ℤ_[p] norm :=
  ⟨fun f =>
    have hqn : ∥CauSeq.lim (cauSeqToRatCauSeq f)∥ ≤ 1 := padic_norm_e_lim_le zero_lt_one fun _ => norm_le_one _
    ⟨⟨_, hqn⟩, fun ε => by
      simpa [← norm, ← norm_def] using CauSeq.equiv_lim (cau_seq_to_rat_cau_seq f) ε⟩⟩

end PadicInt

namespace PadicInt

variable (p : ℕ) [hp_prime : Fact p.Prime]

include hp_prime

theorem exists_pow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, ↑p ^ -((k : ℕ) : ℤ) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
  use k
  rw [← inv_lt_inv hε (_root_.zpow_pos_of_pos _ _)]
  · rw [zpow_neg, inv_invₓ, zpow_coe_nat]
    apply lt_of_lt_of_leₓ hk
    norm_cast
    apply le_of_ltₓ
    convert Nat.lt_pow_self _ _ using 1
    exact hp_prime.1.one_lt
    
  · exact_mod_cast hp_prime.1.Pos
    

theorem exists_pow_neg_lt_rat {ε : ℚ} (hε : 0 < ε) : ∃ k : ℕ, ↑p ^ -((k : ℕ) : ℤ) < ε := by
  obtain ⟨k, hk⟩ :=
    @exists_pow_neg_lt p _ ε
      (by
        exact_mod_cast hε)
  use k
  rw
    [show (p : ℝ) = (p : ℚ) by
      simp ] at
    hk
  exact_mod_cast hk

variable {p}

theorem norm_int_lt_one_iff_dvd (k : ℤ) : ∥(k : ℤ_[p])∥ < 1 ↔ ↑p ∣ k :=
  suffices ∥(k : ℚ_[p])∥ < 1 ↔ ↑p ∣ k by
    rwa [norm_int_cast_eq_padic_norm]
  padicNormE.norm_int_lt_one_iff_dvd k

theorem norm_int_le_pow_iff_dvd {k : ℤ} {n : ℕ} : ∥(k : ℤ_[p])∥ ≤ ↑p ^ (-n : ℤ) ↔ ↑p ^ n ∣ k :=
  suffices ∥(k : ℚ_[p])∥ ≤ ↑p ^ (-n : ℤ) ↔ ↑(p ^ n) ∣ k by
    simpa [← norm_int_cast_eq_padic_norm]
  padicNormE.norm_int_le_pow_iff_dvd _ _

/-! ### Valuation on `ℤ_[p]` -/


/-- `padic_int.valuation` lifts the p-adic valuation on `ℚ` to `ℤ_[p]`.  -/
def valuation (x : ℤ_[p]) :=
  Padic.valuation (x : ℚ_[p])

theorem norm_eq_pow_val {x : ℤ_[p]} (hx : x ≠ 0) : ∥x∥ = p ^ -x.Valuation := by
  convert Padic.norm_eq_pow_val _
  contrapose! hx
  exact Subtype.val_injective hx

@[simp]
theorem valuation_zero : valuation (0 : ℤ_[p]) = 0 :=
  Padic.valuation_zero

@[simp]
theorem valuation_one : valuation (1 : ℤ_[p]) = 0 :=
  Padic.valuation_one

@[simp]
theorem valuation_p : valuation (p : ℤ_[p]) = 1 := by
  simp [← Valuation, -cast_eq_of_rat_of_nat]

theorem valuation_nonneg (x : ℤ_[p]) : 0 ≤ x.Valuation := by
  by_cases' hx : x = 0
  · simp [← hx]
    
  have h : (1 : ℝ) < p := by
    exact_mod_cast hp_prime.1.one_lt
  rw [← neg_nonpos, ← (zpow_strict_mono h).le_iff_le]
  show (p : ℝ) ^ -Valuation x ≤ p ^ 0
  rw [← norm_eq_pow_val hx]
  simpa using x.property

@[simp]
theorem valuation_p_pow_mul (n : ℕ) (c : ℤ_[p]) (hc : c ≠ 0) : (↑p ^ n * c).Valuation = n + c.Valuation := by
  have : ∥↑p ^ n * c∥ = ∥(p ^ n : ℤ_[p])∥ * ∥c∥ := norm_mul _ _
  have aux : ↑p ^ n * c ≠ 0 := by
    contrapose! hc
    rw [mul_eq_zero] at hc
    cases hc
    · refine' (hp_prime.1.ne_zero _).elim
      exact_mod_cast pow_eq_zero hc
      
    · exact hc
      
  rwa [norm_eq_pow_val aux, norm_p_pow, norm_eq_pow_val hc, ← zpow_add₀, ← neg_add, zpow_inj, neg_inj] at this
  · exact_mod_cast hp_prime.1.Pos
    
  · exact_mod_cast hp_prime.1.ne_one
    
  · exact_mod_cast hp_prime.1.ne_zero
    

section Units

/-! ### Units of `ℤ_[p]` -/


attribute [local reducible] PadicInt

theorem mul_inv : ∀ {z : ℤ_[p]}, ∥z∥ = 1 → z * z.inv = 1
  | ⟨k, _⟩, h => by
    have hk : k ≠ 0 := fun h' =>
      @zero_ne_one ℚ_[p] _ _
        (by
          simpa [← h'] using h)
    unfold PadicInt.inv
    rw [norm_eq_padic_norm] at h
    rw [dif_pos h]
    apply Subtype.ext_iff_val.2
    simp [← mul_inv_cancel hk]

theorem inv_mul {z : ℤ_[p]} (hz : ∥z∥ = 1) : z.inv * z = 1 := by
  rw [mul_comm, mul_inv hz]

theorem is_unit_iff {z : ℤ_[p]} : IsUnit z ↔ ∥z∥ = 1 :=
  ⟨fun h => by
    rcases is_unit_iff_dvd_one.1 h with ⟨w, eq⟩
    refine' le_antisymmₓ (norm_le_one _) _
    have := mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z)
    rwa [mul_oneₓ, ← norm_mul, ← Eq, norm_one] at this, fun h => ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩

theorem norm_lt_one_add {z1 z2 : ℤ_[p]} (hz1 : ∥z1∥ < 1) (hz2 : ∥z2∥ < 1) : ∥z1 + z2∥ < 1 :=
  lt_of_le_of_ltₓ (nonarchimedean _ _) (max_ltₓ hz1 hz2)

theorem norm_lt_one_mul {z1 z2 : ℤ_[p]} (hz2 : ∥z2∥ < 1) : ∥z1 * z2∥ < 1 :=
  calc
    ∥z1 * z2∥ = ∥z1∥ * ∥z2∥ := by
      simp
    _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2
    

@[simp]
theorem mem_nonunits {z : ℤ_[p]} : z ∈ Nonunits ℤ_[p] ↔ ∥z∥ < 1 := by
  rw [lt_iff_le_and_ne] <;> simp [← norm_le_one z, ← Nonunits, ← is_unit_iff]

/-- A `p`-adic number `u` with `∥u∥ = 1` is a unit of `ℤ_[p]`. -/
def mkUnits {u : ℚ_[p]} (h : ∥u∥ = 1) : ℤ_[p]ˣ :=
  let z : ℤ_[p] := ⟨u, le_of_eqₓ h⟩
  ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]
theorem mk_units_eq {u : ℚ_[p]} (h : ∥u∥ = 1) : ((mkUnits h : ℤ_[p]) : ℚ_[p]) = u :=
  rfl

@[simp]
theorem norm_units (u : ℤ_[p]ˣ) : ∥(u : ℤ_[p])∥ = 1 :=
  is_unit_iff.mp <| by
    simp

/-- `unit_coeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unit_coeff_spec`. -/
def unitCoeff {x : ℤ_[p]} (hx : x ≠ 0) : ℤ_[p]ˣ :=
  let u : ℚ_[p] := x * p ^ -x.Valuation
  have hu : ∥u∥ = 1 := by
    simp [← hx, ←
      Nat.zpow_ne_zero_of_pos
        (by
          exact_mod_cast hp_prime.1.Pos)
        x.valuation,
      ← norm_eq_pow_val, ← zpow_neg, ← inv_mul_cancel, -cast_eq_of_rat_of_nat]
  mkUnits hu

@[simp]
theorem unit_coeff_coe {x : ℤ_[p]} (hx : x ≠ 0) : (unitCoeff hx : ℚ_[p]) = x * p ^ -x.Valuation :=
  rfl

theorem unit_coeff_spec {x : ℤ_[p]} (hx : x ≠ 0) : x = (unitCoeff hx : ℤ_[p]) * p ^ Int.natAbs (valuation x) := by
  apply Subtype.coe_injective
  push_cast
  have repr : (x : ℚ_[p]) = unit_coeff hx * p ^ x.valuation := by
    rw [unit_coeff_coe, mul_assoc, ← zpow_add₀]
    · simp
      
    · exact_mod_cast hp_prime.1.ne_zero
      
  convert reprₓ using 2
  rw [← zpow_coe_nat, Int.nat_abs_of_nonneg (valuation_nonneg x)]

end Units

section NormLeIff

/-! ### Various characterizations of open unit balls -/


theorem norm_le_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) : ∥x∥ ≤ p ^ (-n : ℤ) ↔ ↑n ≤ x.Valuation := by
  rw [norm_eq_pow_val hx]
  lift x.valuation to ℕ using x.valuation_nonneg with k hk
  simp only [← Int.coe_nat_le, ← zpow_neg, ← zpow_coe_nat]
  have aux : ∀ n : ℕ, 0 < (p ^ n : ℝ) := by
    apply pow_pos
    exact_mod_cast hp_prime.1.Pos
  rw [inv_le_inv (aux _) (aux _)]
  have : p ^ n ≤ p ^ k ↔ n ≤ k := (strict_mono_pow hp_prime.1.one_lt).le_iff_le
  rw [← this]
  norm_cast

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:92:4: warning: unsupported: rw with cfg: { occs := occurrences.pos «expr[ ,]»([2]) }
theorem mem_span_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    x ∈ (Ideal.span {p ^ n} : Ideal ℤ_[p]) ↔ ↑n ≤ x.Valuation := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    suffices c ≠ 0 by
      rw [valuation_p_pow_mul _ _ this, le_add_iff_nonneg_right]
      apply valuation_nonneg
    contrapose! hx
    rw [hx, mul_zero]
    
  · rw [unit_coeff_spec hx]
    lift x.valuation to ℕ using x.valuation_nonneg with k hk
    simp only [← Int.nat_abs_of_nat, ← Units.is_unit, ← IsUnit.dvd_mul_left, ← Int.coe_nat_le]
    intro H
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le H
    simp only [← pow_addₓ, ← dvd_mul_right]
    

theorem norm_le_pow_iff_mem_span_pow (x : ℤ_[p]) (n : ℕ) :
    ∥x∥ ≤ p ^ (-n : ℤ) ↔ x ∈ (Ideal.span {p ^ n} : Ideal ℤ_[p]) := by
  by_cases' hx : x = 0
  · subst hx
    simp only [← norm_zero, ← zpow_neg, ← zpow_coe_nat, ← inv_nonneg, ← iff_trueₓ, ← Submodule.zero_mem]
    exact_mod_cast Nat.zero_leₓ _
    
  rw [norm_le_pow_iff_le_valuation x hx, mem_span_pow_iff_le_valuation x hx]

theorem norm_le_pow_iff_norm_lt_pow_add_one (x : ℤ_[p]) (n : ℤ) : ∥x∥ ≤ p ^ n ↔ ∥x∥ < p ^ (n + 1) := by
  rw [norm_def]
  exact Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _

theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : ℤ_[p]) (n : ℤ) : ∥x∥ < p ^ n ↔ ∥x∥ ≤ p ^ (n - 1) := by
  rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]

theorem norm_lt_one_iff_dvd (x : ℤ_[p]) : ∥x∥ < 1 ↔ ↑p ∣ x := by
  have := norm_le_pow_iff_mem_span_pow x 1
  rw [Ideal.mem_span_singleton, pow_oneₓ] at this
  rw [← this, norm_le_pow_iff_norm_lt_pow_add_one]
  simp only [← zpow_zero, ← Int.coe_nat_zero, ← Int.coe_nat_succ, ← add_left_negₓ, ← zero_addₓ]

@[simp]
theorem pow_p_dvd_int_iff (n : ℕ) (a : ℤ) : (p ^ n : ℤ_[p]) ∣ a ↔ ↑p ^ n ∣ a := by
  rw [← norm_int_le_pow_iff_dvd, norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

end NormLeIff

section Dvr

/-! ### Discrete valuation ring -/


instance : LocalRing ℤ_[p] :=
  LocalRing.of_nonunits_add <| by
    simp only [← mem_nonunits] <;> exact fun x y => norm_lt_one_add

theorem p_nonnunit : (p : ℤ_[p]) ∈ Nonunits ℤ_[p] := by
  have : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one <| by
      exact_mod_cast hp_prime.1.one_lt
  simp [← this]

theorem maximal_ideal_eq_span_p : maximalIdeal ℤ_[p] = Ideal.span {p} := by
  apply le_antisymmₓ
  · intro x hx
    rw [Ideal.mem_span_singleton]
    simp only [← LocalRing.mem_maximal_ideal, ← mem_nonunits] at hx
    rwa [← norm_lt_one_iff_dvd]
    
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact p_nonnunit
    

theorem prime_p : Prime (p : ℤ_[p]) := by
  rw [← Ideal.span_singleton_prime, ← maximal_ideal_eq_span_p]
  · infer_instance
    
  · exact_mod_cast hp_prime.1.ne_zero
    

theorem irreducible_p : Irreducible (p : ℤ_[p]) :=
  Prime.irreducible prime_p

instance : DiscreteValuationRing ℤ_[p] :=
  DiscreteValuationRing.of_has_unit_mul_pow_irreducible_factorization
    ⟨p, irreducible_p, fun x hx =>
      ⟨x.Valuation.natAbs, unitCoeff hx, by
        rw [mul_comm, ← unit_coeff_spec hx]⟩⟩

theorem ideal_eq_span_pow_p {s : Ideal ℤ_[p]} (hs : s ≠ ⊥) : ∃ n : ℕ, s = Ideal.span {p ^ n} :=
  DiscreteValuationRing.ideal_eq_span_pow_irreducible hs irreducible_p

open CauSeq

instance :
    IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p] where prec' := fun x hx => by
    simp only [Ideal.one_eq_top, ← smul_eq_mul, ← mul_oneₓ, ← Smodeq.sub_mem, ← maximal_ideal_eq_span_p, ←
      Ideal.span_singleton_pow, norm_le_pow_iff_mem_span_pow] at hx⊢
    let x' : CauSeq ℤ_[p] norm := ⟨x, _⟩
    swap
    · intro ε hε
      obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
      refine' ⟨m, fun n hn => lt_of_le_of_ltₓ _ hm⟩
      rw [← neg_sub, norm_neg]
      exact hx hn
      
    · refine' ⟨x'.lim, fun n => _⟩
      have : (0 : ℝ) < p ^ (-n : ℤ) := by
        apply zpow_pos_of_pos
        exact_mod_cast hp_prime.1.Pos
      obtain ⟨i, hi⟩ := equiv_def₃ (equiv_lim x') this
      by_cases' hin : i ≤ n
      · exact (hi i le_rfl n hin).le
        
      · push_neg  at hin
        specialize hi i le_rfl i le_rfl
        specialize hx hin.le
        have := nonarchimedean (x n - x i) (x i - x'.lim)
        rw [sub_add_sub_cancel] at this
        refine' this.trans (max_le_iff.mpr ⟨hx, hi.le⟩)
        
      

end Dvr

end PadicInt

