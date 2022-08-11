/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.NumberTheory.Zsqrtd.Basic
import Mathbin.Data.Complex.Basic
import Mathbin.RingTheory.PrincipalIdealDomain
import Mathbin.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Gaussian integers

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `to_complex` into the complex numbers is also defined in this file.

## Main statements

`prime_iff_mod_four_eq_three_of_nat_prime`
A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notations

This file uses the local notation `ℤ[i]` for `gaussian_int`

## Implementation notes

Gaussian integers are implemented using the more general definition `zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `zsqrtd` can easily be used.
-/


open Zsqrtd Complex

/-- The Gaussian integers, defined as `ℤ√(-1)`. -/
@[reducible]
def GaussianInt : Type :=
  Zsqrtd (-1)

-- mathport name: «exprℤ[i]»
local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

instance : HasRepr ℤ[i] :=
  ⟨fun x => "⟨" ++ reprₓ x.re ++ ", " ++ reprₓ x.im ++ "⟩"⟩

instance : CommRingₓ ℤ[i] :=
  Zsqrtd.commRing

section

attribute [-instance] Complex.field

/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
-- Avoid making things noncomputable unnecessarily.
def toComplex : ℤ[i] →+* ℂ :=
  Zsqrtd.lift
    ⟨i, by
      simp ⟩

end

instance : Coe ℤ[i] ℂ :=
  ⟨toComplex⟩

theorem to_complex_def (x : ℤ[i]) : (x : ℂ) = x.re + x.im * I :=
  rfl

theorem to_complex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x + y * I := by
  simp [← to_complex_def]

theorem to_complex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ := by
  apply Complex.ext <;> simp [← to_complex_def]

@[simp]
theorem to_real_re (x : ℤ[i]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re := by
  simp [← to_complex_def]

@[simp]
theorem to_real_im (x : ℤ[i]) : ((x.im : ℤ) : ℝ) = (x : ℂ).im := by
  simp [← to_complex_def]

@[simp]
theorem to_complex_re (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).re = x := by
  simp [← to_complex_def]

@[simp]
theorem to_complex_im (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).im = y := by
  simp [← to_complex_def]

@[simp]
theorem to_complex_add (x y : ℤ[i]) : ((x + y : ℤ[i]) : ℂ) = x + y :=
  toComplex.map_add _ _

@[simp]
theorem to_complex_mul (x y : ℤ[i]) : ((x * y : ℤ[i]) : ℂ) = x * y :=
  toComplex.map_mul _ _

@[simp]
theorem to_complex_one : ((1 : ℤ[i]) : ℂ) = 1 :=
  toComplex.map_one

@[simp]
theorem to_complex_zero : ((0 : ℤ[i]) : ℂ) = 0 :=
  toComplex.map_zero

@[simp]
theorem to_complex_neg (x : ℤ[i]) : ((-x : ℤ[i]) : ℂ) = -x :=
  toComplex.map_neg _

@[simp]
theorem to_complex_sub (x y : ℤ[i]) : ((x - y : ℤ[i]) : ℂ) = x - y :=
  toComplex.map_sub _ _

@[simp]
theorem to_complex_inj {x y : ℤ[i]} : (x : ℂ) = y ↔ x = y := by
  cases x <;> cases y <;> simp [← to_complex_def₂]

@[simp]
theorem to_complex_eq_zero {x : ℤ[i]} : (x : ℂ) = 0 ↔ x = 0 := by
  rw [← to_complex_zero, to_complex_inj]

@[simp]
theorem nat_cast_real_norm (x : ℤ[i]) : (x.norm : ℝ) = (x : ℂ).normSq := by
  rw [norm, norm_sq] <;> simp

@[simp]
theorem nat_cast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = (x : ℂ).normSq := by
  cases x <;> rw [norm, norm_sq] <;> simp

theorem norm_nonneg (x : ℤ[i]) : 0 ≤ norm x :=
  norm_nonneg
    (by
      norm_num)
    _

@[simp]
theorem norm_eq_zero {x : ℤ[i]} : norm x = 0 ↔ x = 0 := by
  rw [← @Int.cast_inj ℝ _ _ _] <;> simp

theorem norm_pos {x : ℤ[i]} : 0 < norm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne.def, eq_comm, norm_eq_zero] <;> simp [← norm_nonneg]

theorem coe_nat_abs_norm (x : ℤ[i]) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.nat_abs_of_nonneg (norm_nonneg _)

@[simp]
theorem nat_cast_nat_abs_norm {α : Type _} [Ringₓ α] (x : ℤ[i]) : (x.norm.natAbs : α) = x.norm := by
  rw [← Int.cast_coe_nat, coe_nat_abs_norm]

theorem nat_abs_norm_eq (x : ℤ[i]) : x.norm.natAbs = x.re.natAbs * x.re.natAbs + x.im.natAbs * x.im.natAbs :=
  Int.coe_nat_inj <| by
    simp
    simp [← norm]

instance : Div ℤ[i] :=
  ⟨fun x y =>
    let n := (Rat.ofInt (norm y))⁻¹
    let c := y.conj
    ⟨round (Rat.ofInt (x * c).re * n : ℚ), round (Rat.ofInt (x * c).im * n : ℚ)⟩⟩

theorem div_def (x y : ℤ[i]) : x / y = ⟨round ((x * conj y).re / norm y : ℚ), round ((x * conj y).im / norm y : ℚ)⟩ :=
  show Zsqrtd.mk _ _ = _ by
    simp [← Rat.of_int_eq_mk, ← Rat.mk_eq_div, ← div_eq_mul_inv]

theorem to_complex_div_re (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).re = round (x / y : ℂ).re := by
  rw [div_def, ← @Rat.round_cast ℝ _ _] <;>
    simp [-Rat.round_cast, ← mul_assoc, ← div_eq_mul_inv, ← mul_addₓ, ← add_mulₓ]

theorem to_complex_div_im (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).im = round (x / y : ℂ).im := by
  rw [div_def, ← @Rat.round_cast ℝ _ _, ← @Rat.round_cast ℝ _ _] <;>
    simp [-Rat.round_cast, ← mul_assoc, ← div_eq_mul_inv, ← mul_addₓ, ← add_mulₓ]

theorem norm_sq_le_norm_sq_of_re_le_of_im_le {x y : ℂ} (hre : abs x.re ≤ abs y.re) (him : abs x.im ≤ abs y.im) :
    x.normSq ≤ y.normSq := by
  rw [norm_sq_apply, norm_sq_apply, ← _root_.abs_mul_self, _root_.abs_mul, ← _root_.abs_mul_self y.re,
      _root_.abs_mul y.re, ← _root_.abs_mul_self x.im, _root_.abs_mul x.im, ← _root_.abs_mul_self y.im,
      _root_.abs_mul y.im] <;>
    exact add_le_add (mul_self_le_mul_self (abs_nonneg _) hre) (mul_self_le_mul_self (abs_nonneg _) him)

theorem norm_sq_div_sub_div_lt_one (x y : ℤ[i]) : ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).normSq < 1 :=
  calc
    ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).normSq =
        ((x / y : ℂ).re - ((x / y : ℤ[i]) : ℂ).re + ((x / y : ℂ).im - ((x / y : ℤ[i]) : ℂ).im) * I : ℂ).normSq :=
      congr_arg _ <| by
        apply Complex.ext <;> simp
    _ ≤ (1 / 2 + 1 / 2 * I).normSq :=
      have : abs (2⁻¹ : ℝ) = 2⁻¹ :=
        abs_of_nonneg
          (by
            norm_num)
      norm_sq_le_norm_sq_of_re_le_of_im_le
        (by
          rw [to_complex_div_re] <;> simp [← norm_sq, ← this] <;> simpa using abs_sub_round (x / y : ℂ).re)
        (by
          rw [to_complex_div_im] <;> simp [← norm_sq, ← this] <;> simpa using abs_sub_round (x / y : ℂ).im)
    _ < 1 := by
      simp [← norm_sq] <;> norm_num
    

instance : Mod ℤ[i] :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : ℤ[i]) : x % y = x - y * (x / y) :=
  rfl

theorem norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
  have : (y : ℂ) ≠ 0 := by
    rwa [Ne.def, ← to_complex_zero, to_complex_inj]
  (@Int.cast_lt ℝ _ _ _ _).1 <|
    calc
      ↑(norm (x % y)) = (x - y * (x / y : ℤ[i]) : ℂ).normSq := by
        simp [← mod_def]
      _ = (y : ℂ).normSq * (x / y - (x / y : ℤ[i]) : ℂ).normSq := by
        rw [← norm_sq_mul, mul_sub, mul_div_cancel' _ this]
      _ < (y : ℂ).normSq * 1 := mul_lt_mul_of_pos_left (norm_sq_div_sub_div_lt_one _ _) (norm_sq_pos.2 this)
      _ = norm y := by
        simp
      

theorem nat_abs_norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm.natAbs < y.norm.natAbs :=
  Int.coe_nat_lt.1
    (by
      simp [-Int.coe_nat_lt, ← norm_mod_lt x hy])

theorem norm_le_norm_mul_left (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [norm_mul, Int.nat_abs_mul] <;>
    exact
      le_mul_of_one_le_right (Nat.zero_leₓ _)
        (Int.coe_nat_le.1
          (by
            rw [coe_nat_abs_norm] <;> exact Int.add_one_le_of_ltₓ (norm_pos.2 hy)))

instance : Nontrivial ℤ[i] :=
  ⟨⟨0, 1, by
      decide⟩⟩

instance : EuclideanDomain ℤ[i] :=
  { GaussianInt.commRing, GaussianInt.nontrivial with Quotient := (· / ·), remainder := (· % ·),
    quotient_zero := by
      simp [← div_def]
      rfl,
    quotient_mul_add_remainder_eq := fun _ _ => by
      simp [← mod_def],
    R := _, r_well_founded := measure_wf (Int.natAbs ∘ norm), remainder_lt := nat_abs_norm_mod_lt,
    mul_left_not_lt := fun a b hb0 => not_lt_of_geₓ <| norm_le_norm_mul_left a hb0 }

open PrincipalIdealRing

theorem mod_four_eq_three_of_nat_prime_of_prime (p : ℕ) [hp : Fact p.Prime] (hpi : Prime (p : ℤ[i])) : p % 4 = 3 :=
  hp.1.eq_two_or_odd.elim
    (fun hp2 =>
      absurd hpi
        ((mt irreducible_iff_prime.2) fun ⟨hu, h⟩ => by
          have := h ⟨1, 1⟩ ⟨1, -1⟩ (hp2.symm ▸ rfl)
          rw [← norm_eq_one_iff, ← norm_eq_one_iff] at this
          exact
            absurd this
              (by
                decide)))
    fun hp1 =>
    by_contradiction fun hp3 : p % 4 ≠ 3 => by
      have hp41 : p % 4 = 1 := by
        rw [← Nat.mod_mul_left_mod p 2 2, show 2 * 2 = 4 from rfl] at hp1
        have :=
          Nat.mod_ltₓ p
            (show 0 < 4 by
              decide)
        revert this hp3 hp1
        generalize p % 4 = m
        decide!
      let ⟨k, hk⟩ :=
        (Zmod.exists_sq_eq_neg_one_iff p).2 <| by
          rw [hp41] <;>
            exact by
              decide
      obtain ⟨k, k_lt_p, rfl⟩ : ∃ (k' : ℕ)(h : k' < p), (k' : Zmod p) = k := by
        refine' ⟨k.val, k.val_lt, Zmod.nat_cast_zmod_val k⟩
      have hpk : p ∣ k ^ 2 + 1 := by
        rw [pow_two, ← CharP.cast_eq_zero_iff (Zmod p) p, Nat.cast_addₓ, Nat.cast_mulₓ, Nat.cast_oneₓ, ← hk,
          add_left_negₓ]
      have hkmul : (k ^ 2 + 1 : ℤ[i]) = ⟨k, 1⟩ * ⟨k, -1⟩ := by
        simp [← sq, ← Zsqrtd.ext]
      have hpne1 : p ≠ 1 := ne_of_gtₓ hp.1.one_lt
      have hkltp : 1 + k * k < p * p :=
        calc
          1 + k * k ≤ k + k * k :=
            add_le_add_right
              (Nat.pos_of_ne_zeroₓ fun hk0 => by
                clear_aux_decl <;> simp_all [← pow_succ'ₓ])
              _
          _ = k * (k + 1) := by
            simp [← add_commₓ, ← mul_addₓ]
          _ < p * p := mul_lt_mul k_lt_p k_lt_p (Nat.succ_posₓ _) (Nat.zero_leₓ _)
          
      have hpk₁ : ¬(p : ℤ[i]) ∣ ⟨k, -1⟩ := fun ⟨x, hx⟩ =>
        lt_irreflₓ (p * x : ℤ[i]).norm.natAbs <|
          calc
            (norm (p * x : ℤ[i])).natAbs = (norm ⟨k, -1⟩).natAbs := by
              rw [hx]
            _ < (norm (p : ℤ[i])).natAbs := by
              simpa [← add_commₓ, ← norm] using hkltp
            _ ≤ (norm (p * x : ℤ[i])).natAbs :=
              norm_le_norm_mul_left _ fun hx0 =>
                show (-1 : ℤ) ≠ 0 by
                    decide <|
                  by
                  simpa [← hx0] using congr_arg Zsqrtd.im hx
            
      have hpk₂ : ¬(p : ℤ[i]) ∣ ⟨k, 1⟩ := fun ⟨x, hx⟩ =>
        lt_irreflₓ (p * x : ℤ[i]).norm.natAbs <|
          calc
            (norm (p * x : ℤ[i])).natAbs = (norm ⟨k, 1⟩).natAbs := by
              rw [hx]
            _ < (norm (p : ℤ[i])).natAbs := by
              simpa [← add_commₓ, ← norm] using hkltp
            _ ≤ (norm (p * x : ℤ[i])).natAbs :=
              norm_le_norm_mul_left _ fun hx0 =>
                show (1 : ℤ) ≠ 0 by
                    decide <|
                  by
                  simpa [← hx0] using congr_arg Zsqrtd.im hx
            
      have hpu : ¬IsUnit (p : ℤ[i]) :=
        mt norm_eq_one_iff.2
          (by
            rw [norm_nat_cast, Int.nat_abs_mul, Nat.mul_eq_one_iff] <;> exact fun h => (ne_of_ltₓ hp.1.one_lt).symm h.1)
      obtain ⟨y, hy⟩ := hpk
      have :=
        hpi.2.2 ⟨k, 1⟩ ⟨k, -1⟩
          ⟨y, by
            rw [← hkmul, ← Nat.cast_mulₓ p, ← hy] <;> simp ⟩
      clear_aux_decl
      tauto

theorem sq_add_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : Fact p.Prime] (hpi : ¬Irreducible (p : ℤ[i])) :
    ∃ a b, a ^ 2 + b ^ 2 = p :=
  have hpu : ¬IsUnit (p : ℤ[i]) :=
    mt norm_eq_one_iff.2 <| by
      rw [norm_nat_cast, Int.nat_abs_mul, Nat.mul_eq_one_iff] <;> exact fun h => (ne_of_ltₓ hp.1.one_lt).symm h.1
  have hab : ∃ a b, (p : ℤ[i]) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [← irreducible_iff, ← hpu, ← not_forall, ← not_or_distrib] using hpi
  let ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : (norm a).natAbs = p :=
    ((hp.1.mul_eq_prime_sq_iff (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1 <| by
        rw [← Int.coe_nat_inj', Int.coe_nat_pow, sq, ← @norm_nat_cast (-1), hpab] <;> simp ).1
  ⟨a.re.natAbs, a.im.natAbs, by
    simpa [← nat_abs_norm_eq, ← sq] using hnap⟩

theorem prime_of_nat_prime_of_mod_four_eq_three (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 4 = 3) : Prime (p : ℤ[i]) :=
  irreducible_iff_prime.1 <|
    Classical.by_contradiction fun hpi =>
      let ⟨a, b, hab⟩ := sq_add_sq_of_nat_prime_of_not_irreducible p hpi
      have : ∀ a b : Zmod 4, a ^ 2 + b ^ 2 ≠ p := by
        erw [← Zmod.nat_cast_mod p 4, hp3] <;>
          exact by
            decide
      this a b
        (hab ▸ by
          simp )

/-- A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4` -/
theorem prime_iff_mod_four_eq_three_of_nat_prime (p : ℕ) [hp : Fact p.Prime] : Prime (p : ℤ[i]) ↔ p % 4 = 3 :=
  ⟨mod_four_eq_three_of_nat_prime_of_prime p, prime_of_nat_prime_of_mod_four_eq_three p⟩

end GaussianInt

