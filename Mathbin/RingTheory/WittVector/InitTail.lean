/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathbin.RingTheory.WittVector.Basic
import Mathbin.RingTheory.WittVector.IsPoly

/-!

# `init` and `tail`

Given a Witt vector `x`, we are sometimes interested
in its components before and after an index `n`.
This file defines those operations, proves that `init` is polynomial,
and shows how that polynomial interacts with `mv_polynomial.bind₁`.

## Main declarations

* `witt_vector.init n x`: the first `n` coefficients of `x`, as a Witt vector. All coefficients at
  indices ≥ `n` are 0.
* `witt_vector.tail n x`: the complementary part to `init`. All coefficients at indices < `n` are 0,
  otherwise they are the same as in `x`.
* `witt_vector.coeff_add_of_disjoint`: if `x` and `y` are Witt vectors such that for every `n`
  the `n`-th coefficient of `x` or of `y` is `0`, then the coefficients of `x + y`
  are just `x.coeff n + y.coeff n`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]

-/


variable {p : ℕ} [hp : Fact p.Prime] (n : ℕ) {R : Type _} [CommRingₓ R]

-- mathport name: «expr𝕎»
local notation "𝕎" => WittVector p

-- type as `\bbW`
namespace Tactic

namespace Interactive

setup_tactic_parser

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- `init_ring` is an auxiliary tactic that discharges goals factoring `init` over ring operations.
-/
unsafe def init_ring (assert : parse (tk "using" *> parser.pexpr)?) : tactic Unit := do
  sorry
  match assert with
    | none => skip
    | some e => do
      sorry
      tactic.replace `h (ppquote.1 ((%%ₓe) p _ h))
      sorry

end Interactive

end Tactic

namespace WittVector

open MvPolynomial

open Classical

noncomputable section

section

/-- `witt_vector.select P x`, for a predicate `P : ℕ → Prop` is the Witt vector
whose `n`-th coefficient is `x.coeff n` if `P n` is true, and `0` otherwise.
-/
def select (P : ℕ → Prop) (x : 𝕎 R) : 𝕎 R :=
  mk p fun n => if P n then x.coeff n else 0

section Select

variable (P : ℕ → Prop)

/-- The polynomial that witnesses that `witt_vector.select` is a polynomial function.
`select_poly n` is `X n` if `P n` holds, and `0` otherwise. -/
def selectPoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if P n then x n else 0

theorem coeff_select (x : 𝕎 R) (n : ℕ) : (select P x).coeff n = aeval x.coeff (selectPoly P n) := by
  dsimp' [← select, ← select_poly]
  split_ifs with hi
  · rw [aeval_X]
    
  · rw [AlgHom.map_zero]
    

@[is_poly]
theorem select_is_poly (P : ℕ → Prop) : IsPoly p fun R _Rcr x => select P x := by
  use select_poly P
  rintro R _Rcr x
  funext i
  apply coeff_select

include hp

theorem select_add_select_not : ∀ x : 𝕎 R, select P x + select (fun i => ¬P i) x = x := by
  ghost_calc _
  intro n
  simp only [← RingHom.map_add]
  suffices
    (bind₁ (select_poly P)) (wittPolynomial p ℤ n) + (bind₁ (select_poly fun i => ¬P i)) (wittPolynomial p ℤ n) =
      wittPolynomial p ℤ n
    by
    apply_fun aeval x.coeff  at this
    simpa only [← AlgHom.map_add, ← aeval_bind₁, coeff_select]
  simp only [← witt_polynomial_eq_sum_C_mul_X_pow, ← select_poly, ← AlgHom.map_sum, ← AlgHom.map_pow, ← AlgHom.map_mul,
    ← bind₁_X_right, ← bind₁_C_right, Finset.sum_add_distrib, mul_addₓ]
  apply Finset.sum_congr rfl
  refine' fun m hm => mul_eq_mul_left_iff.mpr (Or.inl _)
  rw [ite_pow, ite_pow, zero_pow (pow_pos hp.out.pos _)]
  by_cases' Pm : P m
  · rw [if_pos Pm, if_neg _, add_zeroₓ]
    exact not_not.mpr Pm
    
  · rwa [if_neg Pm, if_pos, zero_addₓ]
    

theorem coeff_add_of_disjoint (x y : 𝕎 R) (h : ∀ n, x.coeff n = 0 ∨ y.coeff n = 0) :
    (x + y).coeff n = x.coeff n + y.coeff n := by
  let P : ℕ → Prop := fun n => y.coeff n = 0
  have : DecidablePred P := Classical.decPred P
  set z := mk p fun n => if P n then x.coeff n else y.coeff n with hz
  have hx : select P z = x := by
    ext1 n
    rw [select, coeff_mk, coeff_mk]
    split_ifs with hn
    · rfl
      
    · rw [(h n).resolve_right hn]
      
  have hy : select (fun i => ¬P i) z = y := by
    ext1 n
    rw [select, coeff_mk, coeff_mk]
    split_ifs with hn
    · exact hn.symm
      
    · rfl
      
  calc (x + y).coeff n = z.coeff n := by
      rw [← hx, ← hy, select_add_select_not P z]_ = x.coeff n + y.coeff n := _
  dsimp' [← z]
  split_ifs with hn
  · dsimp' [← P]  at hn
    rw [hn, add_zeroₓ]
    
  · rw [(h n).resolve_right hn, zero_addₓ]
    

end Select

/-- `witt_vector.init n x` is the Witt vector of which the first `n` coefficients are those from `x`
and all other coefficients are `0`.
See `witt_vector.tail` for the complementary part.
-/
def init (n : ℕ) : 𝕎 R → 𝕎 R :=
  select fun i => i < n

/-- `witt_vector.tail n x` is the Witt vector of which the first `n` coefficients are `0`
and all other coefficients are those from `x`.
See `witt_vector.init` for the complementary part. -/
def tail (n : ℕ) : 𝕎 R → 𝕎 R :=
  select fun i => n ≤ i

include hp

@[simp]
theorem init_add_tail (x : 𝕎 R) (n : ℕ) : init n x + tail n x = x := by
  simp only [← init, ← tail, not_ltₓ, ← select_add_select_not]

end

@[simp]
theorem init_init (x : 𝕎 R) (n : ℕ) : init n (init n x) = init n x := by
  init_ring

include hp

theorem init_add (x y : 𝕎 R) (n : ℕ) : init n (x + y) = init n (init n x + init n y) := by
  init_ring using witt_add_vars

theorem init_mul (x y : 𝕎 R) (n : ℕ) : init n (x * y) = init n (init n x * init n y) := by
  init_ring using witt_mul_vars

theorem init_neg (x : 𝕎 R) (n : ℕ) : init n (-x) = init n (-init n x) := by
  init_ring using witt_neg_vars

theorem init_sub (x y : 𝕎 R) (n : ℕ) : init n (x - y) = init n (init n x - init n y) := by
  init_ring using witt_sub_vars

theorem init_nsmul (m : ℕ) (x : 𝕎 R) (n : ℕ) : init n (m • x) = init n (m • init n x) := by
  init_ring using fun p [Fact (Nat.Prime p)] n => witt_nsmul_vars p m n

theorem init_zsmul (m : ℤ) (x : 𝕎 R) (n : ℕ) : init n (m • x) = init n (m • init n x) := by
  init_ring using fun p [Fact (Nat.Prime p)] n => witt_zsmul_vars p m n

theorem init_pow (m : ℕ) (x : 𝕎 R) (n : ℕ) : init n (x ^ m) = init n (init n x ^ m) := by
  init_ring using fun p [Fact (Nat.Prime p)] n => witt_pow_vars p m n

section

variable (p)

omit hp

/-- `witt_vector.init n x` is polynomial in the coefficients of `x`. -/
theorem init_is_poly (n : ℕ) : IsPoly p fun R _Rcr => init n :=
  select_is_poly fun i => i < n

end

end WittVector

