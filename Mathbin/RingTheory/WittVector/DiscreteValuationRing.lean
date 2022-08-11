/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth, Johan Commelin
-/
import Mathbin.RingTheory.WittVector.Domain
import Mathbin.RingTheory.WittVector.MulCoeff
import Mathbin.RingTheory.DiscreteValuationRing
import Mathbin.Tactic.LinearCombination

/-!

# Witt vectors over a perfect ring

This file establishes that Witt vectors over a perfect field are a discrete valuation ring.
When `k` is a perfect ring, a nonzero `a : 𝕎 k` can be written as `p^m * b` for some `m : ℕ` and
`b : 𝕎 k` with nonzero 0th coefficient.
When `k` is also a field, this `b` can be chosen to be a unit of `𝕎 k`.

## Main declarations

* `witt_vector.exists_eq_pow_p_mul`: the existence of this element `b` over a perfect ring
* `witt_vector.exists_eq_pow_p_mul'`: the existence of this unit `b` over a perfect field
* `witt_vector.discrete_valuation_ring`: `𝕎 k` is a discrete valuation ring if `k` is a perfect
    field

-/


noncomputable section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime]

include hp

-- mathport name: «expr𝕎»
local notation "𝕎" => WittVector p

section CommRingₓ

variable {k : Type _} [CommRingₓ k] [CharP k p]

/-- This is the `n+1`st coefficient of our inverse. -/
def succNthValUnits (n : ℕ) (a : Units k) (A : 𝕎 k) (bs : Finₓ (n + 1) → k) : k :=
  -↑(a⁻¹ ^ p ^ (n + 1)) * (A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) + nthRemainder p n (truncateFun (n + 1) A) bs)

/-- Recursively defines the sequence of coefficients for the inverse to a Witt vector whose first entry
is a unit.
-/
noncomputable def inverseCoeff (a : Units k) (A : 𝕎 k) : ℕ → k
  | 0 => ↑a⁻¹
  | n + 1 => succNthValUnits n a A fun i => inverse_coeff i.val

-- ./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr «expr * »(«expr- »(H_coeff), H)], ["with"], { normalize := ff }]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args
/-- Upgrade a Witt vector `A` whose first entry `A.coeff 0` is a unit to be, itself, a unit in `𝕎 k`.
-/
def mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : Units (𝕎 k) :=
  Units.mkOfMulEqOne A (WittVector.mk p (inverseCoeff a A))
    (by
      ext n
      induction' n with n ih
      · simp [← WittVector.mul_coeff_zero, ← inverse_coeff, ← hA]
        
      let H_coeff :=
        A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) +
          nth_remainder p n (truncate_fun (n + 1) A) fun i : Finₓ (n + 1) => inverse_coeff a A i
      have H := Units.mul_inv (a ^ p ^ (n + 1))
      trace
        "./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr «expr * »(«expr- »(H_coeff), H)], [\"with\"], { normalize := ff }]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args"
      have ha : (a : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1)) := by
        norm_cast
      have ha_inv : (↑a⁻¹ : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1))⁻¹ := by
        exact_mod_cast inv_pow _ _
      simp only [← nth_remainder_spec, ← inverse_coeff, ← succ_nth_val_units, ← hA, ← Finₓ.val_eq_coe, ←
        one_coeff_eq_of_pos, ← Nat.succ_pos', ← H_coeff, ← ha_inv, ← ha, ← inv_pow]
      ring!)

@[simp]
theorem coe_mk_unit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : (mkUnit hA : 𝕎 k) = A :=
  rfl

end CommRingₓ

section Field

variable {k : Type _} [Field k] [CharP k p]

theorem is_unit_of_coeff_zero_ne_zero (x : 𝕎 k) (hx : x.coeff 0 ≠ 0) : IsUnit x := by
  let y : kˣ := Units.mk0 (x.coeff 0) hx
  have hy : x.coeff 0 = y := rfl
  exact (mk_unit hy).IsUnit

variable (p)

theorem irreducible : Irreducible (p : 𝕎 k) := by
  have hp : ¬IsUnit (p : 𝕎 k) := by
    intro hp
    simpa only [← constant_coeff_apply, ← coeff_p_zero, ← not_is_unit_zero] using
      (constant_coeff : WittVector p k →+* _).is_unit_map hp
  refine' ⟨hp, fun a b hab => _⟩
  obtain ⟨ha0, hb0⟩ : a ≠ 0 ∧ b ≠ 0 := by
    rw [← mul_ne_zero_iff]
    intro h
    rw [h] at hab
    exact p_nonzero p k hab
  obtain ⟨m, a, ha, rfl⟩ := verschiebung_nonzero ha0
  obtain ⟨n, b, hb, rfl⟩ := verschiebung_nonzero hb0
  cases m
  · exact Or.inl (is_unit_of_coeff_zero_ne_zero a ha)
    
  cases n
  · exact Or.inr (is_unit_of_coeff_zero_ne_zero b hb)
    
  rw [iterate_verschiebung_mul] at hab
  apply_fun fun x => coeff x 1  at hab
  simp only [← coeff_p_one, ← Nat.add_succ, ← add_commₓ _ n, ← Function.iterate_succ', ← Function.comp_app, ←
    verschiebung_coeff_add_one, ← verschiebung_coeff_zero] at hab
  exact (one_ne_zero hab).elim

end Field

section PerfectRing

variable {k : Type _} [CommRingₓ k] [CharP k p] [PerfectRing k p]

theorem exists_eq_pow_p_mul (a : 𝕎 k) (ha : a ≠ 0) : ∃ (m : ℕ)(b : 𝕎 k), b.coeff 0 ≠ 0 ∧ a = p ^ m * b := by
  obtain ⟨m, c, hc, hcm⟩ := WittVector.verschiebung_nonzero ha
  obtain ⟨b, rfl⟩ := (frobenius_bijective p k).Surjective.iterate m c
  rw [WittVector.iterate_frobenius_coeff] at hc
  have := congr_fun (witt_vector.verschiebung_frobenius_comm.comp_iterate m) b
  simp only [← Function.comp_app] at this
  rw [← this] at hcm
  refine' ⟨m, b, _, _⟩
  · contrapose! hc
    have : 0 < p ^ m := pow_pos (Nat.Prime.pos (Fact.out _)) _
    simp [← hc, ← zero_pow this]
    
  · rw [← mul_left_iterate (p : 𝕎 k) m]
    convert hcm
    ext1 x
    rw [mul_comm, ← WittVector.verschiebung_frobenius x]
    

end PerfectRing

section PerfectField

variable {k : Type _} [Field k] [CharP k p] [PerfectRing k p]

theorem exists_eq_pow_p_mul' (a : 𝕎 k) (ha : a ≠ 0) : ∃ (m : ℕ)(b : Units (𝕎 k)), a = p ^ m * b := by
  obtain ⟨m, b, h₁, h₂⟩ := exists_eq_pow_p_mul a ha
  let b₀ := Units.mk0 (b.coeff 0) h₁
  have hb₀ : b.coeff 0 = b₀ := rfl
  exact ⟨m, mk_unit hb₀, h₂⟩

/-- The ring of Witt Vectors of a perfect field of positive characteristic is a DVR.
-/
/-
Note: The following lemma should be an instance, but it seems to cause some
exponential blowups in certain typeclass resolution problems.
See the following Lean4 issue as well as the zulip discussion linked there:
https://github.com/leanprover/lean4/issues/1102
-/
theorem discrete_valuation_ring : DiscreteValuationRing (𝕎 k) :=
  DiscreteValuationRing.of_has_unit_mul_pow_irreducible_factorization
    (by
      refine' ⟨p, Irreducible p, fun x hx => _⟩
      obtain ⟨n, b, hb⟩ := exists_eq_pow_p_mul' x hx
      exact ⟨n, b, hb.symm⟩)

end PerfectField

end WittVector

