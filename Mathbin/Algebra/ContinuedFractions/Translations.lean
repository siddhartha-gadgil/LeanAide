/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathbin.Algebra.ContinuedFractions.Basic

/-!
# Basic Translation Lemmas Between Functions Defined for Continued Fractions

## Summary

Some simple translation lemmas between the different definitions of functions defined in
`algebra.continued_fractions.basic`.
-/


namespace GeneralizedContinuedFraction

section General

/-!
### Translations Between General Access Functions

Here we give some basic translations that hold by definition between the various methods that allow
us to access the numerators and denominators of a continued fraction.
-/


variable {α : Type _} {g : GeneralizedContinuedFraction α} {n : ℕ}

theorem terminated_at_iff_s_terminated_at : g.TerminatedAt n ↔ g.s.TerminatedAt n := by
  rfl

theorem terminated_at_iff_s_none : g.TerminatedAt n ↔ g.s.nth n = none := by
  rfl

theorem part_num_none_iff_s_none : g.partialNumerators.nth n = none ↔ g.s.nth n = none := by
  cases s_nth_eq : g.s.nth n <;> simp [← partial_numerators, ← s_nth_eq]

theorem terminated_at_iff_part_num_none : g.TerminatedAt n ↔ g.partialNumerators.nth n = none := by
  rw [terminated_at_iff_s_none, part_num_none_iff_s_none]

theorem part_denom_none_iff_s_none : g.partialDenominators.nth n = none ↔ g.s.nth n = none := by
  cases s_nth_eq : g.s.nth n <;> simp [← partial_denominators, ← s_nth_eq]

theorem terminated_at_iff_part_denom_none : g.TerminatedAt n ↔ g.partialDenominators.nth n = none := by
  rw [terminated_at_iff_s_none, part_denom_none_iff_s_none]

theorem part_num_eq_s_a {gp : Pair α} (s_nth_eq : g.s.nth n = some gp) : g.partialNumerators.nth n = some gp.a := by
  simp [← partial_numerators, ← s_nth_eq]

theorem part_denom_eq_s_b {gp : Pair α} (s_nth_eq : g.s.nth n = some gp) : g.partialDenominators.nth n = some gp.b := by
  simp [← partial_denominators, ← s_nth_eq]

theorem exists_s_a_of_part_num {a : α} (nth_part_num_eq : g.partialNumerators.nth n = some a) :
    ∃ gp, g.s.nth n = some gp ∧ gp.a = a := by
  simpa [← partial_numerators, ← Seqₓₓ.map_nth] using nth_part_num_eq

theorem exists_s_b_of_part_denom {b : α} (nth_part_denom_eq : g.partialDenominators.nth n = some b) :
    ∃ gp, g.s.nth n = some gp ∧ gp.b = b := by
  simpa [← partial_denominators, ← Seqₓₓ.map_nth] using nth_part_denom_eq

end General

section WithDivisionRing

/-!
### Translations Between Computational Functions

Here we  give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/


variable {K : Type _} {g : GeneralizedContinuedFraction K} {n : ℕ} [DivisionRing K]

theorem nth_cont_eq_succ_nth_cont_aux : g.continuants n = g.continuantsAux (n + 1) :=
  rfl

theorem num_eq_conts_a : g.numerators n = (g.continuants n).a :=
  rfl

theorem denom_eq_conts_b : g.denominators n = (g.continuants n).b :=
  rfl

theorem convergent_eq_num_div_denom : g.convergents n = g.numerators n / g.denominators n :=
  rfl

theorem convergent_eq_conts_a_div_conts_b : g.convergents n = (g.continuants n).a / (g.continuants n).b :=
  rfl

theorem exists_conts_a_of_num {A : K} (nth_num_eq : g.numerators n = A) :
    ∃ conts, g.continuants n = conts ∧ conts.a = A := by
  simpa

theorem exists_conts_b_of_denom {B : K} (nth_denom_eq : g.denominators n = B) :
    ∃ conts, g.continuants n = conts ∧ conts.b = B := by
  simpa

@[simp]
theorem zeroth_continuant_aux_eq_one_zero : g.continuantsAux 0 = ⟨1, 0⟩ :=
  rfl

@[simp]
theorem first_continuant_aux_eq_h_one : g.continuantsAux 1 = ⟨g.h, 1⟩ :=
  rfl

@[simp]
theorem zeroth_continuant_eq_h_one : g.continuants 0 = ⟨g.h, 1⟩ :=
  rfl

@[simp]
theorem zeroth_numerator_eq_h : g.numerators 0 = g.h :=
  rfl

@[simp]
theorem zeroth_denominator_eq_one : g.denominators 0 = 1 :=
  rfl

@[simp]
theorem zeroth_convergent_eq_h : g.convergents 0 = g.h := by
  simp [← convergent_eq_num_div_denom, ← num_eq_conts_a, ← denom_eq_conts_b, ← div_one]

theorem second_continuant_aux_eq {gp : Pair K} (zeroth_s_eq : g.s.nth 0 = some gp) :
    g.continuantsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [← zeroth_s_eq, ← continuants_aux, ← next_continuants, ← next_denominator, ← next_numerator]

theorem first_continuant_eq {gp : Pair K} (zeroth_s_eq : g.s.nth 0 = some gp) :
    g.continuants 1 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [← nth_cont_eq_succ_nth_cont_aux, ← second_continuant_aux_eq zeroth_s_eq]

theorem first_numerator_eq {gp : Pair K} (zeroth_s_eq : g.s.nth 0 = some gp) : g.numerators 1 = gp.b * g.h + gp.a := by
  simp [← num_eq_conts_a, ← first_continuant_eq zeroth_s_eq]

theorem first_denominator_eq {gp : Pair K} (zeroth_s_eq : g.s.nth 0 = some gp) : g.denominators 1 = gp.b := by
  simp [← denom_eq_conts_b, ← first_continuant_eq zeroth_s_eq]

@[simp]
theorem zeroth_convergent'_aux_eq_zero {s : Seqₓₓ <| Pair K} : convergents'Aux s 0 = 0 :=
  rfl

@[simp]
theorem zeroth_convergent'_eq_h : g.convergents' 0 = g.h := by
  simp [← convergents']

end WithDivisionRing

end GeneralizedContinuedFraction

