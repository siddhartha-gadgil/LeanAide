/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.CharP.ExpChar
import Mathbin.FieldTheory.Separable

/-!

# Separable degree

This file contains basics about the separable degree of a polynomial.

## Main results

- `is_separable_contraction`: is the condition that, for `g` a separable polynomial, we have that
   `g(x^(q^m)) = f(x)` for some `m : ℕ`.
- `has_separable_contraction`: the condition of having a separable contraction
- `has_separable_contraction.degree`: the separable degree, defined as the degree of some
  separable contraction
- `irreducible.has_separable_contraction`: any irreducible polynomial can be contracted
  to a separable polynomial
- `has_separable_contraction.dvd_degree'`: the degree of a separable contraction divides the degree,
  in function of the exponential characteristic of the field
- `has_separable_contraction.dvd_degree` and `has_separable_contraction.eq_degree` specialize the
  statement of `separable_degree_dvd_degree`
- `is_separable_contraction.degree_eq`: the separable degree is well-defined, implemented as the
  statement that the degree of any separable contraction equals `has_separable_contraction.degree`

## Tags

separable degree, degree, polynomial
-/


namespace Polynomial

noncomputable section

open Classical Polynomial

section CommSemiringₓ

variable {F : Type} [CommSemiringₓ F] (q : ℕ)

/-- A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some `m : ℕ`.-/
def IsSeparableContraction (f : F[X]) (g : F[X]) : Prop :=
  g.Separable ∧ ∃ m : ℕ, expand F (q ^ m) g = f

/-- The condition of having a separable contration. -/
def HasSeparableContraction (f : F[X]) : Prop :=
  ∃ g : F[X], IsSeparableContraction q f g

variable {q} {f : F[X]} (hf : HasSeparableContraction q f)

/-- A choice of a separable contraction. -/
def HasSeparableContraction.contraction : F[X] :=
  Classical.some hf

/-- The separable degree of a polynomial is the degree of a given separable contraction. -/
def HasSeparableContraction.degree : ℕ :=
  hf.contraction.natDegree

/-- The separable degree divides the degree, in function of the exponential characteristic of F. -/
theorem IsSeparableContraction.dvd_degree' {g} (hf : IsSeparableContraction q f g) :
    ∃ m : ℕ, g.natDegree * q ^ m = f.natDegree := by
  obtain ⟨m, rfl⟩ := hf.2
  use m
  rw [nat_degree_expand]

theorem HasSeparableContraction.dvd_degree' : ∃ m : ℕ, hf.degree * q ^ m = f.natDegree :=
  (Classical.some_spec hf).dvd_degree'

/-- The separable degree divides the degree. -/
theorem HasSeparableContraction.dvd_degree : hf.degree ∣ f.natDegree :=
  let ⟨a, ha⟩ := hf.dvd_degree'
  Dvd.intro (q ^ a) ha

/-- In exponential characteristic one, the separable degree equals the degree. -/
theorem HasSeparableContraction.eq_degree {f : F[X]} (hf : HasSeparableContraction 1 f) : hf.degree = f.natDegree := by
  let ⟨a, ha⟩ := hf.dvd_degree'
  rw [← ha, one_pow a, mul_oneₓ]

end CommSemiringₓ

section Field

variable {F : Type} [Field F]

variable (q : ℕ) {f : F[X]} (hf : HasSeparableContraction q f)

/-- Every irreducible polynomial can be contracted to a separable polynomial.
https://stacks.math.columbia.edu/tag/09H0 -/
theorem _root_.irreducible.has_separable_contraction (q : ℕ) [hF : ExpChar F q] (f : F[X]) (irred : Irreducible f) :
    HasSeparableContraction q f := by
  cases hF
  · exact
      ⟨f, irred.separable,
        ⟨0, by
          rw [pow_zeroₓ, expand_one]⟩⟩
    
  · rcases exists_separable_of_irreducible q irred ‹q.prime›.ne_zero with ⟨n, g, hgs, hge⟩
    exact ⟨g, hgs, n, hge⟩
    

/-- A helper lemma: if two expansions (along the positive characteristic) of two polynomials `g` and
`g'` agree, and the one with the larger degree is separable, then their degrees are the same. -/
theorem contraction_degree_eq_aux [hq : Fact q.Prime] [hF : CharP F q] (g g' : F[X]) (m m' : ℕ)
    (h_expand : expand F (q ^ m) g = expand F (q ^ m') g') (h : m < m') (hg : g.Separable) :
    g.natDegree = g'.natDegree := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [add_assocₓ, pow_addₓ, expand_mul] at h_expand
  let aux := expand_injective (pow_pos hq.1.Pos m) h_expand
  rw [aux] at hg
  have := (is_unit_or_eq_zero_of_separable_expand q (s + 1) hq.out.pos hg).resolve_right s.succ_ne_zero
  rw [aux, nat_degree_expand, nat_degree_eq_of_degree_eq_some (degree_eq_zero_of_is_unit this), zero_mul]

/-- If two expansions (along the positive characteristic) of two separable polynomials
`g` and `g'` agree, then they have the same degree. -/
theorem contraction_degree_eq_or_insep [hq : Fact q.Prime] [CharP F q] (g g' : F[X]) (m m' : ℕ)
    (h_expand : expand F (q ^ m) g = expand F (q ^ m') g') (hg : g.Separable) (hg' : g'.Separable) :
    g.natDegree = g'.natDegree := by
  by_cases' h : m = m'
  · -- if `m = m'` then we show `g.nat_degree = g'.nat_degree` by unfolding the definitions
    rw [h] at h_expand
    have expand_deg : ((expand F (q ^ m')) g).natDegree = (expand F (q ^ m') g').natDegree := by
      rw [h_expand]
    rw [nat_degree_expand (q ^ m') g, nat_degree_expand (q ^ m') g'] at expand_deg
    apply Nat.eq_of_mul_eq_mul_leftₓ (pow_pos hq.1.Pos m')
    rw [mul_comm] at expand_deg
    rw [expand_deg]
    rw [mul_comm]
    
  · cases Ne.lt_or_lt h
    · exact contraction_degree_eq_aux q g g' m m' h_expand h_1 hg
      
    · exact (contraction_degree_eq_aux q g' g m' m h_expand.symm h_1 hg').symm
      
    

/-- The separable degree equals the degree of any separable contraction, i.e., it is unique. -/
theorem IsSeparableContraction.degree_eq [hF : ExpChar F q] (g : F[X]) (hg : IsSeparableContraction q f g) :
    g.natDegree = hf.degree := by
  cases hF
  · rcases hg with ⟨g, m, hm⟩
    rw [one_pow, expand_one] at hm
    rw [hf.eq_degree]
    rw [hm]
    
  · rcases hg with ⟨hg, m, hm⟩
    let g' := Classical.some hf
    cases' (Classical.some_spec hf).2 with m' hm'
    have : Fact q.prime := fact_iff.2 hF_hprime
    apply contraction_degree_eq_or_insep q g g' m m'
    rw [hm, hm']
    exact hg
    exact (Classical.some_spec hf).1
    

end Field

end Polynomial

