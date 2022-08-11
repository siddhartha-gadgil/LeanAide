/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.RingTheory.UniqueFactorizationDomain

/-!
# Squarefree elements of monoids
An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

Results about squarefree natural numbers are proved in `data/nat/squarefree`.

## Main Definitions
 - `squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
 - `multiplicity.squarefree_iff_multiplicity_le_one`: `x` is `squarefree` iff for every `y`, either
  `multiplicity y x ≤ 1` or `is_unit y`.
 - `unique_factorization_monoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
 factorization monoid is squarefree iff `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/


variable {R : Type _}

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def Squarefree [Monoidₓ R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x

@[simp]
theorem IsUnit.squarefree [CommMonoidₓ R] {x : R} (h : IsUnit x) : Squarefree x := fun y hdvd =>
  is_unit_of_mul_is_unit_left (is_unit_of_dvd_unit hdvd h)

@[simp]
theorem squarefree_one [CommMonoidₓ R] : Squarefree (1 : R) :=
  is_unit_one.Squarefree

@[simp]
theorem not_squarefree_zero [MonoidWithZeroₓ R] [Nontrivial R] : ¬Squarefree (0 : R) := by
  erw [not_forall]
  exact
    ⟨0, by
      simp ⟩

theorem Squarefree.ne_zero [MonoidWithZeroₓ R] [Nontrivial R] {m : R} (hm : Squarefree (m : R)) : m ≠ 0 := by
  rintro rfl
  exact not_squarefree_zero hm

@[simp]
theorem Irreducible.squarefree [CommMonoidₓ R] {x : R} (h : Irreducible x) : Squarefree x := by
  rintro y ⟨z, hz⟩
  rw [mul_assoc] at hz
  rcases h.is_unit_or_is_unit hz with (hu | hu)
  · exact hu
    
  · apply is_unit_of_mul_is_unit_left hu
    

@[simp]
theorem Prime.squarefree [CancelCommMonoidWithZero R] {x : R} (h : Prime x) : Squarefree x :=
  h.Irreducible.Squarefree

theorem Squarefree.of_mul_left [CommMonoidₓ R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree m := fun p hp =>
  hmn p (dvd_mul_of_dvd_left hp n)

theorem Squarefree.of_mul_right [CommMonoidₓ R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree n := fun p hp =>
  hmn p (dvd_mul_of_dvd_right hp m)

theorem squarefree_of_dvd_of_squarefree [CommMonoidₓ R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x :=
  fun a h => hsq _ (h.trans hdvd)

namespace multiplicity

section CommMonoidₓ

variable [CommMonoidₓ R] [DecidableRel (Dvd.Dvd : R → R → Prop)]

theorem squarefree_iff_multiplicity_le_one (r : R) : Squarefree r ↔ ∀ x : R, multiplicity x r ≤ 1 ∨ IsUnit x := by
  refine' forall_congrₓ fun a => _
  rw [← sq, pow_dvd_iff_le_multiplicity, or_iff_not_imp_left, not_leₓ, imp_congr _ Iff.rfl]
  simpa using PartEnat.add_one_le_iff_lt (PartEnat.coe_ne_top 1)

end CommMonoidₓ

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero R] [WfDvdMonoid R]

theorem finite_prime_left {a b : R} (ha : Prime a) (hb : b ≠ 0) : multiplicity.Finite a b := by
  classical
  revert hb
  refine'
    WfDvdMonoid.induction_on_irreducible b
      (by
        contradiction)
      (fun u hu hu' => _) fun b p hb hp ih hpb => _
  · rw [multiplicity.finite_iff_dom, multiplicity.is_unit_right ha.not_unit hu]
    exact PartEnat.dom_coe 0
    
  · refine'
      multiplicity.finite_mul ha
        (multiplicity.finite_iff_dom.mpr (PartEnat.dom_of_le_coe (show multiplicity a p ≤ ↑1 from _))) (ih hb)
    norm_cast
    exact ((multiplicity.squarefree_iff_multiplicity_le_one p).mp hp.squarefree a).resolve_right ha.not_unit
    

end CancelCommMonoidWithZero

end multiplicity

section Irreducible

variable [CommMonoidWithZero R] [WfDvdMonoid R]

theorem irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) :
    (∀ x : R, Irreducible x → ¬x * x ∣ r) ↔ (r = 0 ∧ ∀ x : R, ¬Irreducible x) ∨ Squarefree r := by
  symm
  constructor
  · rintro (⟨rfl, h⟩ | h)
    · simpa using h
      
    intro x hx t
    exact hx.not_unit (h x t)
    
  intro h
  rcases eq_or_ne r 0 with (rfl | hr)
  · exact
      Or.inl
        (by
          simpa using h)
    
  right
  intro x hx
  by_contra i
  have : x ≠ 0 := by
    rintro rfl
    apply hr
    simpa only [← zero_dvd_iff, ← mul_zero] using hx
  obtain ⟨j, hj₁, hj₂⟩ := WfDvdMonoid.exists_irreducible_factor i this
  exact h _ hj₁ ((mul_dvd_mul hj₂ hj₂).trans hx)

theorem squarefree_iff_irreducible_sq_not_dvd_of_ne_zero {r : R} (hr : r ≠ 0) :
    Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  simpa [← hr] using (irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree r).symm

theorem squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R} (hr : ∃ x : R, Irreducible x) :
    Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree, ← not_exists]
  simp only [← hr, ← not_true, ← false_orₓ, ← and_falseₓ]

end Irreducible

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero R] [Nontrivial R] [UniqueFactorizationMonoid R]

variable [NormalizationMonoid R]

theorem squarefree_iff_nodup_normalized_factors [DecidableEq R] {x : R} (x0 : x ≠ 0) :
    Squarefree x ↔ Multiset.Nodup (normalizedFactors x) := by
  have drel : DecidableRel (Dvd.Dvd : R → R → Prop) := by
    classical
    infer_instance
  have := drel
  rw [multiplicity.squarefree_iff_multiplicity_le_one, Multiset.nodup_iff_count_le_one]
  constructor <;> intro h a
  · by_cases' hmem : a ∈ normalized_factors x
    · have ha := irreducible_of_normalized_factor _ hmem
      rcases h a with (h | h)
      · rw [← normalize_normalized_factor _ hmem]
        rw [multiplicity_eq_count_normalized_factors ha x0] at h
        assumption_mod_cast
        
      · have := ha.1
        contradiction
        
      
    · simp [← Multiset.count_eq_zero_of_not_mem hmem]
      
    
  · rw [or_iff_not_imp_right]
    intro hu
    by_cases' h0 : a = 0
    · simp [← h0, ← x0]
      
    rcases WfDvdMonoid.exists_irreducible_factor hu h0 with ⟨b, hib, hdvd⟩
    apply le_transₓ (multiplicity.multiplicity_le_multiplicity_of_dvd_left hdvd)
    rw [multiplicity_eq_count_normalized_factors hib x0]
    specialize h (normalize b)
    assumption_mod_cast
    

theorem dvd_pow_iff_dvd_of_squarefree {x y : R} {n : ℕ} (hsq : Squarefree x) (h0 : n ≠ 0) : x ∣ y ^ n ↔ x ∣ y := by
  classical
  by_cases' hx : x = 0
  · simp [← hx, ← pow_eq_zero_iff (Nat.pos_of_ne_zeroₓ h0)]
    
  by_cases' hy : y = 0
  · simp [← hy, ← zero_pow (Nat.pos_of_ne_zeroₓ h0)]
    
  refine' ⟨fun h => _, fun h => h.pow h0⟩
  rw [dvd_iff_normalized_factors_le_normalized_factors hx (pow_ne_zero n hy), normalized_factors_pow,
    ((squarefree_iff_nodup_normalized_factors hx).1 hsq).le_nsmul_iff_le h0] at h
  rwa [dvd_iff_normalized_factors_le_normalized_factors hx hy]

end UniqueFactorizationMonoid

