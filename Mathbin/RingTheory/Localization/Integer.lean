/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathbin.RingTheory.Localization.Basic

/-!
# Integer elements of a localization

## Main definitions

 * `is_localization.is_integer` is a predicate stating that `x : S` is in the image of `R`

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRingₓ R] {M : Submonoid R} {S : Type _} [CommRingₓ S]

variable [Algebra R S] {P : Type _} [CommRingₓ P]

open Function

open BigOperators

namespace IsLocalization

section

variable (R) {M S}

/-- Given `a : S`, `S` a localization of `R`, `is_integer R a` iff `a` is in the image of
the localization map from `R` to `S`. -/
-- TODO: define a subalgebra of `is_integer`s
def IsInteger (a : S) : Prop :=
  a ∈ (algebraMap R S).range

end

theorem is_integer_zero : IsInteger R (0 : S) :=
  Subring.zero_mem _

theorem is_integer_one : IsInteger R (1 : S) :=
  Subring.one_mem _

theorem is_integer_add {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a + b) :=
  Subring.add_mem _ ha hb

theorem is_integer_mul {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a * b) :=
  Subring.mul_mem _ ha hb

theorem is_integer_smul {a : R} {b : S} (hb : IsInteger R b) : IsInteger R (a • b) := by
  rcases hb with ⟨b', hb⟩
  use a * b'
  rw [← hb, (algebraMap R S).map_mul, Algebra.smul_def]

variable (M) {S} [IsLocalization M S]

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `localization_map.surj`.
-/
theorem exists_integer_multiple' (a : S) : ∃ b : M, IsInteger R (a * algebraMap R S b) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalization.surj _ a
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `has_smul` instance.
-/
theorem exists_integer_multiple (a : S) : ∃ b : M, IsInteger R ((b : R) • a) := by
  simp_rw [Algebra.smul_def, mul_comm _ a]
  apply exists_integer_multiple'

/-- We can clear the denominators of a `finset`-indexed family of fractions. -/
theorem exist_integer_multiples {ι : Type _} (s : Finset ι) (f : ι → S) :
    ∃ b : M, ∀, ∀ i ∈ s, ∀, IsLocalization.IsInteger R ((b : R) • f i) := by
  have := Classical.propDecidable
  refine' ⟨∏ i in s, (sec M (f i)).2, fun i hi => ⟨_, _⟩⟩
  · exact (∏ j in s.erase i, (sec M (f j)).2) * (sec M (f i)).1
    
  rw [RingHom.map_mul, sec_spec', ← mul_assoc, ← (algebraMap R S).map_mul, ← Algebra.smul_def]
  congr 2
  refine' trans _ ((Submonoid.subtype M).map_prod _ _).symm
  rw [mul_comm, ← Finset.prod_insert (s.not_mem_erase i), Finset.insert_erase hi]
  rfl

/-- We can clear the denominators of a `fintype`-indexed family of fractions. -/
theorem exist_integer_multiples_of_fintype {ι : Type _} [Fintype ι] (f : ι → S) :
    ∃ b : M, ∀ i, IsLocalization.IsInteger R ((b : R) • f i) := by
  obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ f
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

/-- We can clear the denominators of a finite set of fractions. -/
theorem exist_integer_multiples_of_finset (s : Finset S) : ∃ b : M, ∀, ∀ a ∈ s, ∀, IsInteger R ((b : R) • a) :=
  exist_integer_multiples M s id

/-- A choice of a common multiple of the denominators of a `finset`-indexed family of fractions. -/
noncomputable def commonDenom {ι : Type _} (s : Finset ι) (f : ι → S) : M :=
  (exist_integer_multiples M s f).some

/-- The numerator of a fraction after clearing the denominators
of a `finset`-indexed family of fractions. -/
noncomputable def integerMultiple {ι : Type _} (s : Finset ι) (f : ι → S) (i : s) : R :=
  ((exist_integer_multiples M s f).some_spec i i.Prop).some

@[simp]
theorem map_integer_multiple {ι : Type _} (s : Finset ι) (f : ι → S) (i : s) :
    algebraMap R S (integerMultiple M s f i) = commonDenom M s f • f i :=
  ((exist_integer_multiples M s f).some_spec _ i.Prop).some_spec

/-- A choice of a common multiple of the denominators of a finite set of fractions. -/
noncomputable def commonDenomOfFinset (s : Finset S) : M :=
  commonDenom M s id

/-- The finset of numerators after clearing the denominators of a finite set of fractions. -/
noncomputable def finsetIntegerMultiple [DecidableEq R] (s : Finset S) : Finset R :=
  s.attach.Image fun t => integerMultiple M s id t

open Pointwise

theorem finset_integer_multiple_image [DecidableEq R] (s : Finset S) :
    algebraMap R S '' finsetIntegerMultiple M s = commonDenomOfFinset M s • s := by
  delta' finset_integer_multiple common_denom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integer_multiple]
    exact Set.mem_image_of_mem _ x.prop
    
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integer_multiple M s id _⟩
    

end IsLocalization

