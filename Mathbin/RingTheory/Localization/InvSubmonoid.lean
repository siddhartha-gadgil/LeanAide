/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathbin.GroupTheory.Submonoid.Inverses
import Mathbin.RingTheory.Finiteness
import Mathbin.RingTheory.Localization.Basic
import Mathbin.Tactic.RingExp

/-!
# Submonoid of inverses

## Main definitions

 * `is_localization.inv_submonoid M S` is the submonoid of `S = M⁻¹R` consisting of inverses of
   each element `x ∈ M`

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRingₓ R] (M : Submonoid R) (S : Type _) [CommRingₓ S]

variable [Algebra R S] {P : Type _} [CommRingₓ P]

open Function

open BigOperators

namespace IsLocalization

section InvSubmonoid

variable (M S)

/-- The submonoid of `S = M⁻¹R` consisting of `{ 1 / x | x ∈ M }`. -/
def invSubmonoid : Submonoid S :=
  (M.map (algebraMap R S : R →* S)).left_inv

variable [IsLocalization M S]

theorem submonoid_map_le_is_unit : M.map (algebraMap R S : R →* S) ≤ IsUnit.submonoid S := by
  rintro _ ⟨a, ha, rfl⟩
  exact IsLocalization.map_units S ⟨_, ha⟩

/-- There is an equivalence of monoids between the image of `M` and `inv_submonoid`. -/
noncomputable abbrev equivInvSubmonoid : M.map (algebraMap R S : R →* S) ≃* invSubmonoid M S :=
  ((M.map (algebraMap R S : R →* S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm

/-- There is a canonical map from `M` to `inv_submonoid` sending `x` to `1 / x`. -/
noncomputable def toInvSubmonoid : M →* invSubmonoid M S :=
  (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R →* S).submonoidMap M)

theorem to_inv_submonoid_surjective : Function.Surjective (toInvSubmonoid M S) :=
  Function.Surjective.comp (Equivₓ.surjective _) (MonoidHom.submonoid_map_surjective _ _)

@[simp]
theorem to_inv_submonoid_mul (m : M) : (toInvSubmonoid M S m : S) * algebraMap R S m = 1 :=
  Submonoid.left_inv_equiv_symm_mul _ _ _

@[simp]
theorem mul_to_inv_submonoid (m : M) : algebraMap R S m * (toInvSubmonoid M S m : S) = 1 :=
  Submonoid.mul_left_inv_equiv_symm _ _ ⟨_, _⟩

@[simp]
theorem smul_to_inv_submonoid (m : M) : m • (toInvSubmonoid M S m : S) = 1 := by
  convert mul_to_inv_submonoid M S m
  rw [← Algebra.smul_def]
  rfl

variable {S}

theorem surj' (z : S) : ∃ (r : R)(m : M), z = r • toInvSubmonoid M S m := by
  rcases IsLocalization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebraMap R S r⟩
  refine' ⟨r, m, _⟩
  rw [Algebra.smul_def, ← e, mul_assoc]
  simp

theorem to_inv_submonoid_eq_mk' (x : M) : (toInvSubmonoid M S x : S) = mk' S 1 x := by
  rw [← (IsLocalization.map_units S x).mul_left_inj]
  simp

theorem mem_inv_submonoid_iff_exists_mk' (x : S) : x ∈ invSubmonoid M S ↔ ∃ m : M, mk' S 1 m = x := by
  simp_rw [← to_inv_submonoid_eq_mk']
  exact
    ⟨fun h => ⟨_, congr_arg Subtype.val (to_inv_submonoid_surjective M S ⟨x, h⟩).some_spec⟩, fun h =>
      h.some_spec ▸ (to_inv_submonoid M S h.some).Prop⟩

variable (S)

theorem span_inv_submonoid : Submodule.span R (invSubmonoid M S : Set S) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rcases IsLocalization.surj' M x with ⟨r, m, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span (to_inv_submonoid M S m).Prop)

theorem finite_type_of_monoid_fg [Monoidₓ.Fg M] : Algebra.FiniteType R S := by
  have := Monoidₓ.fg_of_surjective _ (to_inv_submonoid_surjective M S)
  rw [Monoidₓ.fg_iff_submonoid_fg] at this
  rcases this with ⟨s, hs⟩
  refine' ⟨⟨s, _⟩⟩
  rw [eq_top_iff]
  rintro x -
  change x ∈ ((Algebra.adjoin R _ : Subalgebra R S).toSubmodule : Set S)
  rw [Algebra.adjoin_eq_span, hs, span_inv_submonoid]
  trivial

end InvSubmonoid

end IsLocalization

