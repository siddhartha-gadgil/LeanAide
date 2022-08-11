/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.Algebra.Ring.Ulift
import Mathbin.Data.MvPolynomial.Cardinal
import Mathbin.Data.Rat.Denumerable
import Mathbin.FieldTheory.Finite.GaloisField
import Mathbin.Logic.Equiv.TransferInstance
import Mathbin.RingTheory.Localization.Cardinality
import Mathbin.SetTheory.Cardinal.Divisibility
import Mathbin.Data.Nat.Factorization.PrimePow

/-!
# Cardinality of Fields

In this file we show all the possible cardinalities of fields. All infinite cardinals can harbour
a field structure, and so can all types with prime power cardinalities, and this is sharp.

## Main statements

* `fintype.nonempty_field_iff`: A `fintype` can be given a field structure iff its cardinality is a
  prime power.
* `infinite.nonempty_field` : Any infinite type can be endowed a field structure.
* `field.nonempty_iff` : There is a field structure on type iff its cardinality is a prime power.

-/


-- mathport name: «expr‖ ‖»
local notation "‖" x "‖" => Fintype.card x

open Cardinal nonZeroDivisors

universe u

/-- A finite field has prime power cardinality. -/
theorem Fintype.is_prime_pow_card_of_field {α} [Fintype α] [Field α] : IsPrimePow ‖α‖ := by
  cases' CharP.exists α with p _
  have hp := Fact.mk (CharP.char_is_prime α p)
  let b := IsNoetherian.finsetBasis (Zmod p) α
  rw [Module.card_fintype b, Zmod.card, is_prime_pow_pow_iff]
  · exact hp.1.IsPrimePow
    
  rw [← FiniteDimensional.finrank_eq_card_basis b]
  exact finite_dimensional.finrank_pos.ne'

/-- A `fintype` can be given a field structure iff its cardinality is a prime power. -/
theorem Fintype.nonempty_field_iff {α} [Fintype α] : Nonempty (Field α) ↔ IsPrimePow ‖α‖ := by
  refine' ⟨fun ⟨h⟩ => Fintype.is_prime_pow_card_of_field, _⟩
  rintro ⟨p, n, hp, hn, hα⟩
  have := Fact.mk (nat.prime_iff.mpr hp)
  exact ⟨(Fintype.equivOfCardEq ((GaloisField.card p n hn.ne').trans hα)).symm.Field⟩

theorem Fintype.not_is_field_of_card_not_prime_pow {α} [Fintype α] [Ringₓ α] : ¬IsPrimePow ‖α‖ → ¬IsField α :=
  mt fun h => Fintype.nonempty_field_iff.mp ⟨h.toField⟩

/-- Any infinite type can be endowed a field structure. -/
theorem Infinite.nonempty_field {α : Type u} [Infinite α] : Nonempty (Field α) := by
  let K := FractionRing (MvPolynomial α <| ULift.{u} ℚ)
  suffices # α = # K by
    obtain ⟨e⟩ := Cardinal.eq.1 this
    exact ⟨e.field⟩
  rw [← IsLocalization.card (MvPolynomial α <| ULift.{u} ℚ)⁰ K le_rfl]
  apply le_antisymmₓ
  · refine' ⟨⟨fun a => MvPolynomial.monomial (Finsupp.single a 1) (1 : ULift.{u} ℚ), fun x y h => _⟩⟩
    simpa [← MvPolynomial.monomial_eq_monomial_iff, ← Finsupp.single_eq_single_iff] using h
    
  · simpa using @MvPolynomial.cardinal_mk_le_max α (ULift.{u} ℚ) _
    

/-- There is a field structure on type if and only if its cardinality is a prime power. -/
theorem Field.nonempty_iff {α : Type u} : Nonempty (Field α) ↔ IsPrimePow (# α) := by
  rw [Cardinal.is_prime_pow_iff]
  cases' fintypeOrInfinite α with h h
  · simpa only [← Cardinal.mk_fintype, ← Nat.cast_inj, ← exists_eq_left', ← (Cardinal.nat_lt_aleph_0 _).not_le, ←
      false_orₓ] using Fintype.nonempty_field_iff
    
  · simpa only [Cardinal.infinite_iff, ← h, ← true_orₓ, ← iff_trueₓ] using Infinite.nonempty_field
    

