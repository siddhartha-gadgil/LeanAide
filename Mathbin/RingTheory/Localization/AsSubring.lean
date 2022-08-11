/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu
-/
import Mathbin.RingTheory.Localization.LocalizationLocalization

/-!

# Localizations of domains as subalgebras of the fraction field.

Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
does not contain zero, this file constructs the localization of `A` at `S`
as a subalgebra of the field `K` over `A`.

-/


namespace Localization

open nonZeroDivisors

variable {A : Type _} (K : Type _) [CommRingₓ A] (S : Submonoid A) (hS : S ≤ A⁰)

section CommRingₓ

variable [CommRingₓ K] [Algebra A K] [IsFractionRing A K]

theorem map_is_unit_of_le (hS : S ≤ A⁰) (s : S) : IsUnit (algebraMap A K s) := by
  apply IsLocalization.map_units K (⟨s.1, hS s.2⟩ : A⁰)

/-- The canonical map from a localization of `A` at `S` to the fraction ring
  of `A`, given that `S ≤ A⁰`. -/
noncomputable def mapToFractionRing (B : Type _) [CommRingₓ B] [Algebra A B] [IsLocalization S B] (hS : S ≤ A⁰) :
    B →ₐ[A] K :=
  { IsLocalization.lift (map_is_unit_of_le K S hS) with
    commutes' := fun a => by
      simp }

@[simp]
theorem map_to_fraction_ring_apply {B : Type _} [CommRingₓ B] [Algebra A B] [IsLocalization S B] (hS : S ≤ A⁰) (b : B) :
    mapToFractionRing K S B hS b = IsLocalization.lift (map_is_unit_of_le K S hS) b :=
  rfl

theorem mem_range_map_to_fraction_ring_iff (B : Type _) [CommRingₓ B] [Algebra A B] [IsLocalization S B] (hS : S ≤ A⁰)
    (x : K) : x ∈ (mapToFractionRing K S B hS).range ↔ ∃ (a s : A)(hs : s ∈ S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ :=
  ⟨by
    rintro ⟨x, rfl⟩
    obtain ⟨a, s, rfl⟩ := IsLocalization.mk'_surjective S x
    use a, s, s.2
    apply IsLocalization.lift_mk', by
    rintro ⟨a, s, hs, rfl⟩
    use IsLocalization.mk' _ a ⟨s, hs⟩
    apply IsLocalization.lift_mk'⟩

instance is_localization_range_map_to_fraction_ring (B : Type _) [CommRingₓ B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) : IsLocalization S (mapToFractionRing K S B hS).range :=
  IsLocalization.is_localization_of_alg_equiv S <|
    show B ≃ₐ[A] _ from
      AlgEquiv.ofBijective (mapToFractionRing K S B hS).range_restrict
        (by
          refine' ⟨fun a b h => _, Set.surjective_onto_range⟩
          refine' (IsLocalization.lift_injective_iff _).2 (fun a b => _) (Subtype.ext_iff.1 h)
          exact
            ⟨fun h => congr_arg _ (IsLocalization.injective _ hS h), fun h =>
              congr_arg _ (IsFractionRing.injective A K h)⟩)

instance is_fraction_ring_range_map_to_fraction_ring (B : Type _) [CommRingₓ B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) : IsFractionRing (mapToFractionRing K S B hS).range K :=
  IsFractionRing.is_fraction_ring_of_is_localization S _ _ hS

/-- Given a commutative ring `A` with fraction ring `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.

The carrier of this subalgebra is defined as the set of all `x : K` of the form
`is_localization.mk' K a ⟨s, _⟩`, where `s ∈ S`.
-/
noncomputable def subalgebra (hS : S ≤ A⁰) : Subalgebra A K :=
  (mapToFractionRing K S (Localization S) hS).range.copy
      { x | ∃ (a s : A)(hs : s ∈ S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ } <|
    by
    ext
    symm
    apply mem_range_map_to_fraction_ring_iff

namespace Subalgebra

instance is_localization_subalgebra : IsLocalization S (subalgebra K S hS) := by
  dunfold Localization.subalgebra
  rw [Subalgebra.copy_eq]
  infer_instance

instance is_fraction_ring : IsFractionRing (subalgebra K S hS) K :=
  IsFractionRing.is_fraction_ring_of_is_localization S _ _ hS

end Subalgebra

end CommRingₓ

section Field

variable [Field K] [Algebra A K] [IsFractionRing A K]

namespace Subalgebra

theorem mem_range_map_to_fraction_ring_iff_of_field (B : Type _) [CommRingₓ B] [Algebra A B] [IsLocalization S B]
    (x : K) :
    x ∈ (mapToFractionRing K S B hS).range ↔ ∃ (a s : A)(hs : s ∈ S), x = algebraMap A K a * (algebraMap A K s)⁻¹ := by
  rw [mem_range_map_to_fraction_ring_iff]
  iterate 3 
    congr with
  convert Iff.rfl
  rw [Units.coe_inv]
  rfl

/-- Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.

The carrier of this subalgebra is defined as the set of all `x : K` of the form
`algebra_map A K a * (algebra_map A K s)⁻¹` where `a s : A` and `s ∈ S`.
-/
noncomputable def ofField : Subalgebra A K :=
  (mapToFractionRing K S (Localization S) hS).range.copy
      { x | ∃ (a s : A)(hs : s ∈ S), x = algebraMap A K a * (algebraMap A K s)⁻¹ } <|
    by
    ext
    symm
    apply mem_range_map_to_fraction_ring_iff_of_field

instance is_localization_of_field : IsLocalization S (subalgebra.ofField K S hS) := by
  dunfold Localization.subalgebra.ofField
  rw [Subalgebra.copy_eq]
  infer_instance

instance is_fraction_ring_of_field : IsFractionRing (subalgebra.ofField K S hS) K :=
  IsFractionRing.is_fraction_ring_of_is_localization S _ _ hS

end Subalgebra

end Field

end Localization

