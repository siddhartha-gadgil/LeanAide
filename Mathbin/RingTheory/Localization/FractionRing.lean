/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathbin.Algebra.Algebra.Tower
import Mathbin.RingTheory.Localization.Basic

/-!
# Fraction ring / fraction field Frac(R) as localization

## Main definitions

 * `is_fraction_ring R K` expresses that `K` is a field of fractions of `R`, as an abbreviation of
   `is_localization (non_zero_divisors R) K`

## Main results

 * `is_fraction_ring.field`: a definition (not an instance) stating the localization of an integral
   domain `R` at `R \ {0}` is a field
 * `rat.is_fraction_ring` is an instance stating `ℚ` is the field of fractions of `ℤ`

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable (R : Type _) [CommRingₓ R] {M : Submonoid R} (S : Type _) [CommRingₓ S]

variable [Algebra R S] {P : Type _} [CommRingₓ P]

variable {A : Type _} [CommRingₓ A] [IsDomain A] (K : Type _)

/-- `is_fraction_ring R K` states `K` is the field of fractions of an integral domain `R`. -/
-- TODO: should this extend `algebra` instead of assuming it?
abbrev IsFractionRing [CommRingₓ K] [Algebra R K] :=
  IsLocalization (nonZeroDivisors R) K

/-- The cast from `int` to `rat` as a `fraction_ring`. -/
instance Rat.is_fraction_ring : IsFractionRing ℤ ℚ where
  map_units := by
    rintro ⟨x, hx⟩
    rw [mem_non_zero_divisors_iff_ne_zero] at hx
    simpa only [← RingHom.eq_int_cast, ← is_unit_iff_ne_zero, ← Int.cast_eq_zero, ← Ne.def, ← Subtype.coe_mk] using hx
  surj := by
    rintro ⟨n, d, hd, h⟩
    refine' ⟨⟨n, ⟨d, _⟩⟩, Rat.mul_denom_eq_num⟩
    rwa [mem_non_zero_divisors_iff_ne_zero, Int.coe_nat_ne_zero_iff_pos]
  eq_iff_exists := by
    intro x y
    rw [RingHom.eq_int_cast, RingHom.eq_int_cast, Int.cast_inj]
    refine'
      ⟨by
        rintro rfl
        use 1, _⟩
    rintro ⟨⟨c, hc⟩, h⟩
    apply Int.eq_of_mul_eq_mul_right _ h
    rwa [mem_non_zero_divisors_iff_ne_zero] at hc

namespace IsFractionRing

open IsLocalization

variable {R K}

section CommRingₓ

variable [CommRingₓ K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]

theorem to_map_eq_zero_iff {x : R} : algebraMap R K x = 0 ↔ x = 0 :=
  to_map_eq_zero_iff _ (le_of_eqₓ rfl)

variable (R K)

protected theorem injective : Function.Injective (algebraMap R K) :=
  IsLocalization.injective _ (le_of_eqₓ rfl)

variable {R K}

instance (priority := 100) [NoZeroDivisors K] : NoZeroSmulDivisors R K :=
  NoZeroSmulDivisors.of_algebra_map_injective <| IsFractionRing.injective R K

variable {R K}

protected theorem to_map_ne_zero_of_mem_non_zero_divisors [Nontrivial R] {x : R} (hx : x ∈ nonZeroDivisors R) :
    algebraMap R K x ≠ 0 :=
  IsLocalization.to_map_ne_zero_of_mem_non_zero_divisors _ le_rfl hx

variable (A)

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is an
integral domain. -/
protected theorem is_domain : IsDomain K :=
  is_domain_of_le_non_zero_divisors _ (le_reflₓ (nonZeroDivisors A))

attribute [local instance] Classical.decEq

/-- The inverse of an element in the field of fractions of an integral domain. -/
protected noncomputable irreducible_def inv (z : K) : K :=
  if h : z = 0 then 0
  else
    mk' K ↑(sec (nonZeroDivisors A) z).2
      ⟨(sec _ z).1,
        mem_non_zero_divisors_iff_ne_zero.2 fun h0 => h <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) z) h0⟩

attribute [local semireducible] IsFractionRing.inv

protected theorem mul_inv_cancel (x : K) (hx : x ≠ 0) : x * IsFractionRing.inv A x = 1 :=
  show x * dite _ _ _ = 1 by
    rw [dif_neg hx, ←
        IsUnit.mul_left_inj
          (map_units K
            ⟨(sec _ x).1,
              mem_non_zero_divisors_iff_ne_zero.2 fun h0 =>
                hx <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) x) h0⟩),
        one_mulₓ, mul_assoc, mk'_spec, ← eq_mk'_iff_mul_eq] <;>
      exact (mk'_sec _ x).symm

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is a field.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def toField : Field K :=
  { IsFractionRing.is_domain A,
    show CommRingₓ K by
      infer_instance with
    inv := IsFractionRing.inv A, mul_inv_cancel := IsFractionRing.mul_inv_cancel A, inv_zero := dif_pos rfl }

end CommRingₓ

variable {B : Type _} [CommRingₓ B] [IsDomain B] [Field K] {L : Type _} [Field L] [Algebra A K] [IsFractionRing A K]
  {g : A →+* L}

theorem mk'_mk_eq_div {r s} (hs : s ∈ nonZeroDivisors A) : mk' K r ⟨s, hs⟩ = algebraMap A K r / algebraMap A K s :=
  mk'_eq_iff_eq_mul.2 <|
    (div_mul_cancel (algebraMap A K r) (IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors hs)).symm

@[simp]
theorem mk'_eq_div {r} (s : nonZeroDivisors A) : mk' K r s = algebraMap A K r / algebraMap A K s :=
  mk'_mk_eq_div s.2

theorem div_surjective (z : K) : ∃ (x y : A)(hy : y ∈ nonZeroDivisors A), algebraMap _ _ x / algebraMap _ _ y = z :=
  let ⟨x, ⟨y, hy⟩, h⟩ := mk'_surjective (nonZeroDivisors A) z
  ⟨x, y, hy, by
    rwa [mk'_eq_div] at h⟩

theorem is_unit_map_of_injective (hg : Function.Injective g) (y : nonZeroDivisors A) : IsUnit (g y) :=
  IsUnit.mk0 (g y) <| show g.toMonoidWithZeroHom y ≠ 0 from map_ne_zero_of_mem_non_zero_divisors g hg y.2

@[simp]
theorem mk'_eq_zero_iff_eq_zero [Algebra R K] [IsFractionRing R K] {x : R} {y : nonZeroDivisors R} :
    mk' K x y = 0 ↔ x = 0 := by
  refine'
    ⟨fun hxy => _, fun h => by
      rw [h, mk'_zero]⟩
  · simp_rw [mk'_eq_zero_iff, mul_right_coe_non_zero_divisors_eq_zero_iff] at hxy
    exact (exists_const _).mp hxy
    

theorem mk'_eq_one_iff_eq {x : A} {y : nonZeroDivisors A} : mk' K x y = 1 ↔ x = y := by
  refine'
    ⟨_, fun hxy => by
      rw [hxy, mk'_self']⟩
  · intro hxy
    have hy : (algebraMap A K) ↑y ≠ (0 : K) := IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors y.property
    rw [IsFractionRing.mk'_eq_div, div_eq_one_iff_eq hy] at hxy
    exact IsFractionRing.injective A K hxy
    

open Function

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field, we get a
field hom sending `z : K` to `g x * (g y)⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def lift (hg : Injective g) : K →+* L :=
  lift fun y : nonZeroDivisors A => is_unit_map_of_injective hg y

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
the field hom induced from `K` to `L` maps `x` to `g x` for all
`x : A`. -/
@[simp]
theorem lift_algebra_map (hg : Injective g) (x) : lift hg (algebraMap A K x) = g x :=
  lift_eq _ _

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
field hom induced from `K` to `L` maps `f x / f y` to `g x / g y` for all
`x : A, y ∈ non_zero_divisors A`. -/
theorem lift_mk' (hg : Injective g) (x) (y : nonZeroDivisors A) : lift hg (mk' K x y) = g x / g y := by
  simp only [← mk'_eq_div, ← RingHom.map_div, ← lift_algebra_map]

/-- Given integral domains `A, B` with fields of fractions `K`, `L`
and an injective ring hom `j : A →+* B`, we get a field hom
sending `z : K` to `g (j x) * (g (j y))⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def map {A B K L : Type _} [CommRingₓ A] [CommRingₓ B] [IsDomain B] [CommRingₓ K] [Algebra A K]
    [IsFractionRing A K] [CommRingₓ L] [Algebra B L] [IsFractionRing B L] {j : A →+* B} (hj : Injective j) : K →+* L :=
  map L j
    (show nonZeroDivisors A ≤ (nonZeroDivisors B).comap j from
      non_zero_divisors_le_comap_non_zero_divisors_of_injective j hj)

/-- Given integral domains `A, B` and localization maps to their fields of fractions
`f : A →+* K, g : B →+* L`, an isomorphism `j : A ≃+* B` induces an isomorphism of
fields of fractions `K ≃+* L`. -/
noncomputable def fieldEquivOfRingEquiv [Algebra B L] [IsFractionRing B L] (h : A ≃+* B) : K ≃+* L :=
  ringEquivOfRingEquiv K L h
    (by
      ext b
      show b ∈ h.to_equiv '' _ ↔ _
      erw [h.to_equiv.image_eq_preimage, Set.Preimage, Set.mem_set_of_eq, mem_non_zero_divisors_iff_ne_zero,
        mem_non_zero_divisors_iff_ne_zero]
      exact h.symm.map_ne_zero_iff)

variable (S)

theorem is_fraction_ring_iff_of_base_ring_equiv (h : R ≃+* P) :
    IsFractionRing R S ↔ @IsFractionRing P _ S _ ((algebraMap R S).comp h.symm.toRingHom).toAlgebra := by
  delta' IsFractionRing
  convert is_localization_iff_of_base_ring_equiv _ _ h
  ext x
  erw [Submonoid.map_equiv_eq_comap_symm]
  simp only [← MulEquiv.coe_to_monoid_hom, ← RingEquiv.to_mul_equiv_eq_coe, ← Submonoid.mem_comap]
  constructor
  · rintro hx z (hz : z * h.symm x = 0)
    rw [← h.map_eq_zero_iff]
    apply hx
    simpa only [← h.map_zero, ← h.apply_symm_apply, ← h.map_mul] using congr_arg h hz
    
  · rintro (hx : h.symm x ∈ _) z hz
    rw [← h.symm.map_eq_zero_iff]
    apply hx
    rw [← h.symm.map_mul, hz, h.symm.map_zero]
    

protected theorem nontrivial (R S : Type _) [CommRingₓ R] [Nontrivial R] [CommRingₓ S] [Algebra R S]
    [IsFractionRing R S] : Nontrivial S := by
  apply nontrivial_of_ne
  intro h
  apply @zero_ne_one R
  exact
    IsLocalization.injective S (le_of_eqₓ rfl) (((algebraMap R S).map_zero.trans h).trans (algebraMap R S).map_one.symm)

end IsFractionRing

variable (R A)

/-- The fraction ring of a commutative ring `R` as a quotient type.

We instantiate this definition as generally as possible, and assume that the
commutative ring `R` is an integral domain only when this is needed for proving.
-/
@[reducible]
def FractionRing :=
  Localization (nonZeroDivisors R)

namespace FractionRing

instance unique [Subsingleton R] : Unique (FractionRing R) :=
  Localization.unique

instance [Nontrivial R] : Nontrivial (FractionRing R) :=
  ⟨⟨(algebraMap R _) 0, (algebraMap _ _) 1, fun H => zero_ne_one (IsLocalization.injective _ le_rfl H)⟩⟩

variable {A}

noncomputable instance : Field (FractionRing A) :=
  { Localization.commRing, IsFractionRing.toField A with add := (· + ·), mul := (· * ·), neg := Neg.neg, sub := Sub.sub,
    one := 1, zero := 0, nsmul := AddMonoidₓ.nsmul, zsmul := SubNegMonoidₓ.zsmul, npow := Localization.npow _ }

@[simp]
theorem mk_eq_div {r s} :
    (Localization.mk r s : FractionRing A) = (algebraMap _ _ r / algebraMap A _ s : FractionRing A) := by
  rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div]

noncomputable instance [IsDomain R] [Field K] [Algebra R K] [NoZeroSmulDivisors R K] : Algebra (FractionRing R) K :=
  RingHom.toAlgebra (IsFractionRing.lift (NoZeroSmulDivisors.algebra_map_injective R _))

instance [IsDomain R] [Field K] [Algebra R K] [NoZeroSmulDivisors R K] : IsScalarTower R (FractionRing R) K :=
  IsScalarTower.of_algebra_map_eq fun x => (IsFractionRing.lift_algebra_map _ x).symm

variable (A)

/-- Given an integral domain `A` and a localization map to a field of fractions
`f : A →+* K`, we get an `A`-isomorphism between the field of fractions of `A` as a quotient
type and `K`. -/
noncomputable def algEquiv (K : Type _) [Field K] [Algebra A K] [IsFractionRing A K] : FractionRing A ≃ₐ[A] K :=
  Localization.algEquiv (nonZeroDivisors A) K

instance [Algebra R A] [NoZeroSmulDivisors R A] : NoZeroSmulDivisors R (FractionRing A) :=
  NoZeroSmulDivisors.of_algebra_map_injective
    (by
      rw [IsScalarTower.algebra_map_eq R A]
      exact
        Function.Injective.comp (NoZeroSmulDivisors.algebra_map_injective _ _)
          (NoZeroSmulDivisors.algebra_map_injective _ _))

end FractionRing

