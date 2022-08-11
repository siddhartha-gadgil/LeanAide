/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathbin.Algebra.Ring.Equiv
import Mathbin.GroupTheory.MonoidLocalization
import Mathbin.RingTheory.Algebraic
import Mathbin.RingTheory.Ideal.LocalRing
import Mathbin.RingTheory.Ideal.Quotient
import Mathbin.RingTheory.IntegralClosure
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Integer
import Mathbin.RingTheory.NonZeroDivisors
import Mathbin.GroupTheory.Submonoid.Inverses
import Mathbin.Tactic.RingExp

/-!
# Integral and algebraic elements of a fraction field

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRingₓ R] (M : Submonoid R) {S : Type _} [CommRingₓ S]

variable [Algebra R S] {P : Type _} [CommRingₓ P]

open BigOperators Polynomial

namespace IsLocalization

section IntegerNormalization

open Polynomial

variable (M) {S} [IsLocalization M S]

open Classical

/-- `coeff_integer_normalization p` gives the coefficients of the polynomial
`integer_normalization p` -/
noncomputable def coeffIntegerNormalization (p : S[X]) (i : ℕ) : R :=
  if hi : i ∈ p.support then
    Classical.some
      (Classical.some_spec (exist_integer_multiples_of_finset M (p.support.Image p.coeff)) (p.coeff i)
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  else 0

theorem coeff_integer_normalization_of_not_mem_support (p : S[X]) (i : ℕ) (h : coeff p i = 0) :
    coeffIntegerNormalization M p i = 0 := by
  simp only [← coeff_integer_normalization, ← h, ← mem_support_iff, ← eq_self_iff_true, ← not_true, ← Ne.def, ← dif_neg,
    ← not_false_iff]

theorem coeff_integer_normalization_mem_support (p : S[X]) (i : ℕ) (h : coeffIntegerNormalization M p i ≠ 0) :
    i ∈ p.support := by
  contrapose h
  rw [Ne.def, not_not, coeff_integer_normalization, dif_neg h]

/-- `integer_normalization g` normalizes `g` to have integer coefficients
by clearing the denominators -/
noncomputable def integerNormalization (p : S[X]) : R[X] :=
  ∑ i in p.support, monomial i (coeffIntegerNormalization M p i)

@[simp]
theorem integer_normalization_coeff (p : S[X]) (i : ℕ) :
    (integerNormalization M p).coeff i = coeffIntegerNormalization M p i := by
  simp (config := { contextual := true })[← integer_normalization, ← coeff_monomial, ←
    coeff_integer_normalization_of_not_mem_support]

theorem integer_normalization_spec (p : S[X]) :
    ∃ b : M, ∀ i, algebraMap R S ((integerNormalization M p).coeff i) = (b : R) • p.coeff i := by
  use Classical.some (exist_integer_multiples_of_finset M (p.support.image p.coeff))
  intro i
  rw [integer_normalization_coeff, coeff_integer_normalization]
  split_ifs with hi
  · exact
      Classical.some_spec
        (Classical.some_spec (exist_integer_multiples_of_finset M (p.support.image p.coeff)) (p.coeff i)
          (finset.mem_image.mpr ⟨i, hi, rfl⟩))
    
  · convert (smul_zero _).symm
    · apply RingHom.map_zero
      
    · exact not_mem_support_iff.mp hi
      
    

theorem integer_normalization_map_to_map (p : S[X]) :
    ∃ b : M, (integerNormalization M p).map (algebraMap R S) = (b : R) • p :=
  let ⟨b, hb⟩ := integer_normalization_spec M p
  ⟨b,
    Polynomial.ext fun i => by
      rw [coeff_map, coeff_smul]
      exact hb i⟩

variable {R' : Type _} [CommRingₓ R']

theorem integer_normalization_eval₂_eq_zero (g : S →+* R') (p : S[X]) {x : R'} (hx : eval₂ g x p = 0) :
    eval₂ (g.comp (algebraMap R S)) x (integerNormalization M p) = 0 :=
  let ⟨b, hb⟩ := integer_normalization_map_to_map M p
  trans (eval₂_map (algebraMap R S) g x).symm
    (by
      rw [hb, ← IsScalarTower.algebra_map_smul S (b : R) p, eval₂_smul, hx, mul_zero])

theorem integer_normalization_aeval_eq_zero [Algebra R R'] [Algebra S R'] [IsScalarTower R S R'] (p : S[X]) {x : R'}
    (hx : aeval x p = 0) : aeval x (integerNormalization M p) = 0 := by
  rw [aeval_def, IsScalarTower.algebra_map_eq R S R', integer_normalization_eval₂_eq_zero _ _ _ hx]

end IntegerNormalization

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable {A K C : Type _} [CommRingₓ A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

variable [CommRingₓ C]

theorem integer_normalization_eq_zero_iff {p : K[X]} : integerNormalization (nonZeroDivisors A) p = 0 ↔ p = 0 := by
  refine' polynomial.ext_iff.trans (polynomial.ext_iff.trans _).symm
  obtain ⟨⟨b, nonzero⟩, hb⟩ := integer_normalization_spec _ p
  constructor <;> intro h i
  · apply to_map_eq_zero_iff.mp
    rw [hb i, h i]
    apply smul_zero
    assumption
    
  · have hi := h i
    rw [Polynomial.coeff_zero, ← @to_map_eq_zero_iff A _ K, hb i, Algebra.smul_def] at hi
    apply Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hi)
    intro h
    apply mem_non_zero_divisors_iff_ne_zero.mp nonzero
    exact to_map_eq_zero_iff.mp h
    

variable (A K C)

/-- An element of a ring is algebraic over the ring `A` iff it is algebraic
over the field of fractions of `A`.
-/
theorem is_algebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] {x : C} :
    IsAlgebraic A x ↔ IsAlgebraic K x := by
  constructor <;> rintro ⟨p, hp, px⟩
  · refine' ⟨p.map (algebraMap A K), fun h => hp (Polynomial.ext fun i => _), _⟩
    · have : algebraMap A K (p.coeff i) = 0 :=
        trans (Polynomial.coeff_map _ _).symm
          (by
            simp [← h])
      exact to_map_eq_zero_iff.mp this
      
    · rwa [IsScalarTower.aeval_apply _ K] at px
      
    
  · exact
      ⟨integer_normalization _ p, mt integer_normalization_eq_zero_iff.mp hp,
        integer_normalization_aeval_eq_zero _ p px⟩
    

variable {A K C}

/-- A ring is algebraic over the ring `A` iff it is algebraic over the field of fractions of `A`.
-/
theorem comap_is_algebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] :
    Algebra.IsAlgebraic A C ↔ Algebra.IsAlgebraic K C :=
  ⟨fun h x => (is_algebraic_iff A K C).mp (h x), fun h x => (is_algebraic_iff A K C).mpr (h x)⟩

end IsFractionRing

open IsLocalization

section IsIntegral

variable {R S} {Rₘ Sₘ : Type _} [CommRingₓ Rₘ] [CommRingₓ Sₘ]

variable [Algebra R Rₘ] [IsLocalization M Rₘ]

variable [Algebra S Sₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]

variable {S M}

open Polynomial

theorem RingHom.is_integral_elem_localization_at_leading_coeff {R S : Type _} [CommRingₓ R] [CommRingₓ S] (f : R →+* S)
    (x : S) (p : R[X]) (hf : p.eval₂ f x = 0) (M : Submonoid R) (hM : p.leadingCoeff ∈ M) {Rₘ Sₘ : Type _}
    [CommRingₓ Rₘ] [CommRingₓ Sₘ] [Algebra R Rₘ] [IsLocalization M Rₘ] [Algebra S Sₘ]
    [IsLocalization (M.map f : Submonoid S) Sₘ] :
    (map Sₘ f M.le_comap_map : Rₘ →+* _).IsIntegralElem (algebraMap S Sₘ x) := by
  by_cases' triv : (1 : Rₘ) = 0
  · exact ⟨0, ⟨trans leading_coeff_zero triv.symm, eval₂_zero _ _⟩⟩
    
  have : Nontrivial Rₘ := nontrivial_of_ne 1 0 triv
  obtain ⟨b, hb⟩ := is_unit_iff_exists_inv.mp (map_units Rₘ ⟨p.leading_coeff, hM⟩)
  refine' ⟨p.map (algebraMap R Rₘ) * C b, ⟨_, _⟩⟩
  · refine' monic_mul_C_of_leading_coeff_mul_eq_one _
    rwa [leading_coeff_map_of_leading_coeff_ne_zero (algebraMap R Rₘ)]
    refine' fun hfp => zero_ne_one (trans (zero_mul b).symm (hfp ▸ hb) : (0 : Rₘ) = 1)
    
  · refine' eval₂_mul_eq_zero_of_left _ _ _ _
    erw [eval₂_map, IsLocalization.map_comp, ← hom_eval₂ _ f (algebraMap S Sₘ) x]
    exact trans (congr_arg (algebraMap S Sₘ) hf) (RingHom.map_zero _)
    

/-- Given a particular witness to an element being algebraic over an algebra `R → S`,
We can localize to a submonoid containing the leading coefficient to make it integral.
Explicitly, the map between the localizations will be an integral ring morphism -/
theorem is_integral_localization_at_leading_coeff {x : S} (p : R[X]) (hp : aeval x p = 0) (hM : p.leadingCoeff ∈ M) :
    (map Sₘ (algebraMap R S) (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
          Rₘ →+* _).IsIntegralElem
      (algebraMap S Sₘ x) :=
  (algebraMap R S).is_integral_elem_localization_at_leading_coeff x p hp M hM

/-- If `R → S` is an integral extension, `M` is a submonoid of `R`,
`Rₘ` is the localization of `R` at `M`,
and `Sₘ` is the localization of `S` at the image of `M` under the extension map,
then the induced map `Rₘ → Sₘ` is also an integral extension -/
theorem is_integral_localization (H : Algebra.IsIntegral R S) :
    (map Sₘ (algebraMap R S) (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
        Rₘ →+* _).IsIntegral :=
  by
  intro x
  obtain ⟨⟨s, ⟨u, hu⟩⟩, hx⟩ := surj (Algebra.algebraMapSubmonoid S M) x
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := is_unit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩)
  refine' @is_integral_of_is_integral_mul_unit Rₘ _ _ _ (localizationAlgebra M S) x (algebraMap S Sₘ u) v' _ _
  · replace hv' := congr_arg (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) hv'
    rw [RingHom.map_mul, RingHom.map_one, ← RingHom.comp_apply _ (algebraMap R Rₘ)] at hv'
    erw [IsLocalization.map_comp] at hv'
    exact hv.2 ▸ hv'
    
  · obtain ⟨p, hp⟩ := H s
    exact hx.symm ▸ is_integral_localization_at_leading_coeff p hp.2 (hp.1.symm ▸ M.one_mem)
    

theorem is_integral_localization' {R S : Type _} [CommRingₓ R] [CommRingₓ S] {f : R →+* S} (hf : f.IsIntegral)
    (M : Submonoid R) :
    (map (Localization (M.map (f : R →* S))) f (M.le_comap_map : _ ≤ Submonoid.comap (f : R →* S) _) :
        Localization M →+* _).IsIntegral :=
  @is_integral_localization R _ M S _ f.toAlgebra _ _ _ _ _ _ _ _ hf

end IsIntegral

variable {A K : Type _} [CommRingₓ A] [IsDomain A]

namespace IsIntegralClosure

variable (A) {L : Type _} [Field K] [Field L] [Algebra A K] [Algebra A L] [IsFractionRing A K]

variable (C : Type _) [CommRingₓ C] [IsDomain C] [Algebra C L] [IsIntegralClosure C A L]

variable [Algebra A C] [IsScalarTower A C L]

open Algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
theorem is_fraction_ring_of_algebraic (alg : IsAlgebraic A L) (inj : ∀ x, algebraMap A L x = 0 → x = 0) :
    IsFractionRing C L :=
  { map_units := fun ⟨y, hy⟩ =>
      IsUnit.mk0 _
        (show algebraMap C L y ≠ 0 from fun h =>
          mem_non_zero_divisors_iff_ne_zero.mp hy
            ((injective_iff_map_eq_zero (algebraMap C L)).mp (algebra_map_injective C A L) _ h)),
    surj := fun z =>
      let ⟨x, y, hy, hxy⟩ := exists_integral_multiple (alg z) inj
      ⟨⟨mk' C (x : L) x.2, algebraMap _ _ y,
          mem_non_zero_divisors_iff_ne_zero.mpr fun h =>
            hy
              (inj _
                (by
                  rw [IsScalarTower.algebra_map_apply A C L, h, RingHom.map_zero]))⟩,
        by
        rw [SetLike.coe_mk, algebra_map_mk', ← IsScalarTower.algebra_map_apply A C L, hxy]⟩,
    eq_iff_exists := fun x y =>
      ⟨fun h =>
        ⟨1, by
          simpa using algebra_map_injective C A L h⟩,
        fun ⟨c, hc⟩ => congr_arg (algebraMap _ L) (mul_right_cancel₀ (mem_non_zero_divisors_iff_ne_zero.mp c.2) hc)⟩ }

variable (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
theorem is_fraction_ring_of_finite_extension [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L] :
    IsFractionRing C L :=
  is_fraction_ring_of_algebraic A C (IsFractionRing.comap_is_algebraic_iff.mpr (is_algebraic_of_finite K L)) fun x hx =>
    IsFractionRing.to_map_eq_zero_iff.mp
      ((algebraMap K L).map_eq_zero.mp <| (IsScalarTower.algebra_map_apply _ _ _ _).symm.trans hx)

end IsIntegralClosure

namespace integralClosure

variable {L : Type _} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]

open Algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
theorem is_fraction_ring_of_algebraic [Algebra A L] (alg : IsAlgebraic A L) (inj : ∀ x, algebraMap A L x = 0 → x = 0) :
    IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.is_fraction_ring_of_algebraic A (integralClosure A L) alg inj

variable (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
theorem is_fraction_ring_of_finite_extension [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L] :
    IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.is_fraction_ring_of_finite_extension A K L (integralClosure A L)

end integralClosure

namespace IsFractionRing

variable (R S K)

/-- `S` is algebraic over `R` iff a fraction ring of `S` is algebraic over `R` -/
theorem is_algebraic_iff' [Field K] [IsDomain R] [IsDomain S] [Algebra R K] [Algebra S K] [NoZeroSmulDivisors R K]
    [IsFractionRing S K] [IsScalarTower R S K] : Algebra.IsAlgebraic R S ↔ Algebra.IsAlgebraic R K := by
  simp only [← Algebra.IsAlgebraic]
  constructor
  · intro h x
    rw [IsFractionRing.is_algebraic_iff R (FractionRing R) K, is_algebraic_iff_is_integral]
    obtain ⟨a : S, b, ha, rfl⟩ := @div_surjective S _ _ _ _ _ _ x
    obtain ⟨f, hf₁, hf₂⟩ := h b
    rw [div_eq_mul_inv]
    refine' is_integral_mul _ _
    · rw [← is_algebraic_iff_is_integral]
      refine'
        _root_.is_algebraic_of_larger_base_of_injective (NoZeroSmulDivisors.algebra_map_injective R (FractionRing R)) _
      exact is_algebraic_algebra_map_of_is_algebraic (h a)
      
    · rw [← is_algebraic_iff_is_integral]
      use (f.map (algebraMap R (FractionRing R))).reverse
      constructor
      · rwa [Ne.def, Polynomial.reverse_eq_zero, ← Polynomial.degree_eq_bot,
          Polynomial.degree_map_eq_of_injective (NoZeroSmulDivisors.algebra_map_injective R (FractionRing R)),
          Polynomial.degree_eq_bot]
        
      · have : Invertible (algebraMap S K b) :=
          IsUnit.invertible
            (is_unit_of_mem_non_zero_divisors
              (mem_non_zero_divisors_iff_ne_zero.2 fun h =>
                nonZeroDivisors.ne_zero ha
                  ((injective_iff_map_eq_zero (algebraMap S K)).1 (NoZeroSmulDivisors.algebra_map_injective _ _) b h)))
        rw [Polynomial.aeval_def, ← inv_of_eq_inv, Polynomial.eval₂_reverse_eq_zero_iff, Polynomial.eval₂_map, ←
          IsScalarTower.algebra_map_eq, ← Polynomial.aeval_def, ← IsScalarTower.algebra_map_aeval, hf₂,
          RingHom.map_zero]
        
      
    
  · intro h x
    obtain ⟨f, hf₁, hf₂⟩ := h (algebraMap S K x)
    use f, hf₁
    rw [← IsScalarTower.algebra_map_aeval] at hf₂
    exact (injective_iff_map_eq_zero (algebraMap S K)).1 (NoZeroSmulDivisors.algebra_map_injective _ _) _ hf₂
    

open nonZeroDivisors

variable (R) {S K}

/-- If the `S`-multiples of `a` are contained in some `R`-span, then `Frac(S)`-multiples of `a`
are contained in the equivalent `Frac(R)`-span. -/
theorem ideal_span_singleton_map_subset {L : Type _} [IsDomain R] [IsDomain S] [Field K] [Field L] [Algebra R K]
    [Algebra R L] [Algebra S L] [IsIntegralClosure S R L] [IsFractionRing S L] [Algebra K L] [IsScalarTower R S L]
    [IsScalarTower R K L] {a : S} {b : Set S} (alg : Algebra.IsAlgebraic R L)
    (inj : Function.Injective (algebraMap R L)) (h : (Ideal.span ({a} : Set S) : Set S) ⊆ Submodule.span R b) :
    (Ideal.span ({algebraMap S L a} : Set L) : Set L) ⊆ Submodule.span K (algebraMap S L '' b) := by
  intro x hx
  obtain ⟨x', rfl⟩ := ideal.mem_span_singleton.mp hx
  obtain ⟨y', z', rfl⟩ := IsLocalization.mk'_surjective S⁰ x'
  obtain ⟨y, z, hz0, yz_eq⟩ := IsIntegralClosure.exists_smul_eq_mul alg inj y' (nonZeroDivisors.coe_ne_zero z')
  have injRS : Function.Injective (algebraMap R S) := by
    refine' Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ algebraMap R S) from _)
    rwa [← RingHom.coe_comp, ← IsScalarTower.algebra_map_eq]
  have hz0' : algebraMap R S z ∈ S⁰ :=
    map_mem_non_zero_divisors (algebraMap R S) injRS (mem_non_zero_divisors_of_ne_zero hz0)
  have mk_yz_eq : IsLocalization.mk' L y' z' = IsLocalization.mk' L y ⟨_, hz0'⟩ := by
    rw [Algebra.smul_def, mul_comm _ y, mul_comm _ y', ← SetLike.coe_mk (algebraMap R S z) hz0'] at yz_eq
    exact IsLocalization.mk'_eq_of_eq yz_eq.symm
  suffices hy : algebraMap S L (a * y) ∈ Submodule.span K (⇑(algebraMap S L) '' b)
  · rw [mk_yz_eq, IsFractionRing.mk'_eq_div, SetLike.coe_mk, ← IsScalarTower.algebra_map_apply,
      IsScalarTower.algebra_map_apply R K L, div_eq_mul_inv, ← mul_assoc, mul_comm, ← RingHom.map_inv, ←
      Algebra.smul_def, ← _root_.map_mul]
    exact (Submodule.span K _).smul_mem _ hy
    
  refine' Submodule.span_subset_span R K _ _
  rw [Submodule.span_algebra_map_image_of_tower]
  exact Submodule.mem_map_of_mem (h (ideal.mem_span_singleton.mpr ⟨y, rfl⟩))

end IsFractionRing

