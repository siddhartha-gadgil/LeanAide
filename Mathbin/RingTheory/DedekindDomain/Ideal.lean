/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathbin.Algebra.Algebra.Subalgebra.Pointwise
import Mathbin.AlgebraicGeometry.PrimeSpectrum.Noetherian
import Mathbin.Order.Hom.Basic
import Mathbin.RingTheory.DedekindDomain.Basic
import Mathbin.RingTheory.FractionalIdeal

/-!
# Dedekind domains and ideals

In this file, we show a ring is a Dedekind domain iff all fractional ideals are invertible.
Then we prove some results on the unique factorization monoid structure of the ideals.

## Main definitions

 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain where
   every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of
   fractions.
 - `is_dedekind_domain.height_one_spectrum` defines the type of nonzero prime ideals of `R`.

## Main results:
 - `is_dedekind_domain_iff_is_dedekind_domain_inv`
 - `ideal.unique_factorization_monoid`

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ is_field A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (R A K : Type _) [CommRingₓ R] [CommRingₓ A] [Field K]

open nonZeroDivisors Polynomial

variable [IsDomain A]

section Inverse

namespace FractionalIdeal

variable {R₁ : Type _} [CommRingₓ R₁] [IsDomain R₁] [Algebra R₁ K] [IsFractionRing R₁ K]

variable {I J : FractionalIdeal R₁⁰ K}

noncomputable instance : Inv (FractionalIdeal R₁⁰ K) :=
  ⟨fun I => 1 / I⟩

theorem inv_eq : I⁻¹ = 1 / I :=
  rfl

theorem inv_zero' : (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0 :=
  FractionalIdeal.div_zero

theorem inv_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    J⁻¹ = ⟨(1 : FractionalIdeal R₁⁰ K) / J, FractionalIdeal.fractional_div_of_nonzero h⟩ :=
  FractionalIdeal.div_nonzero _

theorem coe_inv_of_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    (↑J⁻¹ : Submodule R₁ K) = IsLocalization.coeSubmodule K ⊤ / J := by
  rwa [inv_nonzero _]
  rfl
  assumption

variable {K}

theorem mem_inv_iff (hI : I ≠ 0) {x : K} : x ∈ I⁻¹ ↔ ∀, ∀ y ∈ I, ∀, x * y ∈ (1 : FractionalIdeal R₁⁰ K) :=
  FractionalIdeal.mem_div_iff_of_nonzero hI

theorem inv_anti_mono (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) : J⁻¹ ≤ I⁻¹ := fun x => by
  simp only [← mem_inv_iff hI, ← mem_inv_iff hJ]
  exact fun h y hy => h y (hIJ hy)

theorem le_self_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) : I ≤ I * I⁻¹ :=
  FractionalIdeal.le_self_mul_one_div hI

variable (K)

theorem coe_ideal_le_self_mul_inv (I : Ideal R₁) : (I : FractionalIdeal R₁⁰ K) ≤ I * I⁻¹ :=
  le_self_mul_inv FractionalIdeal.coe_ideal_le_one

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = I⁻¹ := by
  have hI : I ≠ 0 := FractionalIdeal.ne_zero_of_mul_eq_one I J h
  suffices h' : I * (1 / I) = 1
  · exact congr_arg Units.inv <| @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
    
  apply le_antisymmₓ
  · apply fractional_ideal.mul_le.mpr _
    intro x hx y hy
    rw [mul_comm]
    exact (FractionalIdeal.mem_div_iff_of_nonzero hI).mp hy x hx
    
  rw [← h]
  apply FractionalIdeal.mul_left_mono I
  apply (FractionalIdeal.le_div_iff_of_nonzero hI).mpr _
  intro y hy x hx
  rw [mul_comm]
  exact FractionalIdeal.mul_mem_mul hx hy

theorem mul_inv_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
  ⟨fun h => ⟨I⁻¹, h⟩, fun ⟨J, hJ⟩ => by
    rwa [← right_inverse_eq K I J hJ]⟩

theorem mul_inv_cancel_iff_is_unit {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ IsUnit I :=
  (mul_inv_cancel_iff K).trans is_unit_iff_exists_inv.symm

variable {K' : Type _} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
theorem map_inv (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') : I⁻¹.map (h : K →ₐ[R₁] K') = (I.map h)⁻¹ := by
  rw [inv_eq, FractionalIdeal.map_div, FractionalIdeal.map_one, inv_eq]

open Submodule Submodule.IsPrincipal

@[simp]
theorem span_singleton_inv (x : K) : (FractionalIdeal.spanSingleton R₁⁰ x)⁻¹ = FractionalIdeal.spanSingleton _ x⁻¹ :=
  FractionalIdeal.one_div_span_singleton x

theorem mul_generator_self_inv {R₁ : Type _} [CommRingₓ R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
    (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    I * FractionalIdeal.spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 := by
  -- Rewrite only the `I` that appears alone.
  conv_lhs => congr rw [FractionalIdeal.eq_span_singleton_of_principal I]
  rw [FractionalIdeal.span_singleton_mul_span_singleton, mul_inv_cancel, FractionalIdeal.span_singleton_one]
  intro generator_I_eq_zero
  apply h
  rw [FractionalIdeal.eq_span_singleton_of_principal I, generator_I_eq_zero, FractionalIdeal.span_singleton_zero]

theorem invertible_of_principal (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    I * I⁻¹ = 1 :=
  FractionalIdeal.mul_div_self_cancel_iff.mpr
    ⟨FractionalIdeal.spanSingleton _ (generator (I : Submodule R₁ K))⁻¹, mul_generator_self_inv _ I h⟩

theorem invertible_iff_generator_nonzero (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] :
    I * I⁻¹ = 1 ↔ generator (I : Submodule R₁ K) ≠ 0 := by
  constructor
  · intro hI hg
    apply FractionalIdeal.ne_zero_of_mul_eq_one _ _ hI
    rw [FractionalIdeal.eq_span_singleton_of_principal I, hg, FractionalIdeal.span_singleton_zero]
    
  · intro hg
    apply invertible_of_principal
    rw [FractionalIdeal.eq_span_singleton_of_principal I]
    intro hI
    have := FractionalIdeal.mem_span_singleton_self _ (generator (I : Submodule R₁ K))
    rw [hI, FractionalIdeal.mem_zero_iff] at this
    contradiction
    

theorem is_principal_inv (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    Submodule.IsPrincipal I⁻¹.1 := by
  rw [FractionalIdeal.val_eq_coe, FractionalIdeal.is_principal_iff]
  use (generator (I : Submodule R₁ K))⁻¹
  have hI : I * FractionalIdeal.spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1
  apply mul_generator_self_inv _ I h
  exact (right_inverse_eq _ I (FractionalIdeal.spanSingleton _ (generator (I : Submodule R₁ K))⁻¹) hI).symm

@[simp]
theorem inv_one : (1⁻¹ : FractionalIdeal R₁⁰ K) = 1 :=
  FractionalIdeal.div_one

end FractionalIdeal

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (I «expr ≠ » («expr⊥»() : fractional_ideal «expr ⁰»(A) (fraction_ring A)))
/-- A Dedekind domain is an integral domain such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
In particular we provide a `fractional_ideal.comm_group_with_zero` instance,
assuming `is_dedekind_domain A`, which implies `is_dedekind_domain_inv`. For **integral** ideals,
`is_dedekind_domain`(`_inv`) implies only `ideal.cancel_comm_monoid_with_zero`.
-/
def IsDedekindDomainInv : Prop :=
  ∀ (I) (_ : I ≠ (⊥ : FractionalIdeal A⁰ (FractionRing A))), I * I⁻¹ = 1

open FractionalIdeal

variable {R A K}

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (I «expr ≠ » («expr⊥»() : fractional_ideal «expr ⁰»(A) K))
theorem is_dedekind_domain_inv_iff [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomainInv A ↔ ∀ (I) (_ : I ≠ (⊥ : FractionalIdeal A⁰ K)), I * I⁻¹ = 1 := by
  let h := FractionalIdeal.mapEquiv (FractionRing.algEquiv A K)
  refine' h.to_equiv.forall_congr fun I => _
  rw [← h.to_equiv.apply_eq_iff_eq]
  simp [← IsDedekindDomainInv, ← show ⇑h.to_equiv = h from rfl]

theorem FractionalIdeal.adjoin_integral_eq_one_of_is_unit [Algebra A K] [IsFractionRing A K] (x : K)
    (hx : IsIntegral A x) (hI : IsUnit (adjoinIntegral A⁰ x hx)) : adjoinIntegral A⁰ x hx = 1 := by
  set I := adjoin_integral A⁰ x hx
  have mul_self : I * I = I := by
    apply FractionalIdeal.coe_to_submodule_injective
    simp
  convert congr_arg (· * I⁻¹) mul_self <;> simp only [← (mul_inv_cancel_iff_is_unit K).mpr hI, ← mul_assoc, ← mul_oneₓ]

namespace IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K] (h : IsDedekindDomainInv A)

include h

theorem mul_inv_eq_one {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : I * I⁻¹ = 1 :=
  is_dedekind_domain_inv_iff.mp h I hI

theorem inv_mul_eq_one {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : I⁻¹ * I = 1 :=
  (mul_comm _ _).trans (h.mul_inv_eq_one hI)

protected theorem is_unit {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : IsUnit I :=
  is_unit_of_mul_eq_one _ _ (h.mul_inv_eq_one hI)

theorem is_noetherian_ring : IsNoetherianRing A := by
  refine' is_noetherian_ring_iff.mpr ⟨fun I : Ideal A => _⟩
  by_cases' hI : I = ⊥
  · rw [hI]
    apply Submodule.fg_bot
    
  have hI : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_reflₓ (nonZeroDivisors A))).mpr hI
  exact I.fg_of_is_unit (IsFractionRing.injective A (FractionRing A)) (h.is_unit hI)

theorem integrally_closed : IsIntegrallyClosed A := by
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine' ⟨fun x hx => _⟩
  rw [← Set.mem_range, ← Algebra.mem_bot, ← Subalgebra.mem_to_submodule, Algebra.to_submodule_bot, ←
    coe_span_singleton A⁰ (1 : FractionRing A), FractionalIdeal.span_singleton_one, ←
    FractionalIdeal.adjoin_integral_eq_one_of_is_unit x hx (h.is_unit _)]
  · exact mem_adjoin_integral_self A⁰ x hx
    
  · exact fun h => one_ne_zero (eq_zero_iff.mp h 1 (Subalgebra.one_mem _))
    

open Ringₓ

theorem dimension_le_one : DimensionLeOne A := by
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  rintro P P_ne hP
  refine' ideal.is_maximal_def.mpr ⟨hP.ne_top, fun M hM => _⟩
  -- We may assume `P` and `M` (as fractional ideals) are nonzero.
  have P'_ne : (P : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_reflₓ (nonZeroDivisors A))).mpr P_ne
  have M'_ne : (M : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_reflₓ (nonZeroDivisors A))).mpr (lt_of_le_of_ltₓ bot_le hM).ne'
  -- In particular, we'll show `M⁻¹ * P ≤ P`
  suffices (M⁻¹ * P : FractionalIdeal A⁰ (FractionRing A)) ≤ P by
    rw [eq_top_iff, ← coe_ideal_le_coe_ideal (FractionRing A), FractionalIdeal.coe_ideal_top]
    calc (1 : FractionalIdeal A⁰ (FractionRing A)) = _ * _ * _ := _ _ ≤ _ * _ :=
        mul_right_mono (P⁻¹ * M : FractionalIdeal A⁰ (FractionRing A)) this _ = M := _
    · rw [mul_assoc, ← mul_assoc ↑P, h.mul_inv_eq_one P'_ne, one_mulₓ, h.inv_mul_eq_one M'_ne]
      
    · rw [← mul_assoc ↑P, h.mul_inv_eq_one P'_ne, one_mulₓ]
      
    · infer_instance
      
  -- Suppose we have `x ∈ M⁻¹ * P`, then in fact `x = algebra_map _ _ y` for some `y`.
  intro x hx
  have le_one : (M⁻¹ * P : FractionalIdeal A⁰ (FractionRing A)) ≤ 1 := by
    rw [← h.inv_mul_eq_one M'_ne]
    exact FractionalIdeal.mul_left_mono _ ((coe_ideal_le_coe_ideal (FractionRing A)).mpr hM.le)
  obtain ⟨y, hy, rfl⟩ := (mem_coe_ideal _).mp (le_one hx)
  -- Since `M` is strictly greater than `P`, let `z ∈ M \ P`.
  obtain ⟨z, hzM, hzp⟩ := SetLike.exists_of_lt hM
  -- We have `z * y ∈ M * (M⁻¹ * P) = P`.
  have zy_mem := FractionalIdeal.mul_mem_mul (mem_coe_ideal_of_mem A⁰ hzM) hx
  rw [← RingHom.map_mul, ← mul_assoc, h.mul_inv_eq_one M'_ne, one_mulₓ] at zy_mem
  obtain ⟨zy, hzy, zy_eq⟩ := (mem_coe_ideal A⁰).mp zy_mem
  rw [IsFractionRing.injective A (FractionRing A) zy_eq] at hzy
  -- But `P` is a prime ideal, so `z ∉ P` implies `y ∈ P`, as desired.
  exact mem_coe_ideal_of_mem A⁰ (Or.resolve_left (hP.mem_or_mem hzy) hzp)

/-- Showing one side of the equivalence between the definitions
`is_dedekind_domain_inv` and `is_dedekind_domain` of Dedekind domains. -/
theorem is_dedekind_domain : IsDedekindDomain A :=
  ⟨h.IsNoetherianRing, h.DimensionLeOne, h.integrally_closed⟩

end IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K]

/-- Specialization of `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` to Dedekind domains:
Let `I : ideal A` be a nonzero ideal, where `A` is a Dedekind domain that is not a field.
Then `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` states we can find a product of prime
ideals that is contained within `I`. This lemma extends that result by making the product minimal:
let `M` be a maximal ideal that contains `I`, then the product including `M` is contained within `I`
and the product excluding `M` is not contained within `I`. -/
theorem exists_multiset_prod_cons_le_and_prod_not_le [IsDedekindDomain A] (hNF : ¬IsField A) {I M : Ideal A}
    (hI0 : I ≠ ⊥) (hIM : I ≤ M) [hM : M.IsMaximal] :
    ∃ Z : Multiset (PrimeSpectrum A),
      (M ::ₘ Z.map PrimeSpectrum.asIdeal).Prod ≤ I ∧ ¬Multiset.prod (Z.map PrimeSpectrum.asIdeal) ≤ I :=
  by
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := PrimeSpectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    multiset.well_founded_lt.has_min
      (fun Z => (Z.map PrimeSpectrum.asIdeal).Prod ≤ I ∧ (Z.map PrimeSpectrum.asIdeal).Prod ≠ ⊥) ⟨Z₀, hZ₀⟩
  have hZM : Multiset.prod (Z.map PrimeSpectrum.asIdeal) ≤ M := le_transₓ hZI hIM
  have hZ0 : Z ≠ 0 := by
    rintro rfl
    simpa [← hM.ne_top] using hZM
  obtain ⟨_, hPZ', hPM⟩ := (hM.is_prime.multiset_prod_le (mt multiset.map_eq_zero.mp hZ0)).mp hZM
  -- Then in fact there is a `P ∈ Z` with `P ≤ M`.
  obtain ⟨P, hPZ, rfl⟩ := multiset.mem_map.mp hPZ'
  let this := Classical.decEq (Ideal A)
  have := Multiset.map_erase PrimeSpectrum.asIdeal Subtype.coe_injective P Z
  obtain ⟨hP0, hZP0⟩ : P.as_ideal ≠ ⊥ ∧ ((Z.erase P).map PrimeSpectrum.asIdeal).Prod ≠ ⊥ := by
    rwa [Ne.def, ← Multiset.cons_erase hPZ', Multiset.prod_cons, Ideal.mul_eq_bot, not_or_distrib, ← this] at hprodZ
  -- By maximality of `P` and `M`, we have that `P ≤ M` implies `P = M`.
  have hPM' := (IsDedekindDomain.dimension_le_one _ hP0 P.is_prime).eq_of_le hM.ne_top hPM
  subst hPM'
  -- By minimality of `Z`, erasing `P` from `Z` is exactly what we need.
  refine' ⟨Z.erase P, _, _⟩
  · convert hZI
    rw [this, Multiset.cons_erase hPZ']
    
  · refine' fun h => h_eraseZ (Z.erase P) ⟨h, _⟩ (multiset.erase_lt.mpr hPZ)
    exact hZP0
    

namespace FractionalIdeal

open Ideal

theorem exists_not_mem_one_of_ne_bot [IsDedekindDomain A] (hNF : ¬IsField A) {I : Ideal A} (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    ∃ x : K, x ∈ (I⁻¹ : FractionalIdeal A⁰ K) ∧ x ∉ (1 : FractionalIdeal A⁰ K) := by
  -- WLOG, let `I` be maximal.
  suffices
    ∀ {M : Ideal A} (hM : M.IsMaximal), ∃ x : K, x ∈ (M⁻¹ : FractionalIdeal A⁰ K) ∧ x ∉ (1 : FractionalIdeal A⁰ K) by
    obtain ⟨M, hM, hIM⟩ : ∃ M : Ideal A, is_maximal M ∧ I ≤ M := Ideal.exists_le_maximal I hI1
    skip
    have hM0 := (M.bot_lt_of_maximal hNF).ne'
    obtain ⟨x, hxM, hx1⟩ := this hM
    refine' ⟨x, inv_anti_mono _ _ ((coe_ideal_le_coe_ideal _).mpr hIM) hxM, hx1⟩ <;>
      apply FractionalIdeal.coe_ideal_ne_zero <;> assumption
  -- Let `a` be a nonzero element of `M` and `J` the ideal generated by `a`.
  intro M hM
  skip
  obtain ⟨⟨a, haM⟩, ha0⟩ := Submodule.nonzero_mem_of_bot_lt (M.bot_lt_of_maximal hNF)
  replace ha0 : a ≠ 0 := subtype.coe_injective.ne ha0
  let J : Ideal A := Ideal.span {a}
  have hJ0 : J ≠ ⊥ := mt ideal.span_singleton_eq_bot.mp ha0
  have hJM : J ≤ M := ideal.span_le.mpr (set.singleton_subset_iff.mpr haM)
  have hM0 : ⊥ < M := M.bot_lt_of_maximal hNF
  -- Then we can find a product of prime (hence maximal) ideals contained in `J`,
  -- such that removing element `M` from the product is not contained in `J`.
  obtain ⟨Z, hle, hnle⟩ := exists_multiset_prod_cons_le_and_prod_not_le hNF hJ0 hJM
  -- Choose an element `b` of the product that is not in `J`.
  obtain ⟨b, hbZ, hbJ⟩ := set_like.not_le_iff_exists.mp hnle
  have hnz_fa : algebraMap A K a ≠ 0 := mt ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective A K) a) ha0
  have hb0 : algebraMap A K b ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective A K) b) fun h => hbJ <| h.symm ▸ J.zero_mem
  -- Then `b a⁻¹ : K` is in `M⁻¹` but not in `1`.
  refine' ⟨algebraMap A K b * (algebraMap A K a)⁻¹, (mem_inv_iff _).mpr _, _⟩
  · exact (FractionalIdeal.coe_to_fractional_ideal_ne_zero le_rfl).mpr hM0.ne'
    
  · rintro y₀ hy₀
    obtain ⟨y, h_Iy, rfl⟩ := (FractionalIdeal.mem_coe_ideal _).mp hy₀
    rw [mul_comm, ← mul_assoc, ← RingHom.map_mul]
    have h_yb : y * b ∈ J := by
      apply hle
      rw [Multiset.prod_cons]
      exact Submodule.smul_mem_smul h_Iy hbZ
    rw [Ideal.mem_span_singleton'] at h_yb
    rcases h_yb with ⟨c, hc⟩
    rw [← hc, RingHom.map_mul, mul_assoc, mul_inv_cancel hnz_fa, mul_oneₓ]
    apply FractionalIdeal.coe_mem_one
    
  · refine' mt (FractionalIdeal.mem_one_iff _).mp _
    rintro ⟨x', h₂_abs⟩
    rw [← div_eq_mul_inv, eq_div_iff_mul_eq hnz_fa, ← RingHom.map_mul] at h₂_abs
    have := ideal.mem_span_singleton'.mpr ⟨x', IsFractionRing.injective A K h₂_abs⟩
    contradiction
    

theorem one_mem_inv_coe_ideal {I : Ideal A} (hI : I ≠ ⊥) : (1 : K) ∈ (I : FractionalIdeal A⁰ K)⁻¹ := by
  rw [mem_inv_iff (FractionalIdeal.coe_ideal_ne_zero hI)]
  intro y hy
  rw [one_mulₓ]
  exact coe_ideal_le_one hy
  assumption

theorem mul_inv_cancel_of_le_one [h : IsDedekindDomain A] {I : Ideal A} (hI0 : I ≠ ⊥)
    (hI : ((I * I⁻¹)⁻¹ : FractionalIdeal A⁰ K) ≤ 1) : (I * I⁻¹ : FractionalIdeal A⁰ K) = 1 := by
  -- Handle a few trivial cases.
  by_cases' hI1 : I = ⊤
  · rw [hI1, coe_ideal_top, one_mulₓ, FractionalIdeal.inv_one]
    
  by_cases' hNF : IsField A
  · let this := hNF.to_field
    rcases hI1 (I.eq_bot_or_top.resolve_left hI0) with ⟨⟩
    
  -- We'll show a contradiction with `exists_not_mem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, (J : FractionalIdeal A⁰ K) = I * I⁻¹ :=
    le_one_iff_exists_coe_ideal.mp mul_one_div_le_one
  by_cases' hJ0 : J = ⊥
  · subst hJ0
    refine' absurd _ hI0
    rw [eq_bot_iff, ← coe_ideal_le_coe_ideal K, hJ]
    exact coe_ideal_le_self_mul_inv K I
    infer_instance
    
  by_cases' hJ1 : J = ⊤
  · rw [← hJ, hJ1, coe_ideal_top]
    
  obtain ⟨x, hx, hx1⟩ : ∃ x : K, x ∈ (J : FractionalIdeal A⁰ K)⁻¹ ∧ x ∉ (1 : FractionalIdeal A⁰ K) :=
    exists_not_mem_one_of_ne_bot hNF hJ0 hJ1
  contrapose! hx1 with h_abs
  rw [hJ] at hx
  exact hI hx

/-- Nonzero integral ideals in a Dedekind domain are invertible.

We will use this to show that nonzero fractional ideals are invertible,
and finally conclude that fractional ideals in a Dedekind domain form a group with zero.
-/
theorem coe_ideal_mul_inv [h : IsDedekindDomain A] (I : Ideal A) (hI0 : I ≠ ⊥) : (I * I⁻¹ : FractionalIdeal A⁰ K) = 1 :=
  by
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0
  by_cases' hJ0 : (I * I⁻¹ : FractionalIdeal A⁰ K) = 0
  · rw [hJ0, inv_zero']
    exact FractionalIdeal.zero_le _
    
  intro x hx
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices x ∈ integralClosure A K by
    rwa [IsIntegrallyClosed.integral_closure_eq_bot, Algebra.mem_bot, Set.mem_range, ← FractionalIdeal.mem_one_iff] at
        this <;>
      assumption
  -- For that, we'll find a subalgebra that is f.g. as a module and contains `x`.
  -- `A` is a noetherian ring, so we just need to find a subalgebra between `{x}` and `I⁻¹`.
  rw [mem_integral_closure_iff_mem_fg]
  have x_mul_mem : ∀, ∀ b ∈ (I⁻¹ : FractionalIdeal A⁰ K), ∀, x * b ∈ (I⁻¹ : FractionalIdeal A⁰ K) := by
    intro b hb
    rw [mem_inv_iff] at hx⊢
    swap
    · exact FractionalIdeal.coe_ideal_ne_zero hI0
      
    swap
    · exact hJ0
      
    simp only [← mul_assoc, ← mul_comm b] at hx⊢
    intro y hy
    exact hx _ (FractionalIdeal.mul_mem_mul hy hb)
  -- It turns out the subalgebra consisting of all `p(x)` for `p : polynomial A` works.
  refine'
    ⟨AlgHom.range (Polynomial.aeval x : A[X] →ₐ[A] K),
      is_noetherian_submodule.mp (FractionalIdeal.is_noetherian I⁻¹) _ fun y hy => _,
      ⟨Polynomial.x, Polynomial.aeval_X x⟩⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hy
  rw [Polynomial.aeval_eq_sum_range]
  refine' Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ _
  clear hi
  induction' i with i ih
  · rw [pow_zeroₓ]
    exact one_mem_inv_coe_ideal hI0
    
  · show x ^ i.succ ∈ (I⁻¹ : FractionalIdeal A⁰ K)
    rw [pow_succₓ]
    exact x_mul_mem _ ih
    

/-- Nonzero fractional ideals in a Dedekind domain are units.

This is also available as `_root_.mul_inv_cancel`, using the
`comm_group_with_zero` instance defined below.
-/
protected theorem mul_inv_cancel [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hne : I ≠ 0) : I * I⁻¹ = 1 := by
  obtain ⟨a, J, ha, hJ⟩ : ∃ (a : A)(aI : Ideal A), a ≠ 0 ∧ I = span_singleton A⁰ (algebraMap _ _ a)⁻¹ * aI :=
    exists_eq_span_singleton_mul I
  suffices h₂ : I * (span_singleton A⁰ (algebraMap _ _ a) * J⁻¹) = 1
  · rw [mul_inv_cancel_iff]
    exact ⟨span_singleton A⁰ (algebraMap _ _ a) * J⁻¹, h₂⟩
    
  subst hJ
  rw [mul_assoc, mul_left_commₓ (J : FractionalIdeal A⁰ K), coe_ideal_mul_inv, mul_oneₓ,
    FractionalIdeal.span_singleton_mul_span_singleton, inv_mul_cancel, FractionalIdeal.span_singleton_one]
  · exact mt ((injective_iff_map_eq_zero (algebraMap A K)).mp (IsFractionRing.injective A K) _) ha
    
  · exact fractional_ideal.coe_ideal_ne_zero_iff.mp (right_ne_zero_of_mul hne)
    

theorem mul_right_le_iff [IsDedekindDomain A] {J : FractionalIdeal A⁰ K} (hJ : J ≠ 0) :
    ∀ {I I'}, I * J ≤ I' * J ↔ I ≤ I' := by
  intro I I'
  constructor
  · intro h
    convert mul_right_mono J⁻¹ h <;> rw [mul_assoc, FractionalIdeal.mul_inv_cancel hJ, mul_oneₓ]
    
  · exact fun h => mul_right_mono J h
    

theorem mul_left_le_iff [IsDedekindDomain A] {J : FractionalIdeal A⁰ K} (hJ : J ≠ 0) {I I'} : J * I ≤ J * I' ↔ I ≤ I' :=
  by
  convert FractionalIdeal.mul_right_le_iff hJ using 1 <;> simp only [← mul_comm]

theorem mul_right_strict_mono [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : StrictMono (· * I) :=
  strict_mono_of_le_iff_le fun _ _ => (mul_right_le_iff hI).symm

theorem mul_left_strict_mono [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : StrictMono ((· * ·) I) :=
  strict_mono_of_le_iff_le fun _ _ => (mul_left_le_iff hI).symm

/-- This is also available as `_root_.div_eq_mul_inv`, using the
`comm_group_with_zero` instance defined below.
-/
protected theorem div_eq_mul_inv [IsDedekindDomain A] (I J : FractionalIdeal A⁰ K) : I / J = I * J⁻¹ := by
  by_cases' hJ : J = 0
  · rw [hJ, div_zero, inv_zero', mul_zero]
    
  refine' le_antisymmₓ ((mul_right_le_iff hJ).mp _) ((le_div_iff_mul_le hJ).mpr _)
  · rw [mul_assoc, mul_comm J⁻¹, FractionalIdeal.mul_inv_cancel hJ, mul_oneₓ, mul_le]
    intro x hx y hy
    rw [mem_div_iff_of_nonzero hJ] at hx
    exact hx y hy
    
  rw [mul_assoc, mul_comm J⁻¹, FractionalIdeal.mul_inv_cancel hJ, mul_oneₓ]
  exact le_reflₓ I

end FractionalIdeal

/-- `is_dedekind_domain` and `is_dedekind_domain_inv` are equivalent ways
to express that an integral domain is a Dedekind domain. -/
theorem is_dedekind_domain_iff_is_dedekind_domain_inv : IsDedekindDomain A ↔ IsDedekindDomainInv A :=
  ⟨fun h I hI => FractionalIdeal.mul_inv_cancel hI, fun h => h.IsDedekindDomain⟩

end Inverse

section IsDedekindDomain

variable {R A} [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal

open Ideal

noncomputable instance FractionalIdeal.commGroupWithZero : CommGroupWithZero (FractionalIdeal A⁰ K) :=
  { FractionalIdeal.commSemiring with inv := fun I => I⁻¹, inv_zero := inv_zero' _, div := (· / ·),
    div_eq_mul_inv := FractionalIdeal.div_eq_mul_inv,
    exists_pair_ne :=
      ⟨0, 1,
        (coe_to_fractional_ideal_injective le_rfl).Ne
          (by
            simpa using @zero_ne_one (Ideal A) _ _)⟩,
    mul_inv_cancel := fun I => FractionalIdeal.mul_inv_cancel }

noncomputable instance Ideal.cancelCommMonoidWithZero : CancelCommMonoidWithZero (Ideal A) :=
  Function.Injective.cancelCommMonoidWithZero (coeIdealHom A⁰ (FractionRing A)) coe_ideal_injective (RingHom.map_zero _)
    (RingHom.map_one _) (RingHom.map_mul _) (RingHom.map_pow _)

/-- For ideals in a Dedekind domain, to divide is to contain. -/
theorem Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J ≤ I :=
  ⟨Ideal.le_of_dvd, fun h => by
    by_cases' hI : I = ⊥
    · have hJ : J = ⊥ := by
        rwa [hI, ← eq_bot_iff] at h
      rw [hI, hJ]
      
    have hI' : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 :=
      (FractionalIdeal.coe_to_fractional_ideal_ne_zero (le_reflₓ (nonZeroDivisors A))).mpr hI
    have : (I : FractionalIdeal A⁰ (FractionRing A))⁻¹ * J ≤ 1 :=
      le_transₓ (FractionalIdeal.mul_left_mono (↑I)⁻¹ ((coe_ideal_le_coe_ideal _).mpr h))
        (le_of_eqₓ (inv_mul_cancel hI'))
    obtain ⟨H, hH⟩ := fractional_ideal.le_one_iff_exists_coe_ideal.mp this
    use H
    refine'
      coe_to_fractional_ideal_injective (le_reflₓ (nonZeroDivisors A))
        (show (J : FractionalIdeal A⁰ (FractionRing A)) = _ from _)
    rw [FractionalIdeal.coe_ideal_mul, hH, ← mul_assoc, mul_inv_cancel hI', one_mulₓ]⟩

theorem Ideal.dvd_not_unit_iff_lt {I J : Ideal A} : DvdNotUnit I J ↔ J < I :=
  ⟨fun ⟨hI, H, hunit, hmul⟩ =>
    lt_of_le_of_neₓ (Ideal.dvd_iff_le.mp ⟨H, hmul⟩)
      (mt
        (fun h =>
          have : H = 1 :=
            mul_left_cancel₀ hI
              (by
                rw [← hmul, h, mul_oneₓ])
          show IsUnit H from this.symm ▸ is_unit_one)
        hunit),
    fun h =>
    dvd_not_unit_of_dvd_of_not_dvd (Ideal.dvd_iff_le.mpr (le_of_ltₓ h)) (mt Ideal.dvd_iff_le.mp (not_le_of_lt h))⟩

instance :
    WfDvdMonoid (Ideal A) where well_founded_dvd_not_unit := by
    have : WellFounded ((· > ·) : Ideal A → Ideal A → Prop) :=
      is_noetherian_iff_well_founded.mp (is_noetherian_ring_iff.mp IsDedekindDomain.is_noetherian_ring)
    convert this
    ext
    rw [Ideal.dvd_not_unit_iff_lt]

instance Ideal.unique_factorization_monoid : UniqueFactorizationMonoid (Ideal A) :=
  { Ideal.wf_dvd_monoid with
    irreducible_iff_prime := fun P =>
      ⟨fun hirr =>
        ⟨hirr.ne_zero, hirr.not_unit, fun I J => by
          have : P.is_maximal := by
            refine' ⟨⟨mt ideal.is_unit_iff.mpr hirr.not_unit, _⟩⟩
            intro J hJ
            obtain ⟨J_ne, H, hunit, P_eq⟩ := ideal.dvd_not_unit_iff_lt.mpr hJ
            exact ideal.is_unit_iff.mp ((hirr.is_unit_or_is_unit P_eq).resolve_right hunit)
          rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.dvd_iff_le, SetLike.le_def, SetLike.le_def, SetLike.le_def]
          contrapose!
          rintro ⟨⟨x, x_mem, x_not_mem⟩, ⟨y, y_mem, y_not_mem⟩⟩
          exact ⟨x * y, Ideal.mul_mem_mul x_mem y_mem, mt this.is_prime.mem_or_mem (not_orₓ x_not_mem y_not_mem)⟩⟩,
        Prime.irreducible⟩ }

noncomputable instance Ideal.normalizationMonoid : NormalizationMonoid (Ideal A) :=
  normalizationMonoidOfUniqueUnits

@[simp]
theorem Ideal.dvd_span_singleton {I : Ideal A} {x : A} : I ∣ Ideal.span {x} ↔ x ∈ I :=
  Ideal.dvd_iff_le.trans (Ideal.span_le.trans Set.singleton_subset_iff)

theorem Ideal.is_prime_of_prime {P : Ideal A} (h : Prime P) : IsPrime P := by
  refine' ⟨_, fun x y hxy => _⟩
  · rintro rfl
    rw [← Ideal.one_eq_top] at h
    exact h.not_unit is_unit_one
    
  · simp only [Ideal.dvd_span_singleton, Ideal.span_singleton_mul_span_singleton] at hxy⊢
    exact h.dvd_or_dvd hxy
    

theorem Ideal.prime_of_is_prime {P : Ideal A} (hP : P ≠ ⊥) (h : IsPrime P) : Prime P := by
  refine' ⟨hP, mt ideal.is_unit_iff.mp h.ne_top, fun I J hIJ => _⟩
  simpa only [← Ideal.dvd_iff_le] using h.mul_le.mp (Ideal.le_of_dvd hIJ)

/-- In a Dedekind domain, the (nonzero) prime elements of the monoid with zero `ideal A`
are exactly the prime ideals. -/
theorem Ideal.prime_iff_is_prime {P : Ideal A} (hP : P ≠ ⊥) : Prime P ↔ IsPrime P :=
  ⟨Ideal.is_prime_of_prime, Ideal.prime_of_is_prime hP⟩

/-- In a Dedekind domain, the the prime ideals are the zero ideal together with the prime elements
of the monoid with zero `ideal A`. -/
theorem Ideal.is_prime_iff_bot_or_prime {P : Ideal A} : IsPrime P ↔ P = ⊥ ∨ Prime P :=
  ⟨fun hp => (eq_or_ne P ⊥).imp_right fun hp0 => Ideal.prime_of_is_prime hp0 hp, fun hp =>
    hp.elim (fun h => h.symm ▸ Ideal.bot_prime) Ideal.is_prime_of_prime⟩

theorem Ideal.strict_anti_pow (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) : StrictAnti ((· ^ ·) I : ℕ → Ideal A) :=
  strict_anti_nat_of_succ_lt fun e =>
    Ideal.dvd_not_unit_iff_lt.mp ⟨pow_ne_zero _ hI0, I, mt is_unit_iff.mp hI1, pow_succ'ₓ I e⟩

theorem Ideal.pow_lt_self (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) (he : 2 ≤ e) : I ^ e < I := by
  convert I.strict_anti_pow hI0 hI1 he <;> rw [pow_oneₓ]

theorem Ideal.exists_mem_pow_not_mem_pow_succ (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) :
    ∃ x ∈ I ^ e, x ∉ I ^ (e + 1) :=
  SetLike.exists_of_lt (I.strict_anti_pow hI0 hI1 e.lt_succ_self)

theorem Associates.le_singleton_iff (x : A) (n : ℕ) (I : Ideal A) :
    Associates.mk I ^ n ≤ Associates.mk (Ideal.span {x}) ↔ x ∈ I ^ n := by
  rw [← Associates.dvd_eq_le, ← Associates.mk_pow, Associates.mk_dvd_mk, Ideal.dvd_span_singleton]

open FractionalIdeal

variable {A K}

/-- Strengthening of `is_localization.exist_integer_multiples`:
Let `J ≠ ⊤` be an ideal in a Dedekind domain `A`, and `f ≠ 0` a finite collection
of elements of `K = Frac(A)`, then we can multiply the elements of `f` by some `a : K`
to find a collection of elements of `A` that is not completely contained in `J`. -/
theorem Ideal.exist_integer_multiples_not_mem {J : Ideal A} (hJ : J ≠ ⊤) {ι : Type _} (s : Finset ι) (f : ι → K) {j}
    (hjs : j ∈ s) (hjf : f j ≠ 0) :
    ∃ a : K, (∀, ∀ i ∈ s, ∀, IsLocalization.IsInteger A (a * f i)) ∧ ∃ i ∈ s, a * f i ∉ (J : FractionalIdeal A⁰ K) := by
  -- Consider the fractional ideal `I` spanned by the `f`s.
  let I : FractionalIdeal A⁰ K := FractionalIdeal.spanFinset A s f
  have hI0 : I ≠ 0 := fractional_ideal.span_finset_ne_zero.mpr ⟨j, hjs, hjf⟩
  -- We claim the multiplier `a` we're looking for is in `I⁻¹ \ (J / I)`.
  suffices ↑J / I < I⁻¹ by
    obtain ⟨_, a, hI, hpI⟩ := set_like.lt_iff_le_and_exists.mp this
    rw [mem_inv_iff hI0] at hI
    refine' ⟨a, fun i hi => _, _⟩
    -- By definition, `a ∈ I⁻¹` multiplies elements of `I` into elements of `1`,
    -- in other words, `a * f i` is an integer.
    · exact (mem_one_iff _).mp (hI (f i) (Submodule.subset_span (Set.mem_image_of_mem f hi)))
      
    · contrapose! hpI
      -- And if all `a`-multiples of `I` are an element of `J`,
      -- then `a` is actually an element of `J / I`, contradiction.
      refine' (mem_div_iff_of_nonzero hI0).mpr fun y hy => Submodule.span_induction hy _ _ _ _
      · rintro _ ⟨i, hi, rfl⟩
        exact hpI i hi
        
      · rw [mul_zero]
        exact Submodule.zero_mem _
        
      · intro x y hx hy
        rw [mul_addₓ]
        exact Submodule.add_mem _ hx hy
        
      · intro b x hx
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ b hx
        
      
  -- To show the inclusion of `J / I` into `I⁻¹ = 1 / I`, note that `J < I`.
  calc ↑J / I = ↑J * I⁻¹ := div_eq_mul_inv (↑J) I _ < 1 * I⁻¹ := mul_right_strict_mono (inv_ne_zero hI0) _ _ = I⁻¹ :=
      one_mulₓ _
  · rw [← coe_ideal_top]
    -- And multiplying by `I⁻¹` is indeed strictly monotone.
    exact strict_mono_of_le_iff_le (fun _ _ => (coe_ideal_le_coe_ideal K).symm) (lt_top_iff_ne_top.mpr hJ)
    

end IsDedekindDomain

section IsDedekindDomain

variable {T : Type _} [CommRingₓ T] [IsDomain T] [IsDedekindDomain T] {I J : Ideal T}

open Classical

open Multiset UniqueFactorizationMonoid Ideal

theorem prod_normalized_factors_eq_self (hI : I ≠ ⊥) : (normalizedFactors I).Prod = I :=
  associated_iff_eq.1 (normalized_factors_prod hI)

theorem normalized_factors_prod {α : Multiset (Ideal T)} (h : ∀, ∀ p ∈ α, ∀, Prime p) : normalizedFactors α.Prod = α :=
  by
  simp_rw [← Multiset.rel_eq, ← associated_eq_eq]
  exact prime_factors_unique prime_of_normalized_factor h (normalized_factors_prod (α.prod_ne_zero_of_prime h))

theorem count_le_of_ideal_ge {I J : Ideal T} (h : I ≤ J) (hI : I ≠ ⊥) (K : Ideal T) :
    count K (normalizedFactors J) ≤ count K (normalizedFactors I) :=
  le_iff_count.1 ((dvd_iff_normalized_factors_le_normalized_factors (ne_bot_of_le_ne_bot hI h) hI).1 (dvd_iff_le.2 h)) _

theorem sup_eq_prod_inf_factors (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : I⊔J = (normalizedFactors I ∩ normalizedFactors J).Prod := by
  have H :
    normalized_factors (normalized_factors I ∩ normalized_factors J).Prod =
      normalized_factors I ∩ normalized_factors J :=
    by
    apply _root_.normalized_factors_prod
    intro p hp
    rw [mem_inter] at hp
    exact prime_of_normalized_factor p hp.left
  have :=
    Multiset.prod_ne_zero_of_prime (normalized_factors I ∩ normalized_factors J) fun _ h =>
      prime_of_normalized_factor _ (Multiset.mem_inter.1 h).1
  apply le_antisymmₓ
  · rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
    constructor
    · rw [dvd_iff_normalized_factors_le_normalized_factors this hI, H]
      exact inf_le_left
      
    · rw [dvd_iff_normalized_factors_le_normalized_factors this hJ, H]
      exact inf_le_right
      
    
  · rw [← dvd_iff_le, dvd_iff_normalized_factors_le_normalized_factors, _root_.normalized_factors_prod, le_iff_count]
    · intro a
      rw [Multiset.count_inter]
      exact le_minₓ (count_le_of_ideal_ge le_sup_left hI a) (count_le_of_ideal_ge le_sup_right hJ a)
      
    · intro p hp
      rw [mem_inter] at hp
      exact prime_of_normalized_factor p hp.left
      
    · exact ne_bot_of_le_ne_bot hI le_sup_left
      
    · exact this
      
    

theorem irreducible_pow_sup (hI : I ≠ ⊥) (hJ : Irreducible J) (n : ℕ) :
    J ^ n⊔I = J ^ min ((normalizedFactors I).count J) n := by
  rw [sup_eq_prod_inf_factors (pow_ne_zero n hJ.ne_zero) hI, ← inf_eq_inter, normalized_factors_of_irreducible_pow hJ,
    normalize_eq J, repeat_inf, prod_repeat]

theorem irreducible_pow_sup_of_le (hJ : Irreducible J) (n : ℕ) (hn : ↑n ≤ multiplicity J I) : J ^ n⊔I = J ^ n := by
  by_cases' hI : I = ⊥
  · simp_all
    
  rw [irreducible_pow_sup hI hJ, min_eq_rightₓ]
  rwa [multiplicity_eq_count_normalized_factors hJ hI, PartEnat.coe_le_coe, normalize_eq J] at hn

theorem irreducible_pow_sup_of_ge (hI : I ≠ ⊥) (hJ : Irreducible J) (n : ℕ) (hn : multiplicity J I ≤ n) :
    J ^ n⊔I = J ^ (multiplicity J I).get (PartEnat.dom_of_le_coe hn) := by
  rw [irreducible_pow_sup hI hJ, min_eq_leftₓ]
  congr
  · rw [← PartEnat.coe_inj, PartEnat.coe_get, multiplicity_eq_count_normalized_factors hJ hI, normalize_eq J]
    
  · rwa [multiplicity_eq_count_normalized_factors hJ hI, PartEnat.coe_le_coe, normalize_eq J] at hn
    

end IsDedekindDomain

section HeightOneSpectrum

/-!
### Height one spectrum of a Dedekind domain
If `R` is a Dedekind domain of Krull dimension 1, the maximal ideals of `R` are exactly its nonzero
prime ideals.
We define `height_one_spectrum` and provide lemmas to recover the facts that prime ideals of height
one are prime and irreducible. -/


namespace IsDedekindDomain

variable [IsDomain R] [IsDedekindDomain R]

/-- The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of
`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1. -/
@[ext, nolint has_inhabited_instance unused_arguments]
structure HeightOneSpectrum where
  asIdeal : Ideal R
  IsPrime : as_ideal.IsPrime
  ne_bot : as_ideal ≠ ⊥

variable (v : HeightOneSpectrum R) {R}

theorem HeightOneSpectrum.prime (v : HeightOneSpectrum R) : Prime v.asIdeal :=
  Ideal.prime_of_is_prime v.ne_bot v.IsPrime

theorem HeightOneSpectrum.irreducible (v : HeightOneSpectrum R) : Irreducible v.asIdeal := by
  rw [UniqueFactorizationMonoid.irreducible_iff_prime]
  apply v.prime

theorem HeightOneSpectrum.associates_irreducible (v : HeightOneSpectrum R) : Irreducible (Associates.mk v.asIdeal) := by
  rw [Associates.irreducible_mk _]
  apply v.irreducible

end IsDedekindDomain

end HeightOneSpectrum

section

open Ideal

variable {R} {A} [IsDedekindDomain A] {I : Ideal R} {J : Ideal A}

/-- The map from ideals of `R` dividing `I` to the ideals of `A` dividing `J` induced by
  a homomorphism `f : R/I →+* A/J` -/
@[simps]
def idealFactorsFunOfQuotHom {f : R ⧸ I →+* A ⧸ J} (hf : Function.Surjective f) :
    { p : Ideal R | p ∣ I } →o { p : Ideal A | p ∣ J } where
  toFun := fun X =>
    ⟨comap J (map f (map I X)), by
      have : J.ker ≤ comap J (map f (map I X)) := ker_le_comap J
      rw [mk_ker] at this
      exact dvd_iff_le.mpr this⟩
  monotone' := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ h
    rw [← Subtype.coe_le_coe, Subtype.coe_mk, Subtype.coe_mk] at h⊢
    rw [Subtype.coe_mk, comap_le_comap_iff_of_surjective J quotient.mk_surjective, map_le_iff_le_comap, Subtype.coe_mk,
      comap_map_of_surjective _ hf (map I Y)]
    suffices map I X ≤ map I Y by
      exact le_sup_of_le_left this
    rwa [map_le_iff_le_comap, comap_map_of_surjective I quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, mk_ker,
      sup_eq_left.mpr <| le_of_dvd hY]

@[simp]
theorem ideal_factors_fun_of_quot_hom_id : idealFactorsFunOfQuotHom (RingHom.id (A ⧸ J)).is_surjective = OrderHom.id :=
  OrderHom.ext _ _
    (funext fun X => by
      simp only [← idealFactorsFunOfQuotHom, ← map_id, ← OrderHom.coe_fun_mk, ← OrderHom.id_coe, ← id.def, ←
        comap_map_of_surjective J quotient.mk_surjective, RingHom.ker_eq_comap_bot J, ← mk_ker, ←
        sup_eq_left.mpr (dvd_iff_le.mp X.prop), ← Subtype.coe_eta])

variable {B : Type _} [CommRingₓ B] [IsDomain B] [IsDedekindDomain B] {L : Ideal B}

theorem ideal_factors_fun_of_quot_hom_comp {f : R ⧸ I →+* A ⧸ J} {g : A ⧸ J →+* B ⧸ L} (hf : Function.Surjective f)
    (hg : Function.Surjective g) :
    (idealFactorsFunOfQuotHom hg).comp (idealFactorsFunOfQuotHom hf) =
      idealFactorsFunOfQuotHom (show Function.Surjective (g.comp f) from hg.comp hf) :=
  by
  refine' OrderHom.ext _ _ (funext fun x => _)
  rw [idealFactorsFunOfQuotHom, idealFactorsFunOfQuotHom, OrderHom.comp_coe, OrderHom.coe_fun_mk, OrderHom.coe_fun_mk,
    Function.comp_app, idealFactorsFunOfQuotHom, OrderHom.coe_fun_mk, Subtype.mk_eq_mk, Subtype.coe_mk,
    map_comap_of_surjective J quotient.mk_surjective, map_map]

variable [IsDomain R] [IsDedekindDomain R]

/-- The bijection between ideals of `R` dividing `I` and the ideals of `A` dividing `J` induced by
  an isomorphism `f : R/I ≅ A/J`. -/
@[simps]
def idealFactorsEquivOfQuotEquiv (f : R ⧸ I ≃+* A ⧸ J) : { p : Ideal R | p ∣ I } ≃o { p : Ideal A | p ∣ J } :=
  OrderIso.ofHomInv (idealFactorsFunOfQuotHom (show Function.Surjective (f : R ⧸ I →+* A ⧸ J) from f.Surjective))
    (idealFactorsFunOfQuotHom (show Function.Surjective (f.symm : A ⧸ J →+* R ⧸ I) from f.symm.Surjective))
    (by
      simp only [ideal_factors_fun_of_quot_hom_id, ← OrderHom.coe_eq, ← OrderHom.coe_eq, ←
        ideal_factors_fun_of_quot_hom_comp, RingEquiv.to_ring_hom_eq_coe, RingEquiv.to_ring_hom_eq_coe,
        RingEquiv.to_ring_hom_trans, ← RingEquiv.symm_trans_self, ← RingEquiv.to_ring_hom_refl])
    (by
      simp only [ideal_factors_fun_of_quot_hom_id, ← OrderHom.coe_eq, ← OrderHom.coe_eq, ←
        ideal_factors_fun_of_quot_hom_comp, RingEquiv.to_ring_hom_eq_coe, RingEquiv.to_ring_hom_eq_coe,
        RingEquiv.to_ring_hom_trans, ← RingEquiv.self_trans_symm, ← RingEquiv.to_ring_hom_refl])

end

section ChineseRemainder

open Ideal UniqueFactorizationMonoid

open BigOperators

variable {R}

theorem Ringₓ.DimensionLeOne.prime_le_prime_iff_eq (h : Ringₓ.DimensionLeOne R) {P Q : Ideal R} [hP : P.IsPrime]
    [hQ : Q.IsPrime] (hP0 : P ≠ ⊥) : P ≤ Q ↔ P = Q :=
  ⟨(h P hP0 hP).eq_of_le hQ.ne_top, Eq.le⟩

theorem Ideal.coprime_of_no_prime_ge {I J : Ideal R} (h : ∀ P, I ≤ P → J ≤ P → ¬IsPrime P) : I⊔J = ⊤ := by
  by_contra hIJ
  obtain ⟨P, hP, hIJ⟩ := Ideal.exists_le_maximal _ hIJ
  exact h P (le_transₓ le_sup_left hIJ) (le_transₓ le_sup_right hIJ) hP.is_prime

section DedekindDomain

variable {R} [IsDomain R] [IsDedekindDomain R]

theorem Ideal.IsPrime.mul_mem_pow (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ} (h : a * b ∈ I ^ n) :
    a ∈ I ∨ b ∈ I ^ n := by
  cases n
  · simp
    
  by_cases' hI0 : I = ⊥
  · simpa [← pow_succₓ, ← hI0] using h
    
  simp only [Submodule.span_singleton_le_iff_mem, ← Ideal.submodule_span_eq, Ideal.dvd_iff_le,
    Ideal.span_singleton_mul_span_singleton] at h⊢
  by_cases' ha : I ∣ span {a}
  · exact Or.inl ha
    
  rw [mul_comm] at h
  exact Or.inr (Prime.pow_dvd_of_dvd_mul_right ((Ideal.prime_iff_is_prime hI0).mpr hI) _ ha h)

section

open Classical

theorem Ideal.count_normalized_factors_eq {p x : Ideal R} [hp : p.IsPrime] {n : ℕ} (hle : x ≤ p ^ n)
    (hlt : ¬x ≤ p ^ (n + 1)) : (normalizedFactors x).count p = n :=
  count_normalized_factors_eq' ((Ideal.is_prime_iff_bot_or_prime.mp hp).imp_right Prime.irreducible)
    (by
      have : Unique (Ideal R)ˣ := Ideal.uniqueUnits
      apply normalize_eq)
    (by
      convert ideal.dvd_iff_le.mpr hle)
    (by
      convert mt Ideal.le_of_dvd hlt)

/- Warning: even though a pure term-mode proof typechecks (the `by convert` can simply be
  removed), it's slower to the point of a possible timeout. -/
end

theorem Ideal.le_mul_of_no_prime_factors {I J K : Ideal R} (coprime : ∀ P, J ≤ P → K ≤ P → ¬IsPrime P) (hJ : I ≤ J)
    (hK : I ≤ K) : I ≤ J * K := by
  simp only [Ideal.dvd_iff_le] at coprime hJ hK⊢
  by_cases' hJ0 : J = 0
  · simpa only [← hJ0, ← zero_mul] using hJ
    
  obtain ⟨I', rfl⟩ := hK
  rw [mul_comm]
  exact
    mul_dvd_mul_left K
      (UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors hJ0
        (fun P hPJ hPK => mt Ideal.is_prime_of_prime (coprime P hPJ hPK)) hJ)

theorem Ideal.le_of_pow_le_prime {I P : Ideal R} [hP : P.IsPrime] {n : ℕ} (h : I ^ n ≤ P) : I ≤ P := by
  by_cases' hP0 : P = ⊥
  · simp only [← hP0, ← le_bot_iff] at h⊢
    exact pow_eq_zero h
    
  rw [← Ideal.dvd_iff_le] at h⊢
  exact ((Ideal.prime_iff_is_prime hP0).mpr hP).dvd_of_dvd_pow h

theorem Ideal.pow_le_prime_iff {I P : Ideal R} [hP : P.IsPrime] {n : ℕ} (hn : n ≠ 0) : I ^ n ≤ P ↔ I ≤ P :=
  ⟨Ideal.le_of_pow_le_prime, fun h => trans (Ideal.pow_le_self hn) h⟩

theorem Ideal.prod_le_prime {ι : Type _} {s : Finset ι} {f : ι → Ideal R} {P : Ideal R} [hP : P.IsPrime] :
    (∏ i in s, f i) ≤ P ↔ ∃ i ∈ s, f i ≤ P := by
  by_cases' hP0 : P = ⊥
  · simp only [← hP0, ← le_bot_iff]
    rw [← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
    
  simp only [Ideal.dvd_iff_le]
  exact ((Ideal.prime_iff_is_prime hP0).mpr hP).dvd_finset_prod_iff _

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i j «expr ∈ » s)
/-- The intersection of distinct prime powers in a Dedekind domain is the product of these
prime powers. -/
theorem IsDedekindDomain.inf_prime_pow_eq_prod {ι : Type _} (s : Finset ι) (f : ι → Ideal R) (e : ι → ℕ)
    (prime : ∀, ∀ i ∈ s, ∀, Prime (f i)) (coprime : ∀ (i j) (_ : i ∈ s) (_ : j ∈ s), i ≠ j → f i ≠ f j) :
    (s.inf fun i => f i ^ e i) = ∏ i in s, f i ^ e i := by
  let this := Classical.decEq ι
  revert prime coprime
  refine' s.induction _ _
  · simp
    
  intro a s ha ih prime coprime
  specialize
    ih (fun i hi => Prime i (Finset.mem_insert_of_mem hi)) fun i hi j hj =>
      coprime i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
  rw [Finset.inf_insert, Finset.prod_insert ha, ih]
  refine' le_antisymmₓ (Ideal.le_mul_of_no_prime_factors _ inf_le_left inf_le_right) Ideal.mul_le_inf
  intro P hPa hPs hPp
  have := hPp
  obtain ⟨b, hb, hPb⟩ := ideal.prod_le_prime.mp hPs
  have := Ideal.is_prime_of_prime (Prime a (Finset.mem_insert_self a s))
  have := Ideal.is_prime_of_prime (Prime b (Finset.mem_insert_of_mem hb))
  refine'
    coprime a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb) _
      (((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq _).mp (Ideal.le_of_pow_le_prime hPa)).trans
        ((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq _).mp (Ideal.le_of_pow_le_prime hPb)).symm)
  · rintro rfl
    contradiction
    
  · exact (Prime a (Finset.mem_insert_self a s)).ne_zero
    
  · exact (Prime b (Finset.mem_insert_of_mem hb)).ne_zero
    

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i, P i ^ e i`, then `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def IsDedekindDomain.quotientEquivPiOfProdEq {ι : Type _} [Fintype ι] (I : Ideal R) (P : ι → Ideal R)
    (e : ι → ℕ) (prime : ∀ i, Prime (P i)) (coprime : ∀ i j, i ≠ j → P i ≠ P j) (prod_eq : (∏ i, P i ^ e i) = I) :
    R ⧸ I ≃+* ∀ i, R ⧸ P i ^ e i :=
  (Ideal.quotEquivOfEq
        (by
          simp only [prod_eq, ← Finset.inf_eq_infi, ← Finset.mem_univ, ← cinfi_pos,
            IsDedekindDomain.inf_prime_pow_eq_prod _ _ _ (fun i _ => Prime i) fun i _ j _ => coprime i j])).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun i j hij =>
      Ideal.coprime_of_no_prime_ge
        (by
          intro P hPi hPj hPp
          have := hPp
          have := Ideal.is_prime_of_prime (Prime i)
          have := Ideal.is_prime_of_prime (Prime j)
          exact
            coprime i j hij
              (((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq (Prime i).ne_zero).mp
                    (Ideal.le_of_pow_le_prime hPi)).trans
                ((is_dedekind_domain.dimension_le_one.prime_le_prime_iff_eq (Prime j).ne_zero).mp
                    (Ideal.le_of_pow_le_prime hPj)).symm))

open Classical

/-- **Chinese remainder theorem** for a Dedekind domain: `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`,
where `P i` ranges over the prime factors of `I` and `e i` over the multiplicities. -/
noncomputable def IsDedekindDomain.quotientEquivPiFactors {I : Ideal R} (hI : I ≠ ⊥) :
    R ⧸ I ≃+* ∀ P : (factors I).toFinset, R ⧸ (P : Ideal R) ^ (factors I).count P :=
  IsDedekindDomain.quotientEquivPiOfProdEq _ _ _
    (fun P : (factors I).toFinset => prime_of_factor _ (Multiset.mem_to_finset.mp P.Prop))
    (fun i j hij => Subtype.coe_injective.Ne hij)
    (calc
      (∏ P : (factors I).toFinset, (P : Ideal R) ^ (factors I).count (P : Ideal R)) =
          ∏ P in (factors I).toFinset, P ^ (factors I).count P :=
        (factors I).toFinset.prod_coe_sort fun P => P ^ (factors I).count P
      _ = ((factors I).map fun P => P).Prod := (Finset.prod_multiset_map_count (factors I) id).symm
      _ = (factors I).Prod := by
        rw [Multiset.map_id']
      _ = I := (@associated_iff_eq (Ideal R) _ Ideal.uniqueUnits _ _).mp (factors_prod hI)
      )

@[simp]
theorem IsDedekindDomain.quotient_equiv_pi_factors_mk {I : Ideal R} (hI : I ≠ ⊥) (x : R) :
    IsDedekindDomain.quotientEquivPiFactors hI (Ideal.Quotient.mk I x) = fun P => Ideal.Quotient.mk _ x :=
  rfl

end DedekindDomain

end ChineseRemainder

