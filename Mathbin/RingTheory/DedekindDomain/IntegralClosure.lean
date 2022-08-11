/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathbin.RingTheory.DedekindDomain.Basic
import Mathbin.RingTheory.Trace

/-!
# Integral closure of Dedekind domains

This file shows the integral closure of a Dedekind domain (in particular, the ring of integers
of a number field) is a Dedekind domain.

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

section IsIntegralClosure

/-! ### `is_integral_closure` section

We show that an integral closure of a Dedekind domain in a finite separable
field extension is again a Dedekind domain. This implies the ring of integers
of a number field is a Dedekind domain. -/


open Algebra

open BigOperators

variable {A K} [Algebra A K] [IsFractionRing A K]

variable {L : Type _} [Field L] (C : Type _) [CommRingₓ C]

variable [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L]

variable [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]

theorem IsIntegralClosure.range_le_span_dual_basis [IsSeparable K L] {ι : Type _} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    ((Algebra.linearMap C L).restrictScalars A).range ≤
      Submodule.span A (Set.Range <| (traceForm K L).dualBasis (trace_form_nondegenerate K L) b) :=
  by
  let db := (trace_form K L).dualBasis (trace_form_nondegenerate K L) b
  rintro _ ⟨x, rfl⟩
  simp only [← LinearMap.coe_restrict_scalars_eq_coe, ← Algebra.linear_map_apply]
  have hx : IsIntegral A (algebraMap C L x) := (IsIntegralClosure.is_integral A L x).algebraMap
  suffices ∃ c : ι → A, algebraMap C L x = ∑ i, c i • db i by
    obtain ⟨c, x_eq⟩ := this
    rw [x_eq]
    refine' Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span _)
    rw [Set.mem_range]
    exact ⟨i, rfl⟩
  suffices ∃ c : ι → K, (∀ i, IsIntegral A (c i)) ∧ algebraMap C L x = ∑ i, c i • db i by
    obtain ⟨c, hc, hx⟩ := this
    have hc' : ∀ i, IsLocalization.IsInteger A (c i) := fun i => is_integrally_closed.is_integral_iff.mp (hc i)
    use fun i => Classical.some (hc' i)
    refine' hx.trans (Finset.sum_congr rfl fun i _ => _)
    conv_lhs => rw [← Classical.some_spec (hc' i)]
    rw [← IsScalarTower.algebra_map_smul K (Classical.some (hc' i)) (db i)]
  refine' ⟨fun i => db.repr (algebraMap C L x) i, fun i => _, (db.sum_repr _).symm⟩
  rw [BilinForm.dual_basis_repr_apply]
  exact is_integral_trace (is_integral_mul hx (hb_int i))

theorem integral_closure_le_span_dual_basis [IsSeparable K L] {ι : Type _} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
    (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    (integralClosure A L).toSubmodule ≤
      Submodule.span A (Set.Range <| (traceForm K L).dualBasis (trace_form_nondegenerate K L) b) :=
  by
  refine' le_transₓ _ (IsIntegralClosure.range_le_span_dual_basis (integralClosure A L) b hb_int)
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

variable (A) (K)

include K

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (y «expr ≠ » (0 : A))
/-- Send a set of `x`'es in a finite extension `L` of the fraction field of `R`
to `(y : R) • x ∈ integral_closure R L`. -/
theorem exists_integral_multiples (s : Finset L) : ∃ (y : _)(_ : y ≠ (0 : A)), ∀, ∀ x ∈ s, ∀, IsIntegral A (y • x) := by
  have := Classical.decEq L
  refine' s.induction _ _
  · use 1, one_ne_zero
    rintro x ⟨⟩
    
  · rintro x s hx ⟨y, hy, hs⟩
    obtain ⟨x', y', hy', hx'⟩ :=
      exists_integral_multiple ((IsFractionRing.is_algebraic_iff A K L).mpr (is_algebraic_of_finite _ _ x))
        ((injective_iff_map_eq_zero (algebraMap A L)).mp _)
    refine' ⟨y * y', mul_ne_zero hy hy', fun x'' hx'' => _⟩
    rcases finset.mem_insert.mp hx'' with (rfl | hx'')
    · rw [mul_smul, Algebra.smul_def, Algebra.smul_def, mul_comm _ x'', hx']
      exact is_integral_mul is_integral_algebra_map x'.2
      
    · rw [mul_comm, mul_smul, Algebra.smul_def]
      exact is_integral_mul is_integral_algebra_map (hs _ hx'')
      
    · rw [IsScalarTower.algebra_map_eq A K L]
      apply (algebraMap K L).Injective.comp
      exact IsFractionRing.injective _ _
      
    

variable (L)

/-- If `L` is a finite extension of `K = Frac(A)`,
then `L` has a basis over `A` consisting of integral elements. -/
theorem FiniteDimensional.exists_is_basis_integral : ∃ (s : Finset L)(b : Basis s K L), ∀ x, IsIntegral A (b x) := by
  let this := Classical.decEq L
  let this : IsNoetherian K L := IsNoetherian.iff_fg.2 inferInstance
  let s' := IsNoetherian.finsetBasisIndex K L
  let bs' := IsNoetherian.finsetBasis K L
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (finset.univ.image bs')
  have hy' : algebraMap A L y ≠ 0 := by
    refine' mt ((injective_iff_map_eq_zero (algebraMap A L)).mp _ _) hy
    rw [IsScalarTower.algebra_map_eq A K L]
    exact (algebraMap K L).Injective.comp (IsFractionRing.injective A K)
  refine'
    ⟨s',
      bs'.map
        { Algebra.lmul _ _ (algebraMap A L y) with toFun := fun x => algebraMap A L y * x,
          invFun := fun x => (algebraMap A L y)⁻¹ * x, left_inv := _, right_inv := _ },
      _⟩
  · intro x
    simp only [← inv_mul_cancel_left₀ hy']
    
  · intro x
    simp only [← mul_inv_cancel_left₀ hy']
    
  · rintro ⟨x', hx'⟩
    simp only [← Algebra.smul_def, ← Finset.mem_image, ← exists_prop, ← Finset.mem_univ, ← true_andₓ] at his'
    simp only [← Basis.map_apply, ← LinearEquiv.coe_mk]
    exact his' _ ⟨_, rfl⟩
    

variable (A K L) [IsSeparable K L]

include L

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian over `A`. -/
theorem IsIntegralClosure.is_noetherian [IsIntegrallyClosed A] [IsNoetherianRing A] : IsNoetherian A C := by
  have := Classical.decEq L
  obtain ⟨s, b, hb_int⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' := (trace_form K L).dualBasis (trace_form_nondegenerate K L) b
  let this := is_noetherian_span_of_finite A (Set.finite_range b')
  let f : C →ₗ[A] Submodule.span A (Set.Range b') :=
    (Submodule.ofLe (IsIntegralClosure.range_le_span_dual_basis C b hb_int)).comp
      ((Algebra.linearMap C L).restrictScalars A).range_restrict
  refine' is_noetherian_of_ker_bot f _
  rw [LinearMap.ker_comp, Submodule.ker_of_le, Submodule.comap_bot, LinearMap.ker_cod_restrict]
  exact LinearMap.ker_eq_bot_of_injective (IsIntegralClosure.algebra_map_injective C A L)

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian. -/
theorem IsIntegralClosure.is_noetherian_ring [IsIntegrallyClosed A] [IsNoetherianRing A] : IsNoetherianRing C :=
  is_noetherian_ring_iff.mpr <| is_noetherian_of_tower A (IsIntegralClosure.is_noetherian A K L C)

variable {A K}

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure of `A` in `L` is
Noetherian. -/
theorem integralClosure.is_noetherian_ring [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing (integralClosure A L) :=
  IsIntegralClosure.is_noetherian_ring A K L (integralClosure A L)

variable (A K) [IsDomain C]

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure `C` of `A` in `L` is a Dedekind domain.

Can't be an instance since `A`, `K` or `L` can't be inferred. See also the instance
`integral_closure.is_dedekind_domain_fraction_ring` where `K := fraction_ring A`
and `C := integral_closure A L`.
-/
theorem IsIntegralClosure.is_dedekind_domain [h : IsDedekindDomain A] : IsDedekindDomain C := by
  have : IsFractionRing C L := IsIntegralClosure.is_fraction_ring_of_finite_extension A K L C
  exact
    ⟨IsIntegralClosure.is_noetherian_ring A K L C, h.dimension_le_one.is_integral_closure _ L _,
      (is_integrally_closed_iff L).mpr fun x hx =>
        ⟨IsIntegralClosure.mk' C x (is_integral_trans (IsIntegralClosure.is_integral_algebra A L) _ hx),
          IsIntegralClosure.algebra_map_mk' _ _ _⟩⟩

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

Can't be an instance since `K` can't be inferred. See also the instance
`integral_closure.is_dedekind_domain_fraction_ring` where `K := fraction_ring A`.
-/
theorem integralClosure.is_dedekind_domain [h : IsDedekindDomain A] : IsDedekindDomain (integralClosure A L) :=
  IsIntegralClosure.is_dedekind_domain A K L (integralClosure A L)

omit K

variable [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]

variable [FiniteDimensional (FractionRing A) L] [IsSeparable (FractionRing A) L]

/- If `L` is a finite separable extension of `Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

See also the lemma `integral_closure.is_dedekind_domain` where you can choose
the field of fractions yourself.
-/
instance integralClosure.is_dedekind_domain_fraction_ring [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  integralClosure.is_dedekind_domain A (FractionRing A) L

end IsIntegralClosure

