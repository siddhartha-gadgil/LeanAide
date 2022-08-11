/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Anne Baanen
-/
import Mathbin.RingTheory.DedekindDomain.IntegralClosure
import Mathbin.Algebra.CharP.Algebra

/-!
# Number fields
This file defines a number field, the ring of integers corresponding to it and includes some
basic facts about the embeddings into an algebraic closed field.

## Main definitions
 - `number_field` defines a number field as a field which has characteristic zero and is finite
    dimensional over ℚ.
 - `ring_of_integers` defines the ring of integers (or number ring) corresponding to a number field
    as the integral closure of ℤ in the number field.

## Main Result
 - `eq_roots`: let `x ∈ K` with `K` number field and let `A` be an algebraic closed field of
    char. 0, then the images of `x` by the embeddings of `K` in `A` are exactly the roots in
    `A` of the minimal polynomial of `x` over `ℚ`.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
number field, ring of integers
-/


/-- A number field is a field which has characteristic zero and is finite
dimensional over ℚ. -/
class NumberField (K : Type _) [Field K] : Prop where
  [to_char_zero : CharZero K]
  [to_finite_dimensional : FiniteDimensional ℚ K]

open Function

open Classical BigOperators

/-- `ℤ` with its usual ring structure is not a field. -/
theorem Int.not_is_field : ¬IsField ℤ := fun h =>
  Int.not_even_one <|
    (h.mul_inv_cancel two_ne_zero).imp fun a => by
      rw [← two_mul] <;> exact Eq.symm

namespace NumberField

variable (K L : Type _) [Field K] [Field L] [nf : NumberField K]

include nf

-- See note [lower instance priority]
attribute [instance] NumberField.to_char_zero NumberField.to_finite_dimensional

protected theorem is_algebraic : Algebra.IsAlgebraic ℚ K :=
  Algebra.is_algebraic_of_finite _ _

omit nf

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field. -/
def ringOfIntegers :=
  integralClosure ℤ K

-- mathport name: «expr𝓞»
localized [NumberField] notation "𝓞" => NumberField.ringOfIntegers

theorem mem_ring_of_integers (x : K) : x ∈ 𝓞 K ↔ IsIntegral ℤ x :=
  Iff.rfl

/-- Given an algebra between two fields, create an algebra between their two rings of integers.

For now, this is not an instance by default as it creates an equal-but-not-defeq diamond with
`algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩` not being defeq on subtypes. This
will likely change in Lean 4. -/
def ringOfIntegersAlgebra [Algebra K L] : Algebra (𝓞 K) (𝓞 L) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap K L k, IsIntegral.algebra_map k.2⟩,
      map_zero' :=
        Subtype.ext <| by
          simp only [← Subtype.coe_mk, ← Subalgebra.coe_zero, ← map_zero],
      map_one' :=
        Subtype.ext <| by
          simp only [← Subtype.coe_mk, ← Subalgebra.coe_one, ← map_one],
      map_add' := fun x y =>
        Subtype.ext <| by
          simp only [← map_add, ← Subalgebra.coe_add, ← Subtype.coe_mk],
      map_mul' := fun x y =>
        Subtype.ext <| by
          simp only [← Subalgebra.coe_mul, ← map_mul, ← Subtype.coe_mk] }

namespace RingOfIntegers

variable {K}

instance [NumberField K] : IsFractionRing (𝓞 K) K :=
  integralClosure.is_fraction_ring_of_finite_extension ℚ _

instance : IsIntegralClosure (𝓞 K) ℤ K :=
  integralClosure.is_integral_closure _ _

instance [NumberField K] : IsIntegrallyClosed (𝓞 K) :=
  integralClosure.is_integrally_closed_of_finite_extension ℚ

theorem is_integral_coe (x : 𝓞 K) : IsIntegral ℤ (x : K) :=
  x.2

/-- The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K` -/
protected noncomputable def equiv (R : Type _) [CommRingₓ R] [Algebra R K] [IsIntegralClosure R ℤ K] : 𝓞 K ≃+* R :=
  (IsIntegralClosure.equiv ℤ R K _).symm.toRingEquiv

variable (K)

instance [NumberField K] : CharZero (𝓞 K) :=
  CharZero.of_module _ K

/-- The ring of integers of a number field is not a field. -/
theorem not_is_field [NumberField K] : ¬IsField (𝓞 K) := by
  have h_inj : Function.Injective ⇑(algebraMap ℤ (𝓞 K)) := RingHom.injective_int (algebraMap ℤ (𝓞 K))
  intro hf
  exact Int.not_is_field (((IsIntegralClosure.is_integral_algebra ℤ K).is_field_iff_is_field h_inj).mpr hf)

instance [NumberField K] : IsDedekindDomain (𝓞 K) :=
  IsIntegralClosure.is_dedekind_domain ℤ ℚ K _

end RingOfIntegers

end NumberField

namespace Rat

open NumberField

attribute [local instance] subsingleton_rat_module

instance number_field : NumberField ℚ where
  to_char_zero := inferInstance
  to_finite_dimensional :=-- The vector space structure of `ℚ` over itself can arise in multiple ways:
  -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
  -- all char 0 fields have a canonical embedding of `ℚ` (used in `number_field`).
  -- Show that these coincide:
  by
    convert (inferInstance : FiniteDimensional ℚ ℚ)

/-- The ring of integers of `ℚ` as a number field is just `ℤ`. -/
noncomputable def ringOfIntegersEquiv : ringOfIntegers ℚ ≃+* ℤ :=
  ringOfIntegers.equiv ℤ

end Rat

namespace AdjoinRoot

section

open Polynomial

attribute [-instance] algebraRat

attribute [local instance] algebra_rat_subsingleton

/-- The quotient of `ℚ[X]` by the ideal generated by an irreducible polynomial of `ℚ[X]`
is a number field. -/
instance {f : ℚ[X]} [hf : Fact (Irreducible f)] : NumberField (AdjoinRoot f) where
  to_char_zero := char_zero_of_injective_algebra_map (algebraMap ℚ _).Injective
  to_finite_dimensional := by
    convert (AdjoinRoot.powerBasis hf.out.ne_zero).FiniteDimensional

end

end AdjoinRoot

namespace NumberField.Embeddings

section NumberField

open Set FiniteDimensional Polynomial

variable {K L : Type _} [Field K] [Field L]

variable [NumberField K] [NumberField L] (x : K)

variable {A : Type _} [Field A] [CharZero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : Fintype (K →+* A) :=
  Fintype.ofEquiv (K →ₐ[ℚ] A) RingHom.equivRatAlgHom.symm

variable [IsAlgClosed A]

/-- The number of embeddings of a number field is its finrank. -/
theorem card : Fintype.card (K →+* A) = finrank ℚ K := by
  rw [Fintype.of_equiv_card ring_hom.equiv_rat_alg_hom.symm, AlgHom.card]

/-- For `x ∈ K`, with `K` a number field, the images of `x` by the embeddings of `K` are exactly
the roots of the minimal polynomial of `x` over `ℚ` -/
theorem eq_roots : (Range fun φ : K →+* A => φ x) = (minpoly ℚ x).RootSet A := by
  have hx : IsIntegral ℚ x := IsSeparable.is_integral ℚ x
  ext a
  constructor
  · rintro ⟨φ, hφ⟩
    rw [mem_root_set_iff, ← hφ]
    · let ψ := RingHom.equivRatAlgHom φ
      show (aeval (ψ x)) (minpoly ℚ x) = 0
      rw [aeval_alg_hom_apply ψ x (minpoly ℚ x)]
      simp only [← minpoly.aeval, ← map_zero]
      
    exact minpoly.ne_zero hx
    
  · intro ha
    let Qx := AdjoinRoot (minpoly ℚ x)
    have : Fact (Irreducible <| minpoly ℚ x) := ⟨minpoly.irreducible hx⟩
    have hK : (aeval x) (minpoly ℚ x) = 0 := minpoly.aeval _ _
    have hA : (aeval a) (minpoly ℚ x) = 0 := by
      rw [aeval_def, ← eval_map, ← mem_root_set_iff']
      exact ha
      refine' Polynomial.Monic.ne_zero _
      exact Polynomial.Monic.map (algebraMap ℚ A) (minpoly.monic hx)
    let ψ : Qx →+* A := by
      convert AdjoinRoot.lift (algebraMap ℚ A) a hA
    let this : Algebra Qx A := RingHom.toAlgebra ψ
    let this : Algebra Qx K :=
      RingHom.toAlgebra
        (by
          convert AdjoinRoot.lift (algebraMap ℚ K) x hK)
    let φ₀ : K →ₐ[Qx] A := by
      refine' IsAlgClosed.lift (Algebra.is_algebraic_of_larger_base ℚ Qx _)
      exact NumberField.is_algebraic _
    let φ := φ₀.to_ring_hom
    use φ
    rw [(_ : x = (algebraMap Qx K) (AdjoinRoot.root (minpoly ℚ x)))]
    · rw [(_ : a = ψ (AdjoinRoot.root (minpoly ℚ x)))]
      refine' AlgHom.commutes _ _
      exact (AdjoinRoot.lift_root hA).symm
      
    exact (AdjoinRoot.lift_root hK).symm
    

end NumberField

end NumberField.Embeddings

