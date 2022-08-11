/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
import Mathbin.FieldTheory.Ratfunc
import Mathbin.RingTheory.Algebraic
import Mathbin.RingTheory.DedekindDomain.IntegralClosure
import Mathbin.RingTheory.IntegrallyClosed
import Mathbin.Topology.Algebra.ValuedField

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions
 - `function_field Fq F` states that `F` is a function field over the (finite) field `Fq`,
   i.e. it is a finite extension of the field of rational functions in one variable over `Fq`.
 - `function_field.ring_of_integers` defines the ring of integers corresponding to a function field
    as the integral closure of `polynomial Fq` in the function field.
 - `function_field.infty_valuation` : The place at infinity on `Fq(t)` is the nonarchimedean
    valuation on `Fq(t)` with uniformizer `1/t`.
 -  `function_field.Fqt_infty` : The completion `Fq((t⁻¹))`  of `Fq(t)` with respect to the
    valuation at infinity.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like `finite Fq` or
`is_scalar_tower Fq[X] (fraction_ring Fq[X]) F` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
function field, ring of integers
-/


noncomputable section

open nonZeroDivisors Polynomial DiscreteValuation

variable (Fq F : Type) [Field Fq] [Field F]

/-- `F` is a function field over the finite field `Fq` if it is a finite
extension of the field of rational functions in one variable over `Fq`.

Note that `F` can be a function field over multiple, non-isomorphic, `Fq`.
-/
abbrev FunctionField [Algebra (Ratfunc Fq) F] : Prop :=
  FiniteDimensional (Ratfunc Fq) F

/-- `F` is a function field over `Fq` iff it is a finite extension of `Fq(t)`. -/
protected theorem function_field_iff (Fqt : Type _) [Field Fqt] [Algebra Fq[X] Fqt] [IsFractionRing Fq[X] Fqt]
    [Algebra (Ratfunc Fq) F] [Algebra Fqt F] [Algebra Fq[X] F] [IsScalarTower Fq[X] Fqt F]
    [IsScalarTower Fq[X] (Ratfunc Fq) F] : FunctionField Fq F ↔ FiniteDimensional Fqt F := by
  let e := IsLocalization.algEquiv Fq[X]⁰ (Ratfunc Fq) Fqt
  have : ∀ (c) (x : F), e c • x = c • x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def]
    congr
    refine' congr_fun _ c
    refine' IsLocalization.ext (nonZeroDivisors Fq[X]) _ _ _ _ _ _ _ <;>
      intros <;>
        simp only [← AlgEquiv.map_one, ← RingHom.map_one, ← AlgEquiv.map_mul, ← RingHom.map_mul, ← AlgEquiv.commutes,
          IsScalarTower.algebra_map_apply]
  constructor <;> intro h <;> skip
  · let b := FiniteDimensional.finBasis (Ratfunc Fq) F
    exact FiniteDimensional.of_fintype_basis (b.map_coeffs e this)
    
  · let b := FiniteDimensional.finBasis Fqt F
    refine' FiniteDimensional.of_fintype_basis (b.map_coeffs e.symm _)
    intro c x
    convert (this (e.symm c) x).symm
    simp only [← e.apply_symm_apply]
    

theorem algebra_map_injective [Algebra Fq[X] F] [Algebra (Ratfunc Fq) F] [IsScalarTower Fq[X] (Ratfunc Fq) F] :
    Function.Injective ⇑(algebraMap Fq[X] F) := by
  rw [IsScalarTower.algebra_map_eq Fq[X] (Ratfunc Fq) F]
  exact Function.Injective.comp (algebraMap (Ratfunc Fq) F).Injective (IsFractionRing.injective Fq[X] (Ratfunc Fq))

namespace FunctionField

/-- The function field analogue of `number_field.ring_of_integers`:
`function_field.ring_of_integers Fq Fqt F` is the integral closure of `Fq[t]` in `F`.

We don't actually assume `F` is a function field over `Fq` in the definition,
only when proving its properties.
-/
def ringOfIntegers [Algebra Fq[X] F] :=
  integralClosure Fq[X] F

namespace RingOfIntegers

variable [Algebra Fq[X] F]

instance : IsDomain (ringOfIntegers Fq F) :=
  (ringOfIntegers Fq F).IsDomain

instance : IsIntegralClosure (ringOfIntegers Fq F) Fq[X] F :=
  integralClosure.is_integral_closure _ _

variable [Algebra (Ratfunc Fq) F] [IsScalarTower Fq[X] (Ratfunc Fq) F]

theorem algebra_map_injective : Function.Injective ⇑(algebraMap Fq[X] (ringOfIntegers Fq F)) := by
  have hinj : Function.Injective ⇑(algebraMap Fq[X] F) := by
    rw [IsScalarTower.algebra_map_eq Fq[X] (Ratfunc Fq) F]
    exact Function.Injective.comp (algebraMap (Ratfunc Fq) F).Injective (IsFractionRing.injective Fq[X] (Ratfunc Fq))
  rw [injective_iff_map_eq_zero (algebraMap Fq[X] ↥(ring_of_integers Fq F))]
  intro p hp
  rw [← Subtype.coe_inj, Subalgebra.coe_zero] at hp
  rw [injective_iff_map_eq_zero (algebraMap Fq[X] F)] at hinj
  exact hinj p hp

theorem not_is_field : ¬IsField (ringOfIntegers Fq F) := by
  simpa [(IsIntegralClosure.is_integral_algebra Fq[X] F).is_field_iff_is_field (algebra_map_injective Fq F)] using
    Polynomial.not_is_field Fq

variable [FunctionField Fq F]

instance : IsFractionRing (ringOfIntegers Fq F) F :=
  integralClosure.is_fraction_ring_of_finite_extension (Ratfunc Fq) F

instance : IsIntegrallyClosed (ringOfIntegers Fq F) :=
  integralClosure.is_integrally_closed_of_finite_extension (Ratfunc Fq)

instance [IsSeparable (Ratfunc Fq) F] : IsDedekindDomain (ringOfIntegers Fq F) :=
  IsIntegralClosure.is_dedekind_domain Fq[X] (Ratfunc Fq) F _

end RingOfIntegers

/-! ### The place at infinity on Fq(t) -/


section InftyValuation

variable [DecidableEq (Ratfunc Fq)]

/-- The valuation at infinity is the nonarchimedean valuation on `Fq(t)` with uniformizer `1/t`.
Explicitly, if `f/g ∈ Fq(t)` is a nonzero quotient of polynomials, its valuation at infinity is
`multiplicative.of_add(degree(f) - degree(g))`. -/
def inftyValuationDef (r : Ratfunc Fq) : ℤₘ₀ :=
  if r = 0 then 0 else Multiplicative.ofAdd r.intDegree

theorem InftyValuation.map_zero' : inftyValuationDef Fq 0 = 0 :=
  if_pos rfl

theorem InftyValuation.map_one' : inftyValuationDef Fq 1 = 1 :=
  (if_neg one_ne_zero).trans <| by
    rw [Ratfunc.int_degree_one, of_add_zero, WithZero.coe_one]

theorem InftyValuation.map_mul' (x y : Ratfunc Fq) :
    inftyValuationDef Fq (x * y) = inftyValuationDef Fq x * inftyValuationDef Fq y := by
  rw [infty_valuation_def, infty_valuation_def, infty_valuation_def]
  by_cases' hx : x = 0
  · rw [hx, zero_mul, if_pos (Eq.refl _), zero_mul]
    
  · by_cases' hy : y = 0
    · rw [hy, mul_zero, if_pos (Eq.refl _), mul_zero]
      
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithZero.coe_mul, WithZero.coe_inj, ← of_add_add,
        Ratfunc.int_degree_mul hx hy]
      
    

theorem InftyValuation.map_add_le_max' (x y : Ratfunc Fq) :
    inftyValuationDef Fq (x + y) ≤ max (inftyValuationDef Fq x) (inftyValuationDef Fq y) := by
  by_cases' hx : x = 0
  · rw [hx, zero_addₓ]
    conv_rhs => rw [infty_valuation_def, if_pos (Eq.refl _)]
    rw [max_eq_rightₓ (WithZero.zero_le (infty_valuation_def Fq y))]
    exact le_reflₓ _
    
  · by_cases' hy : y = 0
    · rw [hy, add_zeroₓ]
      conv_rhs => rw [max_commₓ, infty_valuation_def, if_pos (Eq.refl _)]
      rw [max_eq_rightₓ (WithZero.zero_le (infty_valuation_def Fq x))]
      exact le_reflₓ _
      
    · by_cases' hxy : x + y = 0
      · rw [infty_valuation_def, if_pos hxy]
        exact zero_le'
        
      · rw [infty_valuation_def, infty_valuation_def, infty_valuation_def, if_neg hx, if_neg hy, if_neg hxy]
        rw [le_max_iff, WithZero.coe_le_coe, Multiplicative.of_add_le, WithZero.coe_le_coe, Multiplicative.of_add_le, ←
          le_max_iff]
        exact Ratfunc.int_degree_add_le hy hxy
        
      
    

@[simp]
theorem infty_valuation_of_nonzero {x : Ratfunc Fq} (hx : x ≠ 0) :
    inftyValuationDef Fq x = Multiplicative.ofAdd x.intDegree := by
  rw [infty_valuation_def, if_neg hx]

/-- The valuation at infinity on `Fq(t)`. -/
def inftyValuation : Valuation (Ratfunc Fq) ℤₘ₀ where
  toFun := inftyValuationDef Fq
  map_zero' := InftyValuation.map_zero' Fq
  map_one' := InftyValuation.map_one' Fq
  map_mul' := InftyValuation.map_mul' Fq
  map_add_le_max' := InftyValuation.map_add_le_max' Fq

@[simp]
theorem infty_valuation_apply {x : Ratfunc Fq} : inftyValuation Fq x = inftyValuationDef Fq x :=
  rfl

@[simp]
theorem inftyValuation.C {k : Fq} (hk : k ≠ 0) : inftyValuationDef Fq (Ratfunc.c k) = Multiplicative.ofAdd (0 : ℤ) := by
  have hCk : Ratfunc.c k ≠ 0 := (RingHom.map_ne_zero _).mpr hk
  rw [infty_valuation_def, if_neg hCk, Ratfunc.int_degree_C]

@[simp]
theorem inftyValuation.X : inftyValuationDef Fq Ratfunc.x = Multiplicative.ofAdd (1 : ℤ) := by
  rw [infty_valuation_def, if_neg Ratfunc.X_ne_zero, Ratfunc.int_degree_X]

@[simp]
theorem inftyValuation.polynomial {p : Polynomial Fq} (hp : p ≠ 0) :
    inftyValuationDef Fq (algebraMap (Polynomial Fq) (Ratfunc Fq) p) = Multiplicative.ofAdd (p.natDegree : ℤ) := by
  have hp' : algebraMap (Polynomial Fq) (Ratfunc Fq) p ≠ 0 := by
    rw [Ne.def, Ratfunc.algebra_map_eq_zero_iff]
    exact hp
  rw [infty_valuation_def, if_neg hp', Ratfunc.int_degree_polynomial]

/-- The valued field `Fq(t)` with the valuation at infinity. -/
def inftyValuedFqt : Valued (Ratfunc Fq) ℤₘ₀ :=
  Valued.mk' <| inftyValuation Fq

theorem inftyValuedFqt.def {x : Ratfunc Fq} :
    @Valued.v (Ratfunc Fq) _ _ _ (inftyValuedFqt Fq) x = inftyValuationDef Fq x :=
  rfl

/-- The completion `Fq((t⁻¹))`  of `Fq(t)` with respect to the valuation at infinity. -/
def FqtInfty :=
  @UniformSpace.Completion (Ratfunc Fq) <| (inftyValuedFqt Fq).toUniformSpace

instance : Field (FqtInfty Fq) := by
  let this := infty_valued_Fqt Fq
  exact UniformSpace.Completion.field

instance : Inhabited (FqtInfty Fq) :=
  ⟨(0 : FqtInfty Fq)⟩

/-- The valuation at infinity on `k(t)` extends to a valuation on `Fqt_infty`. -/
instance valuedFqtInfty : Valued (FqtInfty Fq) ℤₘ₀ :=
  @Valued.valuedCompletion _ _ _ _ (inftyValuedFqt Fq)

theorem valuedFqtInfty.def {x : FqtInfty Fq} :
    Valued.v x = @Valued.extension (Ratfunc Fq) _ _ _ (inftyValuedFqt Fq) x :=
  rfl

end InftyValuation

end FunctionField

