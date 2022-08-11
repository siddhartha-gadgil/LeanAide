/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.TrivSqZeroExt

/-!
# Dual numbers

The dual numbers over `R` are of the form `a + bε`, where `a` and `b` are typically elements of a
commutative ring `R`, and `ε` is a symbol satisfying `ε^2 = 0`. They are a special case of
`triv_sq_zero_ext R M` with `M = R`.

## Notation

In the `dual_number` locale:

* `R[ε]` is a shorthand for `dual_number R`
* `ε` is a shorthand for `dual_number.eps`

## Main definitions

* `dual_number`
* `dual_number.eps`
* `dual_number.lift`

## Implementation notes

Rather than duplicating the API of `triv_sq_zero_ext`, this file reuses the functions there.

## References

* https://en.wikipedia.org/wiki/Dual_number
-/


variable {R : Type _}

/-- The type of dual numbers, numbers of the form $a + bε$ where $ε^2 = 0$.-/
abbrev DualNumber (R : Type _) : Type _ :=
  TrivSqZeroExt R R

/-- The unit element $ε$ that squares to zero. -/
def DualNumber.eps [Zero R] [One R] : DualNumber R :=
  TrivSqZeroExt.inr 1

-- mathport name: «exprε»
localized [DualNumber] notation "ε" => DualNumber.eps

-- mathport name: «expr [ε]»
localized [DualNumber] postfix:1024 "[ε]" => DualNumber

open DualNumber

namespace DualNumber

open TrivSqZeroExt

@[simp]
theorem fst_eps [Zero R] [One R] : fst ε = (0 : R) :=
  fst_inr _ _

@[simp]
theorem snd_eps [Zero R] [One R] : snd ε = (1 : R) :=
  snd_inr _ _

/-- A version of `triv_sq_zero_ext.snd_mul` with `*` instead of `•`. -/
@[simp]
theorem snd_mul [Semiringₓ R] (x y : R[ε]) : snd (x * y) = fst x * snd y + fst y * snd x :=
  snd_mul _ _

@[simp]
theorem eps_mul_eps [Semiringₓ R] : (ε * ε : R[ε]) = 0 :=
  inr_mul_inr _ _ _

@[simp]
theorem inr_eq_smul_eps [MulZeroOneClassₓ R] (r : R) : inr r = (r • ε : R[ε]) :=
  ext (mul_zero r).symm (mul_oneₓ r).symm

/-- For two algebra morphisms out of `R[ε]` to agree, it suffices for them to agree on `ε`. -/
@[ext]
theorem alg_hom_ext {A} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] ⦃f g : R[ε] →ₐ[R] A⦄ (h : f ε = g ε) : f = g :=
  alg_hom_ext' <| LinearMap.ext_ring <| h

variable {A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

/-- A universal property of the dual numbers, providing a unique `R[ε] →ₐ[R] A` for every element
of `A` which squares to `0`.

This isomorphism is named to match the very similar `complex.lift`. -/
@[simps (config := { attrs := [] })]
def lift : { e : A // e * e = 0 } ≃ (R[ε] →ₐ[R] A) :=
  Equivₓ.trans
    (show { e : A // e * e = 0 } ≃ { f : R →ₗ[R] A // ∀ x y, f x * f y = 0 } from
      (LinearMap.ringLmapEquivSelf R ℕ A).symm.toEquiv.subtypeEquiv fun a => by
        dsimp'
        simp_rw [smul_mul_smul]
        refine'
          ⟨fun h x y => h.symm ▸ smul_zero _, fun h => by
            simpa using h 1 1⟩)
    TrivSqZeroExt.lift

-- When applied to `ε`, `dual_number.lift` produces the element of `A` that squares to 0.
@[simp]
theorem lift_apply_eps (e : { e : A // e * e = 0 }) : lift e (ε : R[ε]) = e :=
  (TrivSqZeroExt.lift_aux_apply_inr _ _ _).trans <| one_smul _ _

-- Lifting `dual_number.eps` itself gives the identity.
@[simp]
theorem lift_eps : lift ⟨ε, eps_mul_eps⟩ = AlgHom.id R R[ε] :=
  alg_hom_ext <| lift_apply_eps _

end DualNumber

