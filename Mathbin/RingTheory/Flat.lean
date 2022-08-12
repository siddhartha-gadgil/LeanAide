/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.RingTheory.Noetherian

/-!
# Flat modules

A module `M` over a commutative ring `R` is *flat*
if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective.

This is equivalent to the claim that for all injective `R`-linear maps `f : M₁ → M₂`
the induced map `M₁ ⊗ M → M₂ ⊗ M` is injective.
See <https://stacks.math.columbia.edu/tag/00HD>.
This result is not yet formalised.

## Main declaration

* `module.flat`: the predicate asserting that an `R`-module `M` is flat.

## TODO

* Show that tensoring with a flat module preserves injective morphisms.
  Show that this is equivalent to be flat.
  See <https://stacks.math.columbia.edu/tag/00HD>.
  To do this, it is probably a good idea to think about a suitable
  categorical induction principle that should be applied to the category of `R`-modules,
  and that will take care of the administrative side of the proof.
* Define flat `R`-algebras
* Define flat ring homomorphisms
  - Show that the identity is flat
  - Show that composition of flat morphisms is flat
* Show that flatness is stable under base change (aka extension of scalars)
  For base change, it will be very useful to have a "characteristic predicate"
  instead of relying on the construction `A ⊗ B`.
  Indeed, such a predicate should allow us to treat both
  `polynomial A` and `A ⊗ polynomial R` as the base change of `polynomial R` to `A`.
  (Similar examples exist with `fin n → R`, `R × R`, `ℤ[i] ⊗ ℝ`, etc...)
* Generalize flatness to noncommutative rings.

-/


universe u v

namespace Module

open Function (Injective)

open LinearMap (lsmul)

open TensorProduct

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective. -/
class Flat (R : Type u) (M : Type v) [CommRingₓ R] [AddCommGroupₓ M] [Module R M] : Prop where
  out : ∀ ⦃I : Ideal R⦄ (hI : I.Fg), Injective (TensorProduct.lift ((lsmul R M).comp I.Subtype))

namespace Flat

open TensorProduct LinearMap _Root_.Submodule

instance self (R : Type u) [CommRingₓ R] : Flat R R :=
  ⟨by
    intro I hI
    rw [← Equivₓ.injective_comp (TensorProduct.rid R I).symm.toEquiv]
    convert Subtype.coe_injective using 1
    ext x
    simp only [← Function.comp_app, ← LinearEquiv.coe_to_equiv, ← rid_symm_apply, ← comp_apply, ← mul_oneₓ, ← lift.tmul,
      ← subtype_apply, ← Algebra.id.smul_eq_mul, ← lsmul_apply]⟩

end Flat

end Module

