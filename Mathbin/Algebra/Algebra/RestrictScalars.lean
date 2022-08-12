/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathbin.Algebra.Algebra.Tower

/-!

# The `restrict_scalars` type alias

See the documentation attached to the `restrict_scalars` definition for advice on how and when to
use this type alias. As described there, it is often a better choice to use the `is_scalar_tower`
typeclass instead.

## Main definitions

* `restrict_scalars R S M`: the `S`-module `M` viewed as an `R` module when `S` is an `R`-algebra.
  Note that by default we do *not* have a `module S (restrict_scalars R S M)` instance
  for the original action.
  This is available as a def `restrict_scalars.module_orig` if really needed.
* `restrict_scalars.add_equiv : restrict_scalars R S M ≃+ M`: the additive equivalence
  between the restricted and original space (in fact, they are definitionally equal,
  but sometimes it is helpful to avoid using this fact, to keep instances from leaking).
* `restrict_scalars.ring_equiv : restrict_scalars R S A ≃+* A`: the ring equivalence
   between the restricted and original space when the module is an algebra.

## See also

There are many similarly-named definitions elsewhere which do not refer to this type alias. These
refer to restricting the scalar type in a bundled type, such as from `A →ₗ[R] B` to `A →ₗ[S] B`:

* `linear_map.restrict_scalars`
* `linear_equiv.restrict_scalars`
* `alg_hom.restrict_scalars`
* `alg_equiv.restrict_scalars`
* `submodule.restrict_scalars`
* `subalgebra.restrict_scalars`
-/


variable (R S M A : Type _)

/-- If we put an `R`-algebra structure on a semiring `S`, we get a natural equivalence from the
category of `S`-modules to the category of representations of the algebra `S` (over `R`). The type
synonym `restrict_scalars` is essentially this equivalence.

Warning: use this type synonym judiciously! Consider an example where we want to construct an
`R`-linear map from `M` to `S`, given:
```lean
variables (R S M : Type*)
variables [comm_semiring R] [semiring S] [algebra R S] [add_comm_monoid M] [module S M]
```
With the assumptions above we can't directly state our map as we have no `module R M` structure, but
`restrict_scalars` permits it to be written as:
```lean
-- an `R`-module structure on `M` is provided by `restrict_scalars` which is compatible
example : restrict_scalars R S M →ₗ[R] S := sorry
```
However, it is usually better just to add this extra structure as an argument:
```lean
-- an `R`-module structure on `M` and proof of its compatibility is provided by the user
example [module R M] [is_scalar_tower R S M] : M →ₗ[R] S := sorry
```
The advantage of the second approach is that it defers the duty of providing the missing typeclasses
`[module R M] [is_scalar_tower R S M]`. If some concrete `M` naturally carries these (as is often
the case) then we have avoided `restrict_scalars` entirely. If not, we can pass
`restrict_scalars R S M` later on instead of `M`.

Note that this means we almost always want to state definitions and lemmas in the language of
`is_scalar_tower` rather than `restrict_scalars`.

An example of when one might want to use `restrict_scalars` would be if one has a vector space
over a field of characteristic zero and wishes to make use of the `ℚ`-algebra structure. -/
@[nolint unused_arguments]
def RestrictScalars (R S M : Type _) : Type _ :=
  M

instance [I : Inhabited M] : Inhabited (RestrictScalars R S M) :=
  I

instance [I : AddCommMonoidₓ M] : AddCommMonoidₓ (RestrictScalars R S M) :=
  I

instance [I : AddCommGroupₓ M] : AddCommGroupₓ (RestrictScalars R S M) :=
  I

section Module

section

variable [Semiringₓ S] [AddCommMonoidₓ M]

/-- We temporarily install an action of the original ring on `restrict_sclars R S M`. -/
def RestrictScalars.moduleOrig [I : Module S M] : Module S (RestrictScalars R S M) :=
  I

variable [CommSemiringₓ R] [Algebra R S]

section

attribute [local instance] RestrictScalars.moduleOrig

/-- When `M` is a module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
module structure over `R`.

The preferred way of setting this up is `[module R M] [module S M] [is_scalar_tower R S M]`.
-/
instance [Module S M] : Module R (RestrictScalars R S M) :=
  Module.compHom M (algebraMap R S)

/-- This instance is only relevant when `restrict_scalars.module_orig` is available as an instance.
-/
instance [Module S M] : IsScalarTower R S (RestrictScalars R S M) :=
  ⟨fun r S M => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩

end

/-- When `M` is a right-module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
right-module structure over `R`.
The preferred way of setting this up is
`[module Rᵐᵒᵖ M] [module Sᵐᵒᵖ M] [is_scalar_tower Rᵐᵒᵖ Sᵐᵒᵖ M]`.
-/
instance RestrictScalars.opModule [Module Sᵐᵒᵖ M] : Module Rᵐᵒᵖ (RestrictScalars R S M) := by
  let this : Module Sᵐᵒᵖ (RestrictScalars R S M) := ‹Module Sᵐᵒᵖ M›
  exact Module.compHom M (algebraMap R S).op

instance RestrictScalars.is_central_scalar [Module S M] [Module Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar R
      (RestrictScalars R S M) where op_smul_eq_smul := fun r x => (op_smul_eq_smul (algebraMap R S r) (_ : M) : _)

/-- The `R`-algebra homomorphism from the original coefficient algebra `S` to endomorphisms
of `restrict_scalars R S M`.
-/
def RestrictScalars.lsmul [Module S M] : S →ₐ[R] Module.End R (RestrictScalars R S M) := by
  -- We use `restrict_scalars.module_orig` in the implementation,
  -- but not in the type.
  let this : Module S (RestrictScalars R S M) := RestrictScalars.moduleOrig R S M
  exact Algebra.lsmul R (RestrictScalars R S M)

end

variable [AddCommMonoidₓ M]

/-- `restrict_scalars.add_equiv` is the additive equivalence with the original module. -/
@[simps]
def RestrictScalars.addEquiv : RestrictScalars R S M ≃+ M :=
  AddEquiv.refl M

variable [CommSemiringₓ R] [Semiringₓ S] [Algebra R S] [Module S M]

theorem restrict_scalars_smul_def (c : R) (x : RestrictScalars R S M) : c • x = (algebraMap R S c • x : M) :=
  rfl

@[simp]
theorem RestrictScalars.add_equiv_map_smul (t : R) (x : RestrictScalars R S M) :
    RestrictScalars.addEquiv R S M (t • x) = algebraMap R S t • RestrictScalars.addEquiv R S M x :=
  rfl

end Module

section Algebra

instance [I : Semiringₓ A] : Semiringₓ (RestrictScalars R S A) :=
  I

instance [I : Ringₓ A] : Ringₓ (RestrictScalars R S A) :=
  I

instance [I : CommSemiringₓ A] : CommSemiringₓ (RestrictScalars R S A) :=
  I

instance [I : CommRingₓ A] : CommRingₓ (RestrictScalars R S A) :=
  I

variable [Semiringₓ A]

/-- Tautological ring isomorphism `restrict_scalars R S A ≃+* A`. -/
def RestrictScalars.ringEquiv : RestrictScalars R S A ≃+* A :=
  RingEquiv.refl _

variable [CommSemiringₓ S] [Algebra S A] [CommSemiringₓ R] [Algebra R S]

@[simp]
theorem RestrictScalars.ring_equiv_map_smul (r : R) (x : RestrictScalars R S A) :
    RestrictScalars.ringEquiv R S A (r • x) = algebraMap R S r • RestrictScalars.ringEquiv R S A x :=
  rfl

/-- `R ⟶ S` induces `S-Alg ⥤ R-Alg` -/
instance : Algebra R (RestrictScalars R S A) :=
  { (algebraMap S A).comp (algebraMap R S) with smul := (· • ·), commutes' := fun r x => Algebra.commutes _ _,
    smul_def' := fun _ _ => Algebra.smul_def _ _ }

@[simp]
theorem RestrictScalars.ring_equiv_algebra_map (r : R) :
    RestrictScalars.ringEquiv R S A (algebraMap R (RestrictScalars R S A) r) = algebraMap S A (algebraMap R S r) :=
  rfl

end Algebra

