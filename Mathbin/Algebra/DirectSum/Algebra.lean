/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.DirectSum.Module
import Mathbin.Algebra.DirectSum.Ring

/-! # Additively-graded algebra structures on `⨁ i, A i`

This file provides `R`-algebra structures on external direct sums of `R`-modules.

Recall that if `A i` are a family of `add_comm_monoid`s indexed by an `add_monoid`, then an instance
of `direct_sum.gmonoid A` is a multiplication `A i → A j → A (i + j)` giving `⨁ i, A i` the
structure of a semiring. In this file, we introduce the `direct_sum.galgebra R A` class for the case
where all `A i` are `R`-modules. This is the extra structure needed to promote `⨁ i, A i` to an
`R`-algebra.

## Main definitions

* `direct_sum.galgebra R A`, the typeclass.
* `direct_sum.galgebra.of_submodules`, for creating the above instance from a collection of
  submodules.
* `direct_sum.to_algebra` extends `direct_sum.to_semiring` to produce an `alg_hom`.

-/


universe uι uR uA uB

variable {ι : Type uι}

namespace DirectSum

open DirectSum

variable (R : Type uR) (A : ι → Type uA) {B : Type uB} [DecidableEq ι]

variable [CommSemiringₓ R] [∀ i, AddCommMonoidₓ (A i)] [∀ i, Module R (A i)]

variable [AddMonoidₓ ι] [Gsemiring A]

section

/-- A graded version of `algebra`. An instance of `direct_sum.galgebra R A` endows `(⨁ i, A i)`
with an `R`-algebra structure. -/
class Galgebra where
  toFun : R →+ A 0
  map_one : to_fun 1 = GradedMonoid.GhasOne.one
  map_mul : ∀ r s, GradedMonoid.mk _ (to_fun (r * s)) = ⟨_, GradedMonoid.GhasMul.mul (to_fun r) (to_fun s)⟩
  commutes : ∀ r x, GradedMonoid.mk _ (to_fun r) * x = x * ⟨_, to_fun r⟩
  smul_def : ∀ (r) (x : GradedMonoid A), GradedMonoid.mk x.1 (r • x.2) = ⟨_, to_fun r⟩ * x

end

variable [Semiringₓ B] [Galgebra R A] [Algebra R B]

instance : Algebra R (⨁ i, A i) where
  toFun := (DirectSum.of A 0).comp Galgebra.toFun
  map_zero' := AddMonoidHom.map_zero _
  map_add' := AddMonoidHom.map_add _
  map_one' := (DirectSum.of A 0).congr_arg Galgebra.map_one
  map_mul' := fun a b => by
    simp only [← AddMonoidHom.comp_apply]
    rw [of_mul_of]
    apply Dfinsupp.single_eq_of_sigma_eq (galgebra.map_mul a b)
  commutes' := fun r x => by
    change AddMonoidHom.mul (DirectSum.of _ _ _) x = add_monoid_hom.mul.flip (DirectSum.of _ _ _) x
    apply AddMonoidHom.congr_fun _ x
    ext i xi : 2
    dsimp' only [← AddMonoidHom.comp_apply, ← AddMonoidHom.mul_apply, ← AddMonoidHom.flip_apply]
    rw [of_mul_of, of_mul_of]
    apply Dfinsupp.single_eq_of_sigma_eq (galgebra.commutes r ⟨i, xi⟩)
  smul_def' := fun r x => by
    change DistribMulAction.toAddMonoidHom _ r x = AddMonoidHom.mul (DirectSum.of _ _ _) x
    apply AddMonoidHom.congr_fun _ x
    ext i xi : 2
    dsimp' only [← AddMonoidHom.comp_apply, ← DistribMulAction.to_add_monoid_hom_apply, ← AddMonoidHom.mul_apply]
    rw [DirectSum.of_mul_of, ← of_smul]
    apply Dfinsupp.single_eq_of_sigma_eq (galgebra.smul_def r ⟨i, xi⟩)

theorem algebra_map_apply (r : R) : algebraMap R (⨁ i, A i) r = DirectSum.of A 0 (Galgebra.toFun r) :=
  rfl

theorem algebra_map_to_add_monoid_hom :
    ↑(algebraMap R (⨁ i, A i)) = (DirectSum.of A 0).comp (Galgebra.toFun : R →+ A 0) :=
  rfl

/-- A family of `linear_map`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
describes an `alg_hom` on `⨁ i, A i`. This is a stronger version of `direct_sum.to_semiring`.

Of particular interest is the case when `A i` are bundled subojects, `f` is the family of
coercions such as `submodule.subtype (A i)`, and the `[gmonoid A]` structure originates from
`direct_sum.gmonoid.of_add_submodules`, in which case the proofs about `ghas_one` and `ghas_mul`
can be discharged by `rfl`. -/
@[simps]
def toAlgebra (f : ∀ i, A i →ₗ[R] B) (hone : f _ GradedMonoid.GhasOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GhasMul.mul ai aj) = f _ ai * f _ aj)
    (hcommutes : ∀ r, (f 0) (Galgebra.toFun r) = (algebraMap R B) r) : (⨁ i, A i) →ₐ[R] B :=
  { toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul with
    toFun := toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul,
    commutes' := fun r => (DirectSum.to_semiring_of _ _ _ _ _).trans (hcommutes r) }

/-- Two `alg_hom`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem alg_hom_ext' ⦃f g : (⨁ i, A i) →ₐ[R] B⦄
    (h : ∀ i, f.toLinearMap.comp (lof _ _ A i) = g.toLinearMap.comp (lof _ _ A i)) : f = g :=
  AlgHom.to_linear_map_injective <| DirectSum.linear_map_ext _ h

theorem alg_hom_ext ⦃f g : (⨁ i, A i) →ₐ[R] B⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) : f = g :=
  (alg_hom_ext' R A) fun i => LinearMap.ext <| h i

end DirectSum

/-! ### Concrete instances -/


/-- A direct sum of copies of a `algebra` inherits the algebra structure.

-/
@[simps]
instance Algebra.directSumGalgebra {R A : Type _} [DecidableEq ι] [AddMonoidₓ ι] [CommSemiringₓ R] [Semiringₓ A]
    [Algebra R A] : DirectSum.Galgebra R fun i : ι => A where
  toFun := (algebraMap R A).toAddMonoidHom
  map_one := (algebraMap R A).map_one
  map_mul := fun a b => Sigma.ext (zero_addₓ _).symm (heq_of_eq <| (algebraMap R A).map_mul a b)
  commutes := fun r ⟨ai, a⟩ => Sigma.ext ((zero_addₓ _).trans (add_zeroₓ _).symm) (heq_of_eq <| Algebra.commutes _ _)
  smul_def := fun r ⟨ai, a⟩ => Sigma.ext (zero_addₓ _).symm (heq_of_eq <| Algebra.smul_def _ _)

namespace Submodule

variable {R A : Type _} [CommSemiringₓ R]

end Submodule

