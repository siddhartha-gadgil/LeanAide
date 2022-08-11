/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import Mathbin.Algebra.Algebra.Operations
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.DirectSum.Algebra

/-!
# Internally graded rings and algebras

This module provides `gsemiring` and `gcomm_semiring` instances for a collection of subobjects `A`
when a `set_like.graded_monoid` instance is available:

* `set_like.gnon_unital_non_assoc_semiring`
* `set_like.gsemiring`
* `set_like.gcomm_semiring`

With these instances in place, it provides the bundled canonical maps out of a direct sum of
subobjects into their carrier type:

* `direct_sum.coe_ring_hom` (a `ring_hom` version of `direct_sum.coe_add_monoid_hom`)
* `direct_sum.coe_alg_hom` (an `alg_hom` version of `direct_sum.submodule_coe`)

Strictly the definitions in this file are not sufficient to fully define an "internal" direct sum;
to represent this case, `(h : direct_sum.is_internal A) [set_like.graded_monoid A]` is
needed. In the future there will likely be a data-carrying, constructive, typeclass version of
`direct_sum.is_internal` for providing an explicit decomposition function.

When `complete_lattice.independent (set.range A)` (a weaker condition than
`direct_sum.is_internal A`), these provide a grading of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

internally graded ring
-/


open DirectSum BigOperators

variable {ι : Type _} {σ S R : Type _}

instance AddCommMonoidₓ.ofSubmonoidOnSemiring [Semiringₓ R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ) :
    ∀ i, AddCommMonoidₓ (A i) := fun i => by
  infer_instance

instance AddCommGroupₓ.ofSubgroupOnSemiring [Ringₓ R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ) :
    ∀ i, AddCommGroupₓ (A i) := fun i => by
  infer_instance

theorem SetLike.HasGradedOne.algebra_map_mem [Zero ι] [CommSemiringₓ S] [Semiringₓ R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.HasGradedOne A] (s : S) : algebraMap S R s ∈ A 0 := by
  rw [Algebra.algebra_map_eq_smul_one]
  exact (A 0).smul_mem s SetLike.HasGradedOne.one_mem

theorem SetLike.HasGradedOne.nat_cast_mem [Zero ι] [AddMonoidWithOneₓ R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι → σ) [SetLike.HasGradedOne A] (n : ℕ) : (n : R) ∈ A 0 := by
  induction n
  · rw [Nat.cast_zeroₓ]
    exact zero_mem (A 0)
    
  · rw [Nat.cast_succₓ]
    exact add_mem n_ih SetLike.HasGradedOne.one_mem
    

theorem SetLike.HasGradedOne.int_cast_mem [Zero ι] [AddGroupWithOneₓ R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.HasGradedOne A] (z : ℤ) : (z : R) ∈ A 0 := by
  induction z
  · rw [Int.cast_of_nat]
    exact SetLike.HasGradedOne.nat_cast_mem _ _
    
  · rw [Int.cast_neg_succ_of_nat]
    exact neg_mem (SetLike.HasGradedOne.nat_cast_mem _ _)
    

section DirectSum

variable [DecidableEq ι]

/-! #### From `add_submonoid`s and `add_subgroup`s -/


namespace SetLike

/-- Build a `gnon_unital_non_assoc_semiring` instance for a collection of additive submonoids. -/
instance gnonUnitalNonAssocSemiring [Add ι] [NonUnitalNonAssocSemiringₓ R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι → σ) [SetLike.HasGradedMul A] : DirectSum.GnonUnitalNonAssocSemiring fun i => A i :=
  { SetLike.ghasMul A with mul_zero := fun i j _ => Subtype.ext (mul_zero _),
    zero_mul := fun i j _ => Subtype.ext (zero_mul _), mul_add := fun i j _ _ _ => Subtype.ext (mul_addₓ _ _ _),
    add_mul := fun i j _ _ _ => Subtype.ext (add_mulₓ _ _ _) }

/-- Build a `gsemiring` instance for a collection of additive submonoids. -/
instance gsemiring [AddMonoidₓ ι] [Semiringₓ R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.Gsemiring fun i => A i :=
  { SetLike.gmonoid A with mul_zero := fun i j _ => Subtype.ext (mul_zero _),
    zero_mul := fun i j _ => Subtype.ext (zero_mul _), mul_add := fun i j _ _ _ => Subtype.ext (mul_addₓ _ _ _),
    add_mul := fun i j _ _ _ => Subtype.ext (add_mulₓ _ _ _),
    natCast := fun n => ⟨n, SetLike.HasGradedOne.nat_cast_mem _ _⟩, nat_cast_zero := Subtype.ext Nat.cast_zeroₓ,
    nat_cast_succ := fun n => Subtype.ext (Nat.cast_succₓ n) }

/-- Build a `gcomm_semiring` instance for a collection of additive submonoids. -/
instance gcommSemiring [AddCommMonoidₓ ι] [CommSemiringₓ R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GcommSemiring fun i => A i :=
  { SetLike.gcommMonoid A, SetLike.gsemiring A with }

/-- Build a `gring` instance for a collection of additive subgroups. -/
instance gring [AddMonoidₓ ι] [Ringₓ R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ) [SetLike.GradedMonoid A] :
    DirectSum.Gring fun i => A i :=
  { SetLike.gsemiring A with intCast := fun z => ⟨z, SetLike.HasGradedOne.int_cast_mem _ _⟩,
    int_cast_of_nat := fun n => Subtype.ext <| Int.cast_of_nat _,
    int_cast_neg_succ_of_nat := fun n => Subtype.ext <| Int.cast_neg_succ_of_nat n }

/-- Build a `gcomm_semiring` instance for a collection of additive submonoids. -/
instance gcommRing [AddCommMonoidₓ ι] [CommRingₓ R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GcommRing fun i => A i :=
  { SetLike.gcommMonoid A, SetLike.gring A with }

end SetLike

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
def DirectSum.coeRingHom [AddMonoidₓ ι] [Semiringₓ R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : (⨁ i, A i) →+* R :=
  DirectSum.toSemiring (fun i => AddSubmonoidClass.subtype (A i)) rfl fun _ _ _ _ => rfl

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
@[simp]
theorem DirectSum.coe_ring_hom_of [AddMonoidₓ ι] [Semiringₓ R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] (i : ι) (x : A i) : DirectSum.coeRingHom A (DirectSum.of (fun i => A i) i x) = x :=
  DirectSum.to_semiring_of _ _ _ _ _

theorem DirectSum.coe_mul_apply [AddMonoidₓ ι] [Semiringₓ R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (i : ι) :
    ((r * r') i : R) =
      ∑ ij in Finset.filter (fun ij : ι × ι => ij.1 + ij.2 = i) (r.support.product r'.support), r ij.1 * r' ij.2 :=
  by
  rw [DirectSum.mul_eq_sum_support_ghas_mul, Dfinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  simp_rw [DirectSum.coe_of_apply, ← Finset.sum_filter, SetLike.coe_ghas_mul]

/-! #### From `submodule`s -/


namespace Submodule

/-- Build a `galgebra` instance for a collection of `submodule`s. -/
instance galgebra [AddMonoidₓ ι] [CommSemiringₓ S] [Semiringₓ R] [Algebra S R] (A : ι → Submodule S R)
    [SetLike.GradedMonoid A] : DirectSum.Galgebra S fun i => A i where
  toFun := ((Algebra.linearMap S R).codRestrict (A 0) <| SetLike.HasGradedOne.algebra_map_mem A).toAddMonoidHom
  map_one := Subtype.ext <| (algebraMap S R).map_one
  map_mul := fun x y => Sigma.subtype_ext (add_zeroₓ 0).symm <| (algebraMap S R).map_mul _ _
  commutes := fun r ⟨i, xi⟩ => Sigma.subtype_ext ((zero_addₓ i).trans (add_zeroₓ i).symm) <| Algebra.commutes _ _
  smul_def := fun r ⟨i, xi⟩ => Sigma.subtype_ext (zero_addₓ i).symm <| Algebra.smul_def _ _

@[simp]
theorem setLike.coe_galgebra_to_fun [AddMonoidₓ ι] [CommSemiringₓ S] [Semiringₓ R] [Algebra S R] (A : ι → Submodule S R)
    [SetLike.GradedMonoid A] (s : S) :
    ↑(@DirectSum.Galgebra.toFun _ S (fun i => A i) _ _ _ _ _ _ _ s) = (algebraMap S R s : R) :=
  rfl

/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
instance nat_power_graded_monoid [CommSemiringₓ S] [Semiringₓ R] [Algebra S R] (p : Submodule S R) :
    SetLike.GradedMonoid fun i : ℕ => p ^ i where
  one_mem := by
    rw [← one_le, pow_zeroₓ]
    exact le_rfl
  mul_mem := fun i j p q hp hq => by
    rw [pow_addₓ]
    exact Submodule.mul_mem_mul hp hq

end Submodule

/-- The canonical algebra isomorphism between `⨁ i, A i` and `R`. -/
def DirectSum.coeAlgHom [AddMonoidₓ ι] [CommSemiringₓ S] [Semiringₓ R] [Algebra S R] (A : ι → Submodule S R)
    [SetLike.GradedMonoid A] : (⨁ i, A i) →ₐ[S] R :=
  DirectSum.toAlgebra S _ (fun i => (A i).Subtype) rfl (fun _ _ _ _ => rfl) fun _ => rfl

/-- The supremum of submodules that form a graded monoid is a subalgebra, and equal to the range of
`direct_sum.coe_alg_hom`. -/
theorem Submodule.supr_eq_to_submodule_range [AddMonoidₓ ι] [CommSemiringₓ S] [Semiringₓ R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] : (⨆ i, A i) = (DirectSum.coeAlgHom A).range.toSubmodule :=
  (Submodule.supr_eq_range_dfinsupp_lsum A).trans <| SetLike.coe_injective rfl

@[simp]
theorem DirectSum.coe_alg_hom_of [AddMonoidₓ ι] [CommSemiringₓ S] [Semiringₓ R] [Algebra S R] (A : ι → Submodule S R)
    [SetLike.GradedMonoid A] (i : ι) (x : A i) : DirectSum.coeAlgHom A (DirectSum.of (fun i => A i) i x) = x :=
  DirectSum.to_semiring_of _ rfl (fun _ _ _ _ => rfl) _ _

end DirectSum

section HomogeneousElement

theorem SetLike.is_homogeneous_zero_submodule [Zero ι] [Semiringₓ S] [AddCommMonoidₓ R] [Module S R]
    (A : ι → Submodule S R) : SetLike.IsHomogeneous A (0 : R) :=
  ⟨0, Submodule.zero_mem _⟩

theorem SetLike.IsHomogeneous.smul [CommSemiringₓ S] [Semiringₓ R] [Algebra S R] {A : ι → Submodule S R} {s : S} {r : R}
    (hr : SetLike.IsHomogeneous A r) : SetLike.IsHomogeneous A (s • r) :=
  let ⟨i, hi⟩ := hr
  ⟨i, Submodule.smul_mem _ _ hi⟩

end HomogeneousElement

