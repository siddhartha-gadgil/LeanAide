/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.Algebra.GradedMonoid
import Mathbin.Algebra.DirectSum.Basic
import Mathbin.Algebra.BigOperators.Pi

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The typeclasses are:

* `direct_sum.gnon_unital_non_assoc_semiring A`
* `direct_sum.gsemiring A`
* `direct_sum.gring A`
* `direct_sum.gcomm_semiring A`
* `direct_sum.gcomm_ring A`

Respectively, these imbue the external direct sum `⨁ i, A i` with:

* `direct_sum.non_unital_non_assoc_semiring`, `direct_sum.non_unital_non_assoc_ring`
* `direct_sum.semiring`
* `direct_sum.ring`
* `direct_sum.comm_semiring`
* `direct_sum.comm_ring`

the base ring `A 0` with:

* `direct_sum.grade_zero.non_unital_non_assoc_semiring`,
  `direct_sum.grade_zero.non_unital_non_assoc_ring`
* `direct_sum.grade_zero.semiring`
* `direct_sum.grade_zero.ring`
* `direct_sum.grade_zero.comm_semiring`
* `direct_sum.grade_zero.comm_ring`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* `direct_sum.grade_zero.has_smul (A 0)`, `direct_sum.grade_zero.smul_with_zero (A 0)`
* `direct_sum.grade_zero.module (A 0)`
* (nothing)
* (nothing)
* (nothing)

Note that in the presence of these instances, `⨁ i, A i` itself inherits an `A 0`-action.

`direct_sum.of_zero_ring_hom : A 0 →+* ⨁ i, A i` provides `direct_sum.of A 0` as a ring
homomorphism.

`direct_sum.to_semiring` extends `direct_sum.to_add_monoid` to produce a `ring_hom`.

## Direct sums of subobjects

Additionally, this module provides helper functions to construct `gsemiring` and `gcomm_semiring`
instances for:

* `A : ι → submonoid S`:
  `direct_sum.gsemiring.of_add_submonoids`, `direct_sum.gcomm_semiring.of_add_submonoids`.
* `A : ι → subgroup S`:
  `direct_sum.gsemiring.of_add_subgroups`, `direct_sum.gcomm_semiring.of_add_subgroups`.
* `A : ι → submodule S`:
  `direct_sum.gsemiring.of_submodules`, `direct_sum.gcomm_semiring.of_submodules`.

If `complete_lattice.independent (set.range A)`, these provide a gradation of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

graded ring, filtered ring, direct sum, add_submonoid
-/


variable {ι : Type _} [DecidableEq ι]

namespace DirectSum

open DirectSum

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type _)

/-- A graded version of `non_unital_non_assoc_semiring`. -/
class GnonUnitalNonAssocSemiring [Add ι] [∀ i, AddCommMonoidₓ (A i)] extends GradedMonoid.GhasMul A where
  mul_zero : ∀ {i j} (a : A i), mul a (0 : A j) = 0
  zero_mul : ∀ {i j} (b : A j), mul (0 : A i) b = 0
  mul_add : ∀ {i j} (a : A i) (b c : A j), mul a (b + c) = mul a b + mul a c
  add_mul : ∀ {i j} (a b : A i) (c : A j), mul (a + b) c = mul a c + mul b c

end Defs

section Defs

variable (A : ι → Type _)

/-- A graded version of `semiring`. -/
class Gsemiring [AddMonoidₓ ι] [∀ i, AddCommMonoidₓ (A i)] extends GnonUnitalNonAssocSemiring A,
  GradedMonoid.Gmonoid A where
  natCast : ℕ → A 0
  nat_cast_zero : nat_cast 0 = 0
  nat_cast_succ : ∀ n : ℕ, nat_cast (n + 1) = nat_cast n + GradedMonoid.GhasOne.one

/-- A graded version of `comm_semiring`. -/
class GcommSemiring [AddCommMonoidₓ ι] [∀ i, AddCommMonoidₓ (A i)] extends Gsemiring A, GradedMonoid.GcommMonoid A

/-- A graded version of `ring`. -/
class Gring [AddMonoidₓ ι] [∀ i, AddCommGroupₓ (A i)] extends Gsemiring A where
  intCast : ℤ → A 0
  int_cast_of_nat : ∀ n : ℕ, int_cast n = nat_cast n
  int_cast_neg_succ_of_nat : ∀ n : ℕ, int_cast (-(n + 1 : ℕ)) = -nat_cast (n + 1 : ℕ)

/-- A graded version of `comm_ring`. -/
class GcommRing [AddCommMonoidₓ ι] [∀ i, AddCommGroupₓ (A i)] extends Gring A, GcommSemiring A

end Defs

theorem of_eq_of_graded_monoid_eq {A : ι → Type _} [∀ i : ι, AddCommMonoidₓ (A i)] {i j : ι} {a : A i} {b : A j}
    (h : GradedMonoid.mk i a = GradedMonoid.mk j b) : DirectSum.of A i a = DirectSum.of A j b :=
  Dfinsupp.single_eq_of_sigma_eq h

variable (A : ι → Type _)

/-! ### Instances for `⨁ i, A i` -/


section One

variable [Zero ι] [GradedMonoid.GhasOne A] [∀ i, AddCommMonoidₓ (A i)]

instance : One (⨁ i, A i) where one := DirectSum.of (fun i => A i) 0 GradedMonoid.GhasOne.one

end One

section Mul

variable [Add ι] [∀ i, AddCommMonoidₓ (A i)] [GnonUnitalNonAssocSemiring A]

open AddMonoidHom (flip_apply coe_comp comp_hom_apply_apply)

/-- The piecewise multiplication from the `has_mul` instance, as a bundled homomorphism. -/
@[simps]
def gmulHom {i j} : A i →+ A j →+ A (i + j) where
  toFun := fun a =>
    { toFun := fun b => GradedMonoid.GhasMul.mul a b, map_zero' := GnonUnitalNonAssocSemiring.mul_zero _,
      map_add' := GnonUnitalNonAssocSemiring.mul_add _ }
  map_zero' := AddMonoidHom.ext fun a => GnonUnitalNonAssocSemiring.zero_mul a
  map_add' := fun a₁ a₂ => AddMonoidHom.ext fun b => GnonUnitalNonAssocSemiring.add_mul _ _ _

/-- The multiplication from the `has_mul` instance, as a bundled homomorphism. -/
def mulHom : (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
  DirectSum.toAddMonoid fun i =>
    AddMonoidHom.flip <|
      DirectSum.toAddMonoid fun j => AddMonoidHom.flip <| (DirectSum.of A _).compHom.comp <| gmulHom A

instance : NonUnitalNonAssocSemiringₓ (⨁ i, A i) :=
  { DirectSum.addCommMonoid _ _ with mul := fun a b => mulHom A a b, zero := 0, add := (· + ·),
    zero_mul := fun a => by
      simp only [← AddMonoidHom.map_zero, ← AddMonoidHom.zero_apply],
    mul_zero := fun a => by
      simp only [← AddMonoidHom.map_zero],
    left_distrib := fun a b c => by
      simp only [← AddMonoidHom.map_add],
    right_distrib := fun a b c => by
      simp only [← AddMonoidHom.map_add, ← AddMonoidHom.add_apply] }

variable {A}

theorem mul_hom_of_of {i j} (a : A i) (b : A j) :
    mulHom A (of _ i a) (of _ j b) = of _ (i + j) (GradedMonoid.GhasMul.mul a b) := by
  unfold MulHom
  rw [to_add_monoid_of, flip_apply, to_add_monoid_of, flip_apply, coe_comp, Function.comp_app, comp_hom_apply_apply,
    coe_comp, Function.comp_app, gmul_hom_apply_apply]

theorem of_mul_of {i j} (a : A i) (b : A j) : of _ i a * of _ j b = of _ (i + j) (GradedMonoid.GhasMul.mul a b) :=
  mul_hom_of_of a b

end Mul

section Semiringₓ

variable [∀ i, AddCommMonoidₓ (A i)] [AddMonoidₓ ι] [Gsemiring A]

open AddMonoidHom (flipHom coe_comp comp_hom_apply_apply flip_apply flip_hom_apply)

private theorem one_mul (x : ⨁ i, A i) : 1 * x = x := by
  suffices mulHom A 1 = AddMonoidHom.id (⨁ i, A i) from AddMonoidHom.congr_fun this x
  apply add_hom_ext
  intro i xi
  unfold One.one
  rw [mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (one_mulₓ <| GradedMonoid.mk i xi)

private theorem mul_one (x : ⨁ i, A i) : x * 1 = x := by
  suffices (mulHom A).flip 1 = AddMonoidHom.id (⨁ i, A i) from AddMonoidHom.congr_fun this x
  apply add_hom_ext
  intro i xi
  unfold One.one
  rw [flip_apply, mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (mul_oneₓ <| GradedMonoid.mk i xi)

private theorem mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) := by
  suffices
    (-- `λ a b c, a * b * c` as a bundled hom
              mulHom
              A).compHom.comp
        (mulHom A) =
      (AddMonoidHom.compHom flipHom <|
          (-- `λ a b c, a * (b * c)` as a bundled hom
                    mulHom
                    A).flip.compHom.comp
            (mulHom A)).flip
    from AddMonoidHom.congr_fun (AddMonoidHom.congr_fun (AddMonoidHom.congr_fun this a) b) c
  ext ai ax bi bx ci cx : 6
  dsimp' only [← coe_comp, ← Function.comp_app, ← comp_hom_apply_apply, ← flip_apply, ← flip_hom_apply]
  rw [mul_hom_of_of, mul_hom_of_of, mul_hom_of_of, mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (mul_assoc (GradedMonoid.mk ai ax) ⟨bi, bx⟩ ⟨ci, cx⟩)

/-- The `semiring` structure derived from `gsemiring A`. -/
instance semiring : Semiringₓ (⨁ i, A i) :=
  { DirectSum.nonUnitalNonAssocSemiring _ with one := 1, mul := (· * ·), zero := 0, add := (· + ·),
    one_mul := one_mulₓ A, mul_one := mul_oneₓ A, mul_assoc := mul_assoc A,
    natCast := fun n => of _ _ (Gsemiring.natCast n),
    nat_cast_zero := by
      rw [gsemiring.nat_cast_zero, map_zero],
    nat_cast_succ := fun n => by
      rw [gsemiring.nat_cast_succ, map_add]
      rfl }

theorem of_pow {i} (a : A i) (n : ℕ) : of _ i a ^ n = of _ (n • i) (GradedMonoid.Gmonoid.gnpow _ a) := by
  induction' n with n
  · exact of_eq_of_graded_monoid_eq (pow_zeroₓ <| GradedMonoid.mk _ a).symm
    
  · rw [pow_succₓ, n_ih, of_mul_of]
    exact of_eq_of_graded_monoid_eq (pow_succₓ (GradedMonoid.mk _ a) n).symm
    

theorem of_list_dprod {α} (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    of A _ (l.dprod fι fA) = (l.map fun a => of A (fι a) (fA a)).Prod := by
  induction l
  · simp only [← List.map_nil, ← List.prod_nil, ← List.dprod_nil]
    rfl
    
  · simp only [← List.map_cons, ← List.prod_cons, ← List.dprod_cons, l_ih, ← DirectSum.of_mul_of]
    rfl
    

theorem list_prod_of_fn_of_eq_dprod (n : ℕ) (fι : Finₓ n → ι) (fA : ∀ a, A (fι a)) :
    (List.ofFnₓ fun a => of A (fι a) (fA a)).Prod = of A _ ((List.finRange n).dprod fι fA) := by
  rw [List.of_fn_eq_map, of_list_dprod]

open BigOperators

/-- A heavily unfolded version of the definition of multiplication -/
theorem mul_eq_sum_support_ghas_mul [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (a a' : ⨁ i, A i) :
    a * a' =
      ∑ ij : ι × ι in (Dfinsupp.support a).product (Dfinsupp.support a'),
        DirectSum.of _ _ (GradedMonoid.GhasMul.mul (a ij.fst) (a' ij.snd)) :=
  by
  change DirectSum.mulHom _ a a' = _
  dsimp' [← DirectSum.mulHom, ← DirectSum.toAddMonoid, ← Dfinsupp.lift_add_hom_apply]
  simp only [← Dfinsupp.sum_add_hom_apply, ← Dfinsupp.sum, ← Dfinsupp.finset_sum_apply, ← AddMonoidHom.coe_finset_sum, ←
    Finset.sum_apply, ← AddMonoidHom.flip_apply, ← AddMonoidHom.comp_hom_apply_apply, ← AddMonoidHom.comp_apply, ←
    DirectSum.gmul_hom_apply_apply]
  rw [Finset.sum_product]

end Semiringₓ

section CommSemiringₓ

variable [∀ i, AddCommMonoidₓ (A i)] [AddCommMonoidₓ ι] [GcommSemiring A]

private theorem mul_comm (a b : ⨁ i, A i) : a * b = b * a := by
  suffices mulHom A = (mulHom A).flip from AddMonoidHom.congr_fun (AddMonoidHom.congr_fun this a) b
  apply add_hom_ext
  intro ai ax
  apply add_hom_ext
  intro bi bx
  rw [AddMonoidHom.flip_apply, mul_hom_of_of, mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (gcomm_semiring.mul_comm ⟨ai, ax⟩ ⟨bi, bx⟩)

/-- The `comm_semiring` structure derived from `gcomm_semiring A`. -/
instance commSemiring : CommSemiringₓ (⨁ i, A i) :=
  { DirectSum.semiring _ with one := 1, mul := (· * ·), zero := 0, add := (· + ·), mul_comm := mul_comm A }

end CommSemiringₓ

section NonUnitalNonAssocRing

variable [∀ i, AddCommGroupₓ (A i)] [Add ι] [GnonUnitalNonAssocSemiring A]

/-- The `ring` derived from `gsemiring A`. -/
instance nonAssocRing : NonUnitalNonAssocRing (⨁ i, A i) :=
  { DirectSum.nonUnitalNonAssocSemiring _, DirectSum.addCommGroup _ with mul := (· * ·), zero := 0, add := (· + ·),
    neg := Neg.neg }

end NonUnitalNonAssocRing

section Ringₓ

variable [∀ i, AddCommGroupₓ (A i)] [AddMonoidₓ ι] [Gring A]

/-- The `ring` derived from `gsemiring A`. -/
instance ring : Ringₓ (⨁ i, A i) :=
  { DirectSum.semiring _, DirectSum.addCommGroup _ with one := 1, mul := (· * ·), zero := 0, add := (· + ·),
    neg := Neg.neg, intCast := fun z => of _ _ (Gring.intCast z),
    int_cast_of_nat := fun z => congr_arg _ <| Gring.int_cast_of_nat _,
    int_cast_neg_succ_of_nat := fun z => (congr_arg _ <| Gring.int_cast_neg_succ_of_nat _).trans (map_neg _ _) }

end Ringₓ

section CommRingₓ

variable [∀ i, AddCommGroupₓ (A i)] [AddCommMonoidₓ ι] [GcommRing A]

/-- The `comm_ring` derived from `gcomm_semiring A`. -/
instance commRing : CommRingₓ (⨁ i, A i) :=
  { DirectSum.ring _, DirectSum.commSemiring _ with one := 1, mul := (· * ·), zero := 0, add := (· + ·),
    neg := Neg.neg }

end CommRingₓ

/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

section One

variable [Zero ι] [GradedMonoid.GhasOne A] [∀ i, AddCommMonoidₓ (A i)]

@[simp]
theorem of_zero_one : of _ 0 (1 : A 0) = 1 :=
  rfl

end One

section Mul

variable [AddZeroClassₓ ι] [∀ i, AddCommMonoidₓ (A i)] [GnonUnitalNonAssocSemiring A]

@[simp]
theorem of_zero_smul {i} (a : A 0) (b : A i) : of _ _ (a • b) = of _ _ a * of _ _ b :=
  (of_eq_of_graded_monoid_eq (GradedMonoid.mk_zero_smul a b)).trans (of_mul_of _ _).symm

@[simp]
theorem of_zero_mul (a b : A 0) : of _ 0 (a * b) = of _ 0 a * of _ 0 b :=
  of_zero_smul A a b

instance GradeZero.nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiringₓ (A 0) :=
  Function.Injective.nonUnitalNonAssocSemiring (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of A 0).map_add
    (of_zero_mul A) fun x n => Dfinsupp.single_smul n x

instance GradeZero.smulWithZero (i : ι) : SmulWithZero (A 0) (A i) := by
  let this := SmulWithZero.compHom (⨁ i, A i) (of A 0).toZeroHom
  refine' dfinsupp.single_injective.smul_with_zero (of A i).toZeroHom (of_zero_smul A)

end Mul

section Semiringₓ

variable [∀ i, AddCommMonoidₓ (A i)] [AddMonoidₓ ι] [Gsemiring A]

@[simp]
theorem of_zero_pow (a : A 0) : ∀ n : ℕ, of _ 0 (a ^ n) = of _ 0 a ^ n
  | 0 => by
    rw [pow_zeroₓ, pow_zeroₓ, DirectSum.of_zero_one]
  | n + 1 => by
    rw [pow_succₓ, pow_succₓ, of_zero_mul, of_zero_pow]

instance : HasNatCast (A 0) :=
  ⟨Gsemiring.natCast⟩

@[simp]
theorem of_nat_cast (n : ℕ) : of A 0 n = n :=
  rfl

/-- The `semiring` structure derived from `gsemiring A`. -/
instance GradeZero.semiring : Semiringₓ (A 0) :=
  Function.Injective.semiring (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A) (of A 0).map_add
    (of_zero_mul A) (of A 0).map_nsmul (fun x n => of_zero_pow _ _ _) (of_nat_cast A)

/-- `of A 0` is a `ring_hom`, using the `direct_sum.grade_zero.semiring` structure. -/
def ofZeroRingHom : A 0 →+* ⨁ i, A i :=
  { of _ 0 with map_one' := of_zero_one A, map_mul' := of_zero_mul A }

/-- Each grade `A i` derives a `A 0`-module structure from `gsemiring A`. Note that this results
in an overall `module (A 0) (⨁ i, A i)` structure via `direct_sum.module`.
-/
instance GradeZero.module {i} : Module (A 0) (A i) := by
  let this := Module.compHom (⨁ i, A i) (of_zero_ring_hom A)
  exact dfinsupp.single_injective.module (A 0) (of A i) fun a => of_zero_smul A a

end Semiringₓ

section CommSemiringₓ

variable [∀ i, AddCommMonoidₓ (A i)] [AddCommMonoidₓ ι] [GcommSemiring A]

/-- The `comm_semiring` structure derived from `gcomm_semiring A`. -/
instance GradeZero.commSemiring : CommSemiringₓ (A 0) :=
  Function.Injective.commSemiring (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A) (of A 0).map_add
    (of_zero_mul A) (fun x n => Dfinsupp.single_smul n x) (fun x n => of_zero_pow _ _ _) (of_nat_cast A)

end CommSemiringₓ

section Ringₓ

variable [∀ i, AddCommGroupₓ (A i)] [AddZeroClassₓ ι] [GnonUnitalNonAssocSemiring A]

/-- The `non_unital_non_assoc_ring` derived from `gnon_unital_non_assoc_semiring A`. -/
instance GradeZero.nonUnitalNonAssocRing : NonUnitalNonAssocRing (A 0) :=
  Function.Injective.nonUnitalNonAssocRing (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of A 0).map_add
    (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub
    (fun x n => by
      let this : ∀ i, DistribMulAction ℕ (A i) := fun i => inferInstance
      exact Dfinsupp.single_smul n x)
    fun x n => by
    let this : ∀ i, DistribMulAction ℤ (A i) := fun i => inferInstance
    exact Dfinsupp.single_smul n x

end Ringₓ

section Ringₓ

variable [∀ i, AddCommGroupₓ (A i)] [AddMonoidₓ ι] [Gring A]

instance : HasIntCast (A 0) :=
  ⟨Gring.intCast⟩

@[simp]
theorem of_int_cast (n : ℤ) : of A 0 n = n :=
  rfl

/-- The `ring` derived from `gsemiring A`. -/
instance GradeZero.ring : Ringₓ (A 0) :=
  Function.Injective.ring (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A) (of A 0).map_add
    (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub
    (fun x n => by
      let this : ∀ i, DistribMulAction ℕ (A i) := fun i => inferInstance
      exact Dfinsupp.single_smul n x)
    (fun x n => by
      let this : ∀ i, DistribMulAction ℤ (A i) := fun i => inferInstance
      exact Dfinsupp.single_smul n x)
    (fun x n => of_zero_pow _ _ _) (of_nat_cast A) (of_int_cast A)

end Ringₓ

section CommRingₓ

variable [∀ i, AddCommGroupₓ (A i)] [AddCommMonoidₓ ι] [GcommRing A]

/-- The `comm_ring` derived from `gcomm_semiring A`. -/
instance GradeZero.commRing : CommRingₓ (A 0) :=
  Function.Injective.commRing (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A) (of A 0).map_add
    (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub
    (fun x n => by
      let this : ∀ i, DistribMulAction ℕ (A i) := fun i => inferInstance
      exact Dfinsupp.single_smul n x)
    (fun x n => by
      let this : ∀ i, DistribMulAction ℤ (A i) := fun i => inferInstance
      exact Dfinsupp.single_smul n x)
    (fun x n => of_zero_pow _ _ _) (of_nat_cast A) (of_int_cast A)

end CommRingₓ

end GradeZero

section ToSemiring

variable {R : Type _} [∀ i, AddCommMonoidₓ (A i)] [AddMonoidₓ ι] [Gsemiring A] [Semiringₓ R]

variable {A}

/-- If two ring homomorphisms from `⨁ i, A i` are equal on each `of A i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem ring_hom_ext' ⦃F G : (⨁ i, A i) →+* R⦄ (h : ∀ i, (↑F : _ →+ R).comp (of A i) = (↑G : _ →+ R).comp (of A i)) :
    F = G :=
  RingHom.coe_add_monoid_hom_injective <| DirectSum.add_hom_ext' h

/-- Two `ring_hom`s out of a direct sum are equal if they agree on the generators. -/
theorem ring_hom_ext ⦃f g : (⨁ i, A i) →+* R⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) : f = g :=
  ring_hom_ext' fun i => AddMonoidHom.ext <| h i

/-- A family of `add_monoid_hom`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
describes a `ring_hom`s on `⨁ i, A i`. This is a stronger version of `direct_sum.to_monoid`.

Of particular interest is the case when `A i` are bundled subojects, `f` is the family of
coercions such as `add_submonoid.subtype (A i)`, and the `[gsemiring A]` structure originates from
`direct_sum.gsemiring.of_add_submonoids`, in which case the proofs about `ghas_one` and `ghas_mul`
can be discharged by `rfl`. -/
@[simps]
def toSemiring (f : ∀ i, A i →+ R) (hone : f _ GradedMonoid.GhasOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GhasMul.mul ai aj) = f _ ai * f _ aj) : (⨁ i, A i) →+* R :=
  { toAddMonoid f with toFun := toAddMonoid f,
    map_one' := by
      change (to_add_monoid f) (of _ 0 _) = 1
      rw [to_add_monoid_of]
      exact hone,
    map_mul' := by
      rw [(to_add_monoid f).map_mul_iff]
      ext xi xv yi yv : 4
      show to_add_monoid f (of A xi xv * of A yi yv) = to_add_monoid f (of A xi xv) * to_add_monoid f (of A yi yv)
      rw [of_mul_of, to_add_monoid_of, to_add_monoid_of, to_add_monoid_of]
      exact hmul _ _ }

@[simp]
theorem to_semiring_of (f : ∀ i, A i →+ R) (hone hmul) (i : ι) (x : A i) : toSemiring f hone hmul (of _ i x) = f _ x :=
  to_add_monoid_of f i x

@[simp]
theorem to_semiring_coe_add_monoid_hom (f : ∀ i, A i →+ R) (hone hmul) :
    (toSemiring f hone hmul : (⨁ i, A i) →+ R) = toAddMonoid f :=
  rfl

/-- Families of `add_monoid_hom`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
are isomorphic to `ring_hom`s on `⨁ i, A i`. This is a stronger version of `dfinsupp.lift_add_hom`.
-/
@[simps]
def liftRingHom :
    { f : ∀ {i}, A i →+ R //
        f GradedMonoid.GhasOne.one = 1 ∧
          ∀ {i j} (ai : A i) (aj : A j), f (GradedMonoid.GhasMul.mul ai aj) = f ai * f aj } ≃
      ((⨁ i, A i) →+* R) where
  toFun := fun f => toSemiring f.1 f.2.1 f.2.2
  invFun := fun F =>
    ⟨fun i => (F : (⨁ i, A i) →+ R).comp (of _ i), by
      simp only [← AddMonoidHom.comp_apply, ← RingHom.coe_add_monoid_hom]
      rw [← F.map_one]
      rfl, fun i j ai aj => by
      simp only [← AddMonoidHom.comp_apply, ← RingHom.coe_add_monoid_hom]
      rw [← F.map_mul, of_mul_of]⟩
  left_inv := fun f => by
    ext xi xv
    exact to_add_monoid_of f.1 xi xv
  right_inv := fun F => by
    apply RingHom.coe_add_monoid_hom_injective
    ext xi xv
    simp only [← RingHom.coe_add_monoid_hom_mk, ← DirectSum.to_add_monoid_of, ← AddMonoidHom.mk_coe, ←
      AddMonoidHom.comp_apply, ← to_semiring_coe_add_monoid_hom]

end ToSemiring

end DirectSum

/-! ### Concrete instances -/


section Uniform

variable (ι)

/-- A direct sum of copies of a `semiring` inherits the multiplication structure. -/
instance NonUnitalNonAssocSemiringₓ.directSumGnonUnitalNonAssocSemiring {R : Type _} [AddMonoidₓ ι]
    [NonUnitalNonAssocSemiringₓ R] : DirectSum.GnonUnitalNonAssocSemiring fun i : ι => R :=
  { Mul.ghasMul ι with mul_zero := fun i j => mul_zero, zero_mul := fun i j => zero_mul, mul_add := fun i j => mul_addₓ,
    add_mul := fun i j => add_mulₓ }

/-- A direct sum of copies of a `semiring` inherits the multiplication structure. -/
instance Semiringₓ.directSumGsemiring {R : Type _} [AddMonoidₓ ι] [Semiringₓ R] : DirectSum.Gsemiring fun i : ι => R :=
  { NonUnitalNonAssocSemiringₓ.directSumGnonUnitalNonAssocSemiring ι, Monoidₓ.gmonoid ι with natCast := fun n => n,
    nat_cast_zero := Nat.cast_zeroₓ, nat_cast_succ := Nat.cast_succₓ }

open DirectSum

-- To check `has_mul.ghas_mul_mul` matches
example {R : Type _} [AddMonoidₓ ι] [Semiringₓ R] (i j : ι) (a b : R) :
    (DirectSum.of _ i a * DirectSum.of _ j b : ⨁ i, R) = DirectSum.of _ (i + j) (a * b) := by
  rw [DirectSum.of_mul_of, Mul.ghas_mul_mul]

/-- A direct sum of copies of a `comm_semiring` inherits the commutative multiplication structure.
-/
instance CommSemiringₓ.directSumGcommSemiring {R : Type _} [AddCommMonoidₓ ι] [CommSemiringₓ R] :
    DirectSum.GcommSemiring fun i : ι => R :=
  { CommMonoidₓ.gcommMonoid ι, Semiringₓ.directSumGsemiring ι with }

end Uniform

