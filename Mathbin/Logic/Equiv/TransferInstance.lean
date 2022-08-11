/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Field.Basic
import Mathbin.Algebra.Group.TypeTags
import Mathbin.Logic.Equiv.Basic
import Mathbin.RingTheory.Ideal.LocalRing

/-!
# Transfer algebraic structures across `equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

## Tags

equiv, group, ring, field, module, algebra
-/


universe u v

variable {α : Type u} {β : Type v}

namespace Equivₓ

section Instances

variable (e : α ≃ β)

/-- Transfer `has_one` across an `equiv` -/
@[to_additive "Transfer `has_zero` across an `equiv`"]
protected def hasOne [One β] : One α :=
  ⟨e.symm 1⟩

@[to_additive]
theorem one_def [One β] : @One.one _ (Equivₓ.hasOne e) = e.symm 1 :=
  rfl

/-- Transfer `has_mul` across an `equiv` -/
@[to_additive "Transfer `has_add` across an `equiv`"]
protected def hasMul [Mul β] : Mul α :=
  ⟨fun x y => e.symm (e x * e y)⟩

@[to_additive]
theorem mul_def [Mul β] (x y : α) : @Mul.mul _ (Equivₓ.hasMul e) x y = e.symm (e x * e y) :=
  rfl

/-- Transfer `has_div` across an `equiv` -/
@[to_additive "Transfer `has_sub` across an `equiv`"]
protected def hasDiv [Div β] : Div α :=
  ⟨fun x y => e.symm (e x / e y)⟩

@[to_additive]
theorem div_def [Div β] (x y : α) : @Div.div _ (Equivₓ.hasDiv e) x y = e.symm (e x / e y) :=
  rfl

/-- Transfer `has_inv` across an `equiv` -/
@[to_additive "Transfer `has_neg` across an `equiv`"]
protected def hasInv [Inv β] : Inv α :=
  ⟨fun x => e.symm (e x)⁻¹⟩

@[to_additive]
theorem inv_def [Inv β] (x : α) : @Inv.inv _ (Equivₓ.hasInv e) x = e.symm (e x)⁻¹ :=
  rfl

/-- Transfer `has_smul` across an `equiv` -/
protected def hasSmul (R : Type _) [HasSmul R β] : HasSmul R α :=
  ⟨fun r x => e.symm (r • e x)⟩

theorem smul_def {R : Type _} [HasSmul R β] (r : R) (x : α) : @HasSmul.smul _ _ (e.HasSmul R) r x = e.symm (r • e x) :=
  rfl

/-- Transfer `has_pow` across an `equiv` -/
@[to_additive HasSmul]
protected def hasPow (N : Type _) [Pow β N] : Pow α N :=
  ⟨fun x n => e.symm (e x ^ n)⟩

theorem pow_def {N : Type _} [Pow β N] (n : N) (x : α) : @Pow.pow _ _ (e.HasPow N) x n = e.symm (e x ^ n) :=
  rfl

/-- An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β`
where the multiplicative structure on `α` is
the one obtained by transporting a multiplicative structure on `β` back along `e`.
-/
@[to_additive
      "An equivalence `e : α ≃ β` gives a additive equivalence `α ≃+ β`\nwhere the additive structure on `α` is\nthe one obtained by transporting an additive structure on `β` back along `e`."]
def mulEquiv (e : α ≃ β) [Mul β] : by
    let this := Equivₓ.hasMul e
    exact α ≃* β := by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        apply e.symm.injective
        simp
        rfl }

@[simp, to_additive]
theorem mul_equiv_apply (e : α ≃ β) [Mul β] (a : α) : (mulEquiv e) a = e a :=
  rfl

@[to_additive]
theorem mul_equiv_symm_apply (e : α ≃ β) [Mul β] (b : β) : by
    let this := Equivₓ.hasMul e
    exact (MulEquiv e).symm b = e.symm b := by
  intros
  rfl

/-- An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ringEquiv (e : α ≃ β) [Add β] [Mul β] : by
    let this := Equivₓ.hasAdd e
    let this := Equivₓ.hasMul e
    exact α ≃+* β := by
  intros
  exact
    { e with
      map_add' := fun x y => by
        apply e.symm.injective
        simp
        rfl,
      map_mul' := fun x y => by
        apply e.symm.injective
        simp
        rfl }

@[simp]
theorem ring_equiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : (ringEquiv e) a = e a :=
  rfl

theorem ring_equiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) : by
    let this := Equivₓ.hasAdd e
    let this := Equivₓ.hasMul e
    exact (RingEquiv e).symm b = e.symm b := by
  intros
  rfl

/-- Transfer `semigroup` across an `equiv` -/
@[to_additive "Transfer `add_semigroup` across an `equiv`"]
protected def semigroup [Semigroupₓ β] : Semigroupₓ α := by
  let mul := e.HasMul
  skip <;> apply e.injective.semigroup _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `semigroup_with_zero` across an `equiv` -/
protected def semigroupWithZero [SemigroupWithZeroₓ β] : SemigroupWithZeroₓ α := by
  let mul := e.HasMul
  let zero := e.HasZero
  skip <;> apply e.injective.semigroup_with_zero _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `comm_semigroup` across an `equiv` -/
@[to_additive "Transfer `add_comm_semigroup` across an `equiv`"]
protected def commSemigroup [CommSemigroupₓ β] : CommSemigroupₓ α := by
  let mul := e.HasMul
  skip <;> apply e.injective.comm_semigroup _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `mul_zero_class` across an `equiv` -/
protected def mulZeroClass [MulZeroClassₓ β] : MulZeroClassₓ α := by
  let zero := e.HasZero
  let mul := e.HasMul
  skip <;> apply e.injective.mul_zero_class _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `mul_one_class` across an `equiv` -/
@[to_additive "Transfer `add_zero_class` across an `equiv`"]
protected def mulOneClass [MulOneClassₓ β] : MulOneClassₓ α := by
  let one := e.HasOne
  let mul := e.HasMul
  skip <;> apply e.injective.mul_one_class _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `mul_zero_one_class` across an `equiv` -/
protected def mulZeroOneClass [MulZeroOneClassₓ β] : MulZeroOneClassₓ α := by
  let zero := e.HasZero
  let one := e.HasOne
  let mul := e.HasMul
  skip <;> apply e.injective.mul_zero_one_class _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `monoid` across an `equiv` -/
@[to_additive "Transfer `add_monoid` across an `equiv`"]
protected def monoid [Monoidₓ β] : Monoidₓ α := by
  let one := e.HasOne
  let mul := e.HasMul
  let pow := e.HasPow ℕ
  skip <;> apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `comm_monoid` across an `equiv` -/
@[to_additive "Transfer `add_comm_monoid` across an `equiv`"]
protected def commMonoid [CommMonoidₓ β] : CommMonoidₓ α := by
  let one := e.HasOne
  let mul := e.HasMul
  let pow := e.HasPow ℕ
  skip <;> apply e.injective.comm_monoid _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `group` across an `equiv` -/
@[to_additive "Transfer `add_group` across an `equiv`"]
protected def group [Groupₓ β] : Groupₓ α := by
  let one := e.HasOne
  let mul := e.HasMul
  let inv := e.HasInv
  let div := e.HasDiv
  let npow := e.HasPow ℕ
  let zpow := e.HasPow ℤ
  skip <;> apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `comm_group` across an `equiv` -/
@[to_additive "Transfer `add_comm_group` across an `equiv`"]
protected def commGroup [CommGroupₓ β] : CommGroupₓ α := by
  let one := e.HasOne
  let mul := e.HasMul
  let inv := e.HasInv
  let div := e.HasDiv
  let npow := e.HasPow ℕ
  let zpow := e.HasPow ℤ
  skip <;> apply e.injective.comm_group _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `non_unital_non_assoc_semiring` across an `equiv` -/
protected def nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiringₓ β] : NonUnitalNonAssocSemiringₓ α := by
  let zero := e.HasZero
  let add := e.HasAdd
  let mul := e.HasMul
  let nsmul := e.HasSmul ℕ
  skip <;> apply e.injective.non_unital_non_assoc_semiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `non_unital_semiring` across an `equiv` -/
protected def nonUnitalSemiring [NonUnitalSemiringₓ β] : NonUnitalSemiringₓ α := by
  let zero := e.HasZero
  let add := e.HasAdd
  let mul := e.HasMul
  let nsmul := e.HasSmul ℕ
  skip <;> apply e.injective.non_unital_semiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `add_monoid_with_one` across an `equiv` -/
protected def addMonoidWithOne [AddMonoidWithOneₓ β] : AddMonoidWithOneₓ α :=
  { e.AddMonoid, e.HasOne with natCast := fun n => e.symm n,
    nat_cast_zero :=
      show e.symm _ = _ by
        simp [← zero_def],
    nat_cast_succ := fun n =>
      show e.symm _ = e.symm (e (e.symm _) + _) by
        simp [← add_def, ← one_def] }

/-- Transfer `add_group_with_one` across an `equiv` -/
protected def addGroupWithOne [AddGroupWithOneₓ β] : AddGroupWithOneₓ α :=
  { e.AddMonoidWithOne, e.AddGroup with intCast := fun n => e.symm n,
    int_cast_of_nat := fun n => by
      rw [Int.cast_coe_nat] <;> rfl,
    int_cast_neg_succ_of_nat := fun n =>
      congr_arg e.symm <| (Int.cast_neg_succ_of_nat _).trans <| congr_arg _ (e.apply_symm_apply _).symm }

/-- Transfer `non_assoc_semiring` across an `equiv` -/
protected def nonAssocSemiring [NonAssocSemiringₓ β] : NonAssocSemiringₓ α := by
  let mul := e.HasMul
  let add_monoid_with_one := e.AddMonoidWithOne
  skip <;> apply e.injective.non_assoc_semiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `semiring` across an `equiv` -/
protected def semiring [Semiringₓ β] : Semiringₓ α := by
  let mul := e.HasMul
  let add_monoid_with_one := e.AddMonoidWithOne
  let npow := e.HasPow ℕ
  skip <;> apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `non_unital_comm_semiring` across an `equiv` -/
protected def nonUnitalCommSemiring [NonUnitalCommSemiring β] : NonUnitalCommSemiring α := by
  let zero := e.HasZero
  let add := e.HasAdd
  let mul := e.HasMul
  let nsmul := e.HasSmul ℕ
  skip <;> apply e.injective.non_unital_comm_semiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `comm_semiring` across an `equiv` -/
protected def commSemiring [CommSemiringₓ β] : CommSemiringₓ α := by
  let mul := e.HasMul
  let add_monoid_with_one := e.AddMonoidWithOne
  let npow := e.HasPow ℕ
  skip <;> apply e.injective.comm_semiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `non_unital_non_assoc_ring` across an `equiv` -/
protected def nonUnitalNonAssocRing [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing α := by
  let zero := e.HasZero
  let add := e.HasAdd
  let mul := e.HasMul
  let neg := e.HasNeg
  let sub := e.HasSub
  let nsmul := e.HasSmul ℕ
  let zsmul := e.HasSmul ℤ
  skip <;> apply e.injective.non_unital_non_assoc_ring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `non_unital_ring` across an `equiv` -/
protected def nonUnitalRing [NonUnitalRing β] : NonUnitalRing α := by
  let zero := e.HasZero
  let add := e.HasAdd
  let mul := e.HasMul
  let neg := e.HasNeg
  let sub := e.HasSub
  let nsmul := e.HasSmul ℕ
  let zsmul := e.HasSmul ℤ
  skip <;> apply e.injective.non_unital_ring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `non_assoc_ring` across an `equiv` -/
protected def nonAssocRing [NonAssocRing β] : NonAssocRing α := by
  let add_group_with_one := e.AddGroupWithOne
  let mul := e.HasMul
  skip <;> apply e.injective.non_assoc_ring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `ring` across an `equiv` -/
protected def ring [Ringₓ β] : Ringₓ α := by
  let mul := e.HasMul
  let add_group_with_one := e.AddGroupWithOne
  let npow := e.HasPow ℕ
  skip <;> apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `non_unital_comm_ring` across an `equiv` -/
protected def nonUnitalCommRing [NonUnitalCommRing β] : NonUnitalCommRing α := by
  let zero := e.HasZero
  let add := e.HasAdd
  let mul := e.HasMul
  let neg := e.HasNeg
  let sub := e.HasSub
  let nsmul := e.HasSmul ℕ
  let zsmul := e.HasSmul ℤ
  skip <;> apply e.injective.non_unital_comm_ring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `comm_ring` across an `equiv` -/
protected def commRing [CommRingₓ β] : CommRingₓ α := by
  let mul := e.HasMul
  let add_group_with_one := e.AddGroupWithOne
  let npow := e.HasPow ℕ
  skip <;> apply e.injective.comm_ring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `nontrivial` across an `equiv` -/
protected theorem nontrivial [Nontrivial β] : Nontrivial α :=
  e.Surjective.Nontrivial

/-- Transfer `is_domain` across an `equiv` -/
protected theorem is_domain [Ringₓ α] [Ringₓ β] [IsDomain β] (e : α ≃+* β) : IsDomain α :=
  Function.Injective.is_domain e.toRingHom e.Injective

/-- Transfer `division_ring` across an `equiv` -/
protected def divisionRing [DivisionRing β] : DivisionRing α := by
  let add_group_with_one := e.AddGroupWithOne
  let mul := e.HasMul
  let inv := e.HasInv
  let div := e.HasDiv
  let mul := e.HasMul
  let npow := e.HasPow ℕ
  let zpow := e.HasPow ℤ
  skip <;> apply e.injective.division_ring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `field` across an `equiv` -/
protected def field [Field β] : Field α := by
  let add_group_with_one := e.AddGroupWithOne
  let mul := e.HasMul
  let neg := e.HasNeg
  let inv := e.HasInv
  let div := e.HasDiv
  let mul := e.HasMul
  let npow := e.HasPow ℕ
  let zpow := e.HasPow ℤ
  skip <;> apply e.injective.field _ <;> intros <;> exact e.apply_symm_apply _

section R

variable (R : Type _)

include R

section

variable [Monoidₓ R]

/-- Transfer `mul_action` across an `equiv` -/
protected def mulAction (e : α ≃ β) [MulAction R β] : MulAction R α :=
  { e.HasSmul R with
    one_smul := by
      simp [← smul_def],
    mul_smul := by
      simp [← smul_def, ← mul_smul] }

/-- Transfer `distrib_mul_action` across an `equiv` -/
protected def distribMulAction (e : α ≃ β) [AddCommMonoidₓ β] : by
    let this := Equivₓ.addCommMonoid e
    exact ∀ [DistribMulAction R β], DistribMulAction R α := by
  intros
  let this := Equivₓ.addCommMonoid e
  exact
    ({ Equivₓ.mulAction R e with
      smul_zero := by
        simp [← zero_def, ← smul_def],
      smul_add := by
        simp [← add_def, ← smul_def, ← smul_add] } :
      DistribMulAction R α)

end

section

variable [Semiringₓ R]

/-- Transfer `module` across an `equiv` -/
protected def module (e : α ≃ β) [AddCommMonoidₓ β] : by
    let this := Equivₓ.addCommMonoid e
    exact ∀ [Module R β], Module R α := by
  intros
  exact
    ({ Equivₓ.distribMulAction R e with
      zero_smul := by
        simp [← zero_def, ← smul_def],
      add_smul := by
        simp [← add_def, ← smul_def, ← add_smul] } :
      Module R α)

/-- An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linearEquiv (e : α ≃ β) [AddCommMonoidₓ β] [Module R β] : by
    let this := Equivₓ.addCommMonoid e
    let this := Equivₓ.module R e
    exact α ≃ₗ[R] β := by
  intros
  exact
    { Equivₓ.addEquiv e with
      map_smul' := fun r x => by
        apply e.symm.injective
        simp
        rfl }

end

section

variable [CommSemiringₓ R]

/-- Transfer `algebra` across an `equiv` -/
protected def algebra (e : α ≃ β) [Semiringₓ β] : by
    let this := Equivₓ.semiring e
    exact ∀ [Algebra R β], Algebra R α := by
  intros
  fapply RingHom.toAlgebra'
  · exact ((RingEquiv e).symm : β →+* α).comp (algebraMap R β)
    
  · intro r x
    simp only [← Function.comp_app, ← RingHom.coe_comp]
    have p := ring_equiv_symm_apply e
    dsimp'  at p
    erw [p]
    clear p
    apply (RingEquiv e).Injective
    simp only [← (RingEquiv e).map_mul]
    simp [← Algebra.commutes]
    

/-- An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def algEquiv (e : α ≃ β) [Semiringₓ β] [Algebra R β] : by
    let this := Equivₓ.semiring e
    let this := Equivₓ.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equivₓ.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp
        rfl }

end

end R

end Instances

end Equivₓ

namespace RingEquiv

protected theorem local_ring {A B : Type _} [CommSemiringₓ A] [LocalRing A] [CommSemiringₓ B] (e : A ≃+* B) :
    LocalRing B := by
  have := e.symm.to_equiv.nontrivial
  exact LocalRing.of_surjective (e : A →+* B) e.surjective

end RingEquiv

