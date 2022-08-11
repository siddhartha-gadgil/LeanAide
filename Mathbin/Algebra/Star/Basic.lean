/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Tactic.ApplyFun
import Mathbin.Algebra.Field.Opposite
import Mathbin.Algebra.FieldPower
import Mathbin.Algebra.Ring.Aut
import Mathbin.GroupTheory.GroupAction.Units
import Mathbin.GroupTheory.GroupAction.Opposite
import Mathbin.Algebra.Ring.CompTypeclasses

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

We also define the class `star_ordered_ring R`, which says that the order on `R` respects the
star operation, i.e. an element `r` is nonnegative iff there exists an `s` such that
`r = star s * s`.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.

## TODO

* In a Banach star algebra without a well-defined square root, the natural ordering is given by the
positive cone which is the closure of the sums of elements `star r * r`. A weaker version of
`star_ordered_ring` could be defined for this case. Note that the current definition has the
advantage of not requiring a topology.
-/


universe u v

open MulOpposite

/-- Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class HasStar (R : Type u) where
  star : R → R

variable {R : Type u}

export HasStar (star)

/-- A star operation (e.g. complex conjugate).
-/
add_decl_doc star

/-- Typeclass for a star operation with is involutive.
-/
class HasInvolutiveStar (R : Type u) extends HasStar R where
  star_involutive : Function.Involutive star

export HasInvolutiveStar (star_involutive)

@[simp]
theorem star_star [HasInvolutiveStar R] (r : R) : star (star r) = r :=
  star_involutive _

theorem star_injective [HasInvolutiveStar R] : Function.Injective (star : R → R) :=
  star_involutive.Injective

/-- `star` as an equivalence when it is involutive. -/
protected def Equivₓ.star [HasInvolutiveStar R] : Equivₓ.Perm R :=
  star_involutive.toPerm _

theorem eq_star_of_eq_star [HasInvolutiveStar R] {r s : R} (h : r = star s) : s = star r := by
  simp [← h]

theorem eq_star_iff_eq_star [HasInvolutiveStar R] {r s : R} : r = star s ↔ s = star r :=
  ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩

theorem star_eq_iff_star_eq [HasInvolutiveStar R] {r s : R} : star r = s ↔ star s = r :=
  eq_comm.trans <| eq_star_iff_eq_star.trans eq_comm

/-- Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
class HasTrivialStar (R : Type u) [HasStar R] : Prop where
  star_trivial : ∀ r : R, star r = r

export HasTrivialStar (star_trivial)

attribute [simp] star_trivial

/-- A `*`-semigroup is a semigroup `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class StarSemigroup (R : Type u) [Semigroupₓ R] extends HasInvolutiveStar R where
  star_mul : ∀ r s : R, star (r * s) = star s * star r

export StarSemigroup (star_mul)

attribute [simp] star_mul

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp]
theorem star_mul' [CommSemigroupₓ R] [StarSemigroup R] (x y : R) : star (x * y) = star x * star y :=
  (star_mul x y).trans (mul_comm _ _)

/-- `star` as an `mul_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starMulEquiv [Semigroupₓ R] [StarSemigroup R] : R ≃* Rᵐᵒᵖ :=
  { (HasInvolutiveStar.star_involutive.toPerm star).trans opEquiv with toFun := fun x => MulOpposite.op (star x),
    map_mul' := fun x y => (star_mul x y).symm ▸ MulOpposite.op_mul _ _ }

/-- `star` as a `mul_aut` for commutative `R`. -/
@[simps apply]
def starMulAut [CommSemigroupₓ R] [StarSemigroup R] : MulAut R :=
  { HasInvolutiveStar.star_involutive.toPerm star with toFun := star, map_mul' := star_mul' }

variable (R)

@[simp]
theorem star_one [Monoidₓ R] [StarSemigroup R] : star (1 : R) = 1 :=
  op_injective <| (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans (op_one _).symm

variable {R}

@[simp]
theorem star_pow [Monoidₓ R] [StarSemigroup R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
  op_injective <| ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm

@[simp]
theorem star_inv [Groupₓ R] [StarSemigroup R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm

@[simp]
theorem star_zpow [Groupₓ R] [StarSemigroup R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <| ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div [CommGroupₓ R] [StarSemigroup R] (x y : R) : star (x / y) = star x / star y :=
  (starMulAut : R ≃* R).toMonoidHom.map_div _ _

section

open BigOperators

@[simp]
theorem star_prod [CommMonoidₓ R] [StarSemigroup R] {α : Type _} (s : Finset α) (f : α → R) :
    star (∏ x in s, f x) = ∏ x in s, star (f x) :=
  (starMulAut : R ≃* R).map_prod _ _

end

/-- Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def starSemigroupOfComm {R : Type _} [CommMonoidₓ R] : StarSemigroup R where
  star := id
  star_involutive := fun x => rfl
  star_mul := mul_comm

section

attribute [local instance] starSemigroupOfComm

/-- Note that since `star_semigroup_of_comm` is reducible, `simp` can already prove this. --/
theorem star_id_of_comm {R : Type _} [CommSemiringₓ R] {x : R} : star x = x :=
  rfl

end

/-- A `*`-additive monoid `R` is an additive monoid with an involutive `star` operation which
preserves addition.
-/
class StarAddMonoid (R : Type u) [AddMonoidₓ R] extends HasInvolutiveStar R where
  star_add : ∀ r s : R, star (r + s) = star r + star s

export StarAddMonoid (star_add)

attribute [simp] star_add

/-- `star` as an `add_equiv` -/
@[simps apply]
def starAddEquiv [AddMonoidₓ R] [StarAddMonoid R] : R ≃+ R :=
  { HasInvolutiveStar.star_involutive.toPerm star with toFun := star, map_add' := star_add }

variable (R)

@[simp]
theorem star_zero [AddMonoidₓ R] [StarAddMonoid R] : star (0 : R) = 0 :=
  (starAddEquiv : R ≃+ R).map_zero

variable {R}

@[simp]
theorem star_eq_zero [AddMonoidₓ R] [StarAddMonoid R] {x : R} : star x = 0 ↔ x = 0 :=
  starAddEquiv.map_eq_zero_iff

theorem star_ne_zero [AddMonoidₓ R] [StarAddMonoid R] {x : R} : star x ≠ 0 ↔ x ≠ 0 :=
  star_eq_zero.Not

@[simp]
theorem star_neg [AddGroupₓ R] [StarAddMonoid R] (r : R) : star (-r) = -star r :=
  (starAddEquiv : R ≃+ R).map_neg _

@[simp]
theorem star_sub [AddGroupₓ R] [StarAddMonoid R] (r s : R) : star (r - s) = star r - star s :=
  (starAddEquiv : R ≃+ R).map_sub _ _

@[simp]
theorem star_nsmul [AddMonoidₓ R] [StarAddMonoid R] (x : R) (n : ℕ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _

@[simp]
theorem star_zsmul [AddGroupₓ R] [StarAddMonoid R] (x : R) (n : ℤ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _

section

open BigOperators

@[simp]
theorem star_sum [AddCommMonoidₓ R] [StarAddMonoid R] {α : Type _} (s : Finset α) (f : α → R) :
    star (∑ x in s, f x) = ∑ x in s, star (f x) :=
  (starAddEquiv : R ≃+ R).map_sum _ _

end

/-- A `*`-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a `*`-semigroup
(i.e. `star (r * s) = star s * star r`).
-/
class StarRing (R : Type u) [NonUnitalSemiringₓ R] extends StarSemigroup R where
  star_add : ∀ r s : R, star (r + s) = star r + star s

instance (priority := 100) StarRing.toStarAddMonoid [NonUnitalSemiringₓ R] [StarRing R] :
    StarAddMonoid R where star_add := StarRing.star_add

/-- `star` as an `ring_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starRingEquiv [NonUnitalSemiringₓ R] [StarRing R] : R ≃+* Rᵐᵒᵖ :=
  { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }

@[simp, norm_cast]
theorem star_nat_cast [Semiringₓ R] [StarRing R] (n : ℕ) : star (n : R) = n :=
  (congr_arg unop (map_nat_cast (starRingEquiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_nat_cast _)

@[simp, norm_cast]
theorem star_int_cast [Ringₓ R] [StarRing R] (z : ℤ) : star (z : R) = z :=
  (congr_arg unop ((starRingEquiv : R ≃+* Rᵐᵒᵖ).toRingHom.map_int_cast z)).trans (unop_int_cast _)

@[simp, norm_cast]
theorem star_rat_cast [DivisionRing R] [CharZero R] [StarRing R] (r : ℚ) : star (r : R) = r :=
  (congr_arg unop <| map_rat_cast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_rat_cast _)

/-- `star` as a ring automorphism, for commutative `R`. -/
@[simps apply]
def starRingAut [CommSemiringₓ R] [StarRing R] : RingAut R :=
  { starAddEquiv, starMulAut with toFun := star }

variable (R)

/-- `star` as a ring endomorphism, for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the locale `complex_conjugate`.

Note that this is the preferred form (over `star_ring_aut`, available under the same hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[star_ring_end R] F`) does not pretty-print if there is a coercion involved, as would be the
case for `(↑star_ring_aut : R →* R)`. -/
def starRingEnd [CommSemiringₓ R] [StarRing R] : R →+* R :=
  @starRingAut R _ _

variable {R}

-- mathport name: «exprconj»
localized [ComplexConjugate] notation "conj" => starRingEnd _

/-- This is not a simp lemma, since we usually want simp to keep `star_ring_end` bundled.
 For example, for complex conjugation, we don't want simp to turn `conj x`
 into the bare function `star x` automatically since most lemmas are about `conj x`. -/
theorem star_ring_end_apply [CommSemiringₓ R] [StarRing R] {x : R} : starRingEnd R x = star x :=
  rfl

@[simp]
theorem star_ring_end_self_apply [CommSemiringₓ R] [StarRing R] (x : R) : starRingEnd R (starRingEnd R x) = x :=
  star_star x

-- A more convenient name for complex conjugation
alias star_ring_end_self_apply ← Complex.conj_conj

alias star_ring_end_self_apply ← IsROrC.conj_conj

@[simp]
theorem star_inv' [DivisionRing R] [StarRing R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| ((starRingEquiv : R ≃+* Rᵐᵒᵖ).toRingHom.map_inv x).trans (op_inv (star x)).symm

@[simp]
theorem star_zpow₀ [DivisionRing R] [StarRing R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <| ((starRingEquiv : R ≃+* Rᵐᵒᵖ).toRingHom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div' [Field R] [StarRing R] (x y : R) : star (x / y) = star x / star y :=
  (starRingEnd R).map_div _ _

@[simp]
theorem star_bit0 [AddMonoidₓ R] [StarAddMonoid R] (r : R) : star (bit0 r) = bit0 (star r) := by
  simp [← bit0]

@[simp]
theorem star_bit1 [Semiringₓ R] [StarRing R] (r : R) : star (bit1 r) = bit1 (star r) := by
  simp [← bit1]

/-- Any commutative semiring admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def starRingOfComm {R : Type _} [CommSemiringₓ R] : StarRing R :=
  { starSemigroupOfComm with star := id, star_add := fun x y => rfl }

/-- An ordered `*`-ring is a ring which is both an `ordered_add_comm_group` and a `*`-ring,
and `0 ≤ r ↔ ∃ s, r = star s * s`.
-/
class StarOrderedRing (R : Type u) [NonUnitalSemiringₓ R] [PartialOrderₓ R] extends StarRing R where
  add_le_add_left : ∀ a b : R, a ≤ b → ∀ c : R, c + a ≤ c + b
  nonneg_iff : ∀ r : R, 0 ≤ r ↔ ∃ s, r = star s * s

namespace StarOrderedRing

variable [Ringₓ R] [PartialOrderₓ R] [StarOrderedRing R]

-- see note [lower instance priority]
instance (priority := 100) : OrderedAddCommGroup R :=
  { show Ringₓ R by
      infer_instance,
    show PartialOrderₓ R by
      infer_instance,
    show StarOrderedRing R by
      infer_instance with }

end StarOrderedRing

theorem star_mul_self_nonneg [NonUnitalSemiringₓ R] [PartialOrderₓ R] [StarOrderedRing R] {r : R} : 0 ≤ star r * r :=
  (StarOrderedRing.nonneg_iff _).mpr ⟨r, rfl⟩

theorem star_mul_self_nonneg' [NonUnitalSemiringₓ R] [PartialOrderₓ R] [StarOrderedRing R] {r : R} : 0 ≤ r * star r :=
  by
  nth_rw_rhs 0[← star_star r]
  exact star_mul_self_nonneg

/-- A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[semiring R] [star_ring R] [add_comm_monoid A] [star_add_monoid A] [module R A]`, and that
the statement only requires `[has_star R] [has_star A] [has_smul R A]`.

If used as `[comm_ring R] [star_ring R] [semiring A] [star_ring A] [algebra R A]`, this represents a
star algebra.
-/
class StarModule (R : Type u) (A : Type v) [HasStar R] [HasStar A] [HasSmul R A] : Prop where
  star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a

export StarModule (star_smul)

attribute [simp] star_smul

/-- A commutative star monoid is a star module over itself via `monoid.to_mul_action`. -/
instance StarSemigroup.to_star_module [CommMonoidₓ R] [StarSemigroup R] : StarModule R R :=
  ⟨star_mul'⟩

namespace RingHomInvPair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ).  -/
instance [CommSemiringₓ R] [StarRing R] : RingHomInvPair (starRingEnd R) (starRingEnd R) :=
  ⟨RingHom.ext star_star, RingHom.ext star_star⟩

end RingHomInvPair

/-! ### Instances -/


namespace Units

variable [Monoidₓ R] [StarSemigroup R]

instance : StarSemigroup Rˣ where
  star := fun u =>
    { val := star u, inv := star ↑u⁻¹,
      val_inv := (star_mul _ _).symm.trans <| (congr_arg star u.inv_val).trans <| star_one _,
      inv_val := (star_mul _ _).symm.trans <| (congr_arg star u.val_inv).trans <| star_one _ }
  star_involutive := fun u => Units.ext (star_involutive _)
  star_mul := fun u v => Units.ext (star_mul _ _)

@[simp]
theorem coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) :=
  rfl

@[simp]
theorem coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) :=
  rfl

instance {A : Type _} [HasStar A] [HasSmul R A] [StarModule R A] : StarModule Rˣ A :=
  ⟨fun u a => (star_smul (↑u) a : _)⟩

end Units

theorem IsUnit.star [Monoidₓ R] [StarSemigroup R] {a : R} : IsUnit a → IsUnit (star a)
  | ⟨u, hu⟩ => ⟨star u, hu ▸ rfl⟩

@[simp]
theorem is_unit_star [Monoidₓ R] [StarSemigroup R] {a : R} : IsUnit (star a) ↔ IsUnit a :=
  ⟨fun h => star_star a ▸ h.star, IsUnit.star⟩

theorem Ringₓ.inverse_star [Semiringₓ R] [StarRing R] (a : R) : Ring.inverse (star a) = star (Ring.inverse a) := by
  by_cases' ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit, ← Units.coe_star, Ring.inverse_unit, ← Units.coe_star_inv]
    
  rw [Ring.inverse_non_unit _ ha, Ring.inverse_non_unit _ (mt is_unit_star.mp ha), star_zero]

instance Invertible.star {R : Type _} [Monoidₓ R] [StarSemigroup R] (r : R) [Invertible r] : Invertible (star r) where
  invOf := star (⅟ r)
  inv_of_mul_self := by
    rw [← star_mul, mul_inv_of_self, star_one]
  mul_inv_of_self := by
    rw [← star_mul, inv_of_mul_self, star_one]

theorem star_inv_of {R : Type _} [Monoidₓ R] [StarSemigroup R] (r : R) [Invertible r] [Invertible (star r)] :
    star (⅟ r) = ⅟ (star r) := by
  let this := Invertible.star r
  convert (rfl : star (⅟ r) = _)

namespace MulOpposite

/-- The opposite type carries the same star operation. -/
instance [HasStar R] : HasStar Rᵐᵒᵖ where star := fun r => op (star r.unop)

@[simp]
theorem unop_star [HasStar R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) :=
  rfl

@[simp]
theorem op_star [HasStar R] (r : R) : op (star r) = star (op r) :=
  rfl

instance [HasInvolutiveStar R] :
    HasInvolutiveStar Rᵐᵒᵖ where star_involutive := fun r => unop_injective (star_star r.unop)

instance [Monoidₓ R] [StarSemigroup R] :
    StarSemigroup Rᵐᵒᵖ where star_mul := fun x y => unop_injective (star_mul y.unop x.unop)

instance [AddMonoidₓ R] [StarAddMonoid R] :
    StarAddMonoid Rᵐᵒᵖ where star_add := fun x y => unop_injective (star_add x.unop y.unop)

instance [Semiringₓ R] [StarRing R] : StarRing Rᵐᵒᵖ :=
  { MulOpposite.starAddMonoid with }

end MulOpposite

/-- A commutative star monoid is a star module over its opposite via
`monoid.to_opposite_mul_action`. -/
instance StarSemigroup.to_opposite_star_module [CommMonoidₓ R] [StarSemigroup R] : StarModule Rᵐᵒᵖ R :=
  ⟨fun r s => star_mul' s r.unop⟩

