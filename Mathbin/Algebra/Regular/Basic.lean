/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Algebra.Order.MonoidLemmas
import Mathbin.Algebra.GroupWithZero.Basic
import Mathbin.Logic.Embedding

/-!
# Regular elements

We introduce left-regular, right-regular and regular elements, along with their `to_additive`
analogues add-left-regular, add-right-regular and add-regular elements.

By definition, a regular element in a commutative ring is a non-zero divisor.
Lemma `is_regular_of_ne_zero` implies that every non-zero element of an integral domain is regular.
Since it assumes that the ring is a `cancel_monoid_with_zero` it applies also, for instance, to `ℕ`.

The lemmas in Section `mul_zero_class` show that the `0` element is (left/right-)regular if and
only if the `mul_zero_class` is trivial.  This is useful when figuring out stopping conditions for
regular sequences: if `0` is ever an element of a regular sequence, then we can extend the sequence
by adding one further `0`.

The final goal is to develop part of the API to prove, eventually, results about non-zero-divisors.
-/


variable {R : Type _} {a b : R}

section Mul

variable [Mul R]

/-- A left-regular element is an element `c` such that multiplication on the left by `c`
is injective. -/
@[to_additive "An add-left-regular element is an element `c` such that addition on the left by `c`\nis injective. -/\n"]
def IsLeftRegular (c : R) :=
  Function.Injective ((· * ·) c)

/-- A right-regular element is an element `c` such that multiplication on the right by `c`
is injective. -/
@[to_additive "An add-right-regular element is an element `c` such that addition on the right by `c`\nis injective."]
def IsRightRegular (c : R) :=
  Function.Injective (· * c)

/-- An add-regular element is an element `c` such that addition by `c` both on the left and
on the right is injective. -/
structure IsAddRegular {R : Type _} [Add R] (c : R) : Prop where
  left : IsAddLeftRegular c
  right : IsAddRightRegular c

/-- A regular element is an element `c` such that multiplication by `c` both on the left and
on the right is injective. -/
structure IsRegular (c : R) : Prop where
  left : IsLeftRegular c
  right : IsRightRegular c

attribute [to_additive] IsRegular

@[to_additive]
protected theorem MulLeCancellable.is_left_regular [PartialOrderₓ R] {a : R} (ha : MulLeCancellable a) :
    IsLeftRegular a :=
  ha.Injective

theorem IsLeftRegular.right_of_commute {a : R} (ca : ∀ b, Commute a b) (h : IsLeftRegular a) : IsRightRegular a :=
  fun x y xy => h <| (ca x).trans <| xy.trans <| (ca y).symm

theorem Commute.is_regular_iff {a : R} (ca : ∀ b, Commute a b) : IsRegular a ↔ IsLeftRegular a :=
  ⟨fun h => h.left, fun h => ⟨h, h.right_of_commute ca⟩⟩

end Mul

section Semigroupₓ

variable [Semigroupₓ R]

/-- In a semigroup, the product of left-regular elements is left-regular. -/
@[to_additive "In an additive semigroup, the sum of add-left-regular elements is add-left.regular."]
theorem IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLeftRegular b) : IsLeftRegular (a * b) :=
  show Function.Injective ((· * ·) (a * b)) from comp_mul_left a b ▸ lra.comp lrb

/-- In a semigroup, the product of right-regular elements is right-regular. -/
@[to_additive "In an additive semigroup, the sum of add-right-regular elements is add-right-regular."]
theorem IsRightRegular.mul (rra : IsRightRegular a) (rrb : IsRightRegular b) : IsRightRegular (a * b) :=
  show Function.Injective (· * (a * b)) from comp_mul_right b a ▸ rrb.comp rra

/-- If an element `b` becomes left-regular after multiplying it on the left by a left-regular
element, then `b` is left-regular. -/
@[to_additive
      "If an element `b` becomes add-left-regular after adding to it on the left a\nadd-left-regular element, then `b` is add-left-regular."]
theorem IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) : IsLeftRegular b :=
  Function.Injective.of_comp
    (by
      rwa [comp_mul_left a b])

/-- An element is left-regular if and only if multiplying it on the left by a left-regular element
is left-regular. -/
@[simp,
  to_additive
      "An element is add-left-regular if and only if adding to it on the left a\nadd-left-regular element is add-left-regular."]
theorem mul_is_left_regular_iff (b : R) (ha : IsLeftRegular a) : IsLeftRegular (a * b) ↔ IsLeftRegular b :=
  ⟨fun ab => IsLeftRegular.of_mul ab, fun ab => IsLeftRegular.mul ha ab⟩

/-- If an element `b` becomes right-regular after multiplying it on the right by a right-regular
element, then `b` is right-regular. -/
@[to_additive
      "If an element `b` becomes add-right-regular after adding to it on the right a\nadd-right-regular element, then `b` is add-right-regular."]
theorem IsRightRegular.of_mul (ab : IsRightRegular (b * a)) : IsRightRegular b := by
  refine' fun x y xy => ab (_ : x * (b * a) = y * (b * a))
  rw [← mul_assoc, ← mul_assoc]
  exact congr_fun (congr_arg Mul.mul xy) a

/-- An element is right-regular if and only if multiplying it on the right with a right-regular
element is right-regular. -/
@[simp,
  to_additive
      "An element is add-right-regular if and only if adding it on the right to a\nadd-right-regular element is add-right-regular."]
theorem mul_is_right_regular_iff (b : R) (ha : IsRightRegular a) : IsRightRegular (b * a) ↔ IsRightRegular b :=
  ⟨fun ab => IsRightRegular.of_mul ab, fun ab => IsRightRegular.mul ab ha⟩

/-- Two elements `a` and `b` are regular if and only if both products `a * b` and `b * a`
are regular. -/
@[to_additive "Two elements `a` and `b` are add-regular if and only if both sums `a + b` and `b + a`\nare add-regular."]
theorem is_regular_mul_and_mul_iff : IsRegular (a * b) ∧ IsRegular (b * a) ↔ IsRegular a ∧ IsRegular b := by
  refine' ⟨_, _⟩
  · rintro ⟨ab, ba⟩
    exact
      ⟨⟨IsLeftRegular.of_mul ba.left, IsRightRegular.of_mul ab.right⟩,
        ⟨IsLeftRegular.of_mul ab.left, IsRightRegular.of_mul ba.right⟩⟩
    
  · rintro ⟨ha, hb⟩
    exact
      ⟨⟨(mul_is_left_regular_iff _ ha.left).mpr hb.left, (mul_is_right_regular_iff _ hb.right).mpr ha.right⟩,
        ⟨(mul_is_left_regular_iff _ hb.left).mpr ha.left, (mul_is_right_regular_iff _ ha.right).mpr hb.right⟩⟩
    

/-- The "most used" implication of `mul_and_mul_iff`, with split hypotheses, instead of `∧`. -/
@[to_additive "The \"most used\" implication of `add_and_add_iff`, with split hypotheses,\ninstead of `∧`."]
theorem IsRegular.and_of_mul_of_mul (ab : IsRegular (a * b)) (ba : IsRegular (b * a)) : IsRegular a ∧ IsRegular b :=
  is_regular_mul_and_mul_iff.mp ⟨ab, ba⟩

end Semigroupₓ

section MulZeroClassₓ

variable [MulZeroClassₓ R]

/-- The element `0` is left-regular if and only if `R` is trivial. -/
theorem IsLeftRegular.subsingleton (h : IsLeftRegular (0 : R)) : Subsingleton R :=
  ⟨fun a b => h <| Eq.trans (zero_mul a) (zero_mul b).symm⟩

/-- The element `0` is right-regular if and only if `R` is trivial. -/
theorem IsRightRegular.subsingleton (h : IsRightRegular (0 : R)) : Subsingleton R :=
  ⟨fun a b => h <| Eq.trans (mul_zero a) (mul_zero b).symm⟩

/-- The element `0` is regular if and only if `R` is trivial. -/
theorem IsRegular.subsingleton (h : IsRegular (0 : R)) : Subsingleton R :=
  h.left.Subsingleton

/-- The element `0` is left-regular if and only if `R` is trivial. -/
theorem is_left_regular_zero_iff_subsingleton : IsLeftRegular (0 : R) ↔ Subsingleton R := by
  refine' ⟨fun h => h.Subsingleton, _⟩
  intro H a b h
  exact @Subsingleton.elimₓ _ H a b

/-- In a non-trivial `mul_zero_class`, the `0` element is not left-regular. -/
theorem not_is_left_regular_zero_iff : ¬IsLeftRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, is_left_regular_zero_iff_subsingleton, subsingleton_iff]
  push_neg
  exact Iff.rfl

/-- The element `0` is right-regular if and only if `R` is trivial. -/
theorem is_right_regular_zero_iff_subsingleton : IsRightRegular (0 : R) ↔ Subsingleton R := by
  refine' ⟨fun h => h.Subsingleton, _⟩
  intro H a b h
  exact @Subsingleton.elimₓ _ H a b

/-- In a non-trivial `mul_zero_class`, the `0` element is not right-regular. -/
theorem not_is_right_regular_zero_iff : ¬IsRightRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, is_right_regular_zero_iff_subsingleton, subsingleton_iff]
  push_neg
  exact Iff.rfl

/-- The element `0` is regular if and only if `R` is trivial. -/
theorem is_regular_iff_subsingleton : IsRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.left.Subsingleton, fun h =>
    ⟨is_left_regular_zero_iff_subsingleton.mpr h, is_right_regular_zero_iff_subsingleton.mpr h⟩⟩

/-- A left-regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine' xy (la _)
  rw [zero_mul, zero_mul]

/-- A right-regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
theorem IsRightRegular.ne_zero [Nontrivial R] (ra : IsRightRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine' xy (ra (_ : x * 0 = y * 0))
  rw [mul_zero, mul_zero]

/-- A regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
theorem IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) : a ≠ 0 :=
  la.left.ne_zero

/-- In a non-trivial ring, the element `0` is not left-regular -- with typeclasses. -/
theorem not_is_left_regular_zero [nR : Nontrivial R] : ¬IsLeftRegular (0 : R) :=
  not_is_left_regular_zero_iff.mpr nR

/-- In a non-trivial ring, the element `0` is not right-regular -- with typeclasses. -/
theorem not_is_right_regular_zero [nR : Nontrivial R] : ¬IsRightRegular (0 : R) :=
  not_is_right_regular_zero_iff.mpr nR

/-- In a non-trivial ring, the element `0` is not regular -- with typeclasses. -/
theorem not_is_regular_zero [Nontrivial R] : ¬IsRegular (0 : R) := fun h => IsRegular.ne_zero h rfl

end MulZeroClassₓ

section MulOneClassₓ

variable [MulOneClassₓ R]

/-- If multiplying by `1` on either side is the identity, `1` is regular. -/
@[to_additive "If adding `0` on either side is the identity, `0` is regular."]
theorem is_regular_one : IsRegular (1 : R) :=
  ⟨fun a b ab => (one_mulₓ a).symm.trans (Eq.trans ab (one_mulₓ b)), fun a b ab =>
    (mul_oneₓ a).symm.trans (Eq.trans ab (mul_oneₓ b))⟩

end MulOneClassₓ

section CommSemigroupₓ

variable [CommSemigroupₓ R]

/-- A product is regular if and only if the factors are. -/
@[to_additive "A sum is add-regular if and only if the summands are."]
theorem is_regular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧ IsRegular b := by
  refine' Iff.trans _ is_regular_mul_and_mul_iff
  refine'
    ⟨fun ab =>
      ⟨ab, by
        rwa [mul_comm]⟩,
      fun rab => rab.1⟩

end CommSemigroupₓ

section Monoidₓ

variable [Monoidₓ R]

/-- An element admitting a left inverse is left-regular. -/
@[to_additive "An element admitting a left additive opposite is add-left-regular."]
theorem is_left_regular_of_mul_eq_one (h : b * a = 1) : IsLeftRegular a :=
  @IsLeftRegular.of_mul R _ a _
    (by
      rw [h]
      exact is_regular_one.left)

/-- An element admitting a right inverse is right-regular. -/
@[to_additive "An element admitting a right additive opposite is add-right-regular."]
theorem is_right_regular_of_mul_eq_one (h : a * b = 1) : IsRightRegular a :=
  @IsRightRegular.of_mul R _ a _
    (by
      rw [h]
      exact is_regular_one.right)

/-- If `R` is a monoid, an element in `Rˣ` is regular. -/
@[to_additive "If `R` is an additive monoid, an element in `add_units R` is add-regular."]
theorem Units.is_regular (a : Rˣ) : IsRegular (a : R) :=
  ⟨is_left_regular_of_mul_eq_one a.inv_mul, is_right_regular_of_mul_eq_one a.mul_inv⟩

/-- A unit in a monoid is regular. -/
@[to_additive "An additive unit in an additive monoid is add-regular."]
theorem IsUnit.is_regular (ua : IsUnit a) : IsRegular a := by
  rcases ua with ⟨a, rfl⟩
  exact Units.is_regular a

end Monoidₓ

section LeftOrRightCancelSemigroup

/-- The embedding of a left cancellative semigroup into itself
by left multiplication by a fixed element.
 -/
@[to_additive
      "The embedding of a left cancellative additive semigroup into itself\n   by left translation by a fixed element.",
  simps]
def mulLeftEmbedding {G : Type _} [LeftCancelSemigroup G] (g : G) : G ↪ G where
  toFun := fun h => g * h
  inj' := mul_right_injective g

/-- The embedding of a right cancellative semigroup into itself
by right multiplication by a fixed element.
 -/
@[to_additive
      "The embedding of a right cancellative additive semigroup into itself\n   by right translation by a fixed element.",
  simps]
def mulRightEmbedding {G : Type _} [RightCancelSemigroup G] (g : G) : G ↪ G where
  toFun := fun h => h * g
  inj' := mul_left_injective g

@[to_additive]
theorem mul_left_embedding_eq_mul_right_embedding {G : Type _} [CancelCommMonoid G] (g : G) :
    mulLeftEmbedding g = mulRightEmbedding g := by
  ext
  exact mul_comm _ _

/-- Elements of a left cancel semigroup are left regular. -/
@[to_additive "Elements of an add left cancel semigroup are add-left-regular."]
theorem is_left_regular_of_left_cancel_semigroup [LeftCancelSemigroup R] (g : R) : IsLeftRegular g :=
  mul_right_injective g

/-- Elements of a right cancel semigroup are right regular. -/
@[to_additive "Elements of an add right cancel semigroup are add-right-regular"]
theorem is_right_regular_of_right_cancel_semigroup [RightCancelSemigroup R] (g : R) : IsRightRegular g :=
  mul_left_injective g

end LeftOrRightCancelSemigroup

section CancelMonoid

variable [CancelMonoid R]

/-- Elements of a cancel monoid are regular.  Cancel semigroups do not appear to exist. -/
@[to_additive "Elements of an add cancel monoid are regular.  Add cancel semigroups do not appear to exist."]
theorem is_regular_of_cancel_monoid (g : R) : IsRegular g :=
  ⟨mul_right_injective g, mul_left_injective g⟩

end CancelMonoid

section CancelMonoidWithZero

variable [CancelMonoidWithZero R]

/-- Non-zero elements of an integral domain are regular. -/
theorem is_regular_of_ne_zero (a0 : a ≠ 0) : IsRegular a :=
  ⟨fun b c => (mul_right_inj' a0).mp, fun b c => (mul_left_inj' a0).mp⟩

/-- In a non-trivial integral domain, an element is regular iff it is non-zero. -/
theorem is_regular_iff_ne_zero [Nontrivial R] : IsRegular a ↔ a ≠ 0 :=
  ⟨IsRegular.ne_zero, is_regular_of_ne_zero⟩

end CancelMonoidWithZero

