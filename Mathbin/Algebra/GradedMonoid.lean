/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Group.InjSurj
import Mathbin.Data.List.BigOperators
import Mathbin.Data.List.Range
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.GroupTheory.Submonoid.Basic
import Mathbin.Data.SetLike.Basic
import Mathbin.Data.Sigma.Basic

/-!
# Additively-graded multiplicative structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `graded_monoid A` such that `(*) : A i → A j → A (i + j)`; that is to say, `A`
forms an additively-graded monoid. The typeclasses are:

* `graded_monoid.ghas_one A`
* `graded_monoid.ghas_mul A`
* `graded_monoid.gmonoid A`
* `graded_monoid.gcomm_monoid A`

With the `sigma_graded` locale open, these respectively imbue:

* `has_one (graded_monoid A)`
* `has_mul (graded_monoid A)`
* `monoid (graded_monoid A)`
* `comm_monoid (graded_monoid A)`

the base type `A 0` with:

* `graded_monoid.grade_zero.has_one`
* `graded_monoid.grade_zero.has_mul`
* `graded_monoid.grade_zero.monoid`
* `graded_monoid.grade_zero.comm_monoid`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* (nothing)
* `graded_monoid.grade_zero.has_smul (A 0)`
* `graded_monoid.grade_zero.mul_action (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `direct_sum.ring` and the rest
of that file.

## Dependent graded products

This also introduces `list.dprod`, which takes the (possibly non-commutative) product of a list
of graded elements of type `A i`. This definition primarily exist to allow `graded_monoid.mk`
and `direct_sum.of` to be pulled outside a product, such as in `graded_monoid.mk_list_dprod` and
`direct_sum.of_list_dprod`.

## Internally graded monoids

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`set_like` subobjects (such as `add_submonoid`s, `add_subgroup`s, or `submodule`s), this file
provides the `Prop` typeclasses:

* `set_like.has_graded_one A` (which provides the obvious `graded_monoid.ghas_one A` instance)
* `set_like.has_graded_mul A` (which provides the obvious `graded_monoid.ghas_mul A` instance)
* `set_like.graded_monoid A` (which provides the obvious `graded_monoid.gmonoid A` and
  `graded_monoid.gcomm_monoid A` instances)
* `set_like.is_homogeneous A` (which says that `a` is homogeneous iff `a ∈ A i` for some `i : ι`)

Strictly this last class is unecessary as it has no fields not present in its parents, but it is
included for convenience. Note that there is no need for `graded_ring` or similar, as all the
information it would contain is already supplied by `graded_monoid` when `A` is a collection
of additively-closed set_like objects such as `submodule`s. These constructions are explored in
`algebra.direct_sum.internal`.

This file also contains the definition of `set_like.homogeneous_submonoid A`, which is, as the name
suggests, the submonoid consisting of all the homogeneous elements.

## tags

graded monoid
-/


variable {ι : Type _}

/-- A type alias of sigma types for graded monoids. -/
def GradedMonoid (A : ι → Type _) :=
  Sigma A

namespace GradedMonoid

instance {A : ι → Type _} [Inhabited ι] [Inhabited (A default)] : Inhabited (GradedMonoid A) :=
  Sigma.inhabited

/-- Construct an element of a graded monoid. -/
def mk {A : ι → Type _} : ∀ i, A i → GradedMonoid A :=
  Sigma.mk

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type _)

/-- A graded version of `has_one`, which must be of grade 0. -/
class GhasOne [Zero ι] where
  one : A 0

/-- `ghas_one` implies `has_one (graded_monoid A)` -/
instance GhasOne.toHasOne [Zero ι] [GhasOne A] : One (GradedMonoid A) :=
  ⟨⟨_, GhasOne.one⟩⟩

/-- A graded version of `has_mul`. Multiplication combines grades additively, like
`add_monoid_algebra`. -/
class GhasMul [Add ι] where
  mul {i j} : A i → A j → A (i + j)

/-- `ghas_mul` implies `has_mul (graded_monoid A)`. -/
instance GhasMul.toHasMul [Add ι] [GhasMul A] : Mul (GradedMonoid A) :=
  ⟨fun x y : GradedMonoid A => ⟨_, GhasMul.mul x.snd y.snd⟩⟩

theorem mk_mul_mk [Add ι] [GhasMul A] {i j} (a : A i) (b : A j) : mk i a * mk j b = mk (i + j) (GhasMul.mul a b) :=
  rfl

namespace Gmonoid

variable {A} [AddMonoidₓ ι] [GhasMul A] [GhasOne A]

/-- A default implementation of power on a graded monoid, like `npow_rec`.
`gmonoid.gnpow` should be used instead. -/
def gnpowRec : ∀ (n : ℕ) {i}, A i → A (n • i)
  | 0, i, a => cast (congr_arg A (zero_nsmul i).symm) GhasOne.one
  | n + 1, i, a => cast (congr_arg A (succ_nsmul i n).symm) (GhasMul.mul a <| gnpow_rec _ a)

@[simp]
theorem gnpow_rec_zero (a : GradedMonoid A) : GradedMonoid.mk _ (gnpowRec 0 a.snd) = 1 :=
  Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_zero'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
unsafe def apply_gnpow_rec_zero_tac : tactic Unit :=
  sorry

@[simp]
theorem gnpow_rec_succ (n : ℕ) (a : GradedMonoid A) :
    (GradedMonoid.mk _ <| gnpowRec n.succ a.snd) = a * ⟨_, gnpowRec n a.snd⟩ :=
  Sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_succ'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
unsafe def apply_gnpow_rec_succ_tac : tactic Unit :=
  sorry

end Gmonoid

/-- A graded version of `monoid`.

Like `monoid.npow`, this has an optional `gmonoid.gnpow` field to allow definitional control of
natural powers of a graded monoid. -/
class Gmonoid [AddMonoidₓ ι] extends GhasMul A, GhasOne A where
  one_mul (a : GradedMonoid A) : 1 * a = a
  mul_one (a : GradedMonoid A) : a * 1 = a
  mul_assoc (a b c : GradedMonoid A) : a * b * c = a * (b * c)
  gnpow : ∀ (n : ℕ) {i}, A i → A (n • i) := Gmonoid.gnpowRec
  gnpow_zero' : ∀ a : GradedMonoid A, GradedMonoid.mk _ (gnpow 0 a.snd) = 1 := by
    run_tac
      gmonoid.apply_gnpow_rec_zero_tac
  gnpow_succ' : ∀ (n : ℕ) (a : GradedMonoid A), (GradedMonoid.mk _ <| gnpow n.succ a.snd) = a * ⟨_, gnpow n a.snd⟩ := by
    run_tac
      gmonoid.apply_gnpow_rec_succ_tac

/-- `gmonoid` implies a `monoid (graded_monoid A)`. -/
instance Gmonoid.toMonoid [AddMonoidₓ ι] [Gmonoid A] : Monoidₓ (GradedMonoid A) where
  one := 1
  mul := (· * ·)
  npow := fun n a => GradedMonoid.mk _ (Gmonoid.gnpow n a.snd)
  npow_zero' := fun a => Gmonoid.gnpow_zero' a
  npow_succ' := fun n a => Gmonoid.gnpow_succ' n a
  one_mul := Gmonoid.one_mul
  mul_one := Gmonoid.mul_one
  mul_assoc := Gmonoid.mul_assoc

theorem mk_pow [AddMonoidₓ ι] [Gmonoid A] {i} (a : A i) (n : ℕ) : mk i a ^ n = mk (n • i) (Gmonoid.gnpow _ a) := by
  induction' n with n
  · rw [pow_zeroₓ]
    exact (gmonoid.gnpow_zero' ⟨_, a⟩).symm
    
  · rw [pow_succₓ, n_ih, mk_mul_mk]
    exact (gmonoid.gnpow_succ' n ⟨_, a⟩).symm
    

/-- A graded version of `comm_monoid`. -/
class GcommMonoid [AddCommMonoidₓ ι] extends Gmonoid A where
  mul_comm (a : GradedMonoid A) (b : GradedMonoid A) : a * b = b * a

/-- `gcomm_monoid` implies a `comm_monoid (graded_monoid A)`, although this is only used as an
instance locally to define notation in `gmonoid` and similar typeclasses. -/
instance GcommMonoid.toCommMonoid [AddCommMonoidₓ ι] [GcommMonoid A] : CommMonoidₓ (GradedMonoid A) :=
  { Gmonoid.toMonoid A with mul_comm := GcommMonoid.mul_comm }

end Defs

/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

variable (A : ι → Type _)

section One

variable [Zero ι] [GhasOne A]

/-- `1 : A 0` is the value provided in `ghas_one.one`. -/
@[nolint unused_arguments]
instance GradeZero.hasOne : One (A 0) :=
  ⟨GhasOne.one⟩

end One

section Mul

variable [AddZeroClassₓ ι] [GhasMul A]

/-- `(•) : A 0 → A i → A i` is the value provided in `graded_monoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + i)` into `A i`.
-/
instance GradeZero.hasSmul (i : ι) : HasSmul (A 0) (A i) where smul := fun x y => (zero_addₓ i).rec (GhasMul.mul x y)

/-- `(*) : A 0 → A 0 → A 0` is the value provided in `graded_monoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + 0)` into `A 0`.
-/
instance GradeZero.hasMul : Mul (A 0) where mul := (· • ·)

variable {A}

@[simp]
theorem mk_zero_smul {i} (a : A 0) (b : A i) : mk _ (a • b) = mk _ a * mk _ b :=
  Sigma.ext (zero_addₓ _).symm <| eq_rec_heq _ _

@[simp]
theorem GradeZero.smul_eq_mul (a b : A 0) : a • b = a * b :=
  rfl

end Mul

section Monoidₓ

variable [AddMonoidₓ ι] [Gmonoid A]

instance : Pow (A 0) ℕ where pow := fun x n => (nsmul_zero n).rec (Gmonoid.gnpow n x : A (n • 0))

variable {A}

@[simp]
theorem mk_zero_pow (a : A 0) (n : ℕ) : mk _ (a ^ n) = mk _ a ^ n :=
  Sigma.ext (nsmul_zero n).symm <| eq_rec_heq _ _

variable (A)

/-- The `monoid` structure derived from `gmonoid A`. -/
instance GradeZero.monoid : Monoidₓ (A 0) :=
  Function.Injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow

end Monoidₓ

section Monoidₓ

variable [AddCommMonoidₓ ι] [GcommMonoid A]

/-- The `comm_monoid` structure derived from `gcomm_monoid A`. -/
instance GradeZero.commMonoid : CommMonoidₓ (A 0) :=
  Function.Injective.commMonoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow

end Monoidₓ

section MulAction

variable [AddMonoidₓ ι] [Gmonoid A]

/-- `graded_monoid.mk 0` is a `monoid_hom`, using the `graded_monoid.grade_zero.monoid` structure.
-/
def mkZeroMonoidHom : A 0 →* GradedMonoid A where
  toFun := mk 0
  map_one' := rfl
  map_mul' := mk_zero_smul

/-- Each grade `A i` derives a `A 0`-action structure from `gmonoid A`. -/
instance GradeZero.mulAction {i} : MulAction (A 0) (A i) := by
  let this := MulAction.compHom (GradedMonoid A) (mk_zero_monoid_hom A)
  exact Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul

end MulAction

end GradeZero

end GradedMonoid

/-! ### Dependent products of graded elements -/


section Dprod

variable {α : Type _} {A : ι → Type _} [AddMonoidₓ ι] [GradedMonoid.Gmonoid A]

/-- The index used by `list.dprod`. Propositionally this is equal to `(l.map fι).sum`, but
definitionally it needs to have a different form to avoid introducing `eq.rec`s in `list.dprod`. -/
def List.dprodIndex (l : List α) (fι : α → ι) : ι :=
  l.foldr (fun i b => fι i + b) 0

@[simp]
theorem List.dprod_index_nil (fι : α → ι) : ([] : List α).dprodIndex fι = 0 :=
  rfl

@[simp]
theorem List.dprod_index_cons (a : α) (l : List α) (fι : α → ι) : (a :: l).dprodIndex fι = fι a + l.dprodIndex fι :=
  rfl

theorem List.dprod_index_eq_map_sum (l : List α) (fι : α → ι) : l.dprodIndex fι = (l.map fι).Sum := by
  dunfold List.dprodIndex
  induction l
  · simp
    
  · simp [← l_ih]
    

/-- A dependent product for graded monoids represented by the indexed family of types `A i`.
This is a dependent version of `(l.map fA).prod`.

For a list `l : list α`, this computes the product of `fA a` over `a`, where each `fA` is of type
`A (fι a)`. -/
def List.dprod (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) : A (l.dprodIndex fι) :=
  l.foldrRecOn _ _ GradedMonoid.GhasOne.one fun i x a ha => GradedMonoid.GhasMul.mul (fA a) x

@[simp]
theorem List.dprod_nil (fι : α → ι) (fA : ∀ a, A (fι a)) : (List.nil : List α).dprod fι fA = GradedMonoid.GhasOne.one :=
  rfl

-- the `( : _)` in this lemma statement results in the type on the RHS not being unfolded, which
-- is nicer in the goal view.
@[simp]
theorem List.dprod_cons (fι : α → ι) (fA : ∀ a, A (fι a)) (a : α) (l : List α) :
    (a :: l).dprod fι fA = (GradedMonoid.GhasMul.mul (fA a) (l.dprod fι fA) : _) :=
  rfl

theorem GradedMonoid.mk_list_dprod (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    GradedMonoid.mk _ (l.dprod fι fA) = (l.map fun a => GradedMonoid.mk (fι a) (fA a)).Prod := by
  induction l
  · simp
    rfl
    
  · simp [l_ih, ← GradedMonoid.mk_mul_mk, ← List.prod_cons]
    rfl
    

/-- A variant of `graded_monoid.mk_list_dprod` for rewriting in the other direction. -/
theorem GradedMonoid.list_prod_map_eq_dprod (l : List α) (f : α → GradedMonoid A) :
    (l.map f).Prod = GradedMonoid.mk _ (l.dprod (fun i => (f i).1) fun i => (f i).2) := by
  rw [GradedMonoid.mk_list_dprod, GradedMonoid.mk]
  simp_rw [Sigma.eta]

theorem GradedMonoid.list_prod_of_fn_eq_dprod {n : ℕ} (f : Finₓ n → GradedMonoid A) :
    (List.ofFnₓ f).Prod = GradedMonoid.mk _ ((List.finRange n).dprod (fun i => (f i).1) fun i => (f i).2) := by
  rw [List.of_fn_eq_map, GradedMonoid.list_prod_map_eq_dprod]

end Dprod

/-! ### Concrete instances -/


section

variable (ι) {R : Type _}

@[simps one]
instance One.ghasOne [Zero ι] [One R] : GradedMonoid.GhasOne fun i : ι => R where one := 1

@[simps mul]
instance Mul.ghasMul [Add ι] [Mul R] : GradedMonoid.GhasMul fun i : ι => R where mul := fun i j => (· * ·)

/-- If all grades are the same type and themselves form a monoid, then there is a trivial grading
structure. -/
@[simps gnpow]
instance Monoidₓ.gmonoid [AddMonoidₓ ι] [Monoidₓ R] : GradedMonoid.Gmonoid fun i : ι => R :=
  { One.ghasOne ι, Mul.ghasMul ι with one_mul := fun a => Sigma.ext (zero_addₓ _) (heq_of_eq (one_mulₓ _)),
    mul_one := fun a => Sigma.ext (add_zeroₓ _) (heq_of_eq (mul_oneₓ _)),
    mul_assoc := fun a b c => Sigma.ext (add_assocₓ _ _ _) (heq_of_eq (mul_assoc _ _ _)), gnpow := fun n i a => a ^ n,
    gnpow_zero' := fun a => Sigma.ext (zero_nsmul _) (heq_of_eq (Monoidₓ.npow_zero' _)),
    gnpow_succ' := fun n ⟨i, a⟩ => Sigma.ext (succ_nsmul _ _) (heq_of_eq (Monoidₓ.npow_succ' _ _)) }

/-- If all grades are the same type and themselves form a commutative monoid, then there is a
trivial grading structure. -/
instance CommMonoidₓ.gcommMonoid [AddCommMonoidₓ ι] [CommMonoidₓ R] : GradedMonoid.GcommMonoid fun i : ι => R :=
  { Monoidₓ.gmonoid ι with mul_comm := fun a b => Sigma.ext (add_commₓ _ _) (heq_of_eq (mul_comm _ _)) }

/-- When all the indexed types are the same, the dependent product is just the regular product. -/
@[simp]
theorem List.dprod_monoid {α} [AddMonoidₓ ι] [Monoidₓ R] (l : List α) (fι : α → ι) (fA : α → R) :
    (l.dprod fι fA : (fun i : ι => R) _) = ((l.map fA).Prod : _) := by
  induction l
  · rw [List.dprod_nil, List.map_nil, List.prod_nil]
    rfl
    
  · rw [List.dprod_cons, List.map_cons, List.prod_cons, l_ih]
    rfl
    

end

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type _}

/-- A version of `graded_monoid.ghas_one` for internally graded objects. -/
class SetLike.HasGradedOne {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S) : Prop where
  one_mem : (1 : R) ∈ A 0

instance SetLike.ghasOne {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S) [SetLike.HasGradedOne A] :
    GradedMonoid.GhasOne fun i => A i where one := ⟨1, SetLike.HasGradedOne.one_mem⟩

@[simp]
theorem SetLike.coe_ghas_one {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S) [SetLike.HasGradedOne A] :
    ↑(@GradedMonoid.GhasOne.one _ (fun i => A i) _ _) = (1 : R) :=
  rfl

/-- A version of `graded_monoid.ghas_one` for internally graded objects. -/
class SetLike.HasGradedMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S) : Prop where
  mul_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ A i → gj ∈ A j → gi * gj ∈ A (i + j)

instance SetLike.ghasMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S) [SetLike.HasGradedMul A] :
    GradedMonoid.GhasMul fun i =>
      A i where mul := fun i j a b => ⟨(a * b : R), SetLike.HasGradedMul.mul_mem a.Prop b.Prop⟩

@[simp]
theorem SetLike.coe_ghas_mul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S) [SetLike.HasGradedMul A] {i j : ι}
    (x : A i) (y : A j) : ↑(@GradedMonoid.GhasMul.mul _ (fun i => A i) _ _ _ _ x y) = (x * y : R) :=
  rfl

/-- A version of `graded_monoid.gmonoid` for internally graded objects. -/
class SetLike.GradedMonoid {S : Type _} [SetLike S R] [Monoidₓ R] [AddMonoidₓ ι] (A : ι → S) extends
  SetLike.HasGradedOne A, SetLike.HasGradedMul A : Prop

namespace SetLike.GradedMonoid

variable {S : Type _} [SetLike S R] [Monoidₓ R] [AddMonoidₓ ι]

variable {A : ι → S} [SetLike.GradedMonoid A]

theorem pow_mem (n : ℕ) {r : R} {i : ι} (h : r ∈ A i) : r ^ n ∈ A (n • i) := by
  induction n
  · rw [pow_zeroₓ, zero_nsmul]
    exact one_mem
    
  · rw [pow_succ'ₓ, succ_nsmul']
    exact mul_mem n_ih h
    

theorem list_prod_map_mem {ι'} (l : List ι') (i : ι' → ι) (r : ι' → R) (h : ∀, ∀ j ∈ l, ∀, r j ∈ A (i j)) :
    (l.map r).Prod ∈ A (l.map i).Sum := by
  induction l
  · rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil]
    exact one_mem
    
  · rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons]
    exact mul_mem (h _ <| List.mem_cons_selfₓ _ _) (l_ih fun j hj => h _ <| List.mem_cons_of_memₓ _ hj)
    

theorem list_prod_of_fn_mem {n} (i : Finₓ n → ι) (r : Finₓ n → R) (h : ∀ j, r j ∈ A (i j)) :
    (List.ofFnₓ r).Prod ∈ A (List.ofFnₓ i).Sum := by
  rw [List.of_fn_eq_map, List.of_fn_eq_map]
  exact list_prod_map_mem _ _ _ fun _ _ => h _

end SetLike.GradedMonoid

/-- Build a `gmonoid` instance for a collection of subobjects. -/
instance SetLike.gmonoid {S : Type _} [SetLike S R] [Monoidₓ R] [AddMonoidₓ ι] (A : ι → S) [SetLike.GradedMonoid A] :
    GradedMonoid.Gmonoid fun i => A i :=
  { SetLike.ghasOne A, SetLike.ghasMul A with one_mul := fun ⟨i, a, h⟩ => Sigma.subtype_ext (zero_addₓ _) (one_mulₓ _),
    mul_one := fun ⟨i, a, h⟩ => Sigma.subtype_ext (add_zeroₓ _) (mul_oneₓ _),
    mul_assoc := fun ⟨i, a, ha⟩ ⟨j, b, hb⟩ ⟨k, c, hc⟩ => Sigma.subtype_ext (add_assocₓ _ _ _) (mul_assoc _ _ _),
    gnpow := fun n i a => ⟨a ^ n, SetLike.GradedMonoid.pow_mem n a.Prop⟩,
    gnpow_zero' := fun n => Sigma.subtype_ext (zero_nsmul _) (pow_zeroₓ _),
    gnpow_succ' := fun n a => Sigma.subtype_ext (succ_nsmul _ _) (pow_succₓ _ _) }

@[simp]
theorem SetLike.coe_gnpow {S : Type _} [SetLike S R] [Monoidₓ R] [AddMonoidₓ ι] (A : ι → S) [SetLike.GradedMonoid A]
    {i : ι} (x : A i) (n : ℕ) : ↑(@GradedMonoid.Gmonoid.gnpow _ (fun i => A i) _ _ n _ x) = (x ^ n : R) :=
  rfl

/-- Build a `gcomm_monoid` instance for a collection of subobjects. -/
instance SetLike.gcommMonoid {S : Type _} [SetLike S R] [CommMonoidₓ R] [AddCommMonoidₓ ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.GcommMonoid fun i => A i :=
  { SetLike.gmonoid A with mul_comm := fun ⟨i, a, ha⟩ ⟨j, b, hb⟩ => Sigma.subtype_ext (add_commₓ _ _) (mul_comm _ _) }

section Dprod

open SetLike SetLike.GradedMonoid

variable {α S : Type _} [SetLike S R] [Monoidₓ R] [AddMonoidₓ ι]

/-- Coercing a dependent product of subtypes is the same as taking the regular product of the
coercions. -/
@[simp]
theorem SetLike.coe_list_dprod (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι) (fA : ∀ a, A (fι a)) (l : List α) :
    ↑(l.dprod fι fA : (fun i => ↥(A i)) _) = (List.prod (l.map fun a => fA a) : R) := by
  induction l
  · rw [List.dprod_nil, coe_ghas_one, List.map_nil, List.prod_nil]
    
  · rw [List.dprod_cons, coe_ghas_mul, List.map_cons, List.prod_cons, l_ih]
    

include R

/-- A version of `list.coe_dprod_set_like` with `subtype.mk`. -/
theorem SetLike.list_dprod_eq (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι) (fA : ∀ a, A (fι a)) (l : List α) :
    (l.dprod fι fA : (fun i => ↥(A i)) _) =
      ⟨List.prod (l.map fun a => fA a),
        (l.dprod_index_eq_map_sum fι).symm ▸ list_prod_map_mem l _ _ fun i hi => (fA i).Prop⟩ :=
  Subtype.ext <| SetLike.coe_list_dprod _ _ _ _

end Dprod

end Subobjects

section HomogeneousElements

variable {R S : Type _} [SetLike S R]

/-- An element `a : R` is said to be homogeneous if there is some `i : ι` such that `a ∈ A i`. -/
def SetLike.IsHomogeneous (A : ι → S) (a : R) : Prop :=
  ∃ i, a ∈ A i

@[simp]
theorem SetLike.is_homogeneous_coe {A : ι → S} {i} (x : A i) : SetLike.IsHomogeneous A (x : R) :=
  ⟨i, x.Prop⟩

theorem SetLike.is_homogeneous_one [Zero ι] [One R] (A : ι → S) [SetLike.HasGradedOne A] :
    SetLike.IsHomogeneous A (1 : R) :=
  ⟨0, SetLike.HasGradedOne.one_mem⟩

theorem SetLike.IsHomogeneous.mul [Add ι] [Mul R] {A : ι → S} [SetLike.HasGradedMul A] {a b : R} :
    SetLike.IsHomogeneous A a → SetLike.IsHomogeneous A b → SetLike.IsHomogeneous A (a * b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.HasGradedMul.mul_mem hi hj⟩

/-- When `A` is a `set_like.graded_monoid A`, then the homogeneous elements forms a submonoid. -/
def SetLike.homogeneousSubmonoid [AddMonoidₓ ι] [Monoidₓ R] (A : ι → S) [SetLike.GradedMonoid A] : Submonoid R where
  Carrier := { a | SetLike.IsHomogeneous A a }
  one_mem' := SetLike.is_homogeneous_one A
  mul_mem' := fun a b => SetLike.IsHomogeneous.mul

end HomogeneousElements

