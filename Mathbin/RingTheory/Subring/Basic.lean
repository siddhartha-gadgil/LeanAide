/-
Copyright (c) 2020 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.RingTheory.Subsemiring.Basic

/-!
# Subrings

Let `R` be a ring. This file defines the "bundled" subring type `subring R`, a type
whose terms correspond to subrings of `R`. This is the preferred way to talk
about subrings in mathlib. Unbundled subrings (`s : set R` and `is_subring s`)
are not in this file, and they will ultimately be deprecated.

We prove that subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `set R` to `subring R`, sending a subset of `R`
to the subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [ring R] (S : Type u) [ring S] (f g : R →+* S)`
`(A : subring R) (B : subring S) (s : set R)`

* `subring R` : the type of subrings of a ring `R`.

* `instance : complete_lattice (subring R)` : the complete lattice structure on the subrings.

* `subring.center` : the center of a ring `R`.

* `subring.closure` : subring closure of a set, i.e., the smallest subring that includes the set.

* `subring.gi` : `closure : set M → subring M` and coercion `coe : subring M → set M`
  form a `galois_insertion`.

* `comap f B : subring A` : the preimage of a subring `B` along the ring homomorphism `f`

* `map f A : subring B` : the image of a subring `A` along the ring homomorphism `f`.

* `prod A B : subring (R × S)` : the product of subrings

* `f.range : subring B` : the range of the ring homomorphism `f`.

* `eq_locus f g : subring R` : given ring homomorphisms `f g : R →+* S`,
     the subring of `R` where `f x = g x`

## Implementation notes

A subring is implemented as a subsemiring which is also an additive subgroup.
The initial PR was as a submonoid which is also an additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subring's underlying set.

## Tags
subring, subrings
-/


open BigOperators

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [Ringₓ R]

section SubringClass

/-- `subring_class S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup. -/
class SubringClass (S : Type _) (R : outParam <| Type u) [Ringₓ R] [SetLike S R] extends SubsemiringClass S R where
  neg_mem : ∀ {s : S} {a : R}, a ∈ s → -a ∈ s

-- See note [lower instance priority]
instance (priority := 100) SubringClass.addSubgroupClass (S : Type _) (R : outParam <| Type u) [SetLike S R] [Ringₓ R]
    [h : SubringClass S R] : AddSubgroupClass S R :=
  { h with }

variable [SetLike S R] [hSR : SubringClass S R] (s : S)

include hSR

theorem coe_int_mem (n : ℤ) : (n : R) ∈ s := by
  simp only [zsmul_one, ← zsmul_mem, ← one_mem]

namespace SubringClass

instance (priority := 75) toHasIntCast : HasIntCast s :=
  ⟨fun n => ⟨n, coe_int_mem s n⟩⟩

/-- A subring of a ring inherits a ring structure -/
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
instance (priority := 75) toRing : Ringₓ s :=
  Subtype.coe_injective.Ring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

omit hSR

/-- A subring of a `comm_ring` is a `comm_ring`. -/
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
instance (priority := 75) toCommRing {R} [CommRingₓ R] [SetLike S R] [SubringClass S R] : CommRingₓ s :=
  Subtype.coe_injective.CommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

/-- A subring of a domain is a domain. -/
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
instance (priority := 75) {R} [Ringₓ R] [IsDomain R] [SetLike S R] [SubringClass S R] : IsDomain s :=
  { SubsemiringClass.nontrivial s, SubsemiringClass.no_zero_divisors s with }

/-- A subring of an `ordered_ring` is an `ordered_ring`. -/
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
instance (priority := 75) toOrderedRing {R} [OrderedRing R] [SetLike S R] [SubringClass S R] : OrderedRing s :=
  Subtype.coe_injective.OrderedRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

/-- A subring of an `ordered_comm_ring` is an `ordered_comm_ring`. -/
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
instance (priority := 75) toOrderedCommRing {R} [OrderedCommRing R] [SetLike S R] [SubringClass S R] :
    OrderedCommRing s :=
  Subtype.coe_injective.OrderedCommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

/-- A subring of a `linear_ordered_ring` is a `linear_ordered_ring`. -/
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
instance (priority := 75) toLinearOrderedRing {R} [LinearOrderedRing R] [SetLike S R] [SubringClass S R] :
    LinearOrderedRing s :=
  Subtype.coe_injective.LinearOrderedRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-- A subring of a `linear_ordered_comm_ring` is a `linear_ordered_comm_ring`. -/
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
instance (priority := 75) toLinearOrderedCommRing {R} [LinearOrderedCommRing R] [SetLike S R] [SubringClass S R] :
    LinearOrderedCommRing s :=
  Subtype.coe_injective.LinearOrderedCommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

include hSR

/-- The natural ring hom from a subring of ring `R` to `R`. -/
def subtype (s : S) : s →+* R :=
  { SubmonoidClass.subtype s, AddSubgroupClass.subtype s with toFun := coe }

@[simp]
theorem coe_subtype : (subtype s : s → R) = coe :=
  rfl

@[simp, norm_cast]
theorem coe_nat_cast (n : ℕ) : ((n : s) : R) = n :=
  map_nat_cast (subtype s) n

@[simp, norm_cast]
theorem coe_int_cast (n : ℤ) : ((n : s) : R) = n :=
  (subtype s : s →+* R).map_int_cast n

end SubringClass

end SubringClass

variable [Ringₓ S] [Ringₓ T]

/-- `subring R` is the type of subrings of `R`. A subring of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
structure Subring (R : Type u) [Ringₓ R] extends Subsemiring R, AddSubgroup R

/-- Reinterpret a `subring` as a `subsemiring`. -/
add_decl_doc Subring.toSubsemiring

/-- Reinterpret a `subring` as an `add_subgroup`. -/
add_decl_doc Subring.toAddSubgroup

namespace Subring

/-- The underlying submonoid of a subring. -/
def toSubmonoid (s : Subring R) : Submonoid R :=
  { s.toSubsemiring.toSubmonoid with Carrier := s.Carrier }

instance : SetLike (Subring R) R where
  coe := Subring.Carrier
  coe_injective' := fun p q h => by
    cases p <;> cases q <;> congr

instance : SubringClass (Subring R) R where
  zero_mem := zero_mem'
  add_mem := add_mem'
  one_mem := one_mem'
  mul_mem := mul_mem'
  neg_mem := neg_mem'

@[simp]
theorem mem_carrier {s : Subring R} {x : R} : x ∈ s.Carrier ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_mk {S : Set R} {x : R} (h₁ h₂ h₃ h₄ h₅) : x ∈ (⟨S, h₁, h₂, h₃, h₄, h₅⟩ : Subring R) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_set_mk (S : Set R) (h₁ h₂ h₃ h₄ h₅) : ((⟨S, h₁, h₂, h₃, h₄, h₅⟩ : Subring R) : Set R) = S :=
  rfl

@[simp]
theorem mk_le_mk {S S' : Set R} (h₁ h₂ h₃ h₄ h₅ h₁' h₂' h₃' h₄' h₅') :
    (⟨S, h₁, h₂, h₃, h₄, h₅⟩ : Subring R) ≤ (⟨S', h₁', h₂', h₃', h₄', h₅'⟩ : Subring R) ↔ S ⊆ S' :=
  Iff.rfl

/-- Two subrings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : Subring R) (s : Set R) (hs : s = ↑S) : Subring R :=
  { S.toSubsemiring.copy s hs with Carrier := s, neg_mem' := hs.symm ▸ S.neg_mem' }

@[simp]
theorem coe_copy (S : Subring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : Subring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem to_subsemiring_injective : Function.Injective (toSubsemiring : Subring R → Subsemiring R)
  | r, s, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem to_subsemiring_strict_mono : StrictMono (toSubsemiring : Subring R → Subsemiring R) := fun _ _ => id

@[mono]
theorem to_subsemiring_mono : Monotone (toSubsemiring : Subring R → Subsemiring R) :=
  to_subsemiring_strict_mono.Monotone

theorem to_add_subgroup_injective : Function.Injective (toAddSubgroup : Subring R → AddSubgroup R)
  | r, s, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem to_add_subgroup_strict_mono : StrictMono (toAddSubgroup : Subring R → AddSubgroup R) := fun _ _ => id

@[mono]
theorem to_add_subgroup_mono : Monotone (toAddSubgroup : Subring R → AddSubgroup R) :=
  to_add_subgroup_strict_mono.Monotone

theorem to_submonoid_injective : Function.Injective (toSubmonoid : Subring R → Submonoid R)
  | r, s, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem to_submonoid_strict_mono : StrictMono (toSubmonoid : Subring R → Submonoid R) := fun _ _ => id

@[mono]
theorem to_submonoid_mono : Monotone (toSubmonoid : Subring R → Submonoid R) :=
  to_submonoid_strict_mono.Monotone

/-- Construct a `subring R` from a set `s`, a submonoid `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sm : Submonoid R) (sa : AddSubgroup R) (hm : ↑sm = s) (ha : ↑sa = s) : Subring R where
  Carrier := s
  zero_mem' := ha ▸ sa.zero_mem
  one_mem' := hm ▸ sm.one_mem
  add_mem' := fun x y => by
    simpa only [ha] using sa.add_mem
  mul_mem' := fun x y => by
    simpa only [hm] using sm.mul_mem
  neg_mem' := fun x => by
    simpa only [ha] using sa.neg_mem

@[simp]
theorem coe_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) :
    (Subring.mk' s sm sa hm ha : Set R) = s :=
  rfl

@[simp]
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) {x : R} :
    x ∈ Subring.mk' s sm sa hm ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mk'_to_submonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) :
    (Subring.mk' s sm sa hm ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
theorem mk'_to_add_subgroup {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) :
    (Subring.mk' s sm sa hm ha).toAddSubgroup = sa :=
  SetLike.coe_injective ha.symm

end Subring

/-- A `subsemiring` containing -1 is a `subring`. -/
def Subsemiring.toSubring (s : Subsemiring R) (hneg : (-1 : R) ∈ s) : Subring R :=
  { s.toSubmonoid, s.toAddSubmonoid with
    neg_mem' := by
      rintro x
      rw [← neg_one_mul]
      apply Subsemiring.mul_mem
      exact hneg }

namespace Subring

variable (s : Subring R)

/-- A subring contains the ring's 1. -/
protected theorem one_mem : (1 : R) ∈ s :=
  one_mem _

/-- A subring contains the ring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem _

/-- A subring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A subring is closed under negation. -/
protected theorem neg_mem {x : R} : x ∈ s → -x ∈ s :=
  neg_mem

/-- A subring is closed under subtraction -/
protected theorem sub_mem {x y : R} (hx : x ∈ s) (hy : y ∈ s) : x - y ∈ s :=
  sub_mem hx hy

/-- Product of a list of elements in a subring is in the subring. -/
protected theorem list_prod_mem {l : List R} : (∀, ∀ x ∈ l, ∀, x ∈ s) → l.Prod ∈ s :=
  list_prod_mem

/-- Sum of a list of elements in a subring is in the subring. -/
protected theorem list_sum_mem {l : List R} : (∀, ∀ x ∈ l, ∀, x ∈ s) → l.Sum ∈ s :=
  list_sum_mem

/-- Product of a multiset of elements in a subring of a `comm_ring` is in the subring. -/
protected theorem multiset_prod_mem {R} [CommRingₓ R] (s : Subring R) (m : Multiset R) :
    (∀, ∀ a ∈ m, ∀, a ∈ s) → m.Prod ∈ s :=
  multiset_prod_mem _

/-- Sum of a multiset of elements in an `subring` of a `ring` is
in the `subring`. -/
protected theorem multiset_sum_mem {R} [Ringₓ R] (s : Subring R) (m : Multiset R) :
    (∀, ∀ a ∈ m, ∀, a ∈ s) → m.Sum ∈ s :=
  multiset_sum_mem _

/-- Product of elements of a subring of a `comm_ring` indexed by a `finset` is in the
    subring. -/
protected theorem prod_mem {R : Type _} [CommRingₓ R] (s : Subring R) {ι : Type _} {t : Finset ι} {f : ι → R}
    (h : ∀, ∀ c ∈ t, ∀, f c ∈ s) : (∏ i in t, f i) ∈ s :=
  prod_mem h

/-- Sum of elements in a `subring` of a `ring` indexed by a `finset`
is in the `subring`. -/
protected theorem sum_mem {R : Type _} [Ringₓ R] (s : Subring R) {ι : Type _} {t : Finset ι} {f : ι → R}
    (h : ∀, ∀ c ∈ t, ∀, f c ∈ s) : (∑ i in t, f i) ∈ s :=
  sum_mem h

/-- A subring of a ring inherits a ring structure -/
instance toRing : Ringₓ s :=
  Subtype.coe_injective.Ring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

protected theorem zsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n

protected theorem pow_mem {x : R} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n

@[simp, norm_cast]
theorem coe_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : s) : (↑(-x) : R) = -↑x :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : s) : R) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : s) (n : ℕ) : (↑(x ^ n) : R) = x ^ n :=
  SubmonoidClass.coe_pow x n

-- TODO: can be generalized to `add_submonoid_class`
@[simp]
theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 :=
  ⟨fun h => Subtype.ext (trans h s.coe_zero.symm), fun h => h.symm ▸ s.coe_zero⟩

/-- A subring of a `comm_ring` is a `comm_ring`. -/
instance toCommRing {R} [CommRingₓ R] (s : Subring R) : CommRingₓ s :=
  Subtype.coe_injective.CommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

/-- A subring of a non-trivial ring is non-trivial. -/
instance {R} [Ringₓ R] [Nontrivial R] (s : Subring R) : Nontrivial s :=
  s.toSubsemiring.Nontrivial

/-- A subring of a ring with no zero divisors has no zero divisors. -/
instance {R} [Ringₓ R] [NoZeroDivisors R] (s : Subring R) : NoZeroDivisors s :=
  s.toSubsemiring.NoZeroDivisors

/-- A subring of a domain is a domain. -/
instance {R} [Ringₓ R] [IsDomain R] (s : Subring R) : IsDomain s :=
  { s.Nontrivial, s.NoZeroDivisors, s.toRing with }

/-- A subring of an `ordered_ring` is an `ordered_ring`. -/
instance toOrderedRing {R} [OrderedRing R] (s : Subring R) : OrderedRing s :=
  Subtype.coe_injective.OrderedRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

/-- A subring of an `ordered_comm_ring` is an `ordered_comm_ring`. -/
instance toOrderedCommRing {R} [OrderedCommRing R] (s : Subring R) : OrderedCommRing s :=
  Subtype.coe_injective.OrderedCommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

/-- A subring of a `linear_ordered_ring` is a `linear_ordered_ring`. -/
instance toLinearOrderedRing {R} [LinearOrderedRing R] (s : Subring R) : LinearOrderedRing s :=
  Subtype.coe_injective.LinearOrderedRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-- A subring of a `linear_ordered_comm_ring` is a `linear_ordered_comm_ring`. -/
instance toLinearOrderedCommRing {R} [LinearOrderedCommRing R] (s : Subring R) : LinearOrderedCommRing s :=
  Subtype.coe_injective.LinearOrderedCommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

/-- The natural ring hom from a subring of ring `R` to `R`. -/
def subtype (s : Subring R) : s →+* R :=
  { s.toSubmonoid.Subtype, s.toAddSubgroup.Subtype with toFun := coe }

@[simp]
theorem coe_subtype : ⇑s.Subtype = coe :=
  rfl

@[simp, norm_cast]
theorem coe_nat_cast : ∀ n : ℕ, ((n : s) : R) = n :=
  map_nat_cast s.Subtype

@[simp, norm_cast]
theorem coe_int_cast (n : ℤ) : ((n : s) : R) = n :=
  s.Subtype.map_int_cast n

/-! ## Partial order -/


@[simp]
theorem mem_to_submonoid {s : Subring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_to_submonoid (s : Subring R) : (s.toSubmonoid : Set R) = s :=
  rfl

@[simp]
theorem mem_to_add_subgroup {s : Subring R} {x : R} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_to_add_subgroup (s : Subring R) : (s.toAddSubgroup : Set R) = s :=
  rfl

/-! ## top -/


/-- The subring `R` of the ring `R`. -/
instance : HasTop (Subring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubgroup R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : Subring R) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : Subring R) : Set R) = Set.Univ :=
  rfl

/-! ## comap -/


/-- The preimage of a subring along a ring homomorphism is a subring. -/
def comap {R : Type u} {S : Type v} [Ringₓ R] [Ringₓ S] (f : R →+* S) (s : Subring S) : Subring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubgroup.comap (f : R →+ S) with Carrier := f ⁻¹' s.Carrier }

@[simp]
theorem coe_comap (s : Subring S) (f : R →+* S) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
theorem mem_comap {s : Subring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_comap (s : Subring T) (g : S →+* T) (f : R →+* S) : (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! ## map -/


/-- The image of a subring along a ring homomorphism is a subring. -/
def map {R : Type u} {S : Type v} [Ringₓ R] [Ringₓ S] (f : R →+* S) (s : Subring R) : Subring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubgroup.map (f : R →+ S) with Carrier := f '' s.Carrier }

@[simp]
theorem coe_map (f : R →+* S) (s : Subring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
theorem mem_map {f : R →+* S} {s : Subring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
  Set.mem_image_iff_bex

@[simp]
theorem map_id : s.map (RingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

theorem map_le_iff_le_comap {f : R →+* S} {s : Subring R} {t : Subring S} : s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff

theorem gc_map_comap (f : R →+* S) : GaloisConnection (map f) (comap f) := fun S T => map_le_iff_le_comap

/-- A subring is isomorphic to its image under an injective function -/
noncomputable def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equivₓ.Set.image f s hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _),
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }

@[simp]
theorem coe_equiv_map_of_injective_apply (f : R →+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end Subring

namespace RingHom

variable (g : S →+* T) (f : R →+* S)

/-! ## range -/


/-- The range of a ring homomorphism, as a subring of the target. See Note [range copy pattern]. -/
def range {R : Type u} {S : Type v} [Ringₓ R] [Ringₓ S] (f : R →+* S) : Subring S :=
  ((⊤ : Subring R).map f).copy (Set.Range f) Set.image_univ.symm

@[simp]
theorem coe_range : (f.range : Set S) = Set.Range f :=
  rfl

@[simp]
theorem mem_range {f : R →+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl

theorem range_eq_map (f : R →+* S) : f.range = Subring.map f ⊤ := by
  ext
  simp

theorem mem_range_self (f : R →+* S) (x : R) : f x ∈ f.range :=
  mem_range.mpr ⟨x, rfl⟩

theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [← range_eq_map] using (⊤ : Subring R).map_map g f

/-- The range of a ring homomorphism is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype S`. -/
instance fintypeRange [Fintype R] [DecidableEq S] (f : R →+* S) : Fintype (range f) :=
  Set.fintypeRange f

end RingHom

namespace Subring

/-! ## bot -/


instance : HasBot (Subring R) :=
  ⟨(Int.castRingHom R).range⟩

instance : Inhabited (Subring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : Subring R) : Set R) = Set.Range (coe : ℤ → R) :=
  RingHom.coe_range (Int.castRingHom R)

theorem mem_bot {x : R} : x ∈ (⊥ : Subring R) ↔ ∃ n : ℤ, ↑n = x :=
  RingHom.mem_range

/-! ## inf -/


/-- The inf of two subrings is their intersection. -/
instance : HasInf (Subring R) :=
  ⟨fun s t => { s.toSubmonoid⊓t.toSubmonoid, s.toAddSubgroup⊓t.toAddSubgroup with Carrier := s ∩ t }⟩

@[simp]
theorem coe_inf (p p' : Subring R) : ((p⊓p' : Subring R) : Set R) = p ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : Subring R} {x : R} : x ∈ p⊓p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : HasInfₓ (Subring R) :=
  ⟨fun s =>
    Subring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, Subring.toSubmonoid t) (⨅ t ∈ s, Subring.toAddSubgroup t)
      (by
        simp )
      (by
        simp )⟩

@[simp, norm_cast]
theorem coe_Inf (S : Set (Subring R)) : ((inf S : Subring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

theorem mem_Inf {S : Set (Subring R)} {x : R} : x ∈ inf S ↔ ∀, ∀ p ∈ S, ∀, x ∈ p :=
  Set.mem_Inter₂

@[simp]
theorem Inf_to_submonoid (s : Set (Subring R)) : (inf s).toSubmonoid = ⨅ t ∈ s, Subring.toSubmonoid t :=
  mk'_to_submonoid _ _

@[simp]
theorem Inf_to_add_subgroup (s : Set (Subring R)) : (inf s).toAddSubgroup = ⨅ t ∈ s, Subring.toAddSubgroup t :=
  mk'_to_add_subgroup _ _

/-- Subrings of a ring form a complete lattice. -/
instance : CompleteLattice (Subring R) :=
  { completeLatticeOfInf (Subring R) fun s =>
      IsGlb.of_image (fun s t => show (s : Set R) ≤ t ↔ s ≤ t from SetLike.coe_subset_coe) is_glb_binfi with
    bot := ⊥,
    bot_le := fun s x hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ coe_int_mem s n,
    top := ⊤, le_top := fun s x hx => trivialₓ, inf := (·⊓·), inf_le_left := fun s t x => And.left,
    inf_le_right := fun s t x => And.right, le_inf := fun s t₁ t₂ h₁ h₂ x hx => ⟨h₁ hx, h₂ hx⟩ }

theorem eq_top_iff' (A : Subring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

/-! ## Center of a ring -/


section

variable (R)

/-- The center of a ring `R` is the set of elements that commute with everything in `R` -/
def center : Subring R :=
  { Subsemiring.center R with Carrier := Set.Center R, neg_mem' := fun a => Set.neg_mem_center }

theorem coe_center : ↑(center R) = Set.Center R :=
  rfl

@[simp]
theorem center_to_subsemiring : (center R).toSubsemiring = Subsemiring.center R :=
  rfl

variable {R}

theorem mem_center_iff {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Iff.rfl

instance decidableMemCenter [DecidableEq R] [Fintype R] : DecidablePred (· ∈ center R) := fun _ =>
  decidableOfIff' _ mem_center_iff

@[simp]
theorem center_eq_top (R) [CommRingₓ R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

/-- The center is commutative. -/
instance : CommRingₓ (center R) :=
  { Subsemiring.center.commSemiring, (center R).toRing with }

end

section DivisionRing

variable {K : Type u} [DivisionRing K]

instance : Field (center K) :=
  { (center K).Nontrivial, center.commRing with inv := fun a => ⟨a⁻¹, Set.inv_mem_center₀ a.Prop⟩,
    mul_inv_cancel := fun ⟨a, ha⟩ h => Subtype.ext <| mul_inv_cancel <| Subtype.coe_injective.Ne h,
    div := fun a b => ⟨a / b, Set.div_mem_center₀ a.Prop b.Prop⟩,
    div_eq_mul_inv := fun a b => Subtype.ext <| div_eq_mul_inv _ _, inv_zero := Subtype.ext inv_zero }

@[simp]
theorem center.coe_inv (a : center K) : ((a⁻¹ : center K) : K) = (a : K)⁻¹ :=
  rfl

@[simp]
theorem center.coe_div (a b : center K) : ((a / b : center K) : K) = (a : K) / (b : K) :=
  rfl

end DivisionRing

/-! ## subring closure of a subset -/


/-- The `subring` generated by a set. -/
def closure (s : Set R) : Subring R :=
  inf { S | s ⊆ S }

theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : Subring R, s ⊆ S → x ∈ S :=
  mem_Inf

/-- The subring generated by a set includes the set. -/
@[simp]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun x hx => mem_closure.2 fun S hS => hS hx

theorem not_mem_of_not_mem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h => hP (subset_closure h)

/-- A subring `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : Subring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => Inf_le h⟩

/-- Subring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure

theorem closure_eq_of_le {s : Set R} {t : Subring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) : closure s = t :=
  le_antisymmₓ (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_eliminator]
theorem closure_induction {s : Set R} {p : R → Prop} {x} (h : x ∈ closure s) (Hs : ∀, ∀ x ∈ s, ∀, p x) (H0 : p 0)
    (H1 : p 1) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hneg : ∀ x : R, p x → p (-x))
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨p, Hmul, H1, Hadd, H0, Hneg⟩).2 Hs h

/-- An induction principle for closure membership, for predicates with two arguments. -/
@[elab_as_eliminator]
theorem closure_induction₂ {s : Set R} {p : R → R → Prop} {a b : R} (ha : a ∈ closure s) (hb : b ∈ closure s)
    (Hs : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, p x y) (H0_left : ∀ x, p 0 x) (H0_right : ∀ x, p x 0) (H1_left : ∀ x, p 1 x)
    (H1_right : ∀ x, p x 1) (Hneg_left : ∀ x y, p x y → p (-x) y) (Hneg_right : ∀ x y, p x y → p x (-y))
    (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y) (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y) (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) :
    p a b := by
  refine' closure_induction hb _ (H0_right _) (H1_right _) (Hadd_right a) (Hneg_right a) (Hmul_right a)
  refine' closure_induction ha Hs (fun x _ => H0_left x) (fun x _ => H1_left x) _ _ _
  · exact fun x y H₁ H₂ z zs => Hadd_left x y z (H₁ z zs) (H₂ z zs)
    
  · exact fun x hx z zs => Hneg_left x z (hx z zs)
    
  · exact fun x y H₁ H₂ z zs => Hmul_left x y z (H₁ z zs) (H₂ z zs)
    

theorem mem_closure_iff {s : Set R} {x} : x ∈ closure s ↔ x ∈ AddSubgroup.closure (Submonoid.closure s : Set R) :=
  ⟨fun h =>
    closure_induction h (fun x hx => AddSubgroup.subset_closure <| Submonoid.subset_closure hx) (AddSubgroup.zero_mem _)
      (AddSubgroup.subset_closure (Submonoid.one_mem (Submonoid.closure s)))
      (fun x y hx hy => AddSubgroup.add_mem _ hx hy) (fun x hx => AddSubgroup.neg_mem _ hx) fun x y hx hy =>
      AddSubgroup.closure_induction hy
        (fun q hq =>
          AddSubgroup.closure_induction hx
            (fun p hp => AddSubgroup.subset_closure ((Submonoid.closure s).mul_mem hp hq))
            (by
              rw [zero_mul q]
              apply AddSubgroup.zero_mem _)
            (fun p₁ p₂ ihp₁ ihp₂ => by
              rw [add_mulₓ p₁ p₂ q]
              apply AddSubgroup.add_mem _ ihp₁ ihp₂)
            fun x hx => by
            have f : -x * q = -(x * q) := by
              simp
            rw [f]
            apply AddSubgroup.neg_mem _ hx)
        (by
          rw [mul_zero x]
          apply AddSubgroup.zero_mem _)
        (fun q₁ q₂ ihq₁ ihq₂ => by
          rw [mul_addₓ x q₁ q₂]
          apply AddSubgroup.add_mem _ ihq₁ ihq₂)
        fun z hz => by
        have f : x * -z = -(x * z) := by
          simp
        rw [f]
        apply AddSubgroup.neg_mem _ hz,
    fun h =>
    AddSubgroup.closure_induction h
      (fun x hx =>
        Submonoid.closure_induction hx (fun x hx => subset_closure hx) (one_mem _) fun x y hx hy => mul_mem hx hy)
      (zero_mem _) (fun x y hx hy => add_mem hx hy) fun x hx => neg_mem hx⟩

/-- If all elements of `s : set A` commute pairwise, then `closure s` is a commutative ring.  -/
def closureCommRingOfComm {s : Set R} (hcomm : ∀, ∀ a ∈ s, ∀, ∀ b ∈ s, ∀, a * b = b * a) : CommRingₓ (closure s) :=
  { (closure s).toRing with
    mul_comm := fun x y => by
      ext
      simp only [← Subring.coe_mul]
      refine'
        closure_induction₂ x.prop y.prop hcomm
          (fun x => by
            simp only [← mul_zero, ← zero_mul])
          (fun x => by
            simp only [← mul_zero, ← zero_mul])
          (fun x => by
            simp only [← mul_oneₓ, ← one_mulₓ])
          (fun x => by
            simp only [← mul_oneₓ, ← one_mulₓ])
          (fun x y hxy => by
            simp only [← mul_neg, ← neg_mul, ← hxy])
          (fun x y hxy => by
            simp only [← mul_neg, ← neg_mul, ← hxy])
          (fun x₁ x₂ y h₁ h₂ => by
            simp only [← add_mulₓ, ← mul_addₓ, ← h₁, ← h₂])
          (fun x₁ x₂ y h₁ h₂ => by
            simp only [← add_mulₓ, ← mul_addₓ, ← h₁, ← h₂])
          (fun x₁ x₂ y h₁ h₂ => by
            rw [← mul_assoc, ← h₁, mul_assoc x₁ y x₂, ← h₂, mul_assoc])
          fun x₁ x₂ y h₁ h₂ => by
          rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }

theorem exists_list_of_mem_closure {s : Set R} {x : R} (h : x ∈ closure s) :
    ∃ L : List (List R), (∀, ∀ t ∈ L, ∀, ∀, ∀ y ∈ t, ∀, y ∈ s ∨ y = (-1 : R)) ∧ (L.map List.prod).Sum = x :=
  AddSubgroup.closure_induction (mem_closure_iff.1 h)
    (fun x hx =>
      let ⟨l, hl, h⟩ := Submonoid.exists_list_of_mem_closure hx
      ⟨[l], by
        simp [← h] <;> clear_aux_decl <;> tauto!⟩)
    ⟨[], by
      simp ⟩
    (fun x y ⟨l, hl1, hl2⟩ ⟨m, hm1, hm2⟩ =>
      ⟨l ++ m, fun t ht => (List.mem_appendₓ.1 ht).elim (hl1 t) (hm1 t), by
        simp [← hl2, ← hm2]⟩)
    fun x ⟨L, hL⟩ =>
    ⟨L.map (List.cons (-1)), List.forall_mem_map_iffₓ.2 fun j hj => List.forall_mem_consₓ.2 ⟨Or.inr rfl, hL.1 j hj⟩,
      hL.2 ▸
        List.recOn L
          (by
            simp )
          (by
            simp (config := { contextual := true })[← List.map_cons, ← add_commₓ])⟩

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) coe where
  choice := fun s _ => closure s
  gc := fun s t => closure_le
  le_l_u := fun s => subset_closure
  choice_eq := fun s h => rfl

variable {R}

/-- Closure of a subring `S` equals `S`. -/
theorem closure_eq (s : Subring R) : closure (s : Set R) = s :=
  (Subring.gi R).l_u_eq s

@[simp]
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (Subring.gi R).gc.l_bot

@[simp]
theorem closure_univ : closure (Set.Univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤

theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s⊔closure t :=
  (Subring.gi R).gc.l_sup

theorem closure_Union {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subring.gi R).gc.l_supr

theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀s) = ⨆ t ∈ s, closure t :=
  (Subring.gi R).gc.l_Sup

theorem map_sup (s t : Subring R) (f : R →+* S) : (s⊔t).map f = s.map f⊔t.map f :=
  (gc_map_comap f).l_sup

theorem map_supr {ι : Sort _} (f : R →+* S) (s : ι → Subring R) : (supr s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_supr

theorem comap_inf (s t : Subring S) (f : R →+* S) : (s⊓t).comap f = s.comap f⊓t.comap f :=
  (gc_map_comap f).u_inf

theorem comap_infi {ι : Sort _} (f : R →+* S) (s : ι → Subring S) : (infi s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_infi

@[simp]
theorem map_bot (f : R →+* S) : (⊥ : Subring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : R →+* S) : (⊤ : Subring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- Given `subring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s ×̂ t`
as a subring of `R × S`. -/
def prod (s : Subring R) (t : Subring S) : Subring (R × S) :=
  { s.toSubmonoid.Prod t.toSubmonoid, s.toAddSubgroup.Prod t.toAddSubgroup with Carrier := (s : Set R) ×ˢ (t : Set S) }

@[norm_cast]
theorem coe_prod (s : Subring R) (t : Subring S) : (s.Prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl

theorem mem_prod {s : Subring R} {t : Subring S} {p : R × S} : p ∈ s.Prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[mono]
theorem prod_mono ⦃s₁ s₂ : Subring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subring S⦄ (ht : t₁ ≤ t₂) : s₁.Prod t₁ ≤ s₂.Prod t₂ :=
  Set.prod_mono hs ht

theorem prod_mono_right (s : Subring R) : Monotone fun t : Subring S => s.Prod t :=
  prod_mono (le_reflₓ s)

theorem prod_mono_left (t : Subring S) : Monotone fun s : Subring R => s.Prod t := fun s₁ s₂ hs =>
  prod_mono hs (le_reflₓ t)

theorem prod_top (s : Subring R) : s.Prod (⊤ : Subring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by
    simp [← mem_prod, ← MonoidHom.coe_fst]

theorem top_prod (s : Subring S) : (⊤ : Subring R).Prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by
    simp [← mem_prod, ← MonoidHom.coe_snd]

@[simp]
theorem top_prod_top : (⊤ : Subring R).Prod (⊤ : Subring S) = ⊤ :=
  (top_prod _).trans <| comap_top _

/-- Product of subrings is isomorphic to their product as rings. -/
def prodEquiv (s : Subring R) (t : Subring S) : s.Prod t ≃+* s × t :=
  { Equivₓ.Set.prod ↑s ↑t with map_mul' := fun x y => rfl, map_add' := fun x y => rfl }

/-- The underlying set of a non-empty directed Sup of subrings is just a union of the subrings.
  Note that this fails without the directedness assumption (the union of two subrings is
  typically not a subring) -/
theorem mem_supr_of_directed {ι} [hι : Nonempty ι] {S : ι → Subring R} (hS : Directed (· ≤ ·) S) {x : R} :
    (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_supr S i) hi⟩
  let U : Subring R :=
    Subring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubmonoid) (⨆ i, (S i).toAddSubgroup)
      (Submonoid.coe_supr_of_directed <| hS.mono_comp _ fun _ _ => id)
      (AddSubgroup.coe_supr_of_directed <| hS.mono_comp _ fun _ _ => id)
  suffices (⨆ i, S i) ≤ U by
    simpa using @this x
  exact supr_le fun i x hx => Set.mem_Union.2 ⟨i, hx⟩

theorem coe_supr_of_directed {ι} [hι : Nonempty ι] {S : ι → Subring R} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subring R) : Set R) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by
    simp [← mem_supr_of_directed hS]

theorem mem_Sup_of_directed_on {S : Set (Subring R)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S) {x : R} :
    x ∈ sup S ↔ ∃ s ∈ S, x ∈ s := by
  have : Nonempty S := Sne.to_subtype
  simp only [← Sup_eq_supr', ← mem_supr_of_directed hS.directed_coe, ← SetCoe.exists, ← Subtype.coe_mk]

theorem coe_Sup_of_directed_on {S : Set (Subring R)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S) :
    (↑(sup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by
    simp [← mem_Sup_of_directed_on Sne hS]

theorem mem_map_equiv {f : R ≃+* S} {K : Subring R} {x : S} : x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (↑K) f.toEquiv x

theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subring R) : K.map (f : R →+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)

theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subring S) : K.comap (f : R →+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end Subring

namespace RingHom

variable {s : Subring R}

open Subring

/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `set.range_factorization`. -/
def rangeRestrict (f : R →+* S) : R →+* f.range :=
  (f.codRestrict f.range) fun x => ⟨x, rfl⟩

@[simp]
theorem coe_range_restrict (f : R →+* S) (x : R) : (f.range_restrict x : S) = f x :=
  rfl

theorem range_restrict_surjective (f : R →+* S) : Function.Surjective f.range_restrict := fun ⟨y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩

theorem range_top_iff_surjective {f : R →+* S} : f.range = (⊤ : Subring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <|
    Iff.trans
      (by
        rw [coe_range, coe_top])
      Set.range_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
theorem range_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) : f.range = (⊤ : Subring S) :=
  range_top_iff_surjective.2 hf

/-- The subring of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a subring of R -/
def eqLocus (f g : R →+* S) : Subring R :=
  { (f : R →* S).eqMlocus g, (f : R →+ S).eqLocus g with Carrier := { x | f x = g x } }

/-- If two ring homomorphisms are equal on a set, then they are equal on its subring closure. -/
theorem eq_on_set_closure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h

theorem eq_of_eq_on_set_top {f g : R →+* S} (h : Set.EqOn f g (⊤ : Subring R)) : f = g :=
  ext fun x => h trivialₓ

theorem eq_of_eq_on_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) : f = g :=
  eq_of_eq_on_set_top <| hs ▸ eq_on_set_closure h

theorem closure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subring generated by a set equals
the subring generated by the image of the set. -/
theorem map_closure (f : R →+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  le_antisymmₓ
    (map_le_iff_le_comap.2 <| le_transₓ (closure_mono <| Set.subset_preimage_image _ _) (closure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)

end RingHom

namespace Subring

open RingHom

/-- The ring homomorphism associated to an inclusion of subrings. -/
def inclusion {S T : Subring R} (h : S ≤ T) : S →+* T :=
  S.Subtype.codRestrict _ fun x => h x.2

@[simp]
theorem range_subtype (s : Subring R) : s.Subtype.range = s :=
  SetLike.coe_injective <| (coe_srange _).trans Subtype.range_coe

@[simp]
theorem range_fst : (fst R S).srange = ⊤ :=
  (fst R S).srange_top_of_surjective <| Prod.fst_surjectiveₓ

@[simp]
theorem range_snd : (snd R S).srange = ⊤ :=
  (snd R S).srange_top_of_surjective <| Prod.snd_surjective

@[simp]
theorem prod_bot_sup_bot_prod (s : Subring R) (t : Subring S) : s.Prod ⊥⊔prod ⊥ t = s.Prod t :=
  (le_antisymmₓ (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le))) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem ((le_sup_left : s.Prod ⊥ ≤ s.Prod ⊥⊔prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t ≤ s.Prod ⊥⊔prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

end Subring

namespace RingEquiv

variable {s t : Subring R}

/-- Makes the identity isomorphism from a proof two subrings of a multiplicative
    monoid are equal. -/
def subringCongr (h : s = t) : s ≃+* t :=
  { Equivₓ.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`ring_hom.range`. -/
def ofLeftInverse {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.range :=
  { f.range_restrict with toFun := fun x => f.range_restrict x, invFun := fun x => (g ∘ f.range.Subtype) x,
    left_inv := h,
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := RingHom.mem_range.mp x.Prop
        show f (g x) = x by
          rw [← hx', h x'] }

@[simp]
theorem of_left_inverse_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[simp]
theorem of_left_inverse_symm_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : f.range) :
    (ofLeftInverse h).symm x = g x :=
  rfl

/-- Given an equivalence `e : R ≃+* S` of rings and a subring `s` of `R`,
`subring_equiv_map e s` is the induced equivalence between `s` and `s.map e` -/
@[simps]
def subringMap (e : R ≃+* S) : s ≃+* s.map e.toRingHom :=
  e.subsemiringMap s.toSubsemiring

end RingEquiv

namespace Subring

variable {s : Set R}

attribute [local reducible] closure

@[elab_as_eliminator]
protected theorem InClosure.rec_on {C : R → Prop} {x : R} (hx : x ∈ closure s) (h1 : C 1) (hneg1 : C (-1))
    (hs : ∀, ∀ z ∈ s, ∀, ∀ n, C n → C (z * n)) (ha : ∀ {x y}, C x → C y → C (x + y)) : C x := by
  have h0 : C 0 := add_neg_selfₓ (1 : R) ▸ ha h1 hneg1
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩
  clear hx
  induction' L with hd tl ih
  · exact h0
    
  rw [List.forall_mem_consₓ] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons, List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1
  clear ih tl
  suffices ∃ L : List R, (∀, ∀ x ∈ L, ∀, x ∈ s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L) by
    rcases this with ⟨L, HL', HP | HP⟩
    · rw [HP]
      clear HP HL hd
      induction' L with hd tl ih
      · exact h1
        
      rw [List.forall_mem_consₓ] at HL'
      rw [List.prod_cons]
      exact hs _ HL'.1 _ (ih HL'.2)
      
    rw [HP]
    clear HP HL hd
    induction' L with hd tl ih
    · exact hneg1
      
    rw [List.prod_cons, neg_mul_eq_mul_neg]
    rw [List.forall_mem_consₓ] at HL'
    exact hs _ HL'.1 _ (ih HL'.2)
  induction' hd with hd tl ih
  · exact ⟨[], List.forall_mem_nilₓ _, Or.inl rfl⟩
    
  rw [List.forall_mem_consₓ] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> cases' HL.1 with hhd hhd
  · exact
      ⟨hd :: L, List.forall_mem_consₓ.2 ⟨hhd, HL'⟩,
        Or.inl <| by
          rw [List.prod_cons, List.prod_cons, HP]⟩
    
  · exact
      ⟨L, HL',
        Or.inr <| by
          rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
    
  · exact
      ⟨hd :: L, List.forall_mem_consₓ.2 ⟨hhd, HL'⟩,
        Or.inr <| by
          rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
    
  · exact
      ⟨L, HL',
        Or.inl <| by
          rw [List.prod_cons, hhd, HP, neg_one_mul, neg_negₓ]⟩
    

theorem closure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

end Subring

theorem AddSubgroup.int_mul_mem {G : AddSubgroup R} (k : ℤ) {g : R} (h : g ∈ G) : (k : R) * g ∈ G := by
  convert AddSubgroup.zsmul_mem G h k
  simp

/-! ## Actions by `subring`s

These are just copies of the definitions about `subsemiring` starting from
`subsemiring.mul_action`.

When `R` is commutative, `algebra.of_subring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subring

variable {α β : Type _}

/-- The action by a subring is the action by the underlying ring. -/
instance [HasSmul R α] (S : Subring R) : HasSmul S α :=
  S.toSubsemiring.HasSmul

theorem smul_def [HasSmul R α] {S : Subring R} (g : S) (m : α) : g • m = (g : R) • m :=
  rfl

instance smul_comm_class_left [HasSmul R β] [HasSmul α β] [SmulCommClass R α β] (S : Subring R) : SmulCommClass S α β :=
  S.toSubsemiring.smul_comm_class_left

instance smul_comm_class_right [HasSmul α β] [HasSmul R β] [SmulCommClass α R β] (S : Subring R) :
    SmulCommClass α S β :=
  S.toSubsemiring.smul_comm_class_right

/-- Note that this provides `is_scalar_tower S R R` which is needed by `smul_mul_assoc`. -/
instance [HasSmul α β] [HasSmul R α] [HasSmul R β] [IsScalarTower R α β] (S : Subring R) : IsScalarTower S α β :=
  S.toSubsemiring.IsScalarTower

instance [HasSmul R α] [HasFaithfulSmul R α] (S : Subring R) : HasFaithfulSmul S α :=
  S.toSubsemiring.HasFaithfulSmul

/-- The action by a subring is the action by the underlying ring. -/
instance [MulAction R α] (S : Subring R) : MulAction S α :=
  S.toSubsemiring.MulAction

/-- The action by a subring is the action by the underlying ring. -/
instance [AddMonoidₓ α] [DistribMulAction R α] (S : Subring R) : DistribMulAction S α :=
  S.toSubsemiring.DistribMulAction

/-- The action by a subring is the action by the underlying ring. -/
instance [Monoidₓ α] [MulDistribMulAction R α] (S : Subring R) : MulDistribMulAction S α :=
  S.toSubsemiring.MulDistribMulAction

/-- The action by a subring is the action by the underlying ring. -/
instance [Zero α] [SmulWithZero R α] (S : Subring R) : SmulWithZero S α :=
  S.toSubsemiring.SmulWithZero

/-- The action by a subring is the action by the underlying ring. -/
instance [Zero α] [MulActionWithZero R α] (S : Subring R) : MulActionWithZero S α :=
  S.toSubsemiring.MulActionWithZero

/-- The action by a subring is the action by the underlying ring. -/
instance [AddCommMonoidₓ α] [Module R α] (S : Subring R) : Module S α :=
  S.toSubsemiring.Module

/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smul_comm_class_left : SmulCommClass (center R) R R :=
  Subsemiring.center.smul_comm_class_left

/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smul_comm_class_right : SmulCommClass R (center R) R :=
  Subsemiring.center.smul_comm_class_right

end Subring

end Actions

/-- The subgroup of positive units of a linear ordered semiring. -/
-- while this definition is not about subrings, this is the earliest we have
-- both ordered ring structures and submonoids available
def Units.posSubgroup (R : Type _) [LinearOrderedSemiring R] : Subgroup Rˣ :=
  { (posSubmonoid R).comap (Units.coeHom R) with Carrier := { x | (0 : R) < x },
    inv_mem' := fun x => Units.inv_pos.mpr }

@[simp]
theorem Units.mem_pos_subgroup {R : Type _} [LinearOrderedSemiring R] (u : Rˣ) :
    u ∈ Units.posSubgroup R ↔ (0 : R) < u :=
  Iff.rfl

