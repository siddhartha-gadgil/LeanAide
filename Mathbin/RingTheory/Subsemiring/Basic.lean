/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Ring.Equiv
import Mathbin.Algebra.Ring.Prod
import Mathbin.Data.Set.Finite
import Mathbin.GroupTheory.Submonoid.Centralizer
import Mathbin.GroupTheory.Submonoid.Membership

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `complete_lattice` structure,
`subtype` and `inclusion` ring homomorphisms, subsemiring `map`, `comap` and range (`srange`) of
a `ring_hom` etc.
-/


open BigOperators

universe u v w

section AddSubmonoidWithOneClass

/-- `add_submonoid_with_one_class S R` says `S` is a type of subsets `s ≤ R` that contain `0`, `1`,
and are closed under `(+)` -/
class AddSubmonoidWithOneClass (S : Type _) (R : outParam <| Type _) [AddMonoidWithOneₓ R] [SetLike S R] extends
  AddSubmonoidClass S R, OneMemClass S R

variable {S R : Type _} [AddMonoidWithOneₓ R] [SetLike S R] (s : S)

theorem nat_cast_mem [AddSubmonoidWithOneClass S R] (n : ℕ) : (n : R) ∈ s := by
  induction n <;> simp [← zero_mem, ← add_mem, ← one_mem, *]

instance (priority := 74) AddSubmonoidWithOneClass.toAddMonoidWithOne [AddSubmonoidWithOneClass S R] :
    AddMonoidWithOneₓ s :=
  { AddSubmonoidClass.toAddMonoid s with one := ⟨_, one_mem s⟩, natCast := fun n => ⟨n, nat_cast_mem s n⟩,
    nat_cast_zero := Subtype.ext Nat.cast_zeroₓ, nat_cast_succ := fun n => Subtype.ext (Nat.cast_succₓ _) }

end AddSubmonoidWithOneClass

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiringₓ R] (M : Submonoid R)

section SubsemiringClass

/-- `subsemiring_class S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative and an additive submonoid. -/
class SubsemiringClass (S : Type _) (R : outParam <| Type u) [NonAssocSemiringₓ R] [SetLike S R] extends
  SubmonoidClass S R where
  add_mem : ∀ {s : S} {a b : R}, a ∈ s → b ∈ s → a + b ∈ s
  zero_mem : ∀ s : S, (0 : R) ∈ s

-- See note [lower instance priority]
instance (priority := 100) SubsemiringClass.addSubmonoidWithOneClass (S : Type _) (R : outParam <| Type u)
    [NonAssocSemiringₓ R] [SetLike S R] [h : SubsemiringClass S R] : AddSubmonoidWithOneClass S R :=
  { h with }

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

include hSR

theorem coe_nat_mem (n : ℕ) : (n : R) ∈ s := by
  rw [← nsmul_one]
  exact nsmul_mem (one_mem _) _

namespace SubsemiringClass

/-- A subsemiring of a `non_assoc_semiring` inherits a `non_assoc_semiring` structure -/
-- Prefer subclasses of `non_assoc_semiring` over subclasses of `subsemiring_class`.
instance (priority := 75) toNonAssocSemiring : NonAssocSemiringₓ s :=
  Subtype.coe_injective.NonAssocSemiring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance nontrivial [Nontrivial R] : Nontrivial s :=
  (nontrivial_of_ne 0 1) fun H => zero_ne_one (congr_arg Subtype.val H)

instance no_zero_divisors [NoZeroDivisors R] :
    NoZeroDivisors
      s where eq_zero_or_eq_zero_of_mul_eq_zero := fun x y h =>
    Or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero <| Subtype.ext_iff.mp h) (fun h => Or.inl <| Subtype.eq h) fun h =>
      Or.inr <| Subtype.eq h

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := coe }

@[simp]
theorem coe_subtype : (subtype s : s → R) = coe :=
  rfl

omit hSR

/-- A subsemiring of a `semiring` is a `semiring`. -/
-- Prefer subclasses of `semiring` over subclasses of `subsemiring_class`.
instance (priority := 75) toSemiring {R} [Semiringₓ R] [SetLike S R] [SubsemiringClass S R] : Semiringₓ s :=
  Subtype.coe_injective.Semiring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ => rfl

@[simp, norm_cast]
theorem coe_pow {R} [Semiringₓ R] [SetLike S R] [SubsemiringClass S R] (x : s) (n : ℕ) :
    ((x ^ n : s) : R) = (x ^ n : R) := by
  induction' n with n ih
  · simp
    
  · simp [← pow_succₓ, ← ih]
    

/-- A subsemiring of a `comm_semiring` is a `comm_semiring`. -/
instance toCommSemiring {R} [CommSemiringₓ R] [SetLike S R] [SubsemiringClass S R] : CommSemiringₓ s :=
  Subtype.coe_injective.CommSemiring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ => rfl

/-- A subsemiring of an `ordered_semiring` is an `ordered_semiring`. -/
instance toOrderedSemiring {R} [OrderedSemiring R] [SetLike S R] [SubsemiringClass S R] : OrderedSemiring s :=
  Subtype.coe_injective.OrderedSemiring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ => rfl

/-- A subsemiring of an `ordered_comm_semiring` is an `ordered_comm_semiring`. -/
instance toOrderedCommSemiring {R} [OrderedCommSemiring R] [SetLike S R] [SubsemiringClass S R] :
    OrderedCommSemiring s :=
  Subtype.coe_injective.OrderedCommSemiring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

/-- A subsemiring of a `linear_ordered_semiring` is a `linear_ordered_semiring`. -/
instance toLinearOrderedSemiring {R} [LinearOrderedSemiring R] [SetLike S R] [SubsemiringClass S R] :
    LinearOrderedSemiring s :=
  Subtype.coe_injective.LinearOrderedSemiring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-! Note: currently, there is no `linear_ordered_comm_semiring`. -/


end SubsemiringClass

end SubsemiringClass

variable [NonAssocSemiringₓ S] [NonAssocSemiringₓ T]

/-- A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative and an additive
submonoid. -/
structure Subsemiring (R : Type u) [NonAssocSemiringₓ R] extends Submonoid R, AddSubmonoid R

/-- Reinterpret a `subsemiring` as a `submonoid`. -/
add_decl_doc Subsemiring.toSubmonoid

/-- Reinterpret a `subsemiring` as an `add_submonoid`. -/
add_decl_doc Subsemiring.toAddSubmonoid

namespace Subsemiring

instance : SetLike (Subsemiring R) R where
  coe := Subsemiring.Carrier
  coe_injective' := fun p q h => by
    cases p <;> cases q <;> congr

instance : SubsemiringClass (Subsemiring R) R where
  zero_mem := zero_mem'
  add_mem := add_mem'
  one_mem := one_mem'
  mul_mem := mul_mem'

@[simp]
theorem mem_carrier {s : Subsemiring R} {x : R} : x ∈ s.Carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two subsemirings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subsemiring with a new `carrier` equal to the old one. Useful to fix definitional
equalities.-/
protected def copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : Subsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with Carrier := s }

@[simp]
theorem coe_copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem to_submonoid_injective : Function.Injective (toSubmonoid : Subsemiring R → Submonoid R)
  | r, s, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem to_submonoid_strict_mono : StrictMono (toSubmonoid : Subsemiring R → Submonoid R) := fun _ _ => id

@[mono]
theorem to_submonoid_mono : Monotone (toSubmonoid : Subsemiring R → Submonoid R) :=
  to_submonoid_strict_mono.Monotone

theorem to_add_submonoid_injective : Function.Injective (toAddSubmonoid : Subsemiring R → AddSubmonoid R)
  | r, s, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem to_add_submonoid_strict_mono : StrictMono (toAddSubmonoid : Subsemiring R → AddSubmonoid R) := fun _ _ => id

@[mono]
theorem to_add_submonoid_mono : Monotone (toAddSubmonoid : Subsemiring R → AddSubmonoid R) :=
  to_add_submonoid_strict_mono.Monotone

/-- Construct a `subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sm : Submonoid R) (hm : ↑sm = s) (sa : AddSubmonoid R) (ha : ↑sa = s) :
    Subsemiring R where
  Carrier := s
  zero_mem' := ha ▸ sa.zero_mem
  one_mem' := hm ▸ sm.one_mem
  add_mem' := fun x y => by
    simpa only [ha] using sa.add_mem
  mul_mem' := fun x y => by
    simpa only [hm] using sm.mul_mem

@[simp]
theorem coe_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s) :
    (Subsemiring.mk' s sm hm sa ha : Set R) = s :=
  rfl

@[simp]
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s) {x : R} :
    x ∈ Subsemiring.mk' s sm hm sa ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mk'_to_submonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s) :
    (Subsemiring.mk' s sm hm sa ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
theorem mk'_to_add_submonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s) :
    (Subsemiring.mk' s sm hm sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm

end Subsemiring

namespace Subsemiring

variable (s : Subsemiring R)

/-- A subsemiring contains the semiring's 1. -/
protected theorem one_mem : (1 : R) ∈ s :=
  one_mem s

/-- A subsemiring contains the semiring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem s

/-- A subsemiring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subsemiring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- Product of a list of elements in a `subsemiring` is in the `subsemiring`. -/
theorem list_prod_mem {R : Type _} [Semiringₓ R] (s : Subsemiring R) {l : List R} :
    (∀, ∀ x ∈ l, ∀, x ∈ s) → l.Prod ∈ s :=
  list_prod_mem

/-- Sum of a list of elements in a `subsemiring` is in the `subsemiring`. -/
protected theorem list_sum_mem {l : List R} : (∀, ∀ x ∈ l, ∀, x ∈ s) → l.Sum ∈ s :=
  list_sum_mem

/-- Product of a multiset of elements in a `subsemiring` of a `comm_semiring`
    is in the `subsemiring`. -/
protected theorem multiset_prod_mem {R} [CommSemiringₓ R] (s : Subsemiring R) (m : Multiset R) :
    (∀, ∀ a ∈ m, ∀, a ∈ s) → m.Prod ∈ s :=
  multiset_prod_mem m

/-- Sum of a multiset of elements in a `subsemiring` of a `semiring` is
in the `add_subsemiring`. -/
protected theorem multiset_sum_mem (m : Multiset R) : (∀, ∀ a ∈ m, ∀, a ∈ s) → m.Sum ∈ s :=
  multiset_sum_mem m

/-- Product of elements of a subsemiring of a `comm_semiring` indexed by a `finset` is in the
    subsemiring. -/
protected theorem prod_mem {R : Type _} [CommSemiringₓ R] (s : Subsemiring R) {ι : Type _} {t : Finset ι} {f : ι → R}
    (h : ∀, ∀ c ∈ t, ∀, f c ∈ s) : (∏ i in t, f i) ∈ s :=
  prod_mem h

/-- Sum of elements in an `subsemiring` of an `semiring` indexed by a `finset`
is in the `add_subsemiring`. -/
protected theorem sum_mem (s : Subsemiring R) {ι : Type _} {t : Finset ι} {f : ι → R} (h : ∀, ∀ c ∈ t, ∀, f c ∈ s) :
    (∑ i in t, f i) ∈ s :=
  sum_mem h

/-- A subsemiring of a `non_assoc_semiring` inherits a `non_assoc_semiring` structure -/
instance toNonAssocSemiring : NonAssocSemiringₓ s :=
  { s.toSubmonoid.toMulOneClass, s.toAddSubmonoid.toAddCommMonoid with mul_zero := fun x => Subtype.eq <| mul_zero x,
    zero_mul := fun x => Subtype.eq <| zero_mul x, right_distrib := fun x y z => Subtype.eq <| right_distrib x y z,
    left_distrib := fun x y z => Subtype.eq <| left_distrib x y z, natCast := fun n => ⟨n, coe_nat_mem s n⟩,
    nat_cast_zero := by
      simp [← Nat.castₓ] <;> rfl,
    nat_cast_succ := fun _ => by
      simp [← Nat.castₓ] <;> rfl }

@[simp, norm_cast]
theorem coe_one : ((1 : s) : R) = (1 : R) :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl

instance nontrivial [Nontrivial R] : Nontrivial s :=
  (nontrivial_of_ne 0 1) fun H => zero_ne_one (congr_arg Subtype.val H)

protected theorem pow_mem {R : Type _} [Semiringₓ R] (s : Subsemiring R) {x : R} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n

instance no_zero_divisors [NoZeroDivisors R] :
    NoZeroDivisors
      s where eq_zero_or_eq_zero_of_mul_eq_zero := fun x y h =>
    Or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero <| Subtype.ext_iff.mp h) (fun h => Or.inl <| Subtype.eq h) fun h =>
      Or.inr <| Subtype.eq h

/-- A subsemiring of a `semiring` is a `semiring`. -/
instance toSemiring {R} [Semiringₓ R] (s : Subsemiring R) : Semiringₓ s :=
  { s.toNonAssocSemiring, s.toSubmonoid.toMonoid with }

@[simp, norm_cast]
theorem coe_pow {R} [Semiringₓ R] (s : Subsemiring R) (x : s) (n : ℕ) : ((x ^ n : s) : R) = (x ^ n : R) := by
  induction' n with n ih
  · simp
    
  · simp [← pow_succₓ, ← ih]
    

/-- A subsemiring of a `comm_semiring` is a `comm_semiring`. -/
instance toCommSemiring {R} [CommSemiringₓ R] (s : Subsemiring R) : CommSemiringₓ s :=
  { s.toSemiring with mul_comm := fun _ _ => Subtype.eq <| mul_comm _ _ }

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { s.toSubmonoid.Subtype, s.toAddSubmonoid.Subtype with toFun := coe }

@[simp]
theorem coe_subtype : ⇑s.Subtype = coe :=
  rfl

/-- A subsemiring of an `ordered_semiring` is an `ordered_semiring`. -/
instance toOrderedSemiring {R} [OrderedSemiring R] (s : Subsemiring R) : OrderedSemiring s :=
  Subtype.coe_injective.OrderedSemiring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ => rfl

/-- A subsemiring of an `ordered_comm_semiring` is an `ordered_comm_semiring`. -/
instance toOrderedCommSemiring {R} [OrderedCommSemiring R] (s : Subsemiring R) : OrderedCommSemiring s :=
  Subtype.coe_injective.OrderedCommSemiring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

/-- A subsemiring of a `linear_ordered_semiring` is a `linear_ordered_semiring`. -/
instance toLinearOrderedSemiring {R} [LinearOrderedSemiring R] (s : Subsemiring R) : LinearOrderedSemiring s :=
  Subtype.coe_injective.LinearOrderedSemiring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-! Note: currently, there is no `linear_ordered_comm_semiring`. -/


protected theorem nsmul_mem {x : R} (hx : x ∈ s) (n : ℕ) : n • x ∈ s :=
  nsmul_mem hx n

@[simp]
theorem mem_to_submonoid {s : Subsemiring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_to_submonoid (s : Subsemiring R) : (s.toSubmonoid : Set R) = s :=
  rfl

@[simp]
theorem mem_to_add_submonoid {s : Subsemiring R} {x : R} : x ∈ s.toAddSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_to_add_submonoid (s : Subsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl

/-- The subsemiring `R` of the semiring `R`. -/
instance : HasTop (Subsemiring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : Subsemiring R) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : Subsemiring R) : Set R) = Set.Univ :=
  rfl

/-- The preimage of a subsemiring along a ring homomorphism is a subsemiring. -/
def comap (f : R →+* S) (s : Subsemiring S) : Subsemiring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubmonoid.comap (f : R →+ S) with Carrier := f ⁻¹' s }

@[simp]
theorem coe_comap (s : Subsemiring S) (f : R →+* S) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
theorem mem_comap {s : Subsemiring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_comap (s : Subsemiring T) (g : S →+* T) (f : R →+* S) : (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-- The image of a subsemiring along a ring homomorphism is a subsemiring. -/
def map (f : R →+* S) (s : Subsemiring R) : Subsemiring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubmonoid.map (f : R →+ S) with Carrier := f '' s }

@[simp]
theorem coe_map (f : R →+* S) (s : Subsemiring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
theorem mem_map {f : R →+* S} {s : Subsemiring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
  Set.mem_image_iff_bex

@[simp]
theorem map_id : s.map (RingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

theorem map_le_iff_le_comap {f : R →+* S} {s : Subsemiring R} {t : Subsemiring S} : s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff

theorem gc_map_comap (f : R →+* S) : GaloisConnection (map f) (comap f) := fun S T => map_le_iff_le_comap

/-- A subsemiring is isomorphic to its image under an injective function -/
noncomputable def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equivₓ.Set.image f s hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _),
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }

@[simp]
theorem coe_equiv_map_of_injective_apply (f : R →+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end Subsemiring

namespace RingHom

variable (g : S →+* T) (f : R →+* S)

/-- The range of a ring homomorphism is a subsemiring. See Note [range copy pattern]. -/
def srange : Subsemiring S :=
  ((⊤ : Subsemiring R).map f).copy (Set.Range f) Set.image_univ.symm

@[simp]
theorem coe_srange : (f.srange : Set S) = Set.Range f :=
  rfl

@[simp]
theorem mem_srange {f : R →+* S} {y : S} : y ∈ f.srange ↔ ∃ x, f x = y :=
  Iff.rfl

theorem srange_eq_map (f : R →+* S) : f.srange = (⊤ : Subsemiring R).map f := by
  ext
  simp

theorem mem_srange_self (f : R →+* S) (x : R) : f x ∈ f.srange :=
  mem_srange.mpr ⟨x, rfl⟩

theorem map_srange : f.srange.map g = (g.comp f).srange := by
  simpa only [← srange_eq_map] using (⊤ : Subsemiring R).map_map g f

/-- The range of a morphism of semirings is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype S`.-/
instance fintypeSrange [Fintype R] [DecidableEq S] (f : R →+* S) : Fintype (srange f) :=
  Set.fintypeRange f

end RingHom

namespace Subsemiring

instance : HasBot (Subsemiring R) :=
  ⟨(Nat.castRingHom R).srange⟩

instance : Inhabited (Subsemiring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : Subsemiring R) : Set R) = Set.Range (coe : ℕ → R) :=
  (Nat.castRingHom R).coe_srange

theorem mem_bot {x : R} : x ∈ (⊥ : Subsemiring R) ↔ ∃ n : ℕ, ↑n = x :=
  RingHom.mem_srange

/-- The inf of two subsemirings is their intersection. -/
instance : HasInf (Subsemiring R) :=
  ⟨fun s t => { s.toSubmonoid⊓t.toSubmonoid, s.toAddSubmonoid⊓t.toAddSubmonoid with Carrier := s ∩ t }⟩

@[simp]
theorem coe_inf (p p' : Subsemiring R) : ((p⊓p' : Subsemiring R) : Set R) = p ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : Subsemiring R} {x : R} : x ∈ p⊓p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : HasInfₓ (Subsemiring R) :=
  ⟨fun s =>
    Subsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, Subsemiring.toSubmonoid t)
      (by
        simp )
      (⨅ t ∈ s, Subsemiring.toAddSubmonoid t)
      (by
        simp )⟩

@[simp, norm_cast]
theorem coe_Inf (S : Set (Subsemiring R)) : ((inf S : Subsemiring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

theorem mem_Inf {S : Set (Subsemiring R)} {x : R} : x ∈ inf S ↔ ∀, ∀ p ∈ S, ∀, x ∈ p :=
  Set.mem_Inter₂

@[simp]
theorem Inf_to_submonoid (s : Set (Subsemiring R)) : (inf s).toSubmonoid = ⨅ t ∈ s, Subsemiring.toSubmonoid t :=
  mk'_to_submonoid _ _

@[simp]
theorem Inf_to_add_submonoid (s : Set (Subsemiring R)) :
    (inf s).toAddSubmonoid = ⨅ t ∈ s, Subsemiring.toAddSubmonoid t :=
  mk'_to_add_submonoid _ _

/-- Subsemirings of a semiring form a complete lattice. -/
instance : CompleteLattice (Subsemiring R) :=
  { completeLatticeOfInf (Subsemiring R) fun s =>
      IsGlb.of_image (fun s t => show (s : Set R) ≤ t ↔ s ≤ t from SetLike.coe_subset_coe) is_glb_binfi with
    bot := ⊥,
    bot_le := fun s x hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ coe_nat_mem s n,
    top := ⊤, le_top := fun s x hx => trivialₓ, inf := (·⊓·), inf_le_left := fun s t x => And.left,
    inf_le_right := fun s t x => And.right, le_inf := fun s t₁ t₂ h₁ h₂ x hx => ⟨h₁ hx, h₂ hx⟩ }

theorem eq_top_iff' (A : Subsemiring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

section Center

/-- The center of a semiring `R` is the set of elements that commute with everything in `R` -/
def center (R) [Semiringₓ R] : Subsemiring R :=
  { Submonoid.center R with Carrier := Set.Center R, zero_mem' := Set.zero_mem_center R,
    add_mem' := fun a b => Set.add_mem_center }

theorem coe_center (R) [Semiringₓ R] : ↑(center R) = Set.Center R :=
  rfl

@[simp]
theorem center_to_submonoid (R) [Semiringₓ R] : (center R).toSubmonoid = Submonoid.center R :=
  rfl

theorem mem_center_iff {R} [Semiringₓ R] {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Iff.rfl

instance decidableMemCenter {R} [Semiringₓ R] [DecidableEq R] [Fintype R] : DecidablePred (· ∈ center R) := fun _ =>
  decidableOfIff' _ mem_center_iff

@[simp]
theorem center_eq_top (R) [CommSemiringₓ R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

/-- The center is commutative. -/
instance {R} [Semiringₓ R] : CommSemiringₓ (center R) :=
  { Submonoid.center.commMonoid, (center R).toSemiring with }

end Center

section Centralizer

/-- The centralizer of a set as subsemiring. -/
def centralizer {R} [Semiringₓ R] (s : Set R) : Subsemiring R :=
  { Submonoid.centralizer s with Carrier := s.Centralizer, zero_mem' := Set.zero_mem_centralizer _,
    add_mem' := fun x y hx hy => Set.add_mem_centralizer hx hy }

@[simp, norm_cast]
theorem coe_centralizer {R} [Semiringₓ R] (s : Set R) : (centralizer s : Set R) = s.Centralizer :=
  rfl

theorem centralizer_to_submonoid {R} [Semiringₓ R] (s : Set R) :
    (centralizer s).toSubmonoid = Submonoid.centralizer s :=
  rfl

theorem mem_centralizer_iff {R} [Semiringₓ R] {s : Set R} {z : R} : z ∈ centralizer s ↔ ∀, ∀ g ∈ s, ∀, g * z = z * g :=
  Iff.rfl

theorem centralizer_le {R} [Semiringₓ R] (s t : Set R) (h : s ⊆ t) : centralizer t ≤ centralizer s :=
  Set.centralizer_subset h

@[simp]
theorem centralizer_univ {R} [Semiringₓ R] : centralizer Set.Univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

end Centralizer

/-- The `subsemiring` generated by a set. -/
def closure (s : Set R) : Subsemiring R :=
  inf { S | s ⊆ S }

theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : Subsemiring R, s ⊆ S → x ∈ S :=
  mem_Inf

/-- The subsemiring generated by a set includes the set. -/
@[simp]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun x hx => mem_closure.2 fun S hS => hS hx

theorem not_mem_of_not_mem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h => hP (subset_closure h)

/-- A subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : Subsemiring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => Inf_le h⟩

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure

theorem closure_eq_of_le {s : Set R} {t : Subsemiring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) : closure s = t :=
  le_antisymmₓ (closure_le.2 h₁) h₂

theorem mem_map_equiv {f : R ≃+* S} {K : Subsemiring R} {x : S} : x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (↑K) f.toEquiv x

theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subsemiring R) : K.map (f : R →+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)

theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subsemiring S) : K.comap (f : R →+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end Subsemiring

namespace Submonoid

/-- The additive closure of a submonoid is a subsemiring. -/
def subsemiringClosure (M : Submonoid R) : Subsemiring R :=
  { AddSubmonoid.closure (M : Set R) with one_mem' := AddSubmonoid.mem_closure.mpr fun y hy => hy M.one_mem,
    mul_mem' := fun x y => MulMemClass.mul_mem_add_closure }

theorem subsemiring_closure_coe : (M.subsemiringClosure : Set R) = AddSubmonoid.closure (M : Set R) :=
  rfl

theorem subsemiring_closure_to_add_submonoid : M.subsemiringClosure.toAddSubmonoid = AddSubmonoid.closure (M : Set R) :=
  rfl

/-- The `subsemiring` generated by a multiplicative submonoid coincides with the
`subsemiring.closure` of the submonoid itself . -/
theorem subsemiring_closure_eq_closure : M.subsemiringClosure = Subsemiring.closure (M : Set R) := by
  ext
  refine' ⟨fun hx => _, fun hx => (subsemiring.mem_closure.mp hx) M.subsemiring_closure fun s sM => _⟩ <;>
    rintro - ⟨H1, rfl⟩ <;> rintro - ⟨H2, rfl⟩
  · exact add_submonoid.mem_closure.mp hx H1.to_add_submonoid H2
    
  · exact H2 sM
    

end Submonoid

namespace Subsemiring

@[simp]
theorem closure_submonoid_closure (s : Set R) : closure ↑(Submonoid.closure s) = closure s :=
  le_antisymmₓ (closure_le.mpr fun y hy => (Submonoid.mem_closure.mp hy) (closure s).toSubmonoid subset_closure)
    (closure_mono Submonoid.subset_closure)

/-- The elements of the subsemiring closure of `M` are exactly the elements of the additive closure
of a multiplicative submonoid `M`. -/
theorem coe_closure_eq (s : Set R) : (closure s : Set R) = AddSubmonoid.closure (Submonoid.closure s : Set R) := by
  simp [Submonoid.subsemiring_closure_to_add_submonoid, ← Submonoid.subsemiring_closure_eq_closure]

theorem mem_closure_iff {s : Set R} {x} : x ∈ closure s ↔ x ∈ AddSubmonoid.closure (Submonoid.closure s : Set R) :=
  Set.ext_iff.mp (coe_closure_eq s) x

@[simp]
theorem closure_add_submonoid_closure {s : Set R} : closure ↑(AddSubmonoid.closure s) = closure s := by
  ext x
  refine' ⟨fun hx => _, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  rintro - ⟨H, rfl⟩
  rintro - ⟨J, rfl⟩
  refine' (add_submonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.to_add_submonoid fun y hy => _
  refine' (submonoid.mem_closure.mp hy) H.to_submonoid fun z hz => _
  exact (add_submonoid.mem_closure.mp hz) H.to_add_submonoid fun w hw => J hw

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_eliminator]
theorem closure_induction {s : Set R} {p : R → Prop} {x} (h : x ∈ closure s) (Hs : ∀, ∀ x ∈ s, ∀, p x) (H0 : p 0)
    (H1 : p 1) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨p, Hmul, H1, Hadd, H0⟩).2 Hs h

/-- An induction principle for closure membership for predicates with two arguments. -/
@[elab_as_eliminator]
theorem closure_induction₂ {s : Set R} {p : R → R → Prop} {x} {y : R} (hx : x ∈ closure s) (hy : y ∈ closure s)
    (Hs : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, p x y) (H0_left : ∀ x, p 0 x) (H0_right : ∀ x, p x 0) (H1_left : ∀ x, p 1 x)
    (H1_right : ∀ x, p x 1) (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂)) (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p x y :=
  closure_induction hx
    (fun x₁ x₁s => closure_induction hy (Hs x₁ x₁s) (H0_right x₁) (H1_right x₁) (Hadd_right x₁) (Hmul_right x₁))
    (H0_left y) (H1_left y) (fun z z' => Hadd_left z z' y) fun z z' => Hmul_left z z' y

theorem mem_closure_iff_exists_list {R} [Semiringₓ R] {s : Set R} {x} :
    x ∈ closure s ↔ ∃ L : List (List R), (∀, ∀ t ∈ L, ∀, ∀, ∀ y ∈ t, ∀, y ∈ s) ∧ (L.map List.prod).Sum = x :=
  ⟨fun hx =>
    AddSubmonoid.closure_induction (mem_closure_iff.1 hx)
      (fun x hx =>
        suffices ∃ t : List R, (∀, ∀ y ∈ t, ∀, y ∈ s) ∧ t.Prod = x from
          let ⟨t, ht1, ht2⟩ := this
          ⟨[t], List.forall_mem_singletonₓ.2 ht1, by
            rw [List.map_singleton, List.sum_singleton, ht2]⟩
        Submonoid.closure_induction hx (fun x hx => ⟨[x], List.forall_mem_singletonₓ.2 hx, one_mulₓ x⟩)
          ⟨[], List.forall_mem_nilₓ _, rfl⟩ fun x y ⟨t, ht1, ht2⟩ ⟨u, hu1, hu2⟩ =>
          ⟨t ++ u, List.forall_mem_appendₓ.2 ⟨ht1, hu1⟩, by
            rw [List.prod_append, ht2, hu2]⟩)
      ⟨[], List.forall_mem_nilₓ _, rfl⟩ fun x y ⟨L, HL1, HL2⟩ ⟨M, HM1, HM2⟩ =>
      ⟨L ++ M, List.forall_mem_appendₓ.2 ⟨HL1, HM1⟩, by
        rw [List.map_append, List.sum_append, HL2, HM2]⟩,
    fun ⟨L, HL1, HL2⟩ =>
    HL2 ▸
      list_sum_mem fun r hr =>
        let ⟨t, ht1, ht2⟩ := List.mem_mapₓ.1 hr
        ht2 ▸ list_prod_mem _ fun y hy => subset_closure <| HL1 t ht1 y hy⟩

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) coe where
  choice := fun s _ => closure s
  gc := fun s t => closure_le
  le_l_u := fun s => subset_closure
  choice_eq := fun s h => rfl

variable {R}

/-- Closure of a subsemiring `S` equals `S`. -/
theorem closure_eq (s : Subsemiring R) : closure (s : Set R) = s :=
  (Subsemiring.gi R).l_u_eq s

@[simp]
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (Subsemiring.gi R).gc.l_bot

@[simp]
theorem closure_univ : closure (Set.Univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤

theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s⊔closure t :=
  (Subsemiring.gi R).gc.l_sup

theorem closure_Union {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subsemiring.gi R).gc.l_supr

theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀s) = ⨆ t ∈ s, closure t :=
  (Subsemiring.gi R).gc.l_Sup

theorem map_sup (s t : Subsemiring R) (f : R →+* S) : (s⊔t).map f = s.map f⊔t.map f :=
  (gc_map_comap f).l_sup

theorem map_supr {ι : Sort _} (f : R →+* S) (s : ι → Subsemiring R) : (supr s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_supr

theorem comap_inf (s t : Subsemiring S) (f : R →+* S) : (s⊓t).comap f = s.comap f⊓t.comap f :=
  (gc_map_comap f).u_inf

theorem comap_infi {ι : Sort _} (f : R →+* S) (s : ι → Subsemiring S) : (infi s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_infi

@[simp]
theorem map_bot (f : R →+* S) : (⊥ : Subsemiring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : R →+* S) : (⊤ : Subsemiring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- Given `subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is `s × t`
as a subsemiring of `R × S`. -/
def prod (s : Subsemiring R) (t : Subsemiring S) : Subsemiring (R × S) :=
  { s.toSubmonoid.Prod t.toSubmonoid, s.toAddSubmonoid.Prod t.toAddSubmonoid with
    Carrier := (s : Set R) ×ˢ (t : Set S) }

@[norm_cast]
theorem coe_prod (s : Subsemiring R) (t : Subsemiring S) : (s.Prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl

theorem mem_prod {s : Subsemiring R} {t : Subsemiring S} {p : R × S} : p ∈ s.Prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[mono]
theorem prod_mono ⦃s₁ s₂ : Subsemiring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ ≤ t₂) :
    s₁.Prod t₁ ≤ s₂.Prod t₂ :=
  Set.prod_mono hs ht

theorem prod_mono_right (s : Subsemiring R) : Monotone fun t : Subsemiring S => s.Prod t :=
  prod_mono (le_reflₓ s)

theorem prod_mono_left (t : Subsemiring S) : Monotone fun s : Subsemiring R => s.Prod t := fun s₁ s₂ hs =>
  prod_mono hs (le_reflₓ t)

theorem prod_top (s : Subsemiring R) : s.Prod (⊤ : Subsemiring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by
    simp [← mem_prod, ← MonoidHom.coe_fst]

theorem top_prod (s : Subsemiring S) : (⊤ : Subsemiring R).Prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by
    simp [← mem_prod, ← MonoidHom.coe_snd]

@[simp]
theorem top_prod_top : (⊤ : Subsemiring R).Prod (⊤ : Subsemiring S) = ⊤ :=
  (top_prod _).trans <| comap_top _

/-- Product of subsemirings is isomorphic to their product as monoids. -/
def prodEquiv (s : Subsemiring R) (t : Subsemiring S) : s.Prod t ≃+* s × t :=
  { Equivₓ.Set.prod ↑s ↑t with map_mul' := fun x y => rfl, map_add' := fun x y => rfl }

theorem mem_supr_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R} (hS : Directed (· ≤ ·) S) {x : R} :
    (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_supr S i) hi⟩
  let U : Subsemiring R :=
    Subsemiring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubmonoid)
      (Submonoid.coe_supr_of_directed <| hS.mono_comp _ fun _ _ => id) (⨆ i, (S i).toAddSubmonoid)
      (AddSubmonoid.coe_supr_of_directed <| hS.mono_comp _ fun _ _ => id)
  suffices (⨆ i, S i) ≤ U by
    simpa using @this x
  exact supr_le fun i x hx => Set.mem_Union.2 ⟨i, hx⟩

theorem coe_supr_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subsemiring R) : Set R) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by
    simp [← mem_supr_of_directed hS]

theorem mem_Sup_of_directed_on {S : Set (Subsemiring R)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S) {x : R} :
    x ∈ sup S ↔ ∃ s ∈ S, x ∈ s := by
  have : Nonempty S := Sne.to_subtype
  simp only [← Sup_eq_supr', ← mem_supr_of_directed hS.directed_coe, ← SetCoe.exists, ← Subtype.coe_mk]

theorem coe_Sup_of_directed_on {S : Set (Subsemiring R)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S) :
    (↑(sup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by
    simp [← mem_Sup_of_directed_on Sne hS]

end Subsemiring

namespace RingHom

variable [NonAssocSemiringₓ T] {s : Subsemiring R}

variable {σR σS : Type _}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

open Subsemiring

/-- Restriction of a ring homomorphism to a subsemiring of the domain. -/
def restrict (f : R →+* S) (s : σR) : s →+* S :=
  f.comp <| SubsemiringClass.subtype s

@[simp]
theorem restrict_apply (f : R →+* S) {s : σR} (x : s) : f.restrict s x = f x :=
  rfl

/-- Restriction of a ring homomorphism to a subsemiring of the codomain. -/
def codRestrict (f : R →+* S) (s : σS) (h : ∀ x, f x ∈ s) : R →+* s :=
  { (f : R →* S).codRestrict s h, (f : R →+ S).codRestrict s h with toFun := fun n => ⟨f n, h n⟩ }

/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `set.range_factorization`. -/
def srangeRestrict (f : R →+* S) : R →+* f.srange :=
  f.codRestrict f.srange f.mem_srange_self

@[simp]
theorem coe_srange_restrict (f : R →+* S) (x : R) : (f.srangeRestrict x : S) = f x :=
  rfl

theorem srange_restrict_surjective (f : R →+* S) : Function.Surjective f.srangeRestrict := fun ⟨y, hy⟩ =>
  let ⟨x, hx⟩ := mem_srange.mp hy
  ⟨x, Subtype.ext hx⟩

theorem srange_top_iff_surjective {f : R →+* S} : f.srange = (⊤ : Subsemiring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <|
    Iff.trans
      (by
        rw [coe_srange, coe_top])
      Set.range_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
theorem srange_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) : f.srange = (⊤ : Subsemiring S) :=
  srange_top_iff_surjective.2 hf

/-- The subsemiring of elements `x : R` such that `f x = g x` -/
def eqSlocus (f g : R →+* S) : Subsemiring R :=
  { (f : R →* S).eqMlocus g, (f : R →+ S).eqMlocus g with Carrier := { x | f x = g x } }

/-- If two ring homomorphisms are equal on a set, then they are equal on its subsemiring closure. -/
theorem eq_on_sclosure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqSlocus g from closure_le.2 h

theorem eq_of_eq_on_stop {f g : R →+* S} (h : Set.EqOn f g (⊤ : Subsemiring R)) : f = g :=
  ext fun x => h trivialₓ

theorem eq_of_eq_on_sdense {s : Set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) : f = g :=
  eq_of_eq_on_stop <| hs ▸ eq_on_sclosure h

theorem sclosure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
theorem map_sclosure (f : R →+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  le_antisymmₓ
    (map_le_iff_le_comap.2 <| le_transₓ (closure_mono <| Set.subset_preimage_image _ _) (sclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)

end RingHom

namespace Subsemiring

open RingHom

/-- The ring homomorphism associated to an inclusion of subsemirings. -/
def inclusion {S T : Subsemiring R} (h : S ≤ T) : S →+* T :=
  S.Subtype.codRestrict _ fun x => h x.2

@[simp]
theorem srange_subtype (s : Subsemiring R) : s.Subtype.srange = s :=
  SetLike.coe_injective <| (coe_srange _).trans Subtype.range_coe

@[simp]
theorem range_fst : (fst R S).srange = ⊤ :=
  (fst R S).srange_top_of_surjective <| Prod.fst_surjectiveₓ

@[simp]
theorem range_snd : (snd R S).srange = ⊤ :=
  (snd R S).srange_top_of_surjective <| Prod.snd_surjective

@[simp]
theorem prod_bot_sup_bot_prod (s : Subsemiring R) (t : Subsemiring S) : s.Prod ⊥⊔prod ⊥ t = s.Prod t :=
  (le_antisymmₓ (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le))) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem ((le_sup_left : s.Prod ⊥ ≤ s.Prod ⊥⊔prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t ≤ s.Prod ⊥⊔prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

end Subsemiring

namespace RingEquiv

variable {s t : Subsemiring R}

/-- Makes the identity isomorphism from a proof two subsemirings of a multiplicative
    monoid are equal. -/
def subsemiringCongr (h : s = t) : s ≃+* t :=
  { Equivₓ.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`ring_hom.srange`. -/
def sofLeftInverse {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.srange :=
  { f.srangeRestrict with toFun := fun x => f.srangeRestrict x, invFun := fun x => (g ∘ f.srange.Subtype) x,
    left_inv := h,
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := RingHom.mem_srange.mp x.Prop
        show f (g x) = x by
          rw [← hx', h x'] }

@[simp]
theorem sof_left_inverse_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(sofLeftInverse h x) = f x :=
  rfl

@[simp]
theorem sof_left_inverse_symm_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : f.srange) :
    (sofLeftInverse h).symm x = g x :=
  rfl

/-- Given an equivalence `e : R ≃+* S` of semirings and a subsemiring `s` of `R`,
`subsemiring_map e s` is the induced equivalence between `s` and `s.map e` -/
@[simps]
def subsemiringMap (e : R ≃+* S) (s : Subsemiring R) : s ≃+* s.map e.toRingHom :=
  { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid, e.toMulEquiv.submonoidMap s.toSubmonoid with }

end RingEquiv

/-! ### Actions by `subsemiring`s

These are just copies of the definitions about `submonoid` starting from `submonoid.mul_action`.
The only new result is `subsemiring.module`.

When `R` is commutative, `algebra.of_subsemiring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subsemiring

variable {R' α β : Type _}

section NonAssocSemiringₓ

variable [NonAssocSemiringₓ R']

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [HasSmul R' α] (S : Subsemiring R') : HasSmul S α :=
  S.toSubmonoid.HasSmul

theorem smul_def [HasSmul R' α] {S : Subsemiring R'} (g : S) (m : α) : g • m = (g : R') • m :=
  rfl

instance smul_comm_class_left [HasSmul R' β] [HasSmul α β] [SmulCommClass R' α β] (S : Subsemiring R') :
    SmulCommClass S α β :=
  S.toSubmonoid.smul_comm_class_left

instance smul_comm_class_right [HasSmul α β] [HasSmul R' β] [SmulCommClass α R' β] (S : Subsemiring R') :
    SmulCommClass α S β :=
  S.toSubmonoid.smul_comm_class_right

/-- Note that this provides `is_scalar_tower S R R` which is needed by `smul_mul_assoc`. -/
instance [HasSmul α β] [HasSmul R' α] [HasSmul R' β] [IsScalarTower R' α β] (S : Subsemiring R') :
    IsScalarTower S α β :=
  S.toSubmonoid.IsScalarTower

instance [HasSmul R' α] [HasFaithfulSmul R' α] (S : Subsemiring R') : HasFaithfulSmul S α :=
  S.toSubmonoid.HasFaithfulSmul

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [Zero α] [SmulWithZero R' α] (S : Subsemiring R') : SmulWithZero S α :=
  SmulWithZero.compHom _ S.Subtype.toMonoidWithZeroHom.toZeroHom

end NonAssocSemiringₓ

variable [Semiringₓ R']

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [MulAction R' α] (S : Subsemiring R') : MulAction S α :=
  S.toSubmonoid.MulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [AddMonoidₓ α] [DistribMulAction R' α] (S : Subsemiring R') : DistribMulAction S α :=
  S.toSubmonoid.DistribMulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [Monoidₓ α] [MulDistribMulAction R' α] (S : Subsemiring R') : MulDistribMulAction S α :=
  S.toSubmonoid.MulDistribMulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [Zero α] [MulActionWithZero R' α] (S : Subsemiring R') : MulActionWithZero S α :=
  MulActionWithZero.compHom _ S.Subtype.toMonoidWithZeroHom

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [AddCommMonoidₓ α] [Module R' α] (S : Subsemiring R') : Module S α :=
  { Module.compHom _ S.Subtype with smul := (· • ·) }

/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smul_comm_class_left : SmulCommClass (center R') R' R' :=
  Submonoid.center.smul_comm_class_left

/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smul_comm_class_right : SmulCommClass R' (center R') R' :=
  Submonoid.center.smul_comm_class_right

/-- If all the elements of a set `s` commute, then `closure s` is a commutative monoid. -/
def closureCommSemiringOfComm {s : Set R'} (hcomm : ∀, ∀ a ∈ s, ∀, ∀ b ∈ s, ∀, a * b = b * a) :
    CommSemiringₓ (closure s) :=
  { (closure s).toSemiring with
    mul_comm := fun x y => by
      ext
      simp only [← Subsemiring.coe_mul]
      refine'
        closure_induction₂ x.prop y.prop hcomm
          (fun x => by
            simp only [← zero_mul, ← mul_zero])
          (fun x => by
            simp only [← zero_mul, ← mul_zero])
          (fun x => by
            simp only [← one_mulₓ, ← mul_oneₓ])
          (fun x => by
            simp only [← one_mulₓ, ← mul_oneₓ])
          (fun x y z h₁ h₂ => by
            simp only [← add_mulₓ, ← mul_addₓ, ← h₁, ← h₂])
          (fun x y z h₁ h₂ => by
            simp only [← add_mulₓ, ← mul_addₓ, ← h₁, ← h₂])
          (fun x y z h₁ h₂ => by
            rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc])
          fun x y z h₁ h₂ => by
          rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }

end Subsemiring

end Actions

/-- Submonoid of positive elements of an ordered semiring. -/
-- While this definition is not about `subsemiring`s, this is the earliest we have
-- both `ordered_semiring` and `submonoid` available.
def posSubmonoid (R : Type _) [OrderedSemiring R] [Nontrivial R] : Submonoid R where
  Carrier := { x | 0 < x }
  one_mem' := show (0 : R) < 1 from zero_lt_one
  mul_mem' := fun x y (hx : 0 < x) (hy : 0 < y) => mul_pos hx hy

@[simp]
theorem mem_pos_monoid {R : Type _} [OrderedSemiring R] [Nontrivial R] (u : Rˣ) : ↑u ∈ posSubmonoid R ↔ (0 : R) < u :=
  Iff.rfl

