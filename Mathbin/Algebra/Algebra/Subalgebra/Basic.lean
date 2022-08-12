/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Data.Set.UnionLift

/-!
# Subalgebras over Commutative Semiring

In this file we define `subalgebra`s and the usual operations on them (`map`, `comap`).

More lemmas about `adjoin` can be found in `ring_theory.adjoin`.
-/


universe u u' v w w'

open BigOperators

/-- A subalgebra is a sub(semi)ring that includes the range of `algebra_map`. -/
structure Subalgebra (R : Type u) (A : Type v) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] extends Subsemiring A :
  Type v where
  algebra_map_mem' : ∀ r, algebraMap R A r ∈ carrier
  zero_mem' := (algebraMap R A).map_zero ▸ algebra_map_mem' 0
  one_mem' := (algebraMap R A).map_one ▸ algebra_map_mem' 1

/-- Reinterpret a `subalgebra` as a `subsemiring`. -/
add_decl_doc Subalgebra.toSubsemiring

namespace Subalgebra

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiringₓ R]

variable [Semiringₓ A] [Algebra R A] [Semiringₓ B] [Algebra R B] [Semiringₓ C] [Algebra R C]

include R

instance : SetLike (Subalgebra R A) A where
  coe := Subalgebra.Carrier
  coe_injective' := fun p q h => by
    cases p <;> cases q <;> congr

instance : SubsemiringClass (Subalgebra R A) A where
  add_mem := add_mem'
  mul_mem := mul_mem'
  one_mem := one_mem'
  zero_mem := zero_mem'

@[simp]
theorem mem_carrier {s : Subalgebra R A} {x : A} : x ∈ s.Carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
theorem ext {S T : Subalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_to_subsemiring {S : Subalgebra R A} {x} : x ∈ S.toSubsemiring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_to_subsemiring (S : Subalgebra R A) : (↑S.toSubsemiring : Set A) = S :=
  rfl

theorem to_subsemiring_injective : Function.Injective (toSubsemiring : Subalgebra R A → Subsemiring A) := fun S T h =>
  ext fun x => by
    rw [← mem_to_subsemiring, ← mem_to_subsemiring, h]

theorem to_subsemiring_inj {S U : Subalgebra R A} : S.toSubsemiring = U.toSubsemiring ↔ S = U :=
  to_subsemiring_injective.eq_iff

/-- Copy of a subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : Subalgebra R A where
  Carrier := s
  add_mem' := hs.symm ▸ S.add_mem'
  mul_mem' := hs.symm ▸ S.mul_mem'
  algebra_map_mem' := hs.symm ▸ S.algebra_map_mem'

@[simp]
theorem coe_copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy s hs : Set A) = s :=
  rfl

theorem copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : Subalgebra R A)

theorem algebra_map_mem (r : R) : algebraMap R A r ∈ S :=
  S.algebra_map_mem' r

theorem srange_le : (algebraMap R A).srange ≤ S.toSubsemiring := fun x ⟨r, hr⟩ => hr ▸ S.algebra_map_mem r

theorem range_subset : Set.Range (algebraMap R A) ⊆ S := fun x ⟨r, hr⟩ => hr ▸ S.algebra_map_mem r

theorem range_le : Set.Range (algebraMap R A) ≤ S :=
  S.range_subset

theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  (Algebra.smul_def r x).symm ▸ mul_mem (S.algebra_map_mem r) hx

protected theorem one_mem : (1 : A) ∈ S :=
  one_mem S

protected theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
  mul_mem hx hy

protected theorem pow_mem {x : A} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
  pow_mem hx n

protected theorem zero_mem : (0 : A) ∈ S :=
  zero_mem S

protected theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
  add_mem hx hy

protected theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n • x ∈ S :=
  nsmul_mem hx n

protected theorem coe_nat_mem (n : ℕ) : (n : A) ∈ S :=
  coe_nat_mem S n

protected theorem list_prod_mem {L : List A} (h : ∀, ∀ x ∈ L, ∀, x ∈ S) : L.Prod ∈ S :=
  list_prod_mem h

protected theorem list_sum_mem {L : List A} (h : ∀, ∀ x ∈ L, ∀, x ∈ S) : L.Sum ∈ S :=
  list_sum_mem h

protected theorem multiset_sum_mem {m : Multiset A} (h : ∀, ∀ x ∈ m, ∀, x ∈ S) : m.Sum ∈ S :=
  multiset_sum_mem m h

protected theorem sum_mem {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀, ∀ x ∈ t, ∀, f x ∈ S) : (∑ x in t, f x) ∈ S :=
  sum_mem h

protected theorem multiset_prod_mem {R : Type u} {A : Type v} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A]
    (S : Subalgebra R A) {m : Multiset A} (h : ∀, ∀ x ∈ m, ∀, x ∈ S) : m.Prod ∈ S :=
  multiset_prod_mem m h

protected theorem prod_mem {R : Type u} {A : Type v} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A]
    (S : Subalgebra R A) {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀, ∀ x ∈ t, ∀, f x ∈ S) : (∏ x in t, f x) ∈ S :=
  prod_mem h

instance {R A : Type _} [CommRingₓ R] [Ringₓ A] [Algebra R A] : SubringClass (Subalgebra R A) A :=
  { Subalgebra.subsemiringClass with neg_mem := fun S x hx => neg_one_smul R x ▸ S.smul_mem hx _ }

protected theorem neg_mem {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) {x : A}
    (hx : x ∈ S) : -x ∈ S :=
  neg_mem hx

protected theorem sub_mem {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) {x y : A}
    (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
  sub_mem hx hy

protected theorem zsmul_mem {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) {x : A}
    (hx : x ∈ S) (n : ℤ) : n • x ∈ S :=
  zsmul_mem hx n

protected theorem coe_int_mem {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A)
    (n : ℤ) : (n : A) ∈ S :=
  coe_int_mem S n

/-- The projection from a subalgebra of `A` to an additive submonoid of `A`. -/
def toAddSubmonoid {R : Type u} {A : Type v} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] (S : Subalgebra R A) :
    AddSubmonoid A :=
  S.toSubsemiring.toAddSubmonoid

/-- The projection from a subalgebra of `A` to a submonoid of `A`. -/
def toSubmonoid {R : Type u} {A : Type v} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] (S : Subalgebra R A) :
    Submonoid A :=
  S.toSubsemiring.toSubmonoid

/-- A subalgebra over a ring is also a `subring`. -/
def toSubring {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) : Subring A :=
  { S.toSubsemiring with neg_mem' := fun _ => S.neg_mem }

@[simp]
theorem mem_to_subring {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] {S : Subalgebra R A} {x} :
    x ∈ S.toSubring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_to_subring {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) :
    (↑S.toSubring : Set A) = S :=
  rfl

theorem to_subring_injective {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] :
    Function.Injective (toSubring : Subalgebra R A → Subring A) := fun S T h =>
  ext fun x => by
    rw [← mem_to_subring, ← mem_to_subring, h]

theorem to_subring_inj {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] {S U : Subalgebra R A} :
    S.toSubring = U.toSubring ↔ S = U :=
  to_subring_injective.eq_iff

instance : Inhabited S :=
  ⟨(0 : S.toSubsemiring)⟩

section

/-! `subalgebra`s inherit structure from their `subsemiring` / `semiring` coercions. -/


instance toSemiring {R A} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] (S : Subalgebra R A) : Semiringₓ S :=
  S.toSubsemiring.toSemiring

instance toCommSemiring {R A} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] (S : Subalgebra R A) :
    CommSemiringₓ S :=
  S.toSubsemiring.toCommSemiring

instance toRing {R A} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) : Ringₓ S :=
  S.toSubring.toRing

instance toCommRing {R A} [CommRingₓ R] [CommRingₓ A] [Algebra R A] (S : Subalgebra R A) : CommRingₓ S :=
  S.toSubring.toCommRing

instance toOrderedSemiring {R A} [CommSemiringₓ R] [OrderedSemiring A] [Algebra R A] (S : Subalgebra R A) :
    OrderedSemiring S :=
  S.toSubsemiring.toOrderedSemiring

instance toOrderedCommSemiring {R A} [CommSemiringₓ R] [OrderedCommSemiring A] [Algebra R A] (S : Subalgebra R A) :
    OrderedCommSemiring S :=
  S.toSubsemiring.toOrderedCommSemiring

instance toOrderedRing {R A} [CommRingₓ R] [OrderedRing A] [Algebra R A] (S : Subalgebra R A) : OrderedRing S :=
  S.toSubring.toOrderedRing

instance toOrderedCommRing {R A} [CommRingₓ R] [OrderedCommRing A] [Algebra R A] (S : Subalgebra R A) :
    OrderedCommRing S :=
  S.toSubring.toOrderedCommRing

instance toLinearOrderedSemiring {R A} [CommSemiringₓ R] [LinearOrderedSemiring A] [Algebra R A] (S : Subalgebra R A) :
    LinearOrderedSemiring S :=
  S.toSubsemiring.toLinearOrderedSemiring

/-! There is no `linear_ordered_comm_semiring`. -/


instance toLinearOrderedRing {R A} [CommRingₓ R] [LinearOrderedRing A] [Algebra R A] (S : Subalgebra R A) :
    LinearOrderedRing S :=
  S.toSubring.toLinearOrderedRing

instance toLinearOrderedCommRing {R A} [CommRingₓ R] [LinearOrderedCommRing A] [Algebra R A] (S : Subalgebra R A) :
    LinearOrderedCommRing S :=
  S.toSubring.toLinearOrderedCommRing

end

/-- Convert a `subalgebra` to `submodule` -/
def toSubmodule : Submodule R A where
  Carrier := S
  zero_mem' := (0 : S).2
  add_mem' := fun x y hx hy => (⟨x, hx⟩ + ⟨y, hy⟩ : S).2
  smul_mem' := fun c x hx => (Algebra.smul_def c x).symm ▸ (⟨algebraMap R A c, S.range_le ⟨c, rfl⟩⟩ * ⟨x, hx⟩ : S).2

@[simp]
theorem mem_to_submodule {x} : x ∈ S.toSubmodule ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_to_submodule (S : Subalgebra R A) : (↑S.toSubmodule : Set A) = S :=
  rfl

theorem to_submodule_injective : Function.Injective (toSubmodule : Subalgebra R A → Submodule R A) := fun S T h =>
  ext fun x => by
    rw [← mem_to_submodule, ← mem_to_submodule, h]

theorem to_submodule_inj {S U : Subalgebra R A} : S.toSubmodule = U.toSubmodule ↔ S = U :=
  to_submodule_injective.eq_iff

section

/-! `subalgebra`s inherit structure from their `submodule` coercions. -/


instance module' [Semiringₓ R'] [HasSmul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  S.toSubmodule.module'

instance : Module R S :=
  S.module'

instance [Semiringₓ R'] [HasSmul R' R] [Module R' A] [IsScalarTower R' R A] : IsScalarTower R' R S :=
  S.toSubmodule.IsScalarTower

instance algebra' [CommSemiringₓ R'] [HasSmul R' R] [Algebra R' A] [IsScalarTower R' R A] : Algebra R' S :=
  { ((algebraMap R' A).codRestrict S) fun x => by
      rw [Algebra.algebra_map_eq_smul_one, ← smul_one_smul R x (1 : A), ← Algebra.algebra_map_eq_smul_one]
      exact algebra_map_mem S _ with
    commutes' := fun c x => Subtype.eq <| Algebra.commutes _ _,
    smul_def' := fun c x => Subtype.eq <| Algebra.smul_def _ _ }

instance : Algebra R S :=
  S.algebra'

end

instance no_zero_smul_divisors_bot [NoZeroSmulDivisors R A] : NoZeroSmulDivisors R S :=
  ⟨fun c x h =>
    have : c = 0 ∨ (x : A) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg coe h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩

protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y :=
  rfl

protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y :=
  rfl

protected theorem coe_zero : ((0 : S) : A) = 0 :=
  rfl

protected theorem coe_one : ((1 : S) : A) = 1 :=
  rfl

protected theorem coe_neg {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] {S : Subalgebra R A} (x : S) :
    (↑(-x) : A) = -↑x :=
  rfl

protected theorem coe_sub {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] {S : Subalgebra R A}
    (x y : S) : (↑(x - y) : A) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_smul [Semiringₓ R'] [HasSmul R' R] [Module R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (↑(r • x) : A) = r • ↑x :=
  rfl

@[simp, norm_cast]
theorem coe_algebra_map [CommSemiringₓ R'] [HasSmul R' R] [Algebra R' A] [IsScalarTower R' R A] (r : R') :
    ↑(algebraMap R' S r) = algebraMap R' A r :=
  rfl

protected theorem coe_pow (x : S) (n : ℕ) : (↑(x ^ n) : A) = ↑x ^ n :=
  SubmonoidClass.coe_pow x n

protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  AddSubmonoidClass.coe_eq_zero

protected theorem coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 :=
  SubmonoidClass.coe_eq_one

/-- Embedding of a subalgebra into the algebra. -/
-- todo: standardize on the names these morphisms
-- compare with submodule.subtype
def val : S →ₐ[R] A := by
  refine_struct { toFun := (coe : S → A) } <;> intros <;> rfl

@[simp]
theorem coe_val : (S.val : S → A) = coe :=
  rfl

theorem val_apply (x : S) : S.val x = (x : A) :=
  rfl

@[simp]
theorem to_subsemiring_subtype : S.toSubsemiring.Subtype = (S.val : S →+* A) :=
  rfl

@[simp]
theorem to_subring_subtype {R A : Type _} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) :
    S.toSubring.Subtype = (S.val : S →+* A) :=
  rfl

/-- Linear equivalence between `S : submodule R A` and `S`. Though these types are equal,
we define it as a `linear_equiv` to avoid type equalities. -/
def toSubmoduleEquiv (S : Subalgebra R A) : S.toSubmodule ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl

/-- Transport a subalgebra via an algebra homomorphism. -/
def map (S : Subalgebra R A) (f : A →ₐ[R] B) : Subalgebra R B :=
  { S.toSubsemiring.map (f : A →+* B) with
    algebra_map_mem' := fun r => f.commutes r ▸ Set.mem_image_of_mem _ (S.algebra_map_mem r) }

theorem map_mono {S₁ S₂ : Subalgebra R A} {f : A →ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  Set.image_subset f

theorem map_injective {S₁ S₂ : Subalgebra R A} (f : A →ₐ[R] B) (hf : Function.Injective f) (ih : S₁.map f = S₂.map f) :
    S₁ = S₂ :=
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

@[simp]
theorem map_id (S : Subalgebra R A) : S.map (AlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (S : Subalgebra R A) (g : B →ₐ[R] C) (f : A →ₐ[R] B) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

theorem mem_map {S : Subalgebra R A} {f : A →ₐ[R] B} {y : B} : y ∈ map S f ↔ ∃ x ∈ S, f x = y :=
  Subsemiring.mem_map

theorem map_to_submodule {S : Subalgebra R A} {f : A →ₐ[R] B} :
    (S.map f).toSubmodule = S.toSubmodule.map f.toLinearMap :=
  SetLike.coe_injective rfl

theorem map_to_subsemiring {S : Subalgebra R A} {f : A →ₐ[R] B} :
    (S.map f).toSubsemiring = S.toSubsemiring.map f.toRingHom :=
  SetLike.coe_injective rfl

@[simp]
theorem coe_map (S : Subalgebra R A) (f : A →ₐ[R] B) : (S.map f : Set B) = f '' S :=
  rfl

/-- Preimage of a subalgebra under an algebra homomorphism. -/
def comap (S : Subalgebra R B) (f : A →ₐ[R] B) : Subalgebra R A :=
  { S.toSubsemiring.comap (f : A →+* B) with
    algebra_map_mem' := fun r => show f (algebraMap R A r) ∈ S from (f.commutes r).symm ▸ S.algebra_map_mem r }

theorem map_le {S : Subalgebra R A} {f : A →ₐ[R] B} {U : Subalgebra R B} : map S f ≤ U ↔ S ≤ comap U f :=
  Set.image_subset_iff

theorem gc_map_comap (f : A →ₐ[R] B) : GaloisConnection (fun S => map S f) fun S => comap S f := fun S U => map_le

@[simp]
theorem mem_comap (S : Subalgebra R B) (f : A →ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_comap (S : Subalgebra R B) (f : A →ₐ[R] B) : (S.comap f : Set A) = f ⁻¹' (S : Set B) :=
  rfl

instance no_zero_divisors {R A : Type _} [CommSemiringₓ R] [Semiringₓ A] [NoZeroDivisors A] [Algebra R A]
    (S : Subalgebra R A) : NoZeroDivisors S :=
  S.toSubsemiring.NoZeroDivisors

instance is_domain {R A : Type _} [CommRingₓ R] [Ringₓ A] [IsDomain A] [Algebra R A] (S : Subalgebra R A) :
    IsDomain S :=
  Subring.is_domain S.toSubring

end Subalgebra

namespace Submodule

variable {R A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable (p : Submodule R A)

/-- A submodule containing `1` and closed under multiplication is a subalgebra. -/
def toSubalgebra (p : Submodule R A) (h_one : (1 : A) ∈ p) (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) :
    Subalgebra R A :=
  { p with mul_mem' := h_mul,
    algebra_map_mem' := fun r => by
      rw [Algebra.algebra_map_eq_smul_one]
      exact p.smul_mem _ h_one }

@[simp]
theorem mem_to_subalgebra {p : Submodule R A} {h_one h_mul} {x} : x ∈ p.toSubalgebra h_one h_mul ↔ x ∈ p :=
  Iff.rfl

@[simp]
theorem coe_to_subalgebra (p : Submodule R A) (h_one h_mul) : (p.toSubalgebra h_one h_mul : Set A) = p :=
  rfl

@[simp]
theorem to_subalgebra_mk (s : Set A) (h0 hadd hsmul h1 hmul) :
    (Submodule.mk s hadd h0 hsmul : Submodule R A).toSubalgebra h1 hmul =
      Subalgebra.mk s (@hmul) h1 (@hadd) h0 fun r => by
        rw [Algebra.algebra_map_eq_smul_one]
        exact hsmul r h1 :=
  rfl

@[simp]
theorem to_subalgebra_to_submodule (p : Submodule R A) (h_one h_mul) : (p.toSubalgebra h_one h_mul).toSubmodule = p :=
  SetLike.coe_injective rfl

@[simp]
theorem _root_.subalgebra.to_submodule_to_subalgebra (S : Subalgebra R A) :
    (S.toSubmodule.toSubalgebra S.one_mem fun _ _ => S.mul_mem) = S :=
  SetLike.coe_injective rfl

end Submodule

namespace AlgHom

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiringₓ R]

variable [Semiringₓ A] [Algebra R A] [Semiringₓ B] [Algebra R B] [Semiringₓ C] [Algebra R C]

variable (φ : A →ₐ[R] B)

/-- Range of an `alg_hom` as a subalgebra. -/
protected def range (φ : A →ₐ[R] B) : Subalgebra R B :=
  { φ.toRingHom.srange with algebra_map_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }

@[simp]
theorem mem_range (φ : A →ₐ[R] B) {y : B} : y ∈ φ.range ↔ ∃ x, φ x = y :=
  RingHom.mem_srange

theorem mem_range_self (φ : A →ₐ[R] B) (x : A) : φ x ∈ φ.range :=
  φ.mem_range.2 ⟨x, rfl⟩

@[simp]
theorem coe_range (φ : A →ₐ[R] B) : (φ.range : Set B) = Set.Range φ := by
  ext
  rw [SetLike.mem_coe, mem_range]
  rfl

theorem range_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range = f.range.map g :=
  SetLike.coe_injective (Set.range_comp g f)

theorem range_comp_le_range (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range ≤ g.range :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/-- Restrict the codomain of an algebra homomorphism. -/
def codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
  { RingHom.codRestrict (f : A →+* B) S hf with commutes' := fun r => Subtype.eq <| f.commutes r }

@[simp]
theorem val_comp_cod_restrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    S.val.comp (f.codRestrict S hf) = f :=
  AlgHom.ext fun _ => rfl

@[simp]
theorem coe_cod_restrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(f.codRestrict S hf x) = f x :=
  rfl

theorem injective_cod_restrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    Function.Injective (f.codRestrict S hf) ↔ Function.Injective f :=
  ⟨fun H x y hxy => H <| Subtype.eq hxy, fun H x y hxy => H (congr_arg Subtype.val hxy : _)⟩

/-- Restrict the codomain of a alg_hom `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible]
def rangeRestrict (f : A →ₐ[R] B) : A →ₐ[R] f.range :=
  f.codRestrict f.range f.mem_range_self

/-- The equalizer of two R-algebra homomorphisms -/
def equalizer (ϕ ψ : A →ₐ[R] B) : Subalgebra R A where
  Carrier := { a | ϕ a = ψ a }
  add_mem' := fun x y (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) => by
    rw [Set.mem_set_of_eq, ϕ.map_add, ψ.map_add, hx, hy]
  mul_mem' := fun x y (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) => by
    rw [Set.mem_set_of_eq, ϕ.map_mul, ψ.map_mul, hx, hy]
  algebra_map_mem' := fun x => by
    rw [Set.mem_set_of_eq, AlgHom.commutes, AlgHom.commutes]

@[simp]
theorem mem_equalizer (ϕ ψ : A →ₐ[R] B) (x : A) : x ∈ ϕ.equalizer ψ ↔ ϕ x = ψ x :=
  Iff.rfl

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `subtype.fintype` if `B` is also a fintype. -/
instance fintypeRange [Fintype A] [DecidableEq B] (φ : A →ₐ[R] B) : Fintype φ.range :=
  Set.fintypeRange φ

end AlgHom

namespace AlgEquiv

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Algebra R A] [Algebra R B]

/-- Restrict an algebra homomorphism with a left inverse to an algebra isomorphism to its range.

This is a computable alternative to `alg_equiv.of_injective`. -/
def ofLeftInverse {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) : A ≃ₐ[R] f.range :=
  { f.range_restrict with toFun := f.range_restrict, invFun := g ∘ f.range.val, left_inv := h,
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := f.mem_range.mp x.Prop
        show f (g x) = x by
          rw [← hx', h x'] }

@[simp]
theorem of_left_inverse_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) (x : A) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[simp]
theorem of_left_inverse_symm_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) (x : f.range) :
    (ofLeftInverse h).symm x = g x :=
  rfl

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
noncomputable def ofInjective (f : A →ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range :=
  ofLeftInverse (Classical.some_spec hf.HasLeftInverse)

@[simp]
theorem of_injective_apply (f : A →ₐ[R] B) (hf : Function.Injective f) (x : A) : ↑(ofInjective f hf x) = f x :=
  rfl

/-- Restrict an algebra homomorphism between fields to an algebra isomorphism -/
noncomputable def ofInjectiveField {E F : Type _} [DivisionRing E] [Semiringₓ F] [Nontrivial F] [Algebra R E]
    [Algebra R F] (f : E →ₐ[R] F) : E ≃ₐ[R] f.range :=
  ofInjective f f.toRingHom.Injective

/-- Given an equivalence `e : A ≃ₐ[R] B` of `R`-algebras and a subalgebra `S` of `A`,
`subalgebra_map` is the induced equivalence between `S` and `S.map e` -/
@[simps]
def subalgebraMap (e : A ≃ₐ[R] B) (S : Subalgebra R A) : S ≃ₐ[R] S.map e.toAlgHom :=
  { e.toRingEquiv.subsemiringMap S.toSubsemiring with
    commutes' := fun r => by
      ext
      simp }

end AlgEquiv

namespace Algebra

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] [Semiringₓ B] [Algebra R B]

/-- The minimal subalgebra that includes `s`. -/
def adjoin (s : Set A) : Subalgebra R A :=
  { Subsemiring.closure (Set.Range (algebraMap R A) ∪ s) with
    algebra_map_mem' := fun r => Subsemiring.subset_closure <| Or.inl ⟨r, rfl⟩ }

variable {R}

protected theorem gc : GaloisConnection (adjoin R : Set A → Subalgebra R A) coe := fun s S =>
  ⟨fun H => le_transₓ (le_transₓ (Set.subset_union_right _ _) Subsemiring.subset_closure) H, fun H =>
    show Subsemiring.closure (Set.Range (algebraMap R A) ∪ s) ≤ S.toSubsemiring from
      Subsemiring.closure_le.2 <| Set.union_subset S.range_subset H⟩

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → Subalgebra R A) coe where
  choice := fun s hs => (adjoin R s).copy s <| le_antisymmₓ (Algebra.gc.le_u_l s) hs
  gc := Algebra.gc
  le_l_u := fun S => (Algebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq := fun _ _ => Subalgebra.copy_eq _ _ _

instance : CompleteLattice (Subalgebra R A) :=
  GaloisInsertion.liftCompleteLattice Algebra.gi

@[simp]
theorem coe_top : (↑(⊤ : Subalgebra R A) : Set A) = Set.Univ :=
  rfl

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : Subalgebra R A) :=
  Set.mem_univ x

@[simp]
theorem top_to_submodule : (⊤ : Subalgebra R A).toSubmodule = ⊤ :=
  rfl

@[simp]
theorem top_to_subsemiring : (⊤ : Subalgebra R A).toSubsemiring = ⊤ :=
  rfl

@[simp]
theorem top_to_subring {R A : Type _} [CommRingₓ R] [Ringₓ A] [Algebra R A] : (⊤ : Subalgebra R A).toSubring = ⊤ :=
  rfl

@[simp]
theorem to_submodule_eq_top {S : Subalgebra R A} : S.toSubmodule = ⊤ ↔ S = ⊤ :=
  Subalgebra.to_submodule_injective.eq_iff' top_to_submodule

@[simp]
theorem to_subsemiring_eq_top {S : Subalgebra R A} : S.toSubsemiring = ⊤ ↔ S = ⊤ :=
  Subalgebra.to_subsemiring_injective.eq_iff' top_to_subsemiring

@[simp]
theorem to_subring_eq_top {R A : Type _} [CommRingₓ R] [Ringₓ A] [Algebra R A] {S : Subalgebra R A} :
    S.toSubring = ⊤ ↔ S = ⊤ :=
  Subalgebra.to_subring_injective.eq_iff' top_to_subring

theorem mem_sup_left {S T : Subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S⊔T :=
  show S ≤ S⊔T from le_sup_left

theorem mem_sup_right {S T : Subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S⊔T :=
  show T ≤ S⊔T from le_sup_right

theorem mul_mem_sup {S T : Subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S⊔T :=
  (S⊔T).mul_mem (mem_sup_left hx) (mem_sup_right hy)

theorem map_sup (f : A →ₐ[R] B) (S T : Subalgebra R A) : (S⊔T).map f = S.map f⊔T.map f :=
  (Subalgebra.gc_map_comap f).l_sup

@[simp, norm_cast]
theorem coe_inf (S T : Subalgebra R A) : (↑(S⊓T) : Set A) = S ∩ T :=
  rfl

@[simp]
theorem mem_inf {S T : Subalgebra R A} {x : A} : x ∈ S⊓T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
theorem inf_to_submodule (S T : Subalgebra R A) : (S⊓T).toSubmodule = S.toSubmodule⊓T.toSubmodule :=
  rfl

@[simp]
theorem inf_to_subsemiring (S T : Subalgebra R A) : (S⊓T).toSubsemiring = S.toSubsemiring⊓T.toSubsemiring :=
  rfl

@[simp, norm_cast]
theorem coe_Inf (S : Set (Subalgebra R A)) : (↑(inf S) : Set A) = ⋂ s ∈ S, ↑s :=
  Inf_image

theorem mem_Inf {S : Set (Subalgebra R A)} {x : A} : x ∈ inf S ↔ ∀, ∀ p ∈ S, ∀, x ∈ p := by
  simp only [SetLike.mem_coe, ← coe_Inf, ← Set.mem_Inter₂]

@[simp]
theorem Inf_to_submodule (S : Set (Subalgebra R A)) : (inf S).toSubmodule = inf (Subalgebra.toSubmodule '' S) :=
  SetLike.coe_injective <| by
    simp

@[simp]
theorem Inf_to_subsemiring (S : Set (Subalgebra R A)) : (inf S).toSubsemiring = inf (Subalgebra.toSubsemiring '' S) :=
  SetLike.coe_injective <| by
    simp

@[simp, norm_cast]
theorem coe_infi {ι : Sort _} {S : ι → Subalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [← infi]

theorem mem_infi {ι : Sort _} {S : ι → Subalgebra R A} {x : A} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [← infi, ← mem_Inf, ← Set.forall_range_iff]

@[simp]
theorem infi_to_submodule {ι : Sort _} (S : ι → Subalgebra R A) : (⨅ i, S i).toSubmodule = ⨅ i, (S i).toSubmodule :=
  SetLike.coe_injective <| by
    simp

instance : Inhabited (Subalgebra R A) :=
  ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : Subalgebra R A) ↔ x ∈ Set.Range (algebraMap R A) :=
  suffices (ofId R A).range = (⊥ : Subalgebra R A) by
    rw [← this, ← SetLike.mem_coe, AlgHom.coe_range]
    rfl
  le_bot_iff.mp fun x hx => Subalgebra.range_le _ ((ofId R A).coe_range ▸ hx)

theorem to_submodule_bot : (⊥ : Subalgebra R A).toSubmodule = R∙1 := by
  ext x
  simp [← mem_bot, -Set.singleton_one, ← Submodule.mem_span_singleton, ← Algebra.smul_def]

@[simp]
theorem coe_bot : ((⊥ : Subalgebra R A) : Set A) = Set.Range (algebraMap R A) := by
  simp [← Set.ext_iff, ← Algebra.mem_bot]

theorem eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by
    rw [h] <;> exact mem_top, fun h => by
    ext x <;> exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]
theorem range_id : (AlgHom.id R A).range = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
theorem map_top (f : A →ₐ[R] B) : Subalgebra.map (⊤ : Subalgebra R A) f = f.range :=
  SetLike.coe_injective Set.image_univ

@[simp]
theorem map_bot (f : A →ₐ[R] B) : Subalgebra.map (⊥ : Subalgebra R A) f = ⊥ :=
  SetLike.coe_injective <| by
    simp only [Set.range_comp, ← (· ∘ ·), ← Algebra.coe_bot, ← Subalgebra.coe_map, ← f.commutes]

@[simp]
theorem comap_top (f : A →ₐ[R] B) : Subalgebra.comap (⊤ : Subalgebra R B) f = ⊤ :=
  eq_top_iff.2 fun x => mem_top

/-- `alg_hom` to `⊤ : subalgebra R A`. -/
def toTop : A →ₐ[R] (⊤ : Subalgebra R A) :=
  (AlgHom.id R A).codRestrict ⊤ fun _ => mem_top

theorem surjective_algebra_map_iff : Function.Surjective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h =>
    eq_bot_iff.2 fun y _ =>
      let ⟨x, hx⟩ := h y
      hx ▸ Subalgebra.algebra_map_mem _ _,
    fun h y => Algebra.mem_bot.1 <| eq_bot_iff.1 h (Algebra.mem_top : y ∈ _)⟩

theorem bijective_algebra_map_iff {R A : Type _} [Field R] [Semiringₓ A] [Nontrivial A] [Algebra R A] :
    Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h => surjective_algebra_map_iff.1 h.2, fun h => ⟨(algebraMap R A).Injective, surjective_algebra_map_iff.2 h⟩⟩

/-- The bottom subalgebra is isomorphic to the base ring. -/
noncomputable def botEquivOfInjective (h : Function.Injective (algebraMap R A)) : (⊥ : Subalgebra R A) ≃ₐ[R] R :=
  AlgEquiv.symm <|
    AlgEquiv.ofBijective (Algebra.ofId R _)
      ⟨fun x y hxy => h (congr_arg Subtype.val hxy : _), fun ⟨y, hy⟩ =>
        let ⟨x, hx⟩ := Algebra.mem_bot.1 hy
        ⟨x, Subtype.eq hx⟩⟩

/-- The bottom subalgebra is isomorphic to the field. -/
@[simps symmApply]
noncomputable def botEquiv (F R : Type _) [Field F] [Semiringₓ R] [Nontrivial R] [Algebra F R] :
    (⊥ : Subalgebra F R) ≃ₐ[F] F :=
  botEquivOfInjective (RingHom.injective _)

end Algebra

namespace Subalgebra

open Algebra

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] [Semiringₓ B] [Algebra R B]

variable (S : Subalgebra R A)

/-- The top subalgebra is isomorphic to the algebra.

This is the algebra version of `submodule.top_equiv`. -/
@[simps]
def topEquiv : (⊤ : Subalgebra R A) ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (Subalgebra.val ⊤) toTop rfl <| AlgHom.ext fun _ => Subtype.ext rfl

-- TODO[gh-6025]: make this an instance once safe to do so
theorem subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (Subalgebra R A) :=
  ⟨fun B C =>
    ext fun x => by
      simp only [← Subsingleton.elimₓ x 0, ← zero_mem B, ← zero_mem C]⟩

/-- For performance reasons this is not an instance. If you need this instance, add
```
local attribute [instance] alg_hom.subsingleton subalgebra.subsingleton_of_subsingleton
```
in the section that needs it.
-/
-- TODO[gh-6025]: make this an instance once safe to do so
theorem _root_.alg_hom.subsingleton [Subsingleton (Subalgebra R A)] : Subsingleton (A →ₐ[R] B) :=
  ⟨fun f g =>
    AlgHom.ext fun a =>
      have : a ∈ (⊥ : Subalgebra R A) := Subsingleton.elimₓ (⊤ : Subalgebra R A) ⊥ ▸ mem_top
      let ⟨x, hx⟩ := Set.mem_range.mp (mem_bot.mp this)
      hx ▸ (f.commutes _).trans (g.commutes _).symm⟩

-- TODO[gh-6025]: make this an instance once safe to do so
theorem _root_.alg_equiv.subsingleton_left [Subsingleton (Subalgebra R A)] : Subsingleton (A ≃ₐ[R] B) := by
  have : Subsingleton (A →ₐ[R] B) := AlgHom.subsingleton
  exact ⟨fun f g => AlgEquiv.ext fun x => alg_hom.ext_iff.mp (Subsingleton.elimₓ f.toAlgHom g.toAlgHom) x⟩

-- TODO[gh-6025]: make this an instance once safe to do so
theorem _root_.alg_equiv.subsingleton_right [Subsingleton (Subalgebra R B)] : Subsingleton (A ≃ₐ[R] B) := by
  have : Subsingleton (B ≃ₐ[R] A) := AlgEquiv.subsingleton_left
  exact
    ⟨fun f g =>
      Eq.trans (AlgEquiv.symm_symm _).symm
        (by
          rw [Subsingleton.elimₓ f.symm g.symm, AlgEquiv.symm_symm])⟩

theorem range_val : S.val.range = S :=
  ext <| Set.ext_iff.1 <| S.val.coe_range.trans Subtype.range_val

instance : Unique (Subalgebra R R) :=
  { Algebra.Subalgebra.inhabited with
    uniq := by
      intro S
      refine' le_antisymmₓ (fun r hr => _) bot_le
      simp only [← Set.mem_range, ← mem_bot, ← id.map_eq_self, ← exists_apply_eq_applyₓ, ← default] }

/-- The map `S → T` when `S` is a subalgebra contained in the subalgebra `T`.

This is the subalgebra version of `submodule.of_le`, or `subring.inclusion`  -/
def inclusion {S T : Subalgebra R A} (h : S ≤ T) : S →ₐ[R] T where
  toFun := Set.inclusion h
  map_one' := rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  commutes' := fun _ => rfl

theorem inclusion_injective {S T : Subalgebra R A} (h : S ≤ T) : Function.Injective (inclusion h) := fun _ _ =>
  Subtype.ext ∘ Subtype.mk.injₓ

@[simp]
theorem inclusion_self {S : Subalgebra R A} : inclusion (le_reflₓ S) = AlgHom.id R S :=
  AlgHom.ext fun x => Subtype.ext rfl

@[simp]
theorem inclusion_mk {S T : Subalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) : inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl

theorem inclusion_right {S T : Subalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) : inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
theorem inclusion_inclusion {S T U : Subalgebra R A} (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_transₓ hst htu) x :=
  Subtype.ext rfl

@[simp]
theorem coe_inclusion {S T : Subalgebra R A} (h : S ≤ T) (s : S) : (inclusion h s : A) = s :=
  rfl

/-- Two subalgebras that are equal are also equivalent as algebras.

This is the `subalgebra` version of `linear_equiv.of_eq` and `equiv.set.of_eq`. -/
@[simps apply]
def equivOfEq (S T : Subalgebra R A) (h : S = T) : S ≃ₐ[R] T :=
  { LinearEquiv.ofEq _ _ (congr_arg toSubmodule h) with toFun := fun x => ⟨x, h ▸ x.2⟩,
    invFun := fun x => ⟨x, h.symm ▸ x.2⟩, map_mul' := fun _ _ => rfl, commutes' := fun _ => rfl }

@[simp]
theorem equiv_of_eq_symm (S T : Subalgebra R A) (h : S = T) : (equivOfEq S T h).symm = equivOfEq T S h.symm :=
  rfl

@[simp]
theorem equiv_of_eq_rfl (S : Subalgebra R A) : equivOfEq S S rfl = AlgEquiv.refl := by
  ext
  rfl

@[simp]
theorem equiv_of_eq_trans (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U) :
    (equivOfEq S T hST).trans (equivOfEq T U hTU) = equivOfEq S U (trans hST hTU) :=
  rfl

section Prod

variable (S₁ : Subalgebra R B)

/-- The product of two subalgebras is a subalgebra. -/
def prod : Subalgebra R (A × B) :=
  { S.toSubsemiring.Prod S₁.toSubsemiring with Carrier := (S : Set A) ×ˢ (S₁ : Set B),
    algebra_map_mem' := fun r => ⟨algebra_map_mem _ _, algebra_map_mem _ _⟩ }

@[simp]
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ (S₁ : Set B) :=
  rfl

theorem prod_to_submodule : (S.Prod S₁).toSubmodule = S.toSubmodule.Prod S₁.toSubmodule :=
  rfl

@[simp]
theorem mem_prod {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B} : x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ :=
  Set.mem_prod

@[simp]
theorem prod_top : (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤ := by
  ext <;> simp

theorem prod_mono {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} : S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono

@[simp]
theorem prod_inf_prod {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} : S.Prod S₁⊓T.Prod T₁ = (S⊓T).Prod (S₁⊓T₁) :=
  SetLike.coe_injective Set.prod_inter_prod

end Prod

section SuprLift

variable {ι : Type _}

theorem coe_supr_of_directed [Nonempty ι] {S : ι → Subalgebra R A} (dir : Directed (· ≤ ·) S) :
    ↑(supr S) = ⋃ i, (S i : Set A) :=
  let K : Subalgebra R A :=
    { Carrier := ⋃ i, S i,
      mul_mem' := fun x y hx hy =>
        let ⟨i, hi⟩ := Set.mem_Union.1 hx
        let ⟨j, hj⟩ := Set.mem_Union.1 hy
        let ⟨k, hik, hjk⟩ := dir i j
        Set.mem_Union.2 ⟨k, Subalgebra.mul_mem (S k) (hik hi) (hjk hj)⟩,
      add_mem' := fun x y hx hy =>
        let ⟨i, hi⟩ := Set.mem_Union.1 hx
        let ⟨j, hj⟩ := Set.mem_Union.1 hy
        let ⟨k, hik, hjk⟩ := dir i j
        Set.mem_Union.2 ⟨k, Subalgebra.add_mem (S k) (hik hi) (hjk hj)⟩,
      algebra_map_mem' := fun r =>
        let i := @Nonempty.some ι inferInstance
        Set.mem_Union.2 ⟨i, Subalgebra.algebra_map_mem _ _⟩ }
  have : supr S = K :=
    le_antisymmₓ (supr_le fun i => Set.subset_Union (fun i => ↑(S i)) i)
      (SetLike.coe_subset_coe.1 (Set.Union_subset fun i => SetLike.coe_subset_coe.2 (le_supr _ _)))
  this.symm ▸ rfl

/-- Define an algebra homomorphism on a directed supremum of subalgebras by defining
it on each subalgebra, and proving that it agrees on the intersection of subalgebras. -/
noncomputable def suprLift [Nonempty ι] (K : ι → Subalgebra R A) (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →ₐ[R] B)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)) (T : Subalgebra R A) (hT : T = supr K) :
    ↥T →ₐ[R] B := by
  subst hT <;>
    exact
      { toFun :=
          Set.unionLift (fun i => ↑(K i)) (fun i x => f i x)
            (fun i j x hxi hxj => by
              let ⟨k, hik, hjk⟩ := dir i j
              rw [hf i k hik, hf j k hjk]
              rfl)
            (↑(supr K))
            (by
              rw [coe_supr_of_directed dir] <;> rfl),
        map_one' :=
          Set.Union_lift_const _ (fun _ => 1) (fun _ => rfl) _
            (by
              simp ),
        map_zero' :=
          Set.Union_lift_const _ (fun _ => 0) (fun _ => rfl) _
            (by
              simp ),
        map_mul' :=
          Set.Union_lift_binary (coe_supr_of_directed dir) dir _ (fun _ => (· * ·)) (fun _ _ _ => rfl) _
            (by
              simp ),
        map_add' :=
          Set.Union_lift_binary (coe_supr_of_directed dir) dir _ (fun _ => (· + ·)) (fun _ _ _ => rfl) _
            (by
              simp ),
        commutes' := fun r =>
          Set.Union_lift_const _ (fun _ => algebraMap _ _ r) (fun _ => rfl) _ fun i => by
            erw [AlgHom.commutes (f i)] }

variable [Nonempty ι] {K : ι → Subalgebra R A} {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
  {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)} {T : Subalgebra R A} {hT : T = supr K}

@[simp]
theorem supr_lift_inclusion {i : ι} (x : K i) (h : K i ≤ T) : suprLift K dir f hf T hT (inclusion h x) = f i x := by
  subst T <;> exact Set.Union_lift_inclusion _ _

@[simp]
theorem supr_lift_comp_inclusion {i : ι} (h : K i ≤ T) : (suprLift K dir f hf T hT).comp (inclusion h) = f i := by
  ext <;> simp

@[simp]
theorem supr_lift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) : suprLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  subst hT <;> exact Set.Union_lift_mk x hx

theorem supr_lift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) : suprLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  subst hT <;> exact Set.Union_lift_of_mem x hx

end SuprLift

/-! ## Actions by `subalgebra`s

These are just copies of the definitions about `subsemiring` starting from
`subring.mul_action`.
-/


section Actions

variable {α β : Type _}

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [HasSmul A α] (S : Subalgebra R A) : HasSmul S α :=
  S.toSubsemiring.HasSmul

theorem smul_def [HasSmul A α] {S : Subalgebra R A} (g : S) (m : α) : g • m = (g : A) • m :=
  rfl

instance smul_comm_class_left [HasSmul A β] [HasSmul α β] [SmulCommClass A α β] (S : Subalgebra R A) :
    SmulCommClass S α β :=
  S.toSubsemiring.smul_comm_class_left

instance smul_comm_class_right [HasSmul α β] [HasSmul A β] [SmulCommClass α A β] (S : Subalgebra R A) :
    SmulCommClass α S β :=
  S.toSubsemiring.smul_comm_class_right

/-- Note that this provides `is_scalar_tower S R R` which is needed by `smul_mul_assoc`. -/
instance is_scalar_tower_left [HasSmul α β] [HasSmul A α] [HasSmul A β] [IsScalarTower A α β] (S : Subalgebra R A) :
    IsScalarTower S α β :=
  S.toSubsemiring.IsScalarTower

instance is_scalar_tower_mid {R S T : Type _} [CommSemiringₓ R] [Semiringₓ S] [AddCommMonoidₓ T] [Algebra R S]
    [Module R T] [Module S T] [IsScalarTower R S T] (S' : Subalgebra R S) : IsScalarTower R S' T :=
  ⟨fun x y z => (smul_assoc _ (y : S) _ : _)⟩

instance [HasSmul A α] [HasFaithfulSmul A α] (S : Subalgebra R A) : HasFaithfulSmul S α :=
  S.toSubsemiring.HasFaithfulSmul

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [MulAction A α] (S : Subalgebra R A) : MulAction S α :=
  S.toSubsemiring.MulAction

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [AddMonoidₓ α] [DistribMulAction A α] (S : Subalgebra R A) : DistribMulAction S α :=
  S.toSubsemiring.DistribMulAction

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [Zero α] [SmulWithZero A α] (S : Subalgebra R A) : SmulWithZero S α :=
  S.toSubsemiring.SmulWithZero

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [Zero α] [MulActionWithZero A α] (S : Subalgebra R A) : MulActionWithZero S α :=
  S.toSubsemiring.MulActionWithZero

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance moduleLeft [AddCommMonoidₓ α] [Module A α] (S : Subalgebra R A) : Module S α :=
  S.toSubsemiring.Module

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance toAlgebra {R A : Type _} [CommSemiringₓ R] [CommSemiringₓ A] [Semiringₓ α] [Algebra R A] [Algebra A α]
    (S : Subalgebra R A) : Algebra S α :=
  Algebra.ofSubsemiring S.toSubsemiring

theorem algebra_map_eq {R A : Type _} [CommSemiringₓ R] [CommSemiringₓ A] [Semiringₓ α] [Algebra R A] [Algebra A α]
    (S : Subalgebra R A) : algebraMap S α = (algebraMap A α).comp S.val :=
  rfl

@[simp]
theorem srange_algebra_map {R A : Type _} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] (S : Subalgebra R A) :
    (algebraMap S A).srange = S.toSubsemiring := by
  rw [algebra_map_eq, Algebra.id.map_eq_id, RingHom.id_comp, ← to_subsemiring_subtype, Subsemiring.srange_subtype]

@[simp]
theorem range_algebra_map {R A : Type _} [CommRingₓ R] [CommRingₓ A] [Algebra R A] (S : Subalgebra R A) :
    (algebraMap S A).range = S.toSubring := by
  rw [algebra_map_eq, Algebra.id.map_eq_id, RingHom.id_comp, ← to_subring_subtype, Subring.range_subtype]

instance no_zero_smul_divisors_top [NoZeroDivisors A] (S : Subalgebra R A) : NoZeroSmulDivisors S A :=
  ⟨fun c x h =>
    have : (c : A) = 0 ∨ x = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h
    this.imp_left (@Subtype.ext_iff _ _ c 0).mpr⟩

end Actions

section Center

theorem _root_.set.algebra_map_mem_center (r : R) : algebraMap R A r ∈ Set.Center A := by
  simp [← Algebra.commutes, ← Set.mem_center_iff]

variable (R A)

/-- The center of an algebra is the set of elements which commute with every element. They form a
subalgebra. -/
def center : Subalgebra R A :=
  { Subsemiring.center A with algebra_map_mem' := Set.algebra_map_mem_center }

theorem coe_center : (center R A : Set A) = Set.Center A :=
  rfl

@[simp]
theorem center_to_subsemiring : (center R A).toSubsemiring = Subsemiring.center A :=
  rfl

@[simp]
theorem center_to_subring (R A : Type _) [CommRingₓ R] [Ringₓ A] [Algebra R A] :
    (center R A).toSubring = Subring.center A :=
  rfl

@[simp]
theorem center_eq_top (A : Type _) [CommSemiringₓ A] [Algebra R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

variable {R A}

instance : CommSemiringₓ (center R A) :=
  Subsemiring.center.commSemiring

instance {A : Type _} [Ringₓ A] [Algebra R A] : CommRingₓ (center R A) :=
  Subring.center.commRing

theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Iff.rfl

end Center

section Centralizer

@[simp]
theorem _root_.set.algebra_map_mem_centralizer {s : Set A} (r : R) : algebraMap R A r ∈ s.Centralizer := fun a h =>
  (Algebra.commutes _ _).symm

variable (R)

/-- The centralizer of a set as a subalgebra. -/
def centralizer (s : Set A) : Subalgebra R A :=
  { Subsemiring.centralizer s with algebra_map_mem' := Set.algebra_map_mem_centralizer }

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.Centralizer :=
  rfl

theorem mem_centralizer_iff {s : Set A} {z : A} : z ∈ centralizer R s ↔ ∀, ∀ g ∈ s, ∀, g * z = z * g :=
  Iff.rfl

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset h

@[simp]
theorem centralizer_univ : centralizer R Set.Univ = center R A :=
  SetLike.ext' (Set.centralizer_univ A)

end Centralizer

end Subalgebra

section Nat

variable {R : Type _} [Semiringₓ R]

/-- A subsemiring is a `ℕ`-subalgebra. -/
def subalgebraOfSubsemiring (S : Subsemiring R) : Subalgebra ℕ R :=
  { S with algebra_map_mem' := fun i => coe_nat_mem S i }

@[simp]
theorem mem_subalgebra_of_subsemiring {x : R} {S : Subsemiring R} : x ∈ subalgebraOfSubsemiring S ↔ x ∈ S :=
  Iff.rfl

end Nat

section Int

variable {R : Type _} [Ringₓ R]

/-- A subring is a `ℤ`-subalgebra. -/
def subalgebraOfSubring (S : Subring R) : Subalgebra ℤ R :=
  { S with
    algebra_map_mem' := fun i =>
      Int.induction_on i
        (by
          simpa using S.zero_mem)
        (fun i ih => by
          simpa using S.add_mem ih S.one_mem)
        fun i ih =>
        show ((-i - 1 : ℤ) : R) ∈ S by
          rw [Int.cast_sub, Int.cast_oneₓ]
          exact S.sub_mem ih S.one_mem }

variable {S : Type _} [Semiringₓ S]

@[simp]
theorem mem_subalgebra_of_subring {x : R} {S : Subring R} : x ∈ subalgebraOfSubring S ↔ x ∈ S :=
  Iff.rfl

end Int

