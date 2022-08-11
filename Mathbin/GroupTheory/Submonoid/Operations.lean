/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.GroupTheory.Submonoid.Basic
import Mathbin.GroupTheory.Subsemigroup.Operations

/-!
# Operations on `submonoid`s

In this file we define various operations on `submonoid`s and `monoid_hom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `submonoid.to_add_submonoid`, `submonoid.to_add_submonoid'`, `add_submonoid.to_submonoid`,
  `add_submonoid.to_submonoid'`: convert between multiplicative and additive submonoids of `M`,
  `multiplicative M`, and `additive M`. These are stated as `order_iso`s.

### (Commutative) monoid structure on a submonoid

* `submonoid.to_monoid`, `submonoid.to_comm_monoid`: a submonoid inherits a (commutative) monoid
  structure.

### Group actions by submonoids

* `submonoid.mul_action`, `submonoid.distrib_mul_action`: a submonoid inherits (distributive)
  multiplicative actions.

### Operations on submonoids

* `submonoid.comap`: preimage of a submonoid under a monoid homomorphism as a submonoid of the
  domain;
* `submonoid.map`: image of a submonoid under a monoid homomorphism as a submonoid of the codomain;
* `submonoid.prod`: product of two submonoids `s : submonoid M` and `t : submonoid N` as a submonoid
  of `M × N`;

### Monoid homomorphisms between submonoid

* `submonoid.subtype`: embedding of a submonoid into the ambient monoid.
* `submonoid.inclusion`: given two submonoids `S`, `T` such that `S ≤ T`, `S.inclusion T` is the
  inclusion of `S` into `T` as a monoid homomorphism;
* `mul_equiv.submonoid_congr`: converts a proof of `S = T` into a monoid isomorphism between `S`
  and `T`.
* `submonoid.prod_equiv`: monoid isomorphism between `s.prod t` and `s × t`;

### Operations on `monoid_hom`s

* `monoid_hom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;
* `monoid_hom.mker`: kernel of a monoid homomorphism as a submonoid of the domain;
* `monoid_hom.restrict`: restrict a monoid homomorphism to a submonoid;
* `monoid_hom.cod_restrict`: restrict the codomain of a monoid homomorphism to a submonoid;
* `monoid_hom.mrange_restrict`: restrict a monoid homomorphism to its range;

## Tags

submonoid, range, product, map, comap
-/


variable {M N P : Type _} [MulOneClassₓ M] [MulOneClassₓ N] [MulOneClassₓ P] (S : Submonoid M)

/-!
### Conversion to/from `additive`/`multiplicative`
-/


section

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `additive M`. -/
@[simps]
def Submonoid.toAddSubmonoid : Submonoid M ≃o AddSubmonoid (Additive M) where
  toFun := fun S => { Carrier := Additive.toMul ⁻¹' S, zero_mem' := S.one_mem', add_mem' := S.mul_mem' }
  invFun := fun S => { Carrier := Additive.ofMul ⁻¹' S, one_mem' := S.zero_mem', mul_mem' := S.add_mem' }
  left_inv := fun x => by
    cases x <;> rfl
  right_inv := fun x => by
    cases x <;> rfl
  map_rel_iff' := fun a b => Iff.rfl

/-- Additive submonoids of an additive monoid `additive M` are isomorphic to submonoids of `M`. -/
abbrev AddSubmonoid.toSubmonoid' : AddSubmonoid (Additive M) ≃o Submonoid M :=
  Submonoid.toAddSubmonoid.symm

theorem Submonoid.to_add_submonoid_closure (S : Set M) :
    (Submonoid.closure S).toAddSubmonoid = AddSubmonoid.closure (Additive.toMul ⁻¹' S) :=
  le_antisymmₓ (Submonoid.toAddSubmonoid.le_symm_apply.1 <| Submonoid.closure_le.2 AddSubmonoid.subset_closure)
    (AddSubmonoid.closure_le.2 Submonoid.subset_closure)

theorem AddSubmonoid.to_submonoid'_closure (S : Set (Additive M)) :
    (AddSubmonoid.closure S).toSubmonoid' = Submonoid.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymmₓ (AddSubmonoid.toSubmonoid'.le_symm_apply.1 <| AddSubmonoid.closure_le.2 Submonoid.subset_closure)
    (Submonoid.closure_le.2 AddSubmonoid.subset_closure)

end

section

variable {A : Type _} [AddZeroClassₓ A]

/-- Additive submonoids of an additive monoid `A` are isomorphic to
multiplicative submonoids of `multiplicative A`. -/
@[simps]
def AddSubmonoid.toSubmonoid : AddSubmonoid A ≃o Submonoid (Multiplicative A) where
  toFun := fun S => { Carrier := Multiplicative.toAdd ⁻¹' S, one_mem' := S.zero_mem', mul_mem' := S.add_mem' }
  invFun := fun S => { Carrier := Multiplicative.ofAdd ⁻¹' S, zero_mem' := S.one_mem', add_mem' := S.mul_mem' }
  left_inv := fun x => by
    cases x <;> rfl
  right_inv := fun x => by
    cases x <;> rfl
  map_rel_iff' := fun a b => Iff.rfl

/-- Submonoids of a monoid `multiplicative A` are isomorphic to additive submonoids of `A`. -/
abbrev Submonoid.toAddSubmonoid' : Submonoid (Multiplicative A) ≃o AddSubmonoid A :=
  AddSubmonoid.toSubmonoid.symm

theorem AddSubmonoid.to_submonoid_closure (S : Set A) :
    (AddSubmonoid.closure S).toSubmonoid = Submonoid.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymmₓ
    (AddSubmonoid.toSubmonoid.to_galois_connection.l_le <| AddSubmonoid.closure_le.2 Submonoid.subset_closure)
    (Submonoid.closure_le.2 AddSubmonoid.subset_closure)

theorem Submonoid.to_add_submonoid'_closure (S : Set (Multiplicative A)) :
    (Submonoid.closure S).toAddSubmonoid' = AddSubmonoid.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymmₓ
    (Submonoid.toAddSubmonoid'.to_galois_connection.l_le <| Submonoid.closure_le.2 AddSubmonoid.subset_closure)
    (AddSubmonoid.closure_le.2 Submonoid.subset_closure)

end

namespace Submonoid

variable {F : Type _} [mc : MonoidHomClass F M N]

open Set

/-!
### `comap` and `map`
-/


include mc

/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The preimage of an `add_submonoid` along an `add_monoid` homomorphism is an\n`add_submonoid`."]
def comap (f : F) (S : Submonoid N) : Submonoid M where
  Carrier := f ⁻¹' S
  one_mem' :=
    show f 1 ∈ S by
      rw [map_one] <;> exact S.one_mem
  mul_mem' := fun a b ha hb =>
    show f (a * b) ∈ S by
      rw [map_mul] <;> exact S.mul_mem ha hb

@[simp, to_additive]
theorem coe_comap (S : Submonoid N) (f : F) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl

@[simp, to_additive]
theorem mem_comap {S : Submonoid N} {f : F} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

omit mc

@[to_additive]
theorem comap_comap (S : Submonoid P) (g : N →* P) (f : M →* N) : (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp, to_additive]
theorem comap_id (S : Submonoid P) : S.comap (MonoidHom.id P) = S :=
  ext
    (by
      simp )

include mc

/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The image of an `add_submonoid` along an `add_monoid` homomorphism is\nan `add_submonoid`."]
def map (f : F) (S : Submonoid M) : Submonoid N where
  Carrier := f '' S
  one_mem' := ⟨1, S.one_mem, map_one f⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact
      ⟨x * y, S.mul_mem hx hy, by
        rw [map_mul] <;> rfl⟩

@[simp, to_additive]
theorem coe_map (f : F) (S : Submonoid M) : (S.map f : Set N) = f '' S :=
  rfl

@[simp, to_additive]
theorem mem_map {f : F} {S : Submonoid M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image_iff_bex

@[to_additive]
theorem mem_map_of_mem (f : F) {S : Submonoid M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx

@[to_additive]
theorem apply_coe_mem_map (f : F) (S : Submonoid M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.Prop

omit mc

@[to_additive]
theorem map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _

include mc

@[to_additive]
theorem mem_map_iff_mem {f : F} (hf : Function.Injective f) {S : Submonoid M} {x : M} : f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image

@[to_additive]
theorem map_le_iff_le_comap {f : F} {S : Submonoid M} {T : Submonoid N} : S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff

@[to_additive]
theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f) := fun S T => map_le_iff_le_comap

@[to_additive]
theorem map_le_of_le_comap {T : Submonoid N} {f : F} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le

@[to_additive]
theorem le_comap_of_map_le {T : Submonoid N} {f : F} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u

@[to_additive]
theorem le_comap_map {f : F} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

@[to_additive]
theorem map_comap_le {S : Submonoid N} {f : F} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _

@[to_additive]
theorem monotone_map {f : F} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

@[to_additive]
theorem monotone_comap {f : F} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[simp, to_additive]
theorem map_comap_map {f : F} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[simp, to_additive]
theorem comap_map_comap {S : Submonoid N} {f : F} : ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

@[to_additive]
theorem map_sup (S T : Submonoid M) (f : F) : (S⊔T).map f = S.map f⊔T.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

@[to_additive]
theorem map_supr {ι : Sort _} (f : F) (s : ι → Submonoid M) : (supr s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_supr

@[to_additive]
theorem comap_inf (S T : Submonoid N) (f : F) : (S⊓T).comap f = S.comap f⊓T.comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_inf

@[to_additive]
theorem comap_infi {ι : Sort _} (f : F) (s : ι → Submonoid N) : (infi s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_infi

@[simp, to_additive]
theorem map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp, to_additive]
theorem comap_top (f : F) : (⊤ : Submonoid N).comap f = ⊤ :=
  (gc_map_comap f).u_top

omit mc

@[simp, to_additive]
theorem map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S :=
  ext fun x => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

section GaloisCoinsertion

variable {ι : Type _} {f : F} (hf : Function.Injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
@[to_additive " `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. "]
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp [← mem_comap, ← mem_map, ← hf.eq_iff]

@[to_additive]
theorem comap_map_eq_of_injective (S : Submonoid M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _

@[to_additive]
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

@[to_additive]
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

@[to_additive]
theorem comap_inf_map_of_injective (S T : Submonoid M) : (S.map f⊓T.map f).comap f = S⊓T :=
  (gciMapComap hf).u_inf_l _ _

@[to_additive]
theorem comap_infi_map_of_injective (S : ι → Submonoid M) : (⨅ i, (S i).map f).comap f = infi S :=
  (gciMapComap hf).u_infi_l _

@[to_additive]
theorem comap_sup_map_of_injective (S T : Submonoid M) : (S.map f⊔T.map f).comap f = S⊔T :=
  (gciMapComap hf).u_sup_l _ _

@[to_additive]
theorem comap_supr_map_of_injective (S : ι → Submonoid M) : (⨆ i, (S i).map f).comap f = supr S :=
  (gciMapComap hf).u_supr_l _

@[to_additive]
theorem map_le_map_iff_of_injective {S T : Submonoid M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff

@[to_additive]
theorem map_strict_mono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strict_mono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type _} {f : F} (hf : Function.Surjective f)

include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
@[to_additive " `map f` and `comap f` form a `galois_insertion` when `f` is surjective. "]
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2
      ⟨y, by
        simp [← hy, ← h]⟩

@[to_additive]
theorem map_comap_eq_of_surjective (S : Submonoid N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _

@[to_additive]
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

@[to_additive]
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

@[to_additive]
theorem map_inf_comap_of_surjective (S T : Submonoid N) : (S.comap f⊓T.comap f).map f = S⊓T :=
  (giMapComap hf).l_inf_u _ _

@[to_additive]
theorem map_infi_comap_of_surjective (S : ι → Submonoid N) : (⨅ i, (S i).comap f).map f = infi S :=
  (giMapComap hf).l_infi_u _

@[to_additive]
theorem map_sup_comap_of_surjective (S T : Submonoid N) : (S.comap f⊔T.comap f).map f = S⊔T :=
  (giMapComap hf).l_sup_u _ _

@[to_additive]
theorem map_supr_comap_of_surjective (S : ι → Submonoid N) : (⨆ i, (S i).comap f).map f = supr S :=
  (giMapComap hf).l_supr_u _

@[to_additive]
theorem comap_le_comap_iff_of_surjective {S T : Submonoid N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff

@[to_additive]
theorem comap_strict_mono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strict_mono_u

end GaloisInsertion

end Submonoid

namespace SubmonoidClass

variable {A : Type _} [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

include hA

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits a zero."]
instance hasOne : One S' :=
  ⟨⟨_, one_mem S'⟩⟩

@[simp, norm_cast, to_additive]
theorem coe_one : ((1 : S') : M) = 1 :=
  rfl

variable {S'}

@[simp, norm_cast, to_additive]
theorem coe_eq_one {x : S'} : (↑x : M) = 1 ↔ x = 1 :=
  (Subtype.ext_iff.symm : (x : M) = (1 : S') ↔ x = 1)

variable (S')

@[to_additive]
theorem one_def : (1 : S') = ⟨1, one_mem S'⟩ :=
  rfl

omit hA

/-- An `add_submonoid` of an `add_monoid` inherits a scalar multiplication. -/
instance _root_.add_submonoid_class.has_nsmul {M} [AddMonoidₓ M] {A : Type _} [SetLike A M] [AddSubmonoidClass A M]
    (S : A) : HasSmul ℕ S :=
  ⟨fun n a => ⟨n • a.1, nsmul_mem a.2 n⟩⟩

/-- A submonoid of a monoid inherits a power operator. -/
instance hasPow {M} [Monoidₓ M] {A : Type _} [SetLike A M] [SubmonoidClass A M] (S : A) : Pow S ℕ :=
  ⟨fun a n => ⟨a.1 ^ n, pow_mem a.2 n⟩⟩

attribute [to_additive] SubmonoidClass.hasPow

@[simp, norm_cast, to_additive]
theorem coe_pow {M} [Monoidₓ M] {A : Type _} [SetLike A M] [SubmonoidClass A M] {S : A} (x : S) (n : ℕ) :
    (↑(x ^ n) : M) = ↑x ^ n :=
  rfl

@[simp, to_additive]
theorem mk_pow {M} [Monoidₓ M] {A : Type _} [SetLike A M] [SubmonoidClass A M] {S : A} (x : M) (hx : x ∈ S) (n : ℕ) :
    (⟨x, hx⟩ : S) ^ n = ⟨x ^ n, pow_mem hx n⟩ :=
  rfl

/-- A submonoid of a unital magma inherits a unital magma structure. -/
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
@[to_additive "An `add_submonoid` of an unital additive magma inherits an unital additive magma\nstructure."]
instance (priority := 75) toMulOneClass {M : Type _} [MulOneClassₓ M] {A : Type _} [SetLike A M] [SubmonoidClass A M]
    (S : A) : MulOneClassₓ S :=
  Subtype.coe_injective.MulOneClass _ rfl fun _ _ => rfl

/-- A submonoid of a monoid inherits a monoid structure. -/
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an `add_monoid`\nstructure."]
instance (priority := 75) toMonoid {M : Type _} [Monoidₓ M] {A : Type _} [SetLike A M] [SubmonoidClass A M] (S : A) :
    Monoidₓ S :=
  Subtype.coe_injective.Monoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of a `comm_monoid` is a `comm_monoid`. -/
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
@[to_additive "An `add_submonoid` of an `add_comm_monoid` is\nan `add_comm_monoid`."]
instance (priority := 75) toCommMonoid {M} [CommMonoidₓ M] {A : Type _} [SetLike A M] [SubmonoidClass A M] (S : A) :
    CommMonoidₓ S :=
  Subtype.coe_injective.CommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of an `ordered_comm_monoid` is an `ordered_comm_monoid`. -/
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
@[to_additive "An `add_submonoid` of an `ordered_add_comm_monoid` is\nan `ordered_add_comm_monoid`."]
instance (priority := 75) toOrderedCommMonoid {M} [OrderedCommMonoid M] {A : Type _} [SetLike A M] [SubmonoidClass A M]
    (S : A) : OrderedCommMonoid S :=
  Subtype.coe_injective.OrderedCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of a `linear_ordered_comm_monoid` is a `linear_ordered_comm_monoid`. -/
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
@[to_additive "An `add_submonoid` of a `linear_ordered_add_comm_monoid` is\na `linear_ordered_add_comm_monoid`."]
instance (priority := 75) toLinearOrderedCommMonoid {M} [LinearOrderedCommMonoid M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : LinearOrderedCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ =>
    rfl

/-- A submonoid of an `ordered_cancel_comm_monoid` is an `ordered_cancel_comm_monoid`. -/
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
@[to_additive "An `add_submonoid` of an `ordered_cancel_add_comm_monoid` is\nan `ordered_cancel_add_comm_monoid`."]
instance (priority := 75) toOrderedCancelCommMonoid {M} [OrderedCancelCommMonoid M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : OrderedCancelCommMonoid S :=
  Subtype.coe_injective.OrderedCancelCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of a `linear_ordered_cancel_comm_monoid` is a `linear_ordered_cancel_comm_monoid`.
-/
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
@[to_additive
      "An `add_submonoid` of a `linear_ordered_cancel_add_comm_monoid` is\na `linear_ordered_cancel_add_comm_monoid`."]
instance (priority := 75) toLinearOrderedCancelCommMonoid {M} [LinearOrderedCancelCommMonoid M] {A : Type _}
    [SetLike A M] [SubmonoidClass A M] (S : A) : LinearOrderedCancelCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCancelCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

include hA

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `add_submonoid` of `add_monoid` `M` to `M`."]
def subtype : S' →* M :=
  ⟨coe, rfl, fun _ _ => rfl⟩

@[simp, to_additive]
theorem coe_subtype : (SubmonoidClass.subtype S' : S' → M) = coe :=
  rfl

end SubmonoidClass

namespace Submonoid

/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an addition."]
instance hasMul : Mul S :=
  ⟨fun a b => ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits a zero."]
instance hasOne : One S :=
  ⟨⟨_, S.one_mem⟩⟩

@[simp, norm_cast, to_additive]
theorem coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y :=
  rfl

@[simp, norm_cast, to_additive]
theorem coe_one : ((1 : S) : M) = 1 :=
  rfl

@[simp, to_additive]
theorem mk_mul_mk (x y : M) (hx : x ∈ S) (hy : y ∈ S) : (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, S.mul_mem hx hy⟩ :=
  rfl

@[to_additive]
theorem mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩ :=
  rfl

@[to_additive]
theorem one_def : (1 : S) = ⟨1, S.one_mem⟩ :=
  rfl

/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive "An `add_submonoid` of an unital additive magma inherits an unital additive magma\nstructure."]
instance toMulOneClass {M : Type _} [MulOneClassₓ M] (S : Submonoid M) : MulOneClassₓ S :=
  Subtype.coe_injective.MulOneClass coe rfl fun _ _ => rfl

@[to_additive]
protected theorem pow_mem {M : Type _} [Monoidₓ M] (S : Submonoid M) {x : M} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
  pow_mem hx n

@[simp, norm_cast, to_additive]
theorem coe_pow {M : Type _} [Monoidₓ M] {S : Submonoid M} (x : S) (n : ℕ) : ↑(x ^ n) = (x ^ n : M) :=
  rfl

/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an `add_monoid`\nstructure."]
instance toMonoid {M : Type _} [Monoidₓ M] (S : Submonoid M) : Monoidₓ S :=
  Subtype.coe_injective.Monoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of a `comm_monoid` is a `comm_monoid`. -/
@[to_additive "An `add_submonoid` of an `add_comm_monoid` is\nan `add_comm_monoid`."]
instance toCommMonoid {M} [CommMonoidₓ M] (S : Submonoid M) : CommMonoidₓ S :=
  Subtype.coe_injective.CommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of an `ordered_comm_monoid` is an `ordered_comm_monoid`. -/
@[to_additive "An `add_submonoid` of an `ordered_add_comm_monoid` is\nan `ordered_add_comm_monoid`."]
instance toOrderedCommMonoid {M} [OrderedCommMonoid M] (S : Submonoid M) : OrderedCommMonoid S :=
  Subtype.coe_injective.OrderedCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of a `linear_ordered_comm_monoid` is a `linear_ordered_comm_monoid`. -/
@[to_additive "An `add_submonoid` of a `linear_ordered_add_comm_monoid` is\na `linear_ordered_add_comm_monoid`."]
instance toLinearOrderedCommMonoid {M} [LinearOrderedCommMonoid M] (S : Submonoid M) : LinearOrderedCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ =>
    rfl

/-- A submonoid of an `ordered_cancel_comm_monoid` is an `ordered_cancel_comm_monoid`. -/
@[to_additive "An `add_submonoid` of an `ordered_cancel_add_comm_monoid` is\nan `ordered_cancel_add_comm_monoid`."]
instance toOrderedCancelCommMonoid {M} [OrderedCancelCommMonoid M] (S : Submonoid M) : OrderedCancelCommMonoid S :=
  Subtype.coe_injective.OrderedCancelCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of a `linear_ordered_cancel_comm_monoid` is a `linear_ordered_cancel_comm_monoid`.
-/
@[to_additive
      "An `add_submonoid` of a `linear_ordered_cancel_add_comm_monoid` is\na `linear_ordered_cancel_add_comm_monoid`."]
instance toLinearOrderedCancelCommMonoid {M} [LinearOrderedCancelCommMonoid M] (S : Submonoid M) :
    LinearOrderedCancelCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCancelCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `add_submonoid` of `add_monoid` `M` to `M`."]
def subtype : S →* M :=
  ⟨coe, rfl, fun _ _ => rfl⟩

@[simp, to_additive]
theorem coe_subtype : ⇑S.Subtype = coe :=
  rfl

/-- The top submonoid is isomorphic to the monoid. -/
@[to_additive "The top additive submonoid is isomorphic to the additive monoid.", simps]
def topEquiv : (⊤ : Submonoid M) ≃* M where
  toFun := fun x => x
  invFun := fun x => ⟨x, mem_top x⟩
  left_inv := fun x => x.eta _
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

@[simp, to_additive]
theorem top_equiv_to_monoid_hom : (topEquiv : _ ≃* M).toMonoidHom = (⊤ : Submonoid M).Subtype :=
  rfl

/-- A submonoid is isomorphic to its image under an injective function -/
@[to_additive "An additive submonoid is isomorphic to its image under an injective function"]
noncomputable def equivMapOfInjective (f : M →* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equivₓ.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[simp, to_additive]
theorem coe_equiv_map_of_injective_apply (f : M →* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl

@[simp, to_additive]
theorem closure_closure_coe_preimage {s : Set M} : closure ((coe : closure s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x =>
    (Subtype.recOn x) fun x hx _ => by
      refine' closure_induction' _ (fun g hg => _) _ (fun g₁ g₂ hg₁ hg₂ => _) hx
      · exact subset_closure hg
        
      · exact Submonoid.one_mem _
        
      · exact Submonoid.mul_mem _
        

/-- Given `submonoid`s `s`, `t` of monoids `M`, `N` respectively, `s × t` as a submonoid
of `M × N`. -/
@[to_additive Prod
      "Given `add_submonoid`s `s`, `t` of `add_monoid`s `A`, `B` respectively, `s × t`\nas an `add_submonoid` of `A × B`."]
def prod (s : Submonoid M) (t : Submonoid N) : Submonoid (M × N) where
  Carrier := (s : Set M) ×ˢ (t : Set N)
  one_mem' := ⟨s.one_mem, t.one_mem⟩
  mul_mem' := fun p q hp hq => ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive coe_prod]
theorem coe_prod (s : Submonoid M) (t : Submonoid N) : (s.Prod t : Set (M × N)) = (s : Set M) ×ˢ (t : Set N) :=
  rfl

@[to_additive mem_prod]
theorem mem_prod {s : Submonoid M} {t : Submonoid N} {p : M × N} : p ∈ s.Prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[to_additive prod_mono]
theorem prod_mono {s₁ s₂ : Submonoid M} {t₁ t₂ : Submonoid N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.Prod t₁ ≤ s₂.Prod t₂ :=
  Set.prod_mono hs ht

@[to_additive prod_top]
theorem prod_top (s : Submonoid M) : s.Prod (⊤ : Submonoid N) = s.comap (MonoidHom.fst M N) :=
  ext fun x => by
    simp [← mem_prod, ← MonoidHom.coe_fst]

@[to_additive top_prod]
theorem top_prod (s : Submonoid N) : (⊤ : Submonoid M).Prod s = s.comap (MonoidHom.snd M N) :=
  ext fun x => by
    simp [← mem_prod, ← MonoidHom.coe_snd]

@[simp, to_additive top_prod_top]
theorem top_prod_top : (⊤ : Submonoid M).Prod (⊤ : Submonoid N) = ⊤ :=
  (top_prod _).trans <| comap_top _

@[to_additive]
theorem bot_prod_bot : (⊥ : Submonoid M).Prod (⊥ : Submonoid N) = ⊥ :=
  SetLike.coe_injective <| by
    simp [← coe_prod, ← Prod.one_eq_mk]

/-- The product of submonoids is isomorphic to their product as monoids. -/
@[to_additive prod_equiv "The product of additive submonoids is isomorphic to their product\nas additive monoids"]
def prodEquiv (s : Submonoid M) (t : Submonoid N) : s.Prod t ≃* s × t :=
  { Equivₓ.Set.prod ↑s ↑t with map_mul' := fun x y => rfl }

open MonoidHom

@[to_additive]
theorem map_inl (s : Submonoid M) : s.map (inl M N) = s.Prod ⊥ :=
  ext fun p =>
    ⟨fun ⟨x, hx, hp⟩ => hp ▸ ⟨hx, Set.mem_singleton 1⟩, fun ⟨hps, hp1⟩ =>
      ⟨p.1, hps, Prod.extₓ rfl <| (Set.eq_of_mem_singleton hp1).symm⟩⟩

@[to_additive]
theorem map_inr (s : Submonoid N) : s.map (inr M N) = prod ⊥ s :=
  ext fun p =>
    ⟨fun ⟨x, hx, hp⟩ => hp ▸ ⟨Set.mem_singleton 1, hx⟩, fun ⟨hp1, hps⟩ =>
      ⟨p.2, hps, Prod.extₓ (Set.eq_of_mem_singleton hp1).symm rfl⟩⟩

@[simp, to_additive prod_bot_sup_bot_prod]
theorem prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) : s.Prod ⊥⊔prod ⊥ t = s.Prod t :=
  (le_antisymmₓ (sup_le (prod_mono (le_reflₓ s) bot_le) (prod_mono bot_le (le_reflₓ t)))) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem ((le_sup_left : s.Prod ⊥ ≤ s.Prod ⊥⊔prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
        ((le_sup_right : prod ⊥ t ≤ s.Prod ⊥⊔prod ⊥ t) ⟨Set.mem_singleton 1, hp.2⟩)

@[to_additive]
theorem mem_map_equiv {f : M ≃* N} {K : Submonoid M} {x : N} : x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (↑K) f.toEquiv x

@[to_additive]
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Submonoid M) : K.map f.toMonoidHom = K.comap f.symm.toMonoidHom :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)

@[to_additive]
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Submonoid M) : K.comap f.toMonoidHom = K.map f.symm.toMonoidHom :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[simp, to_additive]
theorem map_equiv_top (f : M ≃* N) : (⊤ : Submonoid M).map f.toMonoidHom = ⊤ :=
  SetLike.coe_injective <| Set.image_univ.trans f.Surjective.range_eq

@[to_additive le_prod_iff]
theorem le_prod_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    u ≤ s.Prod t ↔ u.map (fst M N) ≤ s ∧ u.map (snd M N) ≤ t := by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
      
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
      
    
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩
    

@[to_additive prod_le_iff]
theorem prod_le_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    s.Prod t ≤ u ↔ s.map (inl M N) ≤ u ∧ t.map (inr M N) ≤ u := by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, Submonoid.one_mem _⟩
      
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨Submonoid.one_mem _, hx⟩
      
    
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : inl M N x1 ∈ u := by
      apply hH
      simpa using h1
    have h2' : inr M N x2 ∈ u := by
      apply hK
      simpa using h2
    simpa using Submonoid.mul_mem _ h1' h2'
    

end Submonoid

namespace MonoidHom

variable {F : Type _} [mc : MonoidHomClass F M N]

open Submonoid

library_note "range copy pattern"/--
For many categories (monoids, modules, rings, ...) the set-theoretic image of a morphism `f` is
a subobject of the codomain. When this is the case, it is useful to define the range of a morphism
in such a way that the underlying carrier set of the range subobject is definitionally
`set.range f`. In particular this means that the types `↥(set.range f)` and `↥f.range` are
interchangeable without proof obligations.

A convenient candidate definition for range which is mathematically correct is `map ⊤ f`, just as
`set.range` could have been defined as `f '' set.univ`. However, this lacks the desired definitional
convenience, in that it both does not match `set.range`, and that it introduces a redudant `x ∈ ⊤`
term which clutters proofs. In such a case one may resort to the `copy`
pattern. A `copy` function converts the definitional problem for the carrier set of a subobject
into a one-off propositional proof obligation which one discharges while writing the definition of
the definitionally convenient range (the parameter `hs` in the example below).

A good example is the case of a morphism of monoids. A convenient definition for
`monoid_hom.mrange` would be `(⊤ : submonoid M).map f`. However since this lacks the required
definitional convenience, we first define `submonoid.copy` as follows:
```lean
protected def copy (S : submonoid M) (s : set M) (hs : s = S) : submonoid M :=
{ carrier  := s,
  one_mem' := hs.symm ▸ S.one_mem',
  mul_mem' := hs.symm ▸ S.mul_mem' }
```
and then finally define:
```lean
def mrange (f : M →* N) : submonoid N :=
((⊤ : submonoid M).map f).copy (set.range f) set.image_univ.symm
```
-/


include mc

/-- The range of a monoid homomorphism is a submonoid. See Note [range copy pattern]. -/
@[to_additive "The range of an `add_monoid_hom` is an `add_submonoid`."]
def mrange (f : F) : Submonoid N :=
  ((⊤ : Submonoid M).map f).copy (Set.Range f) Set.image_univ.symm

@[simp, to_additive]
theorem coe_mrange (f : F) : (mrange f : Set N) = Set.Range f :=
  rfl

@[simp, to_additive]
theorem mem_mrange {f : F} {y : N} : y ∈ mrange f ↔ ∃ x, f x = y :=
  Iff.rfl

@[to_additive]
theorem mrange_eq_map (f : F) : mrange f = (⊤ : Submonoid M).map f :=
  copy_eq _

omit mc

@[to_additive]
theorem map_mrange (g : N →* P) (f : M →* N) : f.mrange.map g = (g.comp f).mrange := by
  simpa only [← mrange_eq_map] using (⊤ : Submonoid M).map_map g f

include mc

@[to_additive]
theorem mrange_top_iff_surjective {f : F} : mrange f = (⊤ : Submonoid N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <|
    Iff.trans
      (by
        rw [coe_mrange, coe_top])
      Set.range_iff_surjective

/-- The range of a surjective monoid hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_monoid` hom is the whole of the codomain."]
theorem mrange_top_of_surjective (f : F) (hf : Function.Surjective f) : mrange f = (⊤ : Submonoid N) :=
  mrange_top_iff_surjective.2 hf

@[to_additive]
theorem mclosure_preimage_le (f : F) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set. -/
@[to_additive
      "The image under an `add_monoid` hom of the `add_submonoid` generated by a set equals\nthe `add_submonoid` generated by the image of the set."]
theorem map_mclosure (f : F) (s : Set M) : (closure s).map f = closure (f '' s) :=
  le_antisymmₓ
    (map_le_iff_le_comap.2 <| le_transₓ (closure_mono <| Set.subset_preimage_image _ _) (mclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)

omit mc

/-- Restriction of a monoid hom to a submonoid of the domain. -/
@[to_additive "Restriction of an add_monoid hom to an `add_submonoid` of the domain."]
def restrict {N S : Type _} [MulOneClassₓ N] [SetLike S M] [SubmonoidClass S M] (f : M →* N) (s : S) : s →* N :=
  f.comp (SubmonoidClass.subtype _)

@[simp, to_additive]
theorem restrict_apply {N S : Type _} [MulOneClassₓ N] [SetLike S M] [SubmonoidClass S M] (f : M →* N) (s : S) (x : s) :
    f.restrict s x = f x :=
  rfl

/-- Restriction of a monoid hom to a submonoid of the codomain. -/
@[to_additive "Restriction of an `add_monoid` hom to an `add_submonoid` of the codomain.", simps apply]
def codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S) (h : ∀ x, f x ∈ s) : M →* s where
  toFun := fun n => ⟨f n, h n⟩
  map_one' := Subtype.eq f.map_one
  map_mul' := fun x y => Subtype.eq (f.map_mul x y)

/-- Restriction of a monoid hom to its range interpreted as a submonoid. -/
@[to_additive "Restriction of an `add_monoid` hom to its range interpreted as a submonoid."]
def mrangeRestrict {N} [MulOneClassₓ N] (f : M →* N) : M →* f.mrange :=
  (f.codRestrict f.mrange) fun x => ⟨x, rfl⟩

@[simp, to_additive]
theorem coe_mrange_restrict {N} [MulOneClassₓ N] (f : M →* N) (x : M) : (f.mrangeRestrict x : N) = f x :=
  rfl

@[to_additive]
theorem mrange_restrict_surjective (f : M →* N) : Function.Surjective f.mrangeRestrict := fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

include mc

/-- The multiplicative kernel of a monoid homomorphism is the submonoid of elements `x : G` such
that `f x = 1` -/
@[to_additive
      "The additive kernel of an `add_monoid` homomorphism is the `add_submonoid` of\nelements such that `f x = 0`"]
def mker (f : F) : Submonoid M :=
  (⊥ : Submonoid N).comap f

@[to_additive]
theorem mem_mker (f : F) {x : M} : x ∈ mker f ↔ f x = 1 :=
  Iff.rfl

@[to_additive]
theorem coe_mker (f : F) : (mker f : Set M) = (f : M → N) ⁻¹' {1} :=
  rfl

@[to_additive]
instance decidableMemMker [DecidableEq N] (f : F) : DecidablePred (· ∈ mker f) := fun x =>
  decidableOfIff (f x = 1) (mem_mker f)

omit mc

@[to_additive]
theorem comap_mker (g : N →* P) (f : M →* N) : g.mker.comap f = (g.comp f).mker :=
  rfl

include mc

@[simp, to_additive]
theorem comap_bot' (f : F) : (⊥ : Submonoid N).comap f = mker f :=
  rfl

omit mc

@[to_additive]
theorem range_restrict_mker (f : M →* N) : mker (mrangeRestrict f) = mker f := by
  ext
  change (⟨f x, _⟩ : mrange f) = ⟨1, _⟩ ↔ f x = 1
  simp only

@[simp, to_additive]
theorem mker_one : (1 : M →* N).mker = ⊤ := by
  ext
  simp [← mem_mker]

@[to_additive]
theorem prod_map_comap_prod' {M' : Type _} {N' : Type _} [MulOneClassₓ M'] [MulOneClassₓ N'] (f : M →* N) (g : M' →* N')
    (S : Submonoid N) (S' : Submonoid N') : (S.Prod S').comap (prodMap f g) = (S.comap f).Prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _

@[to_additive]
theorem mker_prod_map {M' : Type _} {N' : Type _} [MulOneClassₓ M'] [MulOneClassₓ N'] (f : M →* N) (g : M' →* N') :
    (prodMap f g).mker = f.mker.Prod g.mker := by
  rw [← comap_bot', ← comap_bot', ← comap_bot', ← prod_map_comap_prod', bot_prod_bot]

@[simp, to_additive]
theorem mker_inl : (inl M N).mker = ⊥ := by
  ext x
  simp [← mem_mker]

@[simp, to_additive]
theorem mker_inr : (inr M N).mker = ⊥ := by
  ext x
  simp [← mem_mker]

/-- The `monoid_hom` from the preimage of a submonoid to itself. -/
@[to_additive "the `add_monoid_hom` from the preimage of an additive submonoid to itself.", simps]
def submonoidComap (f : M →* N) (N' : Submonoid N) : N'.comap f →* N' where
  toFun := fun x => ⟨f x, x.Prop⟩
  map_one' := Subtype.eq f.map_one
  map_mul' := fun x y => Subtype.eq (f.map_mul x y)

/-- The `monoid_hom` from a submonoid to its image.
See `mul_equiv.submonoid_map` for a variant for `mul_equiv`s. -/
@[to_additive
      "the `add_monoid_hom` from an additive submonoid to its image. See\n`add_equiv.add_submonoid_map` for a variant for `add_equiv`s.",
  simps]
def submonoidMap (f : M →* N) (M' : Submonoid M) : M' →* M'.map f where
  toFun := fun x => ⟨f x, ⟨x, x.Prop, rfl⟩⟩
  map_one' := Subtype.eq <| f.map_one
  map_mul' := fun x y => Subtype.eq <| f.map_mul x y

@[to_additive]
theorem submonoid_map_surjective (f : M →* N) (M' : Submonoid M) : Function.Surjective (f.submonoidMap M') := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

end MonoidHom

namespace Submonoid

open MonoidHom

@[to_additive]
theorem mrange_inl : (inl M N).mrange = prod ⊤ ⊥ := by
  simpa only [← mrange_eq_map] using map_inl ⊤

@[to_additive]
theorem mrange_inr : (inr M N).mrange = prod ⊥ ⊤ := by
  simpa only [← mrange_eq_map] using map_inr ⊤

@[to_additive]
theorem mrange_inl' : (inl M N).mrange = comap (snd M N) ⊥ :=
  mrange_inl.trans (top_prod _)

@[to_additive]
theorem mrange_inr' : (inr M N).mrange = comap (fst M N) ⊥ :=
  mrange_inr.trans (prod_top _)

@[simp, to_additive]
theorem mrange_fst : (fst M N).mrange = ⊤ :=
  mrange_top_of_surjective (fst M N) <| @Prod.fst_surjectiveₓ _ _ ⟨1⟩

@[simp, to_additive]
theorem mrange_snd : (snd M N).mrange = ⊤ :=
  mrange_top_of_surjective (snd M N) <| @Prod.snd_surjective _ _ ⟨1⟩

@[to_additive]
theorem prod_eq_bot_iff {s : Submonoid M} {t : Submonoid N} : s.Prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥ := by
  simp only [← eq_bot_iff, ← prod_le_iff, ← (gc_map_comap _).le_iff_le, ← comap_bot', ← mker_inl, ← mker_inr]

@[to_additive]
theorem prod_eq_top_iff {s : Submonoid M} {t : Submonoid N} : s.Prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [← eq_top_iff, ← le_prod_iff, (gc_map_comap _).le_iff_le, mrange_eq_map, ← mrange_fst, ← mrange_snd]

@[simp, to_additive]
theorem mrange_inl_sup_mrange_inr : (inl M N).mrange⊔(inr M N).mrange = ⊤ := by
  simp only [← mrange_inl, ← mrange_inr, ← prod_bot_sup_bot_prod, ← top_prod_top]

/-- The monoid hom associated to an inclusion of submonoids. -/
@[to_additive "The `add_monoid` hom associated to an inclusion of submonoids."]
def inclusion {S T : Submonoid M} (h : S ≤ T) : S →* T :=
  S.Subtype.codRestrict _ fun x => h x.2

@[simp, to_additive]
theorem range_subtype (s : Submonoid M) : s.Subtype.mrange = s :=
  SetLike.coe_injective <| (coe_mrange _).trans <| Subtype.range_coe

@[to_additive]
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

@[to_additive]
theorem eq_bot_iff_forall : S = ⊥ ↔ ∀, ∀ x ∈ S, ∀, x = (1 : M) :=
  SetLike.ext_iff.trans <| by
    simp (config := { contextual := true })[← iff_def, ← S.one_mem]

@[to_additive]
theorem nontrivial_iff_exists_ne_one (S : Submonoid M) : Nontrivial S ↔ ∃ x ∈ S, x ≠ (1 : M) :=
  calc
    Nontrivial S ↔ ∃ x : S, x ≠ 1 := nontrivial_iff_exists_ne 1
    _ ↔ ∃ (x : _)(hx : x ∈ S), (⟨x, hx⟩ : S) ≠ ⟨1, S.one_mem⟩ := Subtype.exists
    _ ↔ ∃ x ∈ S, x ≠ (1 : M) := by
      simp only [← Ne.def]
    

/-- A submonoid is either the trivial submonoid or nontrivial. -/
@[to_additive "An additive submonoid is either the trivial additive submonoid or nontrivial."]
theorem bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S := by
  simp only [← eq_bot_iff_forall, ← nontrivial_iff_exists_ne_one, not_forall, ← Classical.em]

/-- A submonoid is either the trivial submonoid or contains a nonzero element. -/
@[to_additive "An additive submonoid is either the trivial additive submonoid or contains a nonzero\nelement."]
theorem bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ ∃ x ∈ S, x ≠ (1 : M) :=
  S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp

end Submonoid

namespace MulEquiv

variable {S} {T : Submonoid M}

/-- Makes the identity isomorphism from a proof that two submonoids of a multiplicative
    monoid are equal. -/
@[to_additive "Makes the identity additive isomorphism from a proof two\nsubmonoids of an additive monoid are equal."]
def submonoidCongr (h : S = T) : S ≃* T :=
  { Equivₓ.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

/-- A monoid homomorphism `f : M →* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.mrange`.

This is a bidirectional version of `monoid_hom.mrange_restrict`. -/
-- this name is primed so that the version to `f.range` instead of `f.mrange` can be unprimed.
@[to_additive
      "\nAn additive monoid homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an additive\nequivalence between `M` and `f.mrange`.\n\nThis is a bidirectional version of `add_monoid_hom.mrange_restrict`. ",
  simps (config := { simpRhs := true })]
def ofLeftInverse' (f : M →* N) {g : N → M} (h : Function.LeftInverse g f) : M ≃* f.mrange :=
  { f.mrangeRestrict with toFun := f.mrangeRestrict, invFun := g ∘ f.mrange.Subtype, left_inv := h,
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.Prop
        show f (g x) = x by
          rw [← hx', h x'] }

/-- A `mul_equiv` `φ` between two monoids `M` and `N` induces a `mul_equiv` between
a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`.
See `monoid_hom.submonoid_map` for a variant for `monoid_hom`s. -/
@[to_additive
      "An `add_equiv` `φ` between two additive monoids `M` and `N` induces an `add_equiv`\nbetween a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`. See `add_monoid_hom.add_submonoid_map`\nfor a variant for `add_monoid_hom`s.",
  simps]
def submonoidMap (e : M ≃* N) (S : Submonoid M) : S ≃* S.map e.toMonoidHom :=
  { -- we restate this for `simps` to avoid `⇑e.symm.to_equiv x`
          e.toMonoidHom.submonoidMap
      S,
    e.toEquiv.Image S with toFun := fun x => ⟨e x, _⟩, invFun := fun x => ⟨e.symm x, _⟩ }

end MulEquiv

section Actions

/-! ### Actions by `submonoid`s

These instances tranfer the action by an element `m : M` of a monoid `M` written as `m • a` onto the
action by an element `s : S` of a submonoid `S : submonoid M` such that `s • a = (s : M) • a`.

These instances work particularly well in conjunction with `monoid.to_mul_action`, enabling
`s • m` as an alias for `↑s * m`.
-/


namespace Submonoid

variable {M' : Type _} {α β : Type _}

section MulOneClassₓ

variable [MulOneClassₓ M']

@[to_additive]
instance [HasSmul M' α] (S : Submonoid M') : HasSmul S α :=
  HasSmul.comp _ S.Subtype

@[to_additive]
instance smul_comm_class_left [HasSmul M' β] [HasSmul α β] [SmulCommClass M' α β] (S : Submonoid M') :
    SmulCommClass S α β :=
  ⟨fun a => (smul_comm (a : M') : _)⟩

@[to_additive]
instance smul_comm_class_right [HasSmul α β] [HasSmul M' β] [SmulCommClass α M' β] (S : Submonoid M') :
    SmulCommClass α S β :=
  ⟨fun a s => (smul_comm a (s : M') : _)⟩

/-- Note that this provides `is_scalar_tower S M' M'` which is needed by `smul_mul_assoc`. -/
instance [HasSmul α β] [HasSmul M' α] [HasSmul M' β] [IsScalarTower M' α β] (S : Submonoid M') : IsScalarTower S α β :=
  ⟨fun a => (smul_assoc (a : M') : _)⟩

@[to_additive]
theorem smul_def [HasSmul M' α] {S : Submonoid M'} (g : S) (m : α) : g • m = (g : M') • m :=
  rfl

instance [HasSmul M' α] [HasFaithfulSmul M' α] (S : Submonoid M') : HasFaithfulSmul S α :=
  ⟨fun x y h => Subtype.ext <| eq_of_smul_eq_smul h⟩

end MulOneClassₓ

variable [Monoidₓ M']

/-- The action by a submonoid is the action by the underlying monoid. -/
@[to_additive "The additive action by an add_submonoid is the action by the underlying\nadd_monoid. "]
instance [MulAction M' α] (S : Submonoid M') : MulAction S α :=
  MulAction.compHom _ S.Subtype

/-- The action by a submonoid is the action by the underlying monoid. -/
instance [AddMonoidₓ α] [DistribMulAction M' α] (S : Submonoid M') : DistribMulAction S α :=
  DistribMulAction.compHom _ S.Subtype

/-- The action by a submonoid is the action by the underlying monoid. -/
instance [Monoidₓ α] [MulDistribMulAction M' α] (S : Submonoid M') : MulDistribMulAction S α :=
  MulDistribMulAction.compHom _ S.Subtype

example {S : Submonoid M'} : IsScalarTower S M' M' := by
  infer_instance

end Submonoid

end Actions

