/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky, Jireh Loreaux
-/
import Mathbin.GroupTheory.Subsemigroup.Basic

/-!
# Operations on `subsemigroup`s

In this file we define various operations on `subsemigroup`s and `mul_hom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `subsemigroup.to_add_subsemigroup`, `subsemigroup.to_add_subsemigroup'`,
  `add_subsemigroup.to_subsemigroup`, `add_subsemigroup.to_subsemigroup'`:
  convert between multiplicative and additive subsemigroups of `M`,
  `multiplicative M`, and `additive M`. These are stated as `order_iso`s.

### (Commutative) semigroup structure on a subsemigroup

* `subsemigroup.to_semigroup`, `subsemigroup.to_comm_semigroup`: a subsemigroup inherits a
  (commutative) semigroup structure.

### Operations on subsemigroups

* `subsemigroup.comap`: preimage of a subsemigroup under a semigroup homomorphism as a subsemigroup
  of the domain;
* `subsemigroup.map`: image of a subsemigroup under a semigroup homomorphism as a subsemigroup of
  the codomain;
* `subsemigroup.prod`: product of two subsemigroups `s : subsemigroup M` and `t : subsemigroup N`
  as a subsemigroup of `M × N`;

### Semigroup homomorphisms between subsemigroups

* `subsemigroup.subtype`: embedding of a subsemigroup into the ambient semigroup.
* `subsemigroup.inclusion`: given two subsemigroups `S`, `T` such that `S ≤ T`, `S.inclusion T` is
  the inclusion of `S` into `T` as a semigroup homomorphism;
* `mul_equiv.subsemigroup_congr`: converts a proof of `S = T` into a semigroup isomorphism between
  `S` and `T`.
* `subsemigroup.prod_equiv`: semigroup isomorphism between `s.prod t` and `s × t`;

### Operations on `mul_hom`s

* `mul_hom.srange`: range of a semigroup homomorphism as a subsemigroup of the codomain;
* `mul_hom.restrict`: restrict a semigroup homomorphism to a subsemigroup;
* `mul_hom.cod_restrict`: restrict the codomain of a semigroup homomorphism to a subsemigroup;
* `mul_hom.srange_restrict`: restrict a semigroup homomorphism to its range;

### Implementation notes

This file follows closely `group_theory/submonoid/operations.lean`, omitting only that which is
necessary.

## Tags

subsemigroup, range, product, map, comap
-/


variable {M N P σ : Type _}

/-!
### Conversion to/from `additive`/`multiplicative`
-/


section

variable [Mul M]

/-- Subsemigroups of semigroup `M` are isomorphic to additive subsemigroups of `additive M`. -/
@[simps]
def Subsemigroup.toAddSubsemigroup : Subsemigroup M ≃o AddSubsemigroup (Additive M) where
  toFun := fun S => { Carrier := Additive.toMul ⁻¹' S, add_mem' := S.mul_mem' }
  invFun := fun S => { Carrier := Additive.ofMul ⁻¹' S, mul_mem' := S.add_mem' }
  left_inv := fun x => by
    cases x <;> rfl
  right_inv := fun x => by
    cases x <;> rfl
  map_rel_iff' := fun a b => Iff.rfl

/-- Additive subsemigroups of an additive semigroup `additive M` are isomorphic to subsemigroups
of `M`. -/
abbrev AddSubsemigroup.toSubsemigroup' : AddSubsemigroup (Additive M) ≃o Subsemigroup M :=
  Subsemigroup.toAddSubsemigroup.symm

theorem Subsemigroup.to_add_subsemigroup_closure (S : Set M) :
    (Subsemigroup.closure S).toAddSubsemigroup = AddSubsemigroup.closure (Additive.toMul ⁻¹' S) :=
  le_antisymmₓ
    (Subsemigroup.toAddSubsemigroup.le_symm_apply.1 <| Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)
    (AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)

theorem AddSubsemigroup.to_subsemigroup'_closure (S : Set (Additive M)) :
    (AddSubsemigroup.closure S).toSubsemigroup' = Subsemigroup.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymmₓ
    (AddSubsemigroup.toSubsemigroup'.le_symm_apply.1 <| AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)
    (Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)

end

section

variable {A : Type _} [Add A]

/-- Additive subsemigroups of an additive semigroup `A` are isomorphic to
multiplicative subsemigroups of `multiplicative A`. -/
@[simps]
def AddSubsemigroup.toSubsemigroup : AddSubsemigroup A ≃o Subsemigroup (Multiplicative A) where
  toFun := fun S => { Carrier := Multiplicative.toAdd ⁻¹' S, mul_mem' := S.add_mem' }
  invFun := fun S => { Carrier := Multiplicative.ofAdd ⁻¹' S, add_mem' := S.mul_mem' }
  left_inv := fun x => by
    cases x <;> rfl
  right_inv := fun x => by
    cases x <;> rfl
  map_rel_iff' := fun a b => Iff.rfl

/-- Subsemigroups of a semigroup `multiplicative A` are isomorphic to additive subsemigroups
of `A`. -/
abbrev Subsemigroup.toAddSubsemigroup' : Subsemigroup (Multiplicative A) ≃o AddSubsemigroup A :=
  AddSubsemigroup.toSubsemigroup.symm

theorem AddSubsemigroup.to_subsemigroup_closure (S : Set A) :
    (AddSubsemigroup.closure S).toSubsemigroup = Subsemigroup.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymmₓ
    (AddSubsemigroup.toSubsemigroup.to_galois_connection.l_le <|
      AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)
    (Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)

theorem Subsemigroup.to_add_subsemigroup'_closure (S : Set (Multiplicative A)) :
    (Subsemigroup.closure S).toAddSubsemigroup' = AddSubsemigroup.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymmₓ
    (Subsemigroup.toAddSubsemigroup'.to_galois_connection.l_le <|
      Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)
    (AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)

end

namespace Subsemigroup

open Set

/-!
### `comap` and `map`
-/


variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The preimage of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive "The preimage of an `add_subsemigroup` along an `add_semigroup` homomorphism is an\n`add_subsemigroup`."]
def comap (f : M →ₙ* N) (S : Subsemigroup N) : Subsemigroup M where
  Carrier := f ⁻¹' S
  mul_mem' := fun a b ha hb =>
    show f (a * b) ∈ S by
      rw [map_mul] <;> exact mul_mem ha hb

@[simp, to_additive]
theorem coe_comap (S : Subsemigroup N) (f : M →ₙ* N) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl

@[simp, to_additive]
theorem mem_comap {S : Subsemigroup N} {f : M →ₙ* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

@[to_additive]
theorem comap_comap (S : Subsemigroup P) (g : N →ₙ* P) (f : M →ₙ* N) : (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp, to_additive]
theorem comap_id (S : Subsemigroup P) : S.comap (MulHom.id _) = S :=
  ext
    (by
      simp )

/-- The image of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive "The image of an `add_subsemigroup` along an `add_semigroup` homomorphism is\nan `add_subsemigroup`."]
def map (f : M →ₙ* N) (S : Subsemigroup M) : Subsemigroup N where
  Carrier := f '' S
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact
      ⟨x * y, @mul_mem (Subsemigroup M) M _ _ _ _ _ _ hx hy, by
        rw [map_mul] <;> rfl⟩

@[simp, to_additive]
theorem coe_map (f : M →ₙ* N) (S : Subsemigroup M) : (S.map f : Set N) = f '' S :=
  rfl

@[simp, to_additive]
theorem mem_map {f : M →ₙ* N} {S : Subsemigroup M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image_iff_bex

@[to_additive]
theorem mem_map_of_mem (f : M →ₙ* N) {S : Subsemigroup M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx

@[to_additive]
theorem apply_coe_mem_map (f : M →ₙ* N) (S : Subsemigroup M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.Prop

@[to_additive]
theorem map_map (g : N →ₙ* P) (f : M →ₙ* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _

@[to_additive]
theorem mem_map_iff_mem {f : M →ₙ* N} (hf : Function.Injective f) {S : Subsemigroup M} {x : M} :
    f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image

@[to_additive]
theorem map_le_iff_le_comap {f : M →ₙ* N} {S : Subsemigroup M} {T : Subsemigroup N} : S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff

@[to_additive]
theorem gc_map_comap (f : M →ₙ* N) : GaloisConnection (map f) (comap f) := fun S T => map_le_iff_le_comap

@[to_additive]
theorem map_le_of_le_comap {T : Subsemigroup N} {f : M →ₙ* N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le

@[to_additive]
theorem le_comap_of_map_le {T : Subsemigroup N} {f : M →ₙ* N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u

@[to_additive]
theorem le_comap_map {f : M →ₙ* N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

@[to_additive]
theorem map_comap_le {S : Subsemigroup N} {f : M →ₙ* N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _

@[to_additive]
theorem monotone_map {f : M →ₙ* N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

@[to_additive]
theorem monotone_comap {f : M →ₙ* N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[simp, to_additive]
theorem map_comap_map {f : M →ₙ* N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[simp, to_additive]
theorem comap_map_comap {S : Subsemigroup N} {f : M →ₙ* N} : ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

@[to_additive]
theorem map_sup (S T : Subsemigroup M) (f : M →ₙ* N) : (S⊔T).map f = S.map f⊔T.map f :=
  (gc_map_comap f).l_sup

@[to_additive]
theorem map_supr {ι : Sort _} (f : M →ₙ* N) (s : ι → Subsemigroup M) : (supr s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_supr

@[to_additive]
theorem comap_inf (S T : Subsemigroup N) (f : M →ₙ* N) : (S⊓T).comap f = S.comap f⊓T.comap f :=
  (gc_map_comap f).u_inf

@[to_additive]
theorem comap_infi {ι : Sort _} (f : M →ₙ* N) (s : ι → Subsemigroup N) : (infi s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_infi

@[simp, to_additive]
theorem map_bot (f : M →ₙ* N) : (⊥ : Subsemigroup M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp, to_additive]
theorem comap_top (f : M →ₙ* N) : (⊤ : Subsemigroup N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp, to_additive]
theorem map_id (S : Subsemigroup M) : S.map (MulHom.id M) = S :=
  ext fun x => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

section GaloisCoinsertion

variable {ι : Type _} {f : M →ₙ* N} (hf : Function.Injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
@[to_additive " `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. "]
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp [← mem_comap, ← mem_map, ← hf.eq_iff]

@[to_additive]
theorem comap_map_eq_of_injective (S : Subsemigroup M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _

@[to_additive]
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

@[to_additive]
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

@[to_additive]
theorem comap_inf_map_of_injective (S T : Subsemigroup M) : (S.map f⊓T.map f).comap f = S⊓T :=
  (gciMapComap hf).u_inf_l _ _

@[to_additive]
theorem comap_infi_map_of_injective (S : ι → Subsemigroup M) : (⨅ i, (S i).map f).comap f = infi S :=
  (gciMapComap hf).u_infi_l _

@[to_additive]
theorem comap_sup_map_of_injective (S T : Subsemigroup M) : (S.map f⊔T.map f).comap f = S⊔T :=
  (gciMapComap hf).u_sup_l _ _

@[to_additive]
theorem comap_supr_map_of_injective (S : ι → Subsemigroup M) : (⨆ i, (S i).map f).comap f = supr S :=
  (gciMapComap hf).u_supr_l _

@[to_additive]
theorem map_le_map_iff_of_injective {S T : Subsemigroup M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff

@[to_additive]
theorem map_strict_mono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strict_mono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type _} {f : M →ₙ* N} (hf : Function.Surjective f)

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
theorem map_comap_eq_of_surjective (S : Subsemigroup N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _

@[to_additive]
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

@[to_additive]
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

@[to_additive]
theorem map_inf_comap_of_surjective (S T : Subsemigroup N) : (S.comap f⊓T.comap f).map f = S⊓T :=
  (giMapComap hf).l_inf_u _ _

@[to_additive]
theorem map_infi_comap_of_surjective (S : ι → Subsemigroup N) : (⨅ i, (S i).comap f).map f = infi S :=
  (giMapComap hf).l_infi_u _

@[to_additive]
theorem map_sup_comap_of_surjective (S T : Subsemigroup N) : (S.comap f⊔T.comap f).map f = S⊔T :=
  (giMapComap hf).l_sup_u _ _

@[to_additive]
theorem map_supr_comap_of_surjective (S : ι → Subsemigroup N) : (⨆ i, (S i).comap f).map f = supr S :=
  (giMapComap hf).l_supr_u _

@[to_additive]
theorem comap_le_comap_iff_of_surjective {S T : Subsemigroup N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff

@[to_additive]
theorem comap_strict_mono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strict_mono_u

end GaloisInsertion

end Subsemigroup

namespace MulMemClass

variable {A : Type _} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

include hA

/-- A submagma of a magma inherits a multiplication. -/
-- lower priority so other instances are found first
@[to_additive "An additive submagma of an additive magma inherits an addition."]
instance (priority := 900) hasMul : Mul S' :=
  ⟨fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩⟩

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[simp, norm_cast, to_additive]
theorem coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y :=
  rfl

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[simp, to_additive]
theorem mk_mul_mk (x y : M) (hx : x ∈ S') (hy : y ∈ S') : (⟨x, hx⟩ : S') * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ :=
  rfl

@[to_additive]
theorem mul_def (x y : S') : x * y = ⟨x * y, mul_mem x.2 y.2⟩ :=
  rfl

omit hA

/-- A subsemigroup of a semigroup inherits a semigroup structure. -/
@[to_additive "An `add_subsemigroup` of an `add_semigroup` inherits an `add_semigroup` structure."]
instance toSemigroup {M : Type _} [Semigroupₓ M] {A : Type _} [SetLike A M] [MulMemClass A M] (S : A) : Semigroupₓ S :=
  Subtype.coe_injective.Semigroup coe fun _ _ => rfl

/-- A subsemigroup of a `comm_semigroup` is a `comm_semigroup`. -/
@[to_additive "An `add_subsemigroup` of an `add_comm_semigroup` is an `add_comm_semigroup`."]
instance toCommSemigroup {M} [CommSemigroupₓ M] {A : Type _} [SetLike A M] [MulMemClass A M] (S : A) :
    CommSemigroupₓ S :=
  Subtype.coe_injective.CommSemigroup coe fun _ _ => rfl

include hA

/-- The natural semigroup hom from a subsemigroup of semigroup `M` to `M`. -/
@[to_additive "The natural semigroup hom from an `add_subsemigroup` of `add_semigroup` `M` to `M`."]
def subtype : S' →ₙ* M :=
  ⟨coe, fun _ _ => rfl⟩

@[simp, to_additive]
theorem coe_subtype : (MulMemClass.subtype S' : S' → M) = coe :=
  rfl

end MulMemClass

namespace Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The top subsemigroup is isomorphic to the semigroup. -/
@[to_additive "The top additive subsemigroup is isomorphic to the additive semigroup.", simps]
def topEquiv : (⊤ : Subsemigroup M) ≃* M where
  toFun := fun x => x
  invFun := fun x => ⟨x, mem_top x⟩
  left_inv := fun x => x.eta _
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

@[simp, to_additive]
theorem top_equiv_to_mul_hom : (topEquiv : _ ≃* M).toMulHom = MulMemClass.subtype (⊤ : Subsemigroup M) :=
  rfl

/-- A subsemigroup is isomorphic to its image under an injective function -/
@[to_additive "An additive subsemigroup is isomorphic to its image under an injective function"]
noncomputable def equivMapOfInjective (f : M →ₙ* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equivₓ.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }

@[simp, to_additive]
theorem coe_equiv_map_of_injective_apply (f : M →ₙ* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl

@[simp, to_additive]
theorem closure_closure_coe_preimage {s : Set M} : closure ((coe : closure s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x =>
    (Subtype.recOn x) fun x hx _ => by
      refine' closure_induction' _ (fun g hg => _) (fun g₁ g₂ hg₁ hg₂ => _) hx
      · exact subset_closure hg
        
      · exact Subsemigroup.mul_mem _
        

/-- Given `subsemigroup`s `s`, `t` of semigroups `M`, `N` respectively, `s × t` as a subsemigroup
of `M × N`. -/
@[to_additive Prod
      "Given `add_subsemigroup`s `s`, `t` of `add_semigroup`s `A`, `B` respectively,\n`s × t` as an `add_subsemigroup` of `A × B`."]
def prod (s : Subsemigroup M) (t : Subsemigroup N) : Subsemigroup (M × N) where
  Carrier := (s : Set M) ×ˢ (t : Set N)
  mul_mem' := fun p q hp hq => ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive coe_prod]
theorem coe_prod (s : Subsemigroup M) (t : Subsemigroup N) : (s.Prod t : Set (M × N)) = (s : Set M) ×ˢ (t : Set N) :=
  rfl

@[to_additive mem_prod]
theorem mem_prod {s : Subsemigroup M} {t : Subsemigroup N} {p : M × N} : p ∈ s.Prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[to_additive prod_mono]
theorem prod_mono {s₁ s₂ : Subsemigroup M} {t₁ t₂ : Subsemigroup N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁.Prod t₁ ≤ s₂.Prod t₂ :=
  Set.prod_mono hs ht

@[to_additive prod_top]
theorem prod_top (s : Subsemigroup M) : s.Prod (⊤ : Subsemigroup N) = s.comap (MulHom.fst M N) :=
  ext fun x => by
    simp [← mem_prod, ← MulHom.coe_fst]

@[to_additive top_prod]
theorem top_prod (s : Subsemigroup N) : (⊤ : Subsemigroup M).Prod s = s.comap (MulHom.snd M N) :=
  ext fun x => by
    simp [← mem_prod, ← MulHom.coe_snd]

@[simp, to_additive top_prod_top]
theorem top_prod_top : (⊤ : Subsemigroup M).Prod (⊤ : Subsemigroup N) = ⊤ :=
  (top_prod _).trans <| comap_top _

@[to_additive]
theorem bot_prod_bot : (⊥ : Subsemigroup M).Prod (⊥ : Subsemigroup N) = ⊥ :=
  SetLike.coe_injective <| by
    simp [← coe_prod, ← Prod.one_eq_mk]

/-- The product of subsemigroups is isomorphic to their product as semigroups. -/
@[to_additive prod_equiv "The product of additive subsemigroups is isomorphic to their product\nas additive semigroups"]
def prodEquiv (s : Subsemigroup M) (t : Subsemigroup N) : s.Prod t ≃* s × t :=
  { Equivₓ.Set.prod ↑s ↑t with map_mul' := fun x y => rfl }

open MulHom

@[to_additive]
theorem mem_map_equiv {f : M ≃* N} {K : Subsemigroup M} {x : N} : x ∈ K.map f.toMulHom ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (↑K) f.toEquiv x

@[to_additive]
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Subsemigroup M) : K.map f.toMulHom = K.comap f.symm.toMulHom :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)

@[to_additive]
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Subsemigroup M) : K.comap f.toMulHom = K.map f.symm.toMulHom :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[simp, to_additive]
theorem map_equiv_top (f : M ≃* N) : (⊤ : Subsemigroup M).map f.toMulHom = ⊤ :=
  SetLike.coe_injective <| Set.image_univ.trans f.Surjective.range_eq

@[to_additive le_prod_iff]
theorem le_prod_iff {s : Subsemigroup M} {t : Subsemigroup N} {u : Subsemigroup (M × N)} :
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
    

end Subsemigroup

namespace MulHom

open Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The range of a semigroup homomorphism is a subsemigroup. See Note [range copy pattern]. -/
@[to_additive "The range of an `add_hom` is an `add_subsemigroup`."]
def srange (f : M →ₙ* N) : Subsemigroup N :=
  ((⊤ : Subsemigroup M).map f).copy (Set.Range f) Set.image_univ.symm

@[simp, to_additive]
theorem coe_srange (f : M →ₙ* N) : (f.srange : Set N) = Set.Range f :=
  rfl

@[simp, to_additive]
theorem mem_srange {f : M →ₙ* N} {y : N} : y ∈ f.srange ↔ ∃ x, f x = y :=
  Iff.rfl

@[to_additive]
theorem srange_eq_map (f : M →ₙ* N) : f.srange = (⊤ : Subsemigroup M).map f :=
  copy_eq _

@[to_additive]
theorem map_srange (g : N →ₙ* P) (f : M →ₙ* N) : f.srange.map g = (g.comp f).srange := by
  simpa only [← srange_eq_map] using (⊤ : Subsemigroup M).map_map g f

@[to_additive]
theorem srange_top_iff_surjective {N} [Mul N] {f : M →ₙ* N} : f.srange = (⊤ : Subsemigroup N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <|
    Iff.trans
      (by
        rw [coe_srange, coe_top])
      Set.range_iff_surjective

/-- The range of a surjective semigroup hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_semigroup` hom is the whole of the codomain."]
theorem srange_top_of_surjective {N} [Mul N] (f : M →ₙ* N) (hf : Function.Surjective f) :
    f.srange = (⊤ : Subsemigroup N) :=
  srange_top_iff_surjective.2 hf

@[to_additive]
theorem mclosure_preimage_le (f : M →ₙ* N) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a semigroup hom of the subsemigroup generated by a set equals the subsemigroup
generated by the image of the set. -/
@[to_additive
      "The image under an `add_semigroup` hom of the `add_subsemigroup` generated by a set\nequals the `add_subsemigroup` generated by the image of the set."]
theorem map_mclosure (f : M →ₙ* N) (s : Set M) : (closure s).map f = closure (f '' s) :=
  le_antisymmₓ
    (map_le_iff_le_comap.2 <| le_transₓ (closure_mono <| Set.subset_preimage_image _ _) (mclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)

/-- Restriction of a semigroup hom to a subsemigroup of the domain. -/
@[to_additive "Restriction of an add_semigroup hom to an `add_subsemigroup` of the domain."]
def restrict {N : Type _} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) (S : σ) : S →ₙ* N :=
  f.comp (MulMemClass.subtype S)

@[simp, to_additive]
theorem restrict_apply {N : Type _} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) {S : σ} (x : S) :
    f.restrict S x = f x :=
  rfl

/-- Restriction of a semigroup hom to a subsemigroup of the codomain. -/
@[to_additive "Restriction of an `add_semigroup` hom to an `add_subsemigroup` of the\ncodomain.", simps]
def codRestrict [SetLike σ N] [MulMemClass σ N] (f : M →ₙ* N) (S : σ) (h : ∀ x, f x ∈ S) : M →ₙ* S where
  toFun := fun n => ⟨f n, h n⟩
  map_mul' := fun x y => Subtype.eq (map_mul f x y)

/-- Restriction of a semigroup hom to its range interpreted as a subsemigroup. -/
@[to_additive "Restriction of an `add_semigroup` hom to its range interpreted as a subsemigroup."]
def srangeRestrict {N} [Mul N] (f : M →ₙ* N) : M →ₙ* f.srange :=
  (f.codRestrict f.srange) fun x => ⟨x, rfl⟩

@[simp, to_additive]
theorem coe_srange_restrict {N} [Mul N] (f : M →ₙ* N) (x : M) : (f.srangeRestrict x : N) = f x :=
  rfl

@[to_additive]
theorem srange_restrict_surjective (f : M →ₙ* N) : Function.Surjective f.srangeRestrict := fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

@[to_additive]
theorem prod_map_comap_prod' {M' : Type _} {N' : Type _} [Mul M'] [Mul N'] (f : M →ₙ* N) (g : M' →ₙ* N')
    (S : Subsemigroup N) (S' : Subsemigroup N') : (S.Prod S').comap (prodMap f g) = (S.comap f).Prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _

/-- The `mul_hom` from the preimage of a subsemigroup to itself. -/
@[to_additive "the `add_hom` from the preimage of an additive subsemigroup to itself.", simps]
def subsemigroupComap (f : M →ₙ* N) (N' : Subsemigroup N) : N'.comap f →ₙ* N' where
  toFun := fun x => ⟨f x, x.Prop⟩
  map_mul' := fun x y => Subtype.eq (@map_mul M N _ _ _ _ f x y)

/-- The `mul_hom` from a subsemigroup to its image.
See `mul_equiv.subsemigroup_map` for a variant for `mul_equiv`s. -/
@[to_additive
      "the `add_hom` from an additive subsemigroup to its image. See\n`add_equiv.add_subsemigroup_map` for a variant for `add_equiv`s.",
  simps]
def subsemigroupMap (f : M →ₙ* N) (M' : Subsemigroup M) : M' →ₙ* M'.map f where
  toFun := fun x => ⟨f x, ⟨x, x.Prop, rfl⟩⟩
  map_mul' := fun x y => Subtype.eq <| @map_mul M N _ _ _ _ f x y

@[to_additive]
theorem subsemigroup_map_surjective (f : M →ₙ* N) (M' : Subsemigroup M) : Function.Surjective (f.subsemigroupMap M') :=
  by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

end MulHom

namespace Subsemigroup

open MulHom

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

@[simp, to_additive]
theorem srange_fst [Nonempty N] : (fst M N).srange = ⊤ :=
  (fst M N).srange_top_of_surjective <| Prod.fst_surjectiveₓ

@[simp, to_additive]
theorem srange_snd [Nonempty M] : (snd M N).srange = ⊤ :=
  (snd M N).srange_top_of_surjective <| Prod.snd_surjective

@[to_additive]
theorem prod_eq_top_iff [Nonempty M] [Nonempty N] {s : Subsemigroup M} {t : Subsemigroup N} :
    s.Prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [← eq_top_iff, ← le_prod_iff, (gc_map_comap _).le_iff_le, srange_eq_map, ← srange_fst, ← srange_snd]

/-- The semigroup hom associated to an inclusion of subsemigroups. -/
@[to_additive "The `add_semigroup` hom associated to an inclusion of subsemigroups."]
def inclusion {S T : Subsemigroup M} (h : S ≤ T) : S →ₙ* T :=
  (MulMemClass.subtype S).codRestrict _ fun x => h x.2

@[simp, to_additive]
theorem range_subtype (s : Subsemigroup M) : (MulMemClass.subtype s).srange = s :=
  SetLike.coe_injective <| (coe_srange _).trans <| Subtype.range_coe

@[to_additive]
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

end Subsemigroup

namespace MulEquiv

variable [Mul M] [Mul N] {S T : Subsemigroup M}

/-- Makes the identity isomorphism from a proof that two subsemigroups of a multiplicative
    semigroup are equal. -/
@[to_additive
      "Makes the identity additive isomorphism from a proof two\nsubsemigroups of an additive semigroup are equal."]
def subsemigroupCongr (h : S = T) : S ≃* T :=
  { Equivₓ.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

/-- A semigroup homomorphism `f : M →ₙ* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.srange`.

This is a bidirectional version of `mul_hom.srange_restrict`. -/
-- this name is primed so that the version to `f.range` instead of `f.srange` can be unprimed.
@[to_additive
      "\nAn additive semigroup homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an additive\nequivalence between `M` and `f.srange`.\n\nThis is a bidirectional version of `add_hom.srange_restrict`. ",
  simps (config := { simpRhs := true })]
def ofLeftInverse (f : M →ₙ* N) {g : N → M} (h : Function.LeftInverse g f) : M ≃* f.srange :=
  { f.srangeRestrict with toFun := f.srangeRestrict, invFun := g ∘ MulMemClass.subtype f.srange, left_inv := h,
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MulHom.mem_srange.mp x.Prop
        show f (g x) = x by
          rw [← hx', h x'] }

/-- A `mul_equiv` `φ` between two semigroups `M` and `N` induces a `mul_equiv` between
a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
See `mul_hom.subsemigroup_map` for a variant for `mul_hom`s. -/
@[to_additive
      "An `add_equiv` `φ` between two additive semigroups `M` and `N` induces an `add_equiv`\nbetween a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`. See `add_hom.add_subsemigroup_map`\nfor a variant for `add_hom`s.",
  simps]
def subsemigroupMap (e : M ≃* N) (S : Subsemigroup M) : S ≃* S.map e.toMulHom :=
  { -- we restate this for `simps` to avoid `⇑e.symm.to_equiv x`
          e.toMulHom.subsemigroupMap
      S,
    e.toEquiv.Image S with toFun := fun x => ⟨e x, _⟩, invFun := fun x => ⟨e.symm x, _⟩ }

end MulEquiv

