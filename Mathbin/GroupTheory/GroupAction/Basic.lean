/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Algebra.Hom.GroupAction
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.GroupTheory.GroupAction.Group
import Mathbin.Data.Setoid.Basic
import Mathbin.Data.Fintype.Card

/-!
# Basic properties of group actions

This file primarily concerns itself with orbits, stabilizers, and other objects defined in terms of
actions. Despite this file being called `basic`, low-level helper lemmas for algebraic manipulation
of `•` belong elsewhere.

## Main definitions

* `mul_action.orbit`
* `mul_action.fixed_points`
* `mul_action.fixed_by`
* `mul_action.stabilizer`

-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open BigOperators Pointwise

open Function

namespace MulAction

variable (α) [Monoidₓ α] [MulAction α β]

/-- The orbit of an element under an action. -/
@[to_additive "The orbit of an element under an action."]
def Orbit (b : β) :=
  Set.Range fun x : α => x • b

variable {α}

@[to_additive]
theorem mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ Orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
  Iff.rfl

@[simp, to_additive]
theorem mem_orbit (b : β) (x : α) : x • b ∈ Orbit α b :=
  ⟨x, rfl⟩

@[simp, to_additive]
theorem mem_orbit_self (b : β) : b ∈ Orbit α b :=
  ⟨1, by
    simp [← MulAction.one_smul]⟩

@[to_additive]
theorem orbit_nonempty (b : β) : Set.Nonempty (Orbit α b) :=
  Set.range_nonempty _

@[to_additive]
theorem maps_to_smul_orbit (a : α) (b : β) : Set.MapsTo ((· • ·) a) (Orbit α b) (Orbit α b) :=
  Set.range_subset_iff.2 fun a' => ⟨a * a', mul_smul _ _ _⟩

@[to_additive]
theorem smul_orbit_subset (a : α) (b : β) : a • Orbit α b ⊆ Orbit α b :=
  (maps_to_smul_orbit a b).image_subset

@[to_additive]
theorem orbit_smul_subset (a : α) (b : β) : Orbit α (a • b) ⊆ Orbit α b :=
  Set.range_subset_iff.2 fun a' => mul_smul a' a b ▸ mem_orbit _ _

@[to_additive]
instance {b : β} : MulAction α (Orbit α b) where
  smul := fun a => (maps_to_smul_orbit a b).restrict _ _ _
  one_smul := fun a => Subtype.ext (one_smul α a)
  mul_smul := fun a a' b' => Subtype.ext (mul_smul a a' b')

@[simp, to_additive]
theorem Orbit.coe_smul {b : β} {a : α} {b' : Orbit α b} : ↑(a • b') = a • (b' : β) :=
  rfl

variable (α) (β)

/-- The set of elements fixed under the whole action. -/
@[to_additive "The set of elements fixed under the whole action."]
def FixedPoints : Set β :=
  { b : β | ∀ x : α, x • b = b }

/-- `fixed_by g` is the subfield of elements fixed by `g`. -/
@[to_additive "`fixed_by g` is the subfield of elements fixed by `g`."]
def FixedBy (g : α) : Set β :=
  { x | g • x = x }

@[to_additive]
theorem fixed_eq_Inter_fixed_by : FixedPoints α β = ⋂ g : α, FixedBy α β g :=
  Set.ext fun x => ⟨fun hx => Set.mem_Inter.2 fun g => hx g, fun hx g => (Set.mem_Inter.1 hx g : _)⟩

variable {α} (β)

@[simp, to_additive]
theorem mem_fixed_points {b : β} : b ∈ FixedPoints α β ↔ ∀ x : α, x • b = b :=
  Iff.rfl

@[simp, to_additive]
theorem mem_fixed_by {g : α} {b : β} : b ∈ FixedBy α β g ↔ g • b = b :=
  Iff.rfl

@[to_additive]
theorem mem_fixed_points' {b : β} : b ∈ FixedPoints α β ↔ ∀ b', b' ∈ Orbit α b → b' = b :=
  ⟨fun h b h₁ =>
    let ⟨x, hx⟩ := mem_orbit_iff.1 h₁
    hx ▸ h x,
    fun h b => h _ (mem_orbit _ _)⟩

variable (α) {β}

/-- The stabilizer of a point `b` as a submonoid of `α`. -/
@[to_additive "The stabilizer of a point `b` as an additive submonoid of `α`."]
def Stabilizer.submonoid (b : β) : Submonoid α where
  Carrier := { a | a • b = b }
  one_mem' := one_smul _ b
  mul_mem' := fun a a' (ha : a • b = b) (hb : a' • b = b) =>
    show (a * a') • b = b by
      rw [← smul_smul, hb, ha]

@[simp, to_additive]
theorem mem_stabilizer_submonoid_iff {b : β} {a : α} : a ∈ Stabilizer.submonoid α b ↔ a • b = b :=
  Iff.rfl

@[to_additive]
theorem orbit_eq_univ [IsPretransitive α β] (x : β) : Orbit α x = Set.Univ :=
  (surjective_smul α x).range_eq

variable {α} {β}

@[to_additive]
theorem mem_fixed_points_iff_card_orbit_eq_one {a : β} [Fintype (Orbit α a)] :
    a ∈ FixedPoints α β ↔ Fintype.card (Orbit α a) = 1 := by
  rw [Fintype.card_eq_one_iff, mem_fixed_points]
  constructor
  · exact fun h =>
      ⟨⟨a, mem_orbit_self _⟩, fun ⟨b, ⟨x, hx⟩⟩ =>
        Subtype.eq <| by
          simp [← h x, ← hx.symm]⟩
    
  · intro h x
    rcases h with ⟨⟨z, hz⟩, hz₁⟩
    calc x • a = z := Subtype.mk.injₓ (hz₁ ⟨x • a, mem_orbit _ _⟩)_ = a :=
        (Subtype.mk.injₓ (hz₁ ⟨a, mem_orbit_self _⟩)).symm
    

end MulAction

namespace MulAction

variable (α)

variable [Groupₓ α] [MulAction α β]

/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive
      "The stabilizer of an element under an action, i.e. what sends the element to itself.\nAn additive subgroup."]
def stabilizer (b : β) : Subgroup α :=
  { Stabilizer.submonoid α b with
    inv_mem' := fun a (ha : a • b = b) =>
      show a⁻¹ • b = b by
        rw [inv_smul_eq_iff, ha] }

variable {α} {β}

@[simp, to_additive]
theorem mem_stabilizer_iff {b : β} {a : α} : a ∈ stabilizer α b ↔ a • b = b :=
  Iff.rfl

@[simp, to_additive]
theorem smul_orbit (a : α) (b : β) : a • Orbit α b = Orbit α b :=
  (smul_orbit_subset a b).antisymm <|
    calc
      Orbit α b = a • a⁻¹ • Orbit α b := (smul_inv_smul _ _).symm
      _ ⊆ a • Orbit α b := Set.image_subset _ (smul_orbit_subset _ _)
      

@[simp, to_additive]
theorem orbit_smul (a : α) (b : β) : Orbit α (a • b) = Orbit α b :=
  (orbit_smul_subset a b).antisymm <|
    calc
      Orbit α b = Orbit α (a⁻¹ • a • b) := by
        rw [inv_smul_smul]
      _ ⊆ Orbit α (a • b) := orbit_smul_subset _ _
      

/-- The action of a group on an orbit is transitive. -/
@[to_additive "The action of an additive group on an orbit is transitive."]
instance (x : β) : IsPretransitive α (Orbit α x) :=
  ⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    use b * a⁻¹
    ext1
    simp [← mul_smul]⟩

@[to_additive]
theorem orbit_eq_iff {a b : β} : Orbit α a = Orbit α b ↔ a ∈ Orbit α b :=
  ⟨fun h => h ▸ mem_orbit_self _, fun ⟨c, hc⟩ => hc ▸ orbit_smul _ _⟩

variable (α) {β}

@[to_additive]
theorem mem_orbit_smul (g : α) (a : β) : a ∈ Orbit α (g • a) := by
  simp only [← orbit_smul, ← mem_orbit_self]

@[to_additive]
theorem smul_mem_orbit_smul (g h : α) (a : β) : g • a ∈ Orbit α (h • a) := by
  simp only [← orbit_smul, ← mem_orbit]

variable (α) (β)

/-- The relation 'in the same orbit'. -/
@[to_additive "The relation 'in the same orbit'."]
def orbitRel : Setoidₓ β where
  R := fun a b => a ∈ Orbit α b
  iseqv :=
    ⟨mem_orbit_self, fun a b => by
      simp [← orbit_eq_iff.symm, ← eq_comm], fun a b => by
      simp (config := { contextual := true })[← orbit_eq_iff.symm, ← eq_comm]⟩

attribute [local instance] orbit_rel

variable {α} {β}

/-- When you take a set `U` in `β`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `α`.
-/
@[to_additive]
theorem quotient_preimage_image_eq_union_mul (U : Set β) :
    Quotientₓ.mk ⁻¹' (Quotientₓ.mk '' U) = ⋃ a : α, (· • ·) a '' U := by
  set f : β → Quotientₓ (MulAction.orbitRel α β) := Quotientₓ.mk
  ext
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨a, rfl⟩ := Quotientₓ.exact hxy
    rw [Set.mem_Union]
    exact ⟨a⁻¹, a • x, hy, inv_smul_smul a x⟩
    
  · intro hx
    rw [Set.mem_Union] at hx
    obtain ⟨a, u, hu₁, hu₂⟩ := hx
    rw [Set.mem_preimage, Set.mem_image_iff_bex]
    refine'
      ⟨a⁻¹ • x, _, by
        simp only [← Quotientₓ.eq] <;> use a⁻¹⟩
    rw [← hu₂]
    convert hu₁
    simp only [← inv_smul_smul]
    

@[to_additive]
theorem disjoint_image_image_iff {U V : Set β} :
    Disjoint (Quotientₓ.mk '' U) (Quotientₓ.mk '' V) ↔ ∀, ∀ x ∈ U, ∀, ∀ a : α, a • x ∉ V := by
  set f : β → Quotientₓ (MulAction.orbitRel α β) := Quotientₓ.mk
  refine' ⟨fun h x x_in_U a a_in_V => h ⟨⟨x, x_in_U, Quotientₓ.sound ⟨a⁻¹, _⟩⟩, ⟨a • x, a_in_V, rfl⟩⟩, _⟩
  · simp
    
  · rintro h x ⟨⟨y, hy₁, hy₂⟩, ⟨z, hz₁, hz₂⟩⟩
    obtain ⟨a, rfl⟩ := Quotientₓ.exact (hz₂.trans hy₂.symm)
    exact h y hy₁ a hz₁
    

@[to_additive]
theorem image_inter_image_iff (U V : Set β) :
    Quotientₓ.mk '' U ∩ Quotientₓ.mk '' V = ∅ ↔ ∀, ∀ x ∈ U, ∀, ∀ a : α, a • x ∉ V :=
  Set.disjoint_iff_inter_eq_empty.symm.trans disjoint_image_image_iff

variable (α) (β)

-- mathport name: «exprΩ»
local notation "Ω" => Quotientₓ <| orbitRel α β

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.
This version works with any right inverse to `quotient.mk'` in order to stay computable. In most
cases you'll want to use `quotient.out'`, so we provide `mul_action.self_equiv_sigma_orbits` as
a special case. -/
@[to_additive
      "Decomposition of a type `X` as a disjoint union of its orbits under an additive group\naction. This version works with any right inverse to `quotient.mk'` in order to stay computable.\nIn most cases you'll want to use `quotient.out'`, so we provide `add_action.self_equiv_sigma_orbits`\nas a special case."]
def selfEquivSigmaOrbits' {φ : Ω → β} (hφ : RightInverse φ Quotientₓ.mk') : β ≃ Σω : Ω, Orbit α (φ ω) :=
  calc
    β ≃ Σω : Ω, { b // Quotientₓ.mk' b = ω } := (Equivₓ.sigmaFiberEquiv Quotientₓ.mk').symm
    _ ≃ Σω : Ω, Orbit α (φ ω) :=
      Equivₓ.sigmaCongrRight fun ω =>
        Equivₓ.subtypeEquivRight fun x => by
          rw [← hφ ω, Quotientₓ.eq', hφ ω]
          rfl
    

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[to_additive "Decomposition of a type `X` as a disjoint union of its orbits under an additive group\naction."]
noncomputable def selfEquivSigmaOrbits : β ≃ Σω : Ω, Orbit α ω.out' :=
  selfEquivSigmaOrbits' α β Quotientₓ.out_eq'

variable {α β}

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g • x` is `gSg⁻¹`. -/
theorem stabilizer_smul_eq_stabilizer_map_conj (g : α) (x : β) :
    stabilizer α (g • x) = (stabilizer α x).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← smul_left_cancel_iff g⁻¹, smul_smul, smul_smul, smul_smul, mul_left_invₓ, one_smul, ←
    mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {x y : β} (h : (orbitRel α β).Rel x y) :
    stabilizer α x ≃* stabilizer α y :=
  let g : α := Classical.some h
  have hg : g • y = x := Classical.some_spec h
  have this : stabilizer α x = (stabilizer α y).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, stabilizer_smul_eq_stabilizer_map_conj]
  (MulEquiv.subgroupCongr this).trans ((MulAut.conj g).subgroupMap <| stabilizer α y).symm

end MulAction

namespace AddAction

variable [AddGroupₓ α] [AddAction α β]

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g +ᵥ x` is `g + S + (-g)`. -/
theorem stabilizer_vadd_eq_stabilizer_map_conj (g : α) (x : β) :
    stabilizer α (g +ᵥ x) = (stabilizer α x).map (AddAut.conj g).toAddMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← vadd_left_cancel_iff (-g), vadd_vadd, vadd_vadd, vadd_vadd, add_left_negₓ, zero_vadd, ←
    mem_stabilizer_iff, AddSubgroup.mem_map_equiv, AddAut.conj_symm_apply]

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {x y : β} (h : (orbitRel α β).Rel x y) :
    stabilizer α x ≃+ stabilizer α y :=
  let g : α := Classical.some h
  have hg : g +ᵥ y = x := Classical.some_spec h
  have this : stabilizer α x = (stabilizer α y).map (AddAut.conj g).toAddMonoidHom := by
    rw [← hg, stabilizer_vadd_eq_stabilizer_map_conj]
  (AddEquiv.addSubgroupCongr this).trans ((AddAut.conj g).addSubgroupMap <| stabilizer α y).symm

end AddAction

/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `is_smul_regular`.
The typeclass that restricts all terms of `M` to have this property is `no_zero_smul_divisors`. -/
theorem smul_cancel_of_non_zero_divisor {M R : Type _} [Monoidₓ M] [NonUnitalNonAssocRing R] [DistribMulAction M R]
    (k : M) (h : ∀ x : R, k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) : a = b := by
  rw [← sub_eq_zero]
  refine' h _ _
  rw [smul_sub, h', sub_self]

