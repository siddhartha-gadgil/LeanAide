/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathbin.GroupTheory.Subsemigroup.Operations
import Mathbin.Data.Fintype.Basic

/-!
# Centers of magmas and semigroups

## Main definitions

* `set.center`: the center of a magma
* `subsemigroup.center`: the center of a semigroup
* `set.add_center`: the center of an additive magma
* `add_subsemigroup.center`: the center of an additive semigroup

We provide `submonoid.center`, `add_submonoid.center`, `subgroup.center`, `add_subgroup.center`,
`subsemiring.center`, and `subring.center` in other files.
-/


variable {M : Type _}

namespace Set

variable (M)

/-- The center of a magma. -/
@[to_additive add_center " The center of an additive magma. "]
def Center [Mul M] : Set M :=
  { z | ∀ m, m * z = z * m }

@[to_additive mem_add_center]
theorem mem_center_iff [Mul M] {z : M} : z ∈ Center M ↔ ∀ g, g * z = z * g :=
  Iff.rfl

instance decidableMemCenter [Mul M] [DecidableEq M] [Fintype M] : DecidablePred (· ∈ Center M) := fun _ =>
  decidableOfIff' _ (mem_center_iff M)

@[simp, to_additive zero_mem_add_center]
theorem one_mem_center [MulOneClassₓ M] : (1 : M) ∈ Set.Center M := by
  simp [← mem_center_iff]

@[simp]
theorem zero_mem_center [MulZeroClassₓ M] : (0 : M) ∈ Set.Center M := by
  simp [← mem_center_iff]

variable {M}

@[simp, to_additive add_mem_add_center]
theorem mul_mem_center [Semigroupₓ M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) :
    a * b ∈ Set.Center M := fun g => by
  rw [mul_assoc, ← hb g, ← mul_assoc, ha g, mul_assoc]

@[simp, to_additive neg_mem_add_center]
theorem inv_mem_center [Groupₓ M] {a : M} (ha : a ∈ Set.Center M) : a⁻¹ ∈ Set.Center M := fun g => by
  rw [← inv_inj, mul_inv_rev, inv_invₓ, ← ha, mul_inv_rev, inv_invₓ]

@[simp]
theorem add_mem_center [Distribₓ M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) : a + b ∈ Set.Center M :=
  fun c => by
  rw [add_mulₓ, mul_addₓ, ha c, hb c]

@[simp]
theorem neg_mem_center [Ringₓ M] {a : M} (ha : a ∈ Set.Center M) : -a ∈ Set.Center M := fun c => by
  rw [← neg_mul_comm, ha (-c), neg_mul_comm]

@[to_additive subset_add_center_add_units]
theorem subset_center_units [Monoidₓ M] : (coe : Mˣ → M) ⁻¹' Center M ⊆ Set.Center Mˣ := fun a ha b => Units.ext <| ha _

theorem center_units_subset [GroupWithZeroₓ M] : Set.Center Mˣ ⊆ (coe : Mˣ → M) ⁻¹' Center M := fun a ha b => by
  obtain rfl | hb := eq_or_ne b 0
  · rw [zero_mul, mul_zero]
    
  · exact units.ext_iff.mp (ha (Units.mk0 _ hb))
    

/-- In a group with zero, the center of the units is the preimage of the center. -/
theorem center_units_eq [GroupWithZeroₓ M] : Set.Center Mˣ = (coe : Mˣ → M) ⁻¹' Center M :=
  Subset.antisymm center_units_subset subset_center_units

@[simp]
theorem inv_mem_center₀ [GroupWithZeroₓ M] {a : M} (ha : a ∈ Set.Center M) : a⁻¹ ∈ Set.Center M := by
  obtain rfl | ha0 := eq_or_ne a 0
  · rw [inv_zero]
    exact zero_mem_center M
    
  rcases IsUnit.mk0 _ ha0 with ⟨a, rfl⟩
  rw [← Units.coe_inv]
  exact center_units_subset (inv_mem_center (subset_center_units ha))

@[simp, to_additive sub_mem_add_center]
theorem div_mem_center [Groupₓ M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) : a / b ∈ Set.Center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)

@[simp]
theorem div_mem_center₀ [GroupWithZeroₓ M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) :
    a / b ∈ Set.Center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center₀ hb)

variable (M)

@[simp, to_additive add_center_eq_univ]
theorem center_eq_univ [CommSemigroupₓ M] : Center M = Set.Univ :=
  (Subset.antisymm (subset_univ _)) fun x _ y => mul_comm y x

end Set

namespace Subsemigroup

section

variable (M) [Semigroupₓ M]

/-- The center of a semigroup `M` is the set of elements that commute with everything in `M` -/
@[to_additive "The center of a semigroup `M` is the set of elements that commute with everything in\n`M`"]
def center : Subsemigroup M where
  Carrier := Set.Center M
  mul_mem' := fun a b => Set.mul_mem_center

@[to_additive]
theorem coe_center : ↑(center M) = Set.Center M :=
  rfl

variable {M}

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g :=
  Iff.rfl

@[to_additive]
instance decidableMemCenter [DecidableEq M] [Fintype M] : DecidablePred (· ∈ center M) := fun _ =>
  decidableOfIff' _ mem_center_iff

/-- The center of a semigroup is commutative. -/
@[to_additive "The center of an additive semigroup is commutative."]
instance : CommSemigroupₓ (center M) :=
  { MulMemClass.toSemigroup (center M) with mul_comm := fun a b => Subtype.ext <| b.Prop _ }

end

section

variable (M) [CommSemigroupₓ M]

@[to_additive, simp]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)

end

end Subsemigroup

