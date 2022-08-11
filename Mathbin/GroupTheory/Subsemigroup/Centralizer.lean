/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
import Mathbin.GroupTheory.Subsemigroup.Center

/-!
# Centralizers of magmas and semigroups

## Main definitions

* `set.centralizer`: the centralizer of a subset of a magma
* `subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `set.add_centralizer`: the centralizer of a subset of an additive magma
* `add_subsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `monoid.centralizer`, `add_monoid.centralizer`, `subgroup.centralizer`, and
`add_subgroup.centralizer` in other files.
-/


variable {M : Type _} {S T : Set M}

namespace Set

variable (S)

/-- The centralizer of a subset of a magma. -/
@[to_additive add_centralizer " The centralizer of a subset of an additive magma. "]
def Centralizer [Mul M] : Set M :=
  { c | ∀, ∀ m ∈ S, ∀, m * c = c * m }

variable {S}

@[to_additive mem_add_centralizer]
theorem mem_centralizer_iff [Mul M] {c : M} : c ∈ Centralizer S ↔ ∀, ∀ m ∈ S, ∀, m * c = c * m :=
  Iff.rfl

@[to_additive decidable_mem_add_centralizer]
instance decidableMemCentralizer [Mul M] [DecidableEq M] [Fintype M] [DecidablePred (· ∈ S)] :
    DecidablePred (· ∈ Centralizer S) := fun _ => decidableOfIff' _ mem_centralizer_iff

variable (S)

@[simp, to_additive zero_mem_add_centralizer]
theorem one_mem_centralizer [MulOneClassₓ M] : (1 : M) ∈ Centralizer S := by
  simp [← mem_centralizer_iff]

@[simp]
theorem zero_mem_centralizer [MulZeroClassₓ M] : (0 : M) ∈ Centralizer S := by
  simp [← mem_centralizer_iff]

variable {S} {a b : M}

@[simp, to_additive add_mem_add_centralizer]
theorem mul_mem_centralizer [Semigroupₓ M] (ha : a ∈ Centralizer S) (hb : b ∈ Centralizer S) : a * b ∈ Centralizer S :=
  fun g hg => by
  rw [mul_assoc, ← hb g hg, ← mul_assoc, ha g hg, mul_assoc]

@[simp, to_additive neg_mem_add_centralizer]
theorem inv_mem_centralizer [Groupₓ M] (ha : a ∈ Centralizer S) : a⁻¹ ∈ Centralizer S := fun g hg => by
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]

@[simp]
theorem add_mem_centralizer [Distribₓ M] (ha : a ∈ Centralizer S) (hb : b ∈ Centralizer S) : a + b ∈ Centralizer S :=
  fun c hc => by
  rw [add_mulₓ, mul_addₓ, ha c hc, hb c hc]

@[simp]
theorem neg_mem_centralizer [Mul M] [HasDistribNeg M] (ha : a ∈ Centralizer S) : -a ∈ Centralizer S := fun c hc => by
  rw [mul_neg, ha c hc, neg_mul]

@[simp]
theorem inv_mem_centralizer₀ [GroupWithZeroₓ M] (ha : a ∈ Centralizer S) : a⁻¹ ∈ Centralizer S :=
  (eq_or_ne a 0).elim
    (fun h => by
      rw [h, inv_zero]
      exact zero_mem_centralizer S)
    fun ha0 c hc => by
    rw [mul_inv_eq_iff_eq_mul₀ ha0, mul_assoc, eq_inv_mul_iff_mul_eq₀ ha0, ha c hc]

@[simp, to_additive sub_mem_add_centralizer]
theorem div_mem_centralizer [Groupₓ M] (ha : a ∈ Centralizer S) (hb : b ∈ Centralizer S) : a / b ∈ Centralizer S := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer hb)

@[simp]
theorem div_mem_centralizer₀ [GroupWithZeroₓ M] (ha : a ∈ Centralizer S) (hb : b ∈ Centralizer S) :
    a / b ∈ Centralizer S := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer₀ hb)

@[to_additive add_centralizer_subset]
theorem centralizer_subset [Mul M] (h : S ⊆ T) : Centralizer T ⊆ Centralizer S := fun t ht s hs => ht s (h hs)

variable (M)

@[simp, to_additive add_centralizer_univ]
theorem centralizer_univ [Mul M] : Centralizer Univ = Center M :=
  Subset.antisymm (fun a ha b => ha b (Set.mem_univ b)) fun a ha b hb => ha b

variable {M} (S)

@[simp, to_additive add_centralizer_eq_univ]
theorem centralizer_eq_univ [CommSemigroupₓ M] : Centralizer S = univ :=
  (Subset.antisymm (subset_univ _)) fun x hx y hy => mul_comm y x

end Set

namespace Subsemigroup

section

variable {M} [Semigroupₓ M] (S)

/-- The centralizer of a subset of a semigroup `M`. -/
@[to_additive "The centralizer of a subset of an additive semigroup."]
def centralizer : Subsemigroup M where
  Carrier := S.Centralizer
  mul_mem' := fun a b => Set.mul_mem_centralizer

@[simp, norm_cast, to_additive]
theorem coe_centralizer : ↑(centralizer S) = S.Centralizer :=
  rfl

variable {S}

@[to_additive]
theorem mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀, ∀ g ∈ S, ∀, g * z = z * g :=
  Iff.rfl

@[to_additive]
instance decidableMemCentralizer [DecidableEq M] [Fintype M] [DecidablePred (· ∈ S)] :
    DecidablePred (· ∈ centralizer S) := fun _ => decidableOfIff' _ mem_centralizer_iff

@[to_additive]
theorem centralizer_le (h : S ⊆ T) : centralizer T ≤ centralizer S :=
  Set.centralizer_subset h

variable (M)

@[simp, to_additive]
theorem centralizer_univ : centralizer Set.Univ = center M :=
  SetLike.ext' (Set.centralizer_univ M)

end

end Subsemigroup

