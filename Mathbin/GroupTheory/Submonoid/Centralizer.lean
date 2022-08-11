/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.GroupTheory.Subsemigroup.Centralizer
import Mathbin.GroupTheory.Submonoid.Center

/-!
# Centralizers of magmas and monoids

## Main definitions

* `submonoid.centralizer`: the centralizer of a subset of a monoid
* `add_submonoid.centralizer`: the centralizer of a subset of an additive monoid

We provide `subgroup.centralizer`, `add_subgroup.centralizer` in other files.
-/


variable {M : Type _} {S T : Set M}

namespace Submonoid

section

variable [Monoidₓ M] (S)

/-- The centralizer of a subset of a monoid `M`. -/
@[to_additive "The centralizer of a subset of an additive monoid."]
def centralizer : Submonoid M where
  Carrier := S.Centralizer
  one_mem' := S.one_mem_centralizer
  mul_mem' := fun a b => Set.mul_mem_centralizer

@[simp, norm_cast, to_additive]
theorem coe_centralizer : ↑(centralizer S) = S.Centralizer :=
  rfl

theorem centralizer_to_subsemigroup : (centralizer S).toSubsemigroup = Subsemigroup.centralizer S :=
  rfl

theorem _root_.add_submonoid.centralizer_to_add_subsemigroup {M} [AddMonoidₓ M] (S : Set M) :
    (AddSubmonoid.centralizer S).toAddSubsemigroup = AddSubsemigroup.centralizer S :=
  rfl

attribute [to_additive AddSubmonoid.centralizer_to_add_subsemigroup] Submonoid.centralizer_to_subsemigroup

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

end Submonoid

