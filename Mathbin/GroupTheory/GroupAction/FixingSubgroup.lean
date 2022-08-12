/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.GroupTheory.GroupAction.Basic

/-!

# Fixing submonoid, fixing subgroup of an action

In the presence of of an action of a monoid or a group,
this file defines the fixing submonoid or the fixing subgroup,
and relates it to the set of fixed points via a Galois connection.

## Main definitions

* `fixing_submonoid M s` : in the presence of `mul_action M α` (with `monoid M`)
  it is the `submonoid M` consisting of elements which fix `s : set α` pointwise.

* `fixing_submonoid_fixed_points_gc M α` is the `galois_connection`
  that relates `fixing_submonoid` with `fixed_points`.

* `fixing_subgroup M s` : in the presence of `mul_action M α` (with `group M`)
  it is the `subgroup M` consisting of elements which fix `s : set α` pointwise.

* `fixing_subgroup_fixed_points_gc M α` is the `galois_connection`
  that relates `fixing_subgroup` with `fixed_points`.

TODO :

* Maybe other lemmas are useful

* Treat semigroups ?

-/


section Monoidₓ

open MulAction

variable (M : Type _) {α : Type _} [Monoidₓ M] [MulAction M α]

/-- The submonoid fixing a set under a `mul_action`. -/
@[to_additive " The additive submonoid fixing a set under an `add_action`. "]
def fixingSubmonoid (s : Set α) : Submonoid M where
  Carrier := { ϕ : M | ∀ x : s, ϕ • (x : α) = x }
  one_mem' := fun _ => one_smul _ _
  mul_mem' := fun x y hx hy z => by
    rw [mul_smul, hy z, hx z]

theorem mem_fixing_submonoid_iff {s : Set α} {m : M} : m ∈ fixingSubmonoid M s ↔ ∀, ∀ y ∈ s, ∀, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

variable (α)

/-- The Galois connection between fixing submonoids and fixed points of a monoid action -/
theorem fixing_submonoid_fixed_points_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubmonoid M)
      ((fun P : Submonoid M => FixedPoints P α) ∘ OrderDual.ofDual) :=
  fun s P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

theorem fixing_submonoid_antitone : Antitone fun s : Set α => fixingSubmonoid M s :=
  (fixing_submonoid_fixed_points_gc M α).monotone_l

theorem fixed_points_antitone : Antitone fun P : Submonoid M => FixedPoints P α :=
  (fixing_submonoid_fixed_points_gc M α).monotone_u.dual_left

/-- Fixing submonoid of union is intersection -/
theorem fixing_submonoid_union {s t : Set α} : fixingSubmonoid M (s ∪ t) = fixingSubmonoid M s⊓fixingSubmonoid M t :=
  (fixing_submonoid_fixed_points_gc M α).l_sup

/-- Fixing submonoid of Union is intersection -/
theorem fixing_submonoid_Union {ι : Sort _} {s : ι → Set α} :
    fixingSubmonoid M (⋃ i, s i) = ⨅ i, fixingSubmonoid M (s i) :=
  (fixing_submonoid_fixed_points_gc M α).l_supr

/-- Fixed points of sup of submonoids is intersection -/
theorem fixed_points_submonoid_sup {P Q : Submonoid M} : FixedPoints (↥(P⊔Q)) α = FixedPoints P α ∩ FixedPoints Q α :=
  (fixing_submonoid_fixed_points_gc M α).u_inf

/-- Fixed points of supr of submonoids is intersection -/
theorem fixed_points_submonoid_supr {ι : Sort _} {P : ι → Submonoid M} :
    FixedPoints (↥(supr P)) α = ⋂ i, FixedPoints (P i) α :=
  (fixing_submonoid_fixed_points_gc M α).u_infi

end Monoidₓ

section Groupₓ

open MulAction

variable (M : Type _) {α : Type _} [Groupₓ M] [MulAction M α]

/-- The subgroup fixing a set under a `mul_action`. -/
@[to_additive " The additive subgroup fixing a set under an `add_action`. "]
def fixingSubgroup (s : Set α) : Subgroup M :=
  { fixingSubmonoid M s with
    inv_mem' := fun _ hx z => by
      rw [inv_smul_eq_iff, hx z] }

theorem mem_fixing_subgroup_iff {s : Set α} {m : M} : m ∈ fixingSubgroup M s ↔ ∀, ∀ y ∈ s, ∀, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

variable (α)

/-- The Galois connection between fixing subgroups and fixed points of a group action -/
theorem fixing_subgroup_fixed_points_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubgroup M)
      ((fun P : Subgroup M => FixedPoints P α) ∘ OrderDual.ofDual) :=
  fun s P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

theorem fixing_subgroup_antitone : Antitone (fixingSubgroup M : Set α → Subgroup M) :=
  (fixing_subgroup_fixed_points_gc M α).monotone_l

theorem fixed_points_subgroup_antitone : Antitone fun P : Subgroup M => FixedPoints P α :=
  (fixing_subgroup_fixed_points_gc M α).monotone_u.dual_left

/-- Fixing subgroup of union is intersection -/
theorem fixing_subgroup_union {s t : Set α} : fixingSubgroup M (s ∪ t) = fixingSubgroup M s⊓fixingSubgroup M t :=
  (fixing_subgroup_fixed_points_gc M α).l_sup

/-- Fixing subgroup of Union is intersection -/
theorem fixing_subgroup_Union {ι : Sort _} {s : ι → Set α} :
    fixingSubgroup M (⋃ i, s i) = ⨅ i, fixingSubgroup M (s i) :=
  (fixing_subgroup_fixed_points_gc M α).l_supr

/-- Fixed points of sup of subgroups is intersection -/
theorem fixed_points_subgroup_sup {P Q : Subgroup M} : FixedPoints (↥(P⊔Q)) α = FixedPoints P α ∩ FixedPoints Q α :=
  (fixing_subgroup_fixed_points_gc M α).u_inf

/-- Fixed points of supr of subgroups is intersection -/
theorem fixed_points_subgroup_supr {ι : Sort _} {P : ι → Subgroup M} :
    FixedPoints (↥(supr P)) α = ⋂ i, FixedPoints (P i) α :=
  (fixing_subgroup_fixed_points_gc M α).u_infi

end Groupₓ

