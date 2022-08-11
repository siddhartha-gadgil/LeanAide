/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import Mathbin.Topology.Algebra.Group
import Mathbin.Logic.Function.Iterate

/-!
# Flows and invariant sets

This file defines a flow on a topological space `α` by a topological
monoid `τ` as a continuous monoid-act of `τ` on `α`. Anticipating the
cases where `τ` is one of `ℕ`, `ℤ`, `ℝ⁺`, or `ℝ`, we use additive
notation for the monoids, though the definition does not require
commutativity.

A subset `s` of `α` is invariant under a family of maps `ϕₜ : α → α`
if `ϕₜ s ⊆ s` for all `t`. In many cases `ϕ` will be a flow on
`α`. For the cases where `ϕ` is a flow by an ordered (additive,
commutative) monoid, we additionally define forward invariance, where
`t` ranges over those elements which are nonnegative.

Additionally, we define such constructions as the restriction of a
flow onto an invariant subset, and the time-reveral of a flow by a
group.
-/


open Set Function Filter

/-!
### Invariant sets
-/


section Invariant

variable {τ : Type _} {α : Type _}

/-- A set `s ⊆ α` is invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t` in `τ`. -/
def IsInvariant (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ t, MapsTo (ϕ t) s s

variable (ϕ : τ → α → α) (s : Set α)

theorem is_invariant_iff_image : IsInvariant ϕ s ↔ ∀ t, ϕ t '' s ⊆ s := by
  simp_rw [IsInvariant, maps_to']

/-- A set `s ⊆ α` is forward-invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t ≥ 0`. -/
def IsFwInvariant [Preorderₓ τ] [Zero τ] (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ ⦃t⦄, 0 ≤ t → MapsTo (ϕ t) s s

theorem IsInvariant.is_fw_invariant [Preorderₓ τ] [Zero τ] {ϕ : τ → α → α} {s : Set α} (h : IsInvariant ϕ s) :
    IsFwInvariant ϕ s := fun t ht => h t

/-- If `τ` is a `canonically_ordered_add_monoid` (e.g., `ℕ` or `ℝ≥0`), then the notions
`is_fw_invariant` and `is_invariant` are equivalent. -/
theorem IsFwInvariant.is_invariant [CanonicallyOrderedAddMonoid τ] {ϕ : τ → α → α} {s : Set α} (h : IsFwInvariant ϕ s) :
    IsInvariant ϕ s := fun t => h (zero_le t)

/-- If `τ` is a `canonically_ordered_add_monoid` (e.g., `ℕ` or `ℝ≥0`), then the notions
`is_fw_invariant` and `is_invariant` are equivalent. -/
theorem is_fw_invariant_iff_is_invariant [CanonicallyOrderedAddMonoid τ] {ϕ : τ → α → α} {s : Set α} :
    IsFwInvariant ϕ s ↔ IsInvariant ϕ s :=
  ⟨IsFwInvariant.is_invariant, IsInvariant.is_fw_invariant⟩

end Invariant

/-!
### Flows
-/


/-- A flow on a topological space `α` by an a additive topological
    monoid `τ` is a continuous monoid action of `τ` on `α`.-/
structure Flow (τ : Type _) [TopologicalSpace τ] [AddMonoidₓ τ] [HasContinuousAdd τ] (α : Type _)
  [TopologicalSpace α] where
  toFun : τ → α → α
  cont' : Continuous (uncurry to_fun)
  map_add' : ∀ t₁ t₂ x, to_fun (t₁ + t₂) x = to_fun t₁ (to_fun t₂ x)
  map_zero' : ∀ x, to_fun 0 x = x

namespace Flow

variable {τ : Type _} [AddMonoidₓ τ] [TopologicalSpace τ] [HasContinuousAdd τ] {α : Type _} [TopologicalSpace α]
  (ϕ : Flow τ α)

instance : Inhabited (Flow τ α) :=
  ⟨{ toFun := fun _ x => x, cont' := continuous_snd, map_add' := fun _ _ _ => rfl, map_zero' := fun _ => rfl }⟩

instance : CoeFun (Flow τ α) fun _ => τ → α → α :=
  ⟨Flow.toFun⟩

@[ext]
theorem ext : ∀ {ϕ₁ ϕ₂ : Flow τ α}, (∀ t x, ϕ₁ t x = ϕ₂ t x) → ϕ₁ = ϕ₂
  | ⟨f₁, _, _, _⟩, ⟨f₂, _, _, _⟩, h => by
    congr
    funext
    exact h _ _

@[continuity]
protected theorem continuous {β : Type _} [TopologicalSpace β] {t : β → τ} (ht : Continuous t) {f : β → α}
    (hf : Continuous f) : Continuous fun x => ϕ (t x) (f x) :=
  ϕ.cont'.comp (ht.prod_mk hf)

alias Flow.continuous ← _root_.continuous.flow

theorem map_add (t₁ t₂ : τ) (x : α) : ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x) :=
  ϕ.map_add' _ _ _

@[simp]
theorem map_zero : ϕ 0 = id :=
  funext ϕ.map_zero'

theorem map_zero_apply (x : α) : ϕ 0 x = x :=
  ϕ.map_zero' x

/-- Iterations of a continuous function from a topological space `α`
    to itself defines a semiflow by `ℕ` on `α`. -/
def fromIter {g : α → α} (h : Continuous g) : Flow ℕ α where
  toFun := fun n x => (g^[n]) x
  cont' := continuous_uncurry_of_discrete_topology_left (Continuous.iterate h)
  map_add' := iterate_add_apply _
  map_zero' := fun x => rfl

/-- Restriction of a flow onto an invariant set. -/
def restrict {s : Set α} (h : IsInvariant ϕ s) : Flow τ ↥s where
  toFun := fun t => (h t).restrict _ _ _
  cont' := continuous_subtype_mk _ (ϕ.Continuous continuous_fst (continuous_subtype_coe.comp continuous_snd))
  map_add' := fun _ _ _ => Subtype.ext (map_add _ _ _ _)
  map_zero' := fun _ => Subtype.ext (map_zero_apply _ _)

end Flow

namespace Flow

variable {τ : Type _} [AddCommGroupₓ τ] [TopologicalSpace τ] [TopologicalAddGroup τ] {α : Type _} [TopologicalSpace α]
  (ϕ : Flow τ α)

theorem is_invariant_iff_image_eq (s : Set α) : IsInvariant ϕ s ↔ ∀ t, ϕ t '' s = s :=
  (is_invariant_iff_image _ _).trans
    (Iff.intro
      (fun h t =>
        Subset.antisymm (h t) fun _ hx =>
          ⟨_, h (-t) ⟨_, hx, rfl⟩, by
            simp [map_add]⟩)
      fun h t => by
      rw [h t])

/-- The time-reversal of a flow `ϕ` by a (commutative, additive) group
    is defined `ϕ.reverse t x = ϕ (-t) x`. -/
def reverse : Flow τ α where
  toFun := fun t => ϕ (-t)
  cont' := ϕ.Continuous continuous_fst.neg continuous_snd
  map_add' := fun _ _ _ => by
    rw [neg_add, map_add]
  map_zero' := fun _ => by
    rw [neg_zero, map_zero_apply]

/-- The map `ϕ t` as a homeomorphism. -/
def toHomeomorph (t : τ) : α ≃ₜ α where
  toFun := ϕ t
  invFun := ϕ (-t)
  left_inv := fun x => by
    rw [← map_add, neg_add_selfₓ, map_zero_apply]
  right_inv := fun x => by
    rw [← map_add, add_neg_selfₓ, map_zero_apply]

theorem image_eq_preimage (t : τ) (s : Set α) : ϕ t '' s = ϕ (-t) ⁻¹' s :=
  (ϕ.toHomeomorph t).toEquiv.image_eq_preimage s

end Flow

