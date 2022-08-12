/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Data.Set.Intervals.UnorderedInterval
import Mathbin.Data.Set.Lattice

/-!
# Order-connected sets

We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α` is a
`linear_ordered_field`, then this condition is also equivalent to `convex α s`.

In this file we prove that intersection of a family of `ord_connected` sets is `ord_connected` and
that all standard intervals are `ord_connected`.
-/


namespace Set

section Preorderₓ

variable {α β : Type _} [Preorderₓ α] [Preorderₓ β] {s t : Set α}

/-- We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α` is a
`linear_ordered_field`, then this condition is also equivalent to `convex α s`.
-/
class OrdConnected (s : Set α) : Prop where
  out' ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) : Icc x y ⊆ s

theorem OrdConnected.out (h : OrdConnected s) : ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), Icc x y ⊆ s :=
  h.1

theorem ord_connected_def : OrdConnected s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), Icc x y ⊆ s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- It suffices to prove `[x, y] ⊆ s` for `x y ∈ s`, `x ≤ y`. -/
theorem ord_connected_iff : OrdConnected s ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, x ≤ y → Icc x y ⊆ s :=
  ord_connected_def.trans
    ⟨fun hs x hx y hy hxy => hs hx hy, fun H x hx y hy z hz => H x hx y hy (le_transₓ hz.1 hz.2) hz⟩

theorem ord_connected_of_Ioo {α : Type _} [PartialOrderₓ α] {s : Set α}
    (hs : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, x < y → Ioo x y ⊆ s) : OrdConnected s := by
  rw [ord_connected_iff]
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with (rfl | hxy')
  · simpa
    
  rw [← Ioc_insert_left hxy, ← Ioo_insert_right hxy']
  exact insert_subset.2 ⟨hx, insert_subset.2 ⟨hy, hs x hx y hy hxy'⟩⟩

theorem OrdConnected.preimage_mono {f : β → α} (hs : OrdConnected s) (hf : Monotone f) : OrdConnected (f ⁻¹' s) :=
  ⟨fun x hx y hy z hz => hs.out hx hy ⟨hf hz.1, hf hz.2⟩⟩

theorem OrdConnected.preimage_anti {f : β → α} (hs : OrdConnected s) (hf : Antitone f) : OrdConnected (f ⁻¹' s) :=
  ⟨fun x hx y hy z hz => hs.out hy hx ⟨hf hz.2, hf hz.1⟩⟩

protected theorem Icc_subset (s : Set α) [hs : OrdConnected s] {x y} (hx : x ∈ s) (hy : y ∈ s) : Icc x y ⊆ s :=
  hs.out hx hy

theorem OrdConnected.inter {s t : Set α} (hs : OrdConnected s) (ht : OrdConnected t) : OrdConnected (s ∩ t) :=
  ⟨fun x hx y hy => subset_inter (hs.out hx.1 hy.1) (ht.out hx.2 hy.2)⟩

instance OrdConnected.inter' {s t : Set α} [OrdConnected s] [OrdConnected t] : OrdConnected (s ∩ t) :=
  OrdConnected.inter ‹_› ‹_›

theorem OrdConnected.dual {s : Set α} (hs : OrdConnected s) : OrdConnected (OrderDual.ofDual ⁻¹' s) :=
  ⟨fun x hx y hy z hz => hs.out hy hx ⟨hz.2, hz.1⟩⟩

theorem ord_connected_dual {s : Set α} : OrdConnected (OrderDual.ofDual ⁻¹' s) ↔ OrdConnected s :=
  ⟨fun h => by
    simpa only [← ord_connected_def] using h.dual, fun h => h.dual⟩

theorem ord_connected_sInter {S : Set (Set α)} (hS : ∀, ∀ s ∈ S, ∀, OrdConnected s) : OrdConnected (⋂₀ S) :=
  ⟨fun x hx y hy => subset_sInter fun s hs => (hS s hs).out (hx s hs) (hy s hs)⟩

theorem ord_connected_Inter {ι : Sort _} {s : ι → Set α} (hs : ∀ i, OrdConnected (s i)) : OrdConnected (⋂ i, s i) :=
  ord_connected_sInter <| forall_range_iff.2 hs

instance ord_connected_Inter' {ι : Sort _} {s : ι → Set α} [∀ i, OrdConnected (s i)] : OrdConnected (⋂ i, s i) :=
  ord_connected_Inter ‹_›

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem ord_connected_bInter {ι : Sort _} {p : ι → Prop} {s : ∀ (i : ι) (hi : p i), Set α}
    (hs : ∀ i hi, OrdConnected (s i hi)) : OrdConnected (⋂ (i) (hi), s i hi) :=
  ord_connected_Inter fun i => ord_connected_Inter <| hs i

theorem ord_connected_pi {ι : Type _} {α : ι → Type _} [∀ i, Preorderₓ (α i)] {s : Set ι} {t : ∀ i, Set (α i)}
    (h : ∀, ∀ i ∈ s, ∀, OrdConnected (t i)) : OrdConnected (s.pi t) :=
  ⟨fun x hx y hy z hz i hi => (h i hi).out (hx i hi) (hy i hi) ⟨hz.1 i, hz.2 i⟩⟩

instance ord_connected_pi' {ι : Type _} {α : ι → Type _} [∀ i, Preorderₓ (α i)] {s : Set ι} {t : ∀ i, Set (α i)}
    [h : ∀ i, OrdConnected (t i)] : OrdConnected (s.pi t) :=
  ord_connected_pi fun i hi => h i

@[instance]
theorem ord_connected_Ici {a : α} : OrdConnected (Ici a) :=
  ⟨fun x hx y hy z hz => le_transₓ hx hz.1⟩

@[instance]
theorem ord_connected_Iic {a : α} : OrdConnected (Iic a) :=
  ⟨fun x hx y hy z hz => le_transₓ hz.2 hy⟩

@[instance]
theorem ord_connected_Ioi {a : α} : OrdConnected (Ioi a) :=
  ⟨fun x hx y hy z hz => lt_of_lt_of_leₓ hx hz.1⟩

@[instance]
theorem ord_connected_Iio {a : α} : OrdConnected (Iio a) :=
  ⟨fun x hx y hy z hz => lt_of_le_of_ltₓ hz.2 hy⟩

@[instance]
theorem ord_connected_Icc {a b : α} : OrdConnected (Icc a b) :=
  ord_connected_Ici.inter ord_connected_Iic

@[instance]
theorem ord_connected_Ico {a b : α} : OrdConnected (Ico a b) :=
  ord_connected_Ici.inter ord_connected_Iio

@[instance]
theorem ord_connected_Ioc {a b : α} : OrdConnected (Ioc a b) :=
  ord_connected_Ioi.inter ord_connected_Iic

@[instance]
theorem ord_connected_Ioo {a b : α} : OrdConnected (Ioo a b) :=
  ord_connected_Ioi.inter ord_connected_Iio

@[instance]
theorem ord_connected_singleton {α : Type _} [PartialOrderₓ α] {a : α} : OrdConnected ({a} : Set α) := by
  rw [← Icc_self]
  exact ord_connected_Icc

@[instance]
theorem ord_connected_empty : OrdConnected (∅ : Set α) :=
  ⟨fun x => False.elim⟩

@[instance]
theorem ord_connected_univ : OrdConnected (Univ : Set α) :=
  ⟨fun _ _ _ _ => subset_univ _⟩

/-- In a dense order `α`, the subtype from an `ord_connected` set is also densely ordered. -/
instance [DenselyOrdered α] {s : Set α} [hs : OrdConnected s] : DenselyOrdered s :=
  ⟨fun a b (h : (a : α) < b) =>
    let ⟨x, H⟩ := exists_between h
    ⟨⟨x, (hs.out a.2 b.2) (Ioo_subset_Icc_self H)⟩, H⟩⟩

@[instance]
theorem ord_connected_image {E : Type _} [OrderIsoClass E α β] (e : E) {s : Set α} [hs : OrdConnected s] :
    OrdConnected (e '' s) := by
  constructor
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z ⟨hxz, hzy⟩
  exact
    ⟨EquivLike.inv e z, hs.out hx hy ⟨(le_map_inv_iff e).mpr hxz, (map_inv_le_iff e).mpr hzy⟩, EquivLike.right_inv e z⟩

@[instance]
theorem ord_connected_range {E : Type _} [OrderIsoClass E α β] (e : E) : OrdConnected (Range e) := by
  simp_rw [← image_univ, ord_connected_image e]

end Preorderₓ

section LinearOrderₓ

variable {α : Type _} [LinearOrderₓ α] {s : Set α} {x : α}

@[instance]
theorem ord_connected_interval {a b : α} : OrdConnected (Interval a b) :=
  ord_connected_Icc

theorem OrdConnected.interval_subset (hs : OrdConnected s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) : Interval x y ⊆ s := by
  cases le_totalₓ x y <;> simp only [← interval_of_le, ← interval_of_ge, *] <;> apply hs.out <;> assumption

theorem ord_connected_iff_interval_subset : OrdConnected s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), Interval x y ⊆ s :=
  ⟨fun h => h.interval_subset, fun h =>
    ord_connected_iff.2 fun x hx y hy hxy => by
      simpa only [← interval_of_le hxy] using h hx hy⟩

theorem ord_connected_iff_interval_subset_left (hx : x ∈ s) : OrdConnected s ↔ ∀ ⦃y⦄, y ∈ s → Interval x y ⊆ s := by
  refine' ⟨fun hs => hs.interval_subset hx, fun hs => ord_connected_iff_interval_subset.2 fun y hy z hz => _⟩
  suffices h : interval y x ∪ interval x z ⊆ s
  · exact interval_subset_interval_union_interval.trans h
    
  rw [interval_swap, union_subset_iff]
  exact ⟨hs hy, hs hz⟩

theorem ord_connected_iff_interval_subset_right (hx : x ∈ s) : OrdConnected s ↔ ∀ ⦃y⦄, y ∈ s → Interval y x ⊆ s := by
  simp_rw [ord_connected_iff_interval_subset_left hx, interval_swap]

end LinearOrderₓ

end Set

