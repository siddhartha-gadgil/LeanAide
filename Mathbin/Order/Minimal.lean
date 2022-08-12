/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Antichain

/-!
# Minimal/maximal elements of a set

This file defines minimal and maximal of a set with respect to an arbitrary relation.

## Main declarations

* `maximals r s`: Maximal elements of `s` with respect to `r`.
* `minimals r s`: Minimal elements of `s` with respect to `r`.

## TODO

Do we need a `finset` version?
-/


open Function Set

variable {α : Type _} (r r₁ r₂ : α → α → Prop) (s t : Set α) (a : α)

/-- Turns a set into an antichain by keeping only the "maximal" elements. -/
def Maximals : Set α :=
  { a ∈ s | ∀ ⦃b⦄, b ∈ s → r a b → a = b }

/-- Turns a set into an antichain by keeping only the "minimal" elements. -/
def Minimals : Set α :=
  { a ∈ s | ∀ ⦃b⦄, b ∈ s → r b a → a = b }

theorem maximals_subset : Maximals r s ⊆ s :=
  sep_subset _ _

theorem minimals_subset : Minimals r s ⊆ s :=
  sep_subset _ _

@[simp]
theorem maximals_empty : Maximals r ∅ = ∅ :=
  sep_empty _

@[simp]
theorem minimals_empty : Minimals r ∅ = ∅ :=
  sep_empty _

@[simp]
theorem maximals_singleton : Maximals r {a} = {a} :=
  (maximals_subset _ _).antisymm <| singleton_subset_iff.2 <| ⟨rfl, fun b hb _ => hb.symm⟩

@[simp]
theorem minimals_singleton : Minimals r {a} = {a} :=
  maximals_singleton _ _

theorem maximals_swap : Maximals (swap r) s = Minimals r s :=
  rfl

theorem minimals_swap : Minimals (swap r) s = Maximals r s :=
  rfl

theorem maximals_antichain : IsAntichain r (Maximals r s) := fun a ha b hb hab h => hab <| ha.2 hb.1 h

theorem minimals_antichain : IsAntichain r (Minimals r s) :=
  (maximals_antichain _ _).swap

theorem maximals_eq_minimals [IsSymm α r] : Maximals r s = Minimals r s := by
  congr
  ext a b
  exact comm

variable {r r₁ r₂ s t a}

theorem Set.Subsingleton.maximals_eq (h : s.Subsingleton) : Maximals r s = s :=
  h.induction_on (minimals_empty _) (maximals_singleton _)

theorem Set.Subsingleton.minimals_eq (h : s.Subsingleton) : Minimals r s = s :=
  h.maximals_eq

theorem maximals_mono (h : ∀ a b, r₁ a b → r₂ a b) : Maximals r₂ s ⊆ Maximals r₁ s := fun a ha =>
  ⟨ha.1, fun b hb => ha.2 hb ∘ h _ _⟩

theorem minimals_mono (h : ∀ a b, r₁ a b → r₂ a b) : Minimals r₂ s ⊆ Minimals r₁ s := fun a ha =>
  ⟨ha.1, fun b hb => ha.2 hb ∘ h _ _⟩

theorem maximals_union : Maximals r (s ∪ t) ⊆ Maximals r s ∪ Maximals r t := by
  intro a ha
  obtain h | h := ha.1
  · exact Or.inl ⟨h, fun b hb => ha.2 <| Or.inl hb⟩
    
  · exact Or.inr ⟨h, fun b hb => ha.2 <| Or.inr hb⟩
    

theorem minimals_union : Minimals r (s ∪ t) ⊆ Minimals r s ∪ Minimals r t :=
  maximals_union

theorem maximals_inter_subset : Maximals r s ∩ t ⊆ Maximals r (s ∩ t) := fun a ha =>
  ⟨⟨ha.1.1, ha.2⟩, fun b hb => ha.1.2 hb.1⟩

theorem minimals_inter_subset : Minimals r s ∩ t ⊆ Minimals r (s ∩ t) :=
  maximals_inter_subset

theorem inter_maximals_subset : s ∩ Maximals r t ⊆ Maximals r (s ∩ t) := fun a ha =>
  ⟨⟨ha.1, ha.2.1⟩, fun b hb => ha.2.2 hb.2⟩

theorem inter_minimals_subset : s ∩ Minimals r t ⊆ Minimals r (s ∩ t) :=
  inter_maximals_subset

theorem _root_.is_antichain.maximals_eq (h : IsAntichain r s) : Maximals r s = s :=
  (maximals_subset _ _).antisymm fun a ha => ⟨ha, fun b => h.Eq ha⟩

theorem _root_.is_antichain.minimals_eq (h : IsAntichain r s) : Minimals r s = s :=
  (minimals_subset _ _).antisymm fun a ha => ⟨ha, fun b => h.eq' ha⟩

@[simp]
theorem maximals_idem : Maximals r (Maximals r s) = Maximals r s :=
  (maximals_antichain _ _).maximals_eq

@[simp]
theorem minimals_idem : Minimals r (Minimals r s) = Minimals r s :=
  maximals_idem

/-- If `maximals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
theorem IsAntichain.max_maximals (ht : IsAntichain r t) (h : Maximals r s ⊆ t)
    (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ Maximals r s, r b a) : Maximals r s = t := by
  refine' h.antisymm fun a ha => _
  obtain ⟨b, hb, hr⟩ := hs ha
  rwa [of_not_not fun hab => ht (h hb) ha (Ne.symm hab) hr]

/-- If `minimals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
theorem IsAntichain.max_minimals (ht : IsAntichain r t) (h : Minimals r s ⊆ t)
    (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ Minimals r s, r a b) : Minimals r s = t := by
  refine' h.antisymm fun a ha => _
  obtain ⟨b, hb, hr⟩ := hs ha
  rwa [of_not_not fun hab => ht ha (h hb) hab hr]

variable [PartialOrderₓ α]

theorem IsLeast.mem_minimals (h : IsLeast s a) : a ∈ Minimals (· ≤ ·) s :=
  ⟨h.1, fun b hb => (h.2 hb).antisymm⟩

theorem IsGreatest.mem_maximals (h : IsGreatest s a) : a ∈ Maximals (· ≤ ·) s :=
  ⟨h.1, fun b hb => (h.2 hb).antisymm'⟩

theorem IsLeast.minimals_eq (h : IsLeast s a) : Minimals (· ≤ ·) s = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨h.mem_minimals, fun b hb => hb.2 h.1 <| h.2 hb.1⟩

theorem IsGreatest.maximals_eq (h : IsGreatest s a) : Maximals (· ≤ ·) s = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨h.mem_maximals, fun b hb => hb.2 h.1 <| h.2 hb.1⟩

theorem IsAntichain.max_lower_set_of (hs : IsAntichain (· ≤ ·) s) : Maximals (· ≤ ·) { x | ∃ y ∈ s, x ≤ y } = s := by
  ext x
  simp only [← Maximals, ← exists_prop, ← mem_set_of_eq, ← forall_exists_index, ← and_imp, ← sep_set_of]
  refine'
    ⟨fun h => Exists.elim h.1 fun y hy => (h.2 _ hy.1 rfl.le hy.2).symm.subst hy.1, fun h =>
      ⟨⟨x, h, rfl.le⟩, fun b y hy hby hxy => _⟩⟩
  have : x = y := by_contra fun h_eq => (hs h hy h_eq (hxy.trans hby)).elim
  exact hxy.antisymm (this.symm.subst hby)

theorem IsAntichain.min_upper_set_of (hs : IsAntichain (· ≤ ·) s) : Minimals (· ≤ ·) { x | ∃ y ∈ s, y ≤ x } = s :=
  hs.toDual.max_lower_set_of

