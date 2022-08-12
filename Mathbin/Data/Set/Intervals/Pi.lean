/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Data.Set.Lattice

/-!
# Intervals in `pi`-space

In this we prove various simple lemmas about intervals in `Π i, α i`. Closed intervals (`Ici x`,
`Iic x`, `Icc x y`) are equal to products of their projections to `α i`, while (semi-)open intervals
usually include the corresponding products as proper subsets.
-/


variable {ι : Type _} {α : ι → Type _}

namespace Set

section PiPreorder

variable [∀ i, Preorderₓ (α i)] (x y : ∀ i, α i)

@[simp]
theorem pi_univ_Ici : (Pi Univ fun i => Ici (x i)) = Ici x :=
  ext fun y => by
    simp [← Pi.le_def]

@[simp]
theorem pi_univ_Iic : (Pi Univ fun i => Iic (x i)) = Iic x :=
  ext fun y => by
    simp [← Pi.le_def]

@[simp]
theorem pi_univ_Icc : (Pi Univ fun i => Icc (x i) (y i)) = Icc x y :=
  ext fun y => by
    simp [← Pi.le_def, ← forall_and_distrib]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ∉ » s)
theorem piecewise_mem_Icc {s : Set ι} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, α i}
    (h₁ : ∀, ∀ i ∈ s, ∀, f₁ i ∈ Icc (g₁ i) (g₂ i)) (h₂ : ∀ (i) (_ : i ∉ s), f₂ i ∈ Icc (g₁ i) (g₂ i)) :
    s.piecewise f₁ f₂ ∈ Icc g₁ g₂ :=
  ⟨le_piecewise (fun i hi => (h₁ i hi).1) fun i hi => (h₂ i hi).1,
    piecewise_le (fun i hi => (h₁ i hi).2) fun i hi => (h₂ i hi).2⟩

theorem piecewise_mem_Icc' {s : Set ι} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, α i} (h₁ : f₁ ∈ Icc g₁ g₂)
    (h₂ : f₂ ∈ Icc g₁ g₂) : s.piecewise f₁ f₂ ∈ Icc g₁ g₂ :=
  piecewise_mem_Icc (fun i hi => ⟨h₁.1 _, h₁.2 _⟩) fun i hi => ⟨h₂.1 _, h₂.2 _⟩

section Nonempty

variable [Nonempty ι]

theorem pi_univ_Ioi_subset : (Pi Univ fun i => Ioi (x i)) ⊆ Ioi x := fun z hz =>
  ⟨fun i => le_of_ltₓ <| hz i trivialₓ, fun h => (Nonempty.elimₓ ‹Nonempty ι›) fun i => (h i).not_lt (hz i trivialₓ)⟩

theorem pi_univ_Iio_subset : (Pi Univ fun i => Iio (x i)) ⊆ Iio x :=
  @pi_univ_Ioi_subset ι (fun i => (α i)ᵒᵈ) _ x _

theorem pi_univ_Ioo_subset : (Pi Univ fun i => Ioo (x i) (y i)) ⊆ Ioo x y := fun x hx =>
  ⟨(pi_univ_Ioi_subset _) fun i hi => (hx i hi).1, (pi_univ_Iio_subset _) fun i hi => (hx i hi).2⟩

theorem pi_univ_Ioc_subset : (Pi Univ fun i => Ioc (x i) (y i)) ⊆ Ioc x y := fun x hx =>
  ⟨(pi_univ_Ioi_subset _) fun i hi => (hx i hi).1, fun i => (hx i trivialₓ).2⟩

theorem pi_univ_Ico_subset : (Pi Univ fun i => Ico (x i) (y i)) ⊆ Ico x y := fun x hx =>
  ⟨fun i => (hx i trivialₓ).1, (pi_univ_Iio_subset _) fun i hi => (hx i hi).2⟩

end Nonempty

variable [DecidableEq ι]

open Function (update)

theorem pi_univ_Ioc_update_left {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} (hm : x i₀ ≤ m) :
    (Pi Univ fun i => Ioc (update x i₀ m i) (y i)) = { z | m < z i₀ } ∩ Pi Univ fun i => Ioc (x i) (y i) := by
  have : Ioc m (y i₀) = Ioi m ∩ Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, ← inter_assoc, inter_eq_self_of_subset_left (Ioi_subset_Ioi hm)]
  simp_rw [univ_pi_update i₀ _ _ fun i z => Ioc z (y i), ← pi_inter_compl ({i₀} : Set ι), singleton_pi', ← inter_assoc,
    this]
  rfl

theorem pi_univ_Ioc_update_right {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} (hm : m ≤ y i₀) :
    (Pi Univ fun i => Ioc (x i) (update y i₀ m i)) = { z | z i₀ ≤ m } ∩ Pi Univ fun i => Ioc (x i) (y i) := by
  have : Ioc (x i₀) m = Iic m ∩ Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_left_comm, inter_eq_self_of_subset_left (Iic_subset_Iic.2 hm)]
  simp_rw [univ_pi_update i₀ y m fun i z => Ioc (x i) z, ← pi_inter_compl ({i₀} : Set ι), singleton_pi', ← inter_assoc,
    this]
  rfl

theorem disjoint_pi_univ_Ioc_update_left_right {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} :
    Disjoint (Pi Univ fun i => Ioc (x i) (update y i₀ m i)) (Pi Univ fun i => Ioc (update x i₀ m i) (y i)) := by
  rintro z ⟨h₁, h₂⟩
  refine' (h₁ i₀ (mem_univ _)).2.not_lt _
  simpa only [← Function.update_same] using (h₂ i₀ (mem_univ _)).1

end PiPreorder

variable [DecidableEq ι] [∀ i, LinearOrderₓ (α i)]

open Function (update)

theorem pi_univ_Ioc_update_union (x y : ∀ i, α i) (i₀ : ι) (m : α i₀) (hm : m ∈ Icc (x i₀) (y i₀)) :
    ((Pi Univ fun i => Ioc (x i) (update y i₀ m i)) ∪ Pi Univ fun i => Ioc (update x i₀ m i) (y i)) =
      Pi Univ fun i => Ioc (x i) (y i) :=
  by
  simp_rw [pi_univ_Ioc_update_left hm.1, pi_univ_Ioc_update_right hm.2, ← union_inter_distrib_right, ← set_of_or,
    le_or_ltₓ, set_of_true, univ_inter]

/-- If `x`, `y`, `x'`, and `y'` are functions `Π i : ι, α i`, then
the set difference between the box `[x, y]` and the product of the open intervals `(x' i, y' i)`
is covered by the union of the following boxes: for each `i : ι`, we take
`[x, update y i (x' i)]` and `[update x i (y' i), y]`.

E.g., if `x' = x` and `y' = y`, then this lemma states that the difference between a closed box
`[x, y]` and the corresponding open box `{z | ∀ i, x i < z i < y i}` is covered by the union
of the faces of `[x, y]`. -/
theorem Icc_diff_pi_univ_Ioo_subset (x y x' y' : ∀ i, α i) :
    (Icc x y \ Pi Univ fun i => Ioo (x' i) (y' i)) ⊆
      (⋃ i : ι, Icc x (update y i (x' i))) ∪ ⋃ i : ι, Icc (update x i (y' i)) y :=
  by
  rintro a ⟨⟨hxa, hay⟩, ha'⟩
  simpa [← le_update_iff, ← update_le_iff, ← hxa, ← hay, ← hxa _, ← hay _, exists_or_distrib, ← not_and_distrib] using
    ha'

/-- If `x`, `y`, `z` are functions `Π i : ι, α i`, then
the set difference between the box `[x, z]` and the product of the intervals `(y i, z i]`
is covered by the union of the boxes `[x, update z i (y i)]`.

E.g., if `x = y`, then this lemma states that the difference between a closed box
`[x, y]` and the product of half-open intervals `{z | ∀ i, x i < z i ≤ y i}` is covered by the union
of the faces of `[x, y]` adjacent to `x`. -/
theorem Icc_diff_pi_univ_Ioc_subset (x y z : ∀ i, α i) :
    (Icc x z \ Pi Univ fun i => Ioc (y i) (z i)) ⊆ ⋃ i : ι, Icc x (update z i (y i)) := by
  rintro a ⟨⟨hax, haz⟩, hay⟩
  simpa [← not_and_distrib, ← hax, ← le_update_iff, ← haz _] using hay

end Set

