/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Set.Basic

/-!
# Sets in sigma types

This file defines `set.sigma`, the indexed sum of sets.
-/


namespace Set

variable {ι ι' : Type _} {α β : ι → Type _} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)} {u : Set (Σi, α i)}
  {x : Σi, α i} {i j : ι} {a : α i}

@[simp]
theorem range_sigma_mk (i : ι) : Range (Sigma.mk i : α i → Sigma α) = Sigma.fst ⁻¹' {i} := by
  apply subset.antisymm
  · rintro _ ⟨b, rfl⟩
    simp
    
  · rintro ⟨x, y⟩ (rfl | _)
    exact mem_range_self y
    

theorem preimage_image_sigma_mk_of_ne (h : i ≠ j) (s : Set (α j)) : Sigma.mk i ⁻¹' (Sigma.mk j '' s) = ∅ := by
  ext x
  simp [← h.symm]

theorem image_sigma_mk_preimage_sigma_map_subset {β : ι' → Type _} (f : ι → ι') (g : ∀ i, α i → β (f i)) (i : ι)
    (s : Set (β (f i))) : Sigma.mk i '' (g i ⁻¹' s) ⊆ Sigma.map f g ⁻¹' (Sigma.mk (f i) '' s) :=
  image_subset_iff.2 fun x hx => ⟨g i x, hx, rfl⟩

theorem image_sigma_mk_preimage_sigma_map {β : ι' → Type _} {f : ι → ι'} (hf : Function.Injective f)
    (g : ∀ i, α i → β (f i)) (i : ι) (s : Set (β (f i))) :
    Sigma.mk i '' (g i ⁻¹' s) = Sigma.map f g ⁻¹' (Sigma.mk (f i) '' s) := by
  refine' (image_sigma_mk_preimage_sigma_map_subset f g i s).antisymm _
  rintro ⟨j, x⟩ ⟨y, hys, hxy⟩
  simp only [← hf.eq_iff, ← Sigma.map] at hxy
  rcases hxy with ⟨rfl, hxy⟩
  rw [heq_iff_eq] at hxy
  subst y
  exact ⟨x, hys, rfl⟩

/-- Indexed sum of sets. `s.sigma t` is the set of dependent pairs `⟨i, a⟩` such that `i ∈ s` and
`a ∈ t i`.-/
protected def Sigma (s : Set ι) (t : ∀ i, Set (α i)) : Set (Σi, α i) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t x.1 }

@[simp]
theorem mem_sigma_iff : x ∈ s.Sigma t ↔ x.1 ∈ s ∧ x.2 ∈ t x.1 :=
  Iff.rfl

@[simp]
theorem mk_sigma_iff : (⟨i, a⟩ : Σi, α i) ∈ s.Sigma t ↔ i ∈ s ∧ a ∈ t i :=
  Iff.rfl

theorem mk_mem_sigma (hi : i ∈ s) (ha : a ∈ t i) : (⟨i, a⟩ : Σi, α i) ∈ s.Sigma t :=
  ⟨hi, ha⟩

theorem sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.Sigma t₁ ⊆ s₂.Sigma t₂ := fun x hx =>
  ⟨hs hx.1, ht _ hx.2⟩

theorem sigma_subset_iff : s.Sigma t ⊆ u ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃a⦄, a ∈ t i → (⟨i, a⟩ : Σi, α i) ∈ u :=
  ⟨fun h i hi a ha => h <| mk_mem_sigma hi ha, fun h ⟨i, a⟩ ha => h ha.1 ha.2⟩

theorem forall_sigma_iff {p : (Σi, α i) → Prop} :
    (∀, ∀ x ∈ s.Sigma t, ∀, p x) ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃a⦄, a ∈ t i → p ⟨i, a⟩ :=
  sigma_subset_iff

theorem exists_sigma_iff {p : (Σi, α i) → Prop} : (∃ x ∈ s.Sigma t, p x) ↔ ∃ i ∈ s, ∃ a ∈ t i, p ⟨i, a⟩ :=
  ⟨fun ⟨⟨i, a⟩, ha, h⟩ => ⟨i, ha.1, a, ha.2, h⟩, fun ⟨i, hi, a, ha, h⟩ => ⟨⟨i, a⟩, ⟨hi, ha⟩, h⟩⟩

@[simp]
theorem sigma_empty : (s.Sigma fun _ => (∅ : Set (α i))) = ∅ :=
  ext fun _ => and_falseₓ _

@[simp]
theorem empty_sigma : (∅ : Set ι).Sigma t = ∅ :=
  ext fun _ => false_andₓ _

theorem univ_sigma_univ : ((@Univ ι).Sigma fun _ => @Univ (α i)) = univ :=
  ext fun _ => true_andₓ _

@[simp]
theorem sigma_univ : s.Sigma (fun _ => Univ : ∀ i, Set (α i)) = Sigma.fst ⁻¹' s :=
  ext fun _ => and_trueₓ _

@[simp]
theorem singleton_sigma : ({i} : Set ι).Sigma t = Sigma.mk i '' t i :=
  ext fun x => by
    constructor
    · obtain ⟨j, a⟩ := x
      rintro ⟨rfl : j = i, ha⟩
      exact mem_image_of_mem _ ha
      
    · rintro ⟨b, hb, rfl⟩
      exact ⟨rfl, hb⟩
      

@[simp]
theorem sigma_singleton {a : ∀ i, α i} : (s.Sigma fun i => ({a i} : Set (α i))) = (fun i => Sigma.mk i <| a i) '' s :=
  by
  ext ⟨x, y⟩
  simp [← And.left_comm, ← eq_comm]

theorem singleton_sigma_singleton {a : ∀ i, α i} : (({i} : Set ι).Sigma fun i => ({a i} : Set (α i))) = {⟨i, a i⟩} := by
  rw [sigma_singleton, image_singleton]

@[simp]
theorem union_sigma : (s₁ ∪ s₂).Sigma t = s₁.Sigma t ∪ s₂.Sigma t :=
  ext fun _ => or_and_distrib_right

@[simp]
theorem sigma_union : (s.Sigma fun i => t₁ i ∪ t₂ i) = s.Sigma t₁ ∪ s.Sigma t₂ :=
  ext fun _ => and_or_distrib_left

theorem sigma_inter_sigma : s₁.Sigma t₁ ∩ s₂.Sigma t₂ = (s₁ ∩ s₂).Sigma fun i => t₁ i ∩ t₂ i := by
  ext ⟨x, y⟩
  simp [← and_assoc, ← And.left_comm]

theorem insert_sigma : (insert i s).Sigma t = Sigma.mk i '' t i ∪ s.Sigma t := by
  rw [insert_eq, union_sigma, singleton_sigma]

theorem sigma_insert {a : ∀ i, α i} : (s.Sigma fun i => insert (a i) (t i)) = (fun i => ⟨i, a i⟩) '' s ∪ s.Sigma t := by
  simp_rw [insert_eq, sigma_union, sigma_singleton]

theorem sigma_preimage_eq {f : ι' → ι} {g : ∀ i, β i → α i} :
    ((f ⁻¹' s).Sigma fun i => g (f i) ⁻¹' t (f i)) = (fun p : Σi, β (f i) => Sigma.mk _ (g _ p.2)) ⁻¹' s.Sigma t :=
  rfl

theorem sigma_preimage_left {f : ι' → ι} :
    ((f ⁻¹' s).Sigma fun i => t (f i)) = (fun p : Σi, α (f i) => Sigma.mk _ p.2) ⁻¹' s.Sigma t :=
  rfl

theorem sigma_preimage_right {g : ∀ i, β i → α i} :
    (s.Sigma fun i => g i ⁻¹' t i) = (fun p : Σi, β i => Sigma.mk p.1 (g _ p.2)) ⁻¹' s.Sigma t :=
  rfl

theorem preimage_sigma_map_sigma {α' : ι' → Type _} (f : ι → ι') (g : ∀ i, α i → α' (f i)) (s : Set ι')
    (t : ∀ i, Set (α' i)) : Sigma.map f g ⁻¹' s.Sigma t = (f ⁻¹' s).Sigma fun i => g i ⁻¹' t (f i) :=
  rfl

@[simp]
theorem mk_preimage_sigma (hi : i ∈ s) : Sigma.mk i ⁻¹' s.Sigma t = t i :=
  ext fun _ => and_iff_right hi

@[simp]
theorem mk_preimage_sigma_eq_empty (hi : i ∉ s) : Sigma.mk i ⁻¹' s.Sigma t = ∅ :=
  ext fun _ => iff_of_false (hi ∘ And.left) id

theorem mk_preimage_sigma_eq_if [DecidablePred (· ∈ s)] : Sigma.mk i ⁻¹' s.Sigma t = if i ∈ s then t i else ∅ := by
  split_ifs <;> simp [← h]

theorem mk_preimage_sigma_fn_eq_if {β : Type _} [DecidablePred (· ∈ s)] (g : β → α i) :
    (fun b => Sigma.mk i (g b)) ⁻¹' s.Sigma t = if i ∈ s then g ⁻¹' t i else ∅ :=
  ext fun _ => by
    split_ifs <;> simp [← h]

theorem sigma_univ_range_eq {f : ∀ i, α i → β i} :
    ((Univ : Set ι).Sigma fun i => Range (f i)) = Range fun x : Σi, α i => ⟨x.1, f _ x.2⟩ :=
  ext <| by
    simp [← range]

protected theorem Nonempty.sigma : s.Nonempty → (∀ i, (t i).Nonempty) → (s.Sigma t : Set _).Nonempty := fun ⟨i, hi⟩ h =>
  let ⟨a, ha⟩ := h i
  ⟨⟨i, a⟩, hi, ha⟩

theorem Nonempty.sigma_fst : (s.Sigma t : Set _).Nonempty → s.Nonempty := fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩

theorem Nonempty.sigma_snd : (s.Sigma t : Set _).Nonempty → ∃ i ∈ s, (t i).Nonempty := fun ⟨x, hx⟩ =>
  ⟨x.1, hx.1, x.2, hx.2⟩

theorem sigma_nonempty_iff : (s.Sigma t : Set _).Nonempty ↔ ∃ i ∈ s, (t i).Nonempty :=
  ⟨Nonempty.sigma_snd, fun ⟨i, hi, a, ha⟩ => ⟨⟨i, a⟩, hi, ha⟩⟩

theorem sigma_eq_empty_iff : s.Sigma t = ∅ ↔ ∀, ∀ i ∈ s, ∀, t i = ∅ :=
  not_nonempty_iff_eq_empty.symm.trans <|
    sigma_nonempty_iff.Not.trans <| by
      simp only [← not_nonempty_iff_eq_empty, ← not_exists]

theorem image_sigma_mk_subset_sigma_left {a : ∀ i, α i} (ha : ∀ i, a i ∈ t i) :
    (fun i => Sigma.mk i (a i)) '' s ⊆ s.Sigma t :=
  image_subset_iff.2 fun i hi => ⟨hi, ha _⟩

theorem image_sigma_mk_subset_sigma_right (hi : i ∈ s) : Sigma.mk i '' t i ⊆ s.Sigma t :=
  image_subset_iff.2 fun a => And.intro hi

theorem sigma_subset_preimage_fst (s : Set ι) (t : ∀ i, Set (α i)) : s.Sigma t ⊆ Sigma.fst ⁻¹' s := fun a => And.left

theorem fst_image_sigma_subset (s : Set ι) (t : ∀ i, Set (α i)) : Sigma.fst '' s.Sigma t ⊆ s :=
  image_subset_iff.2 fun a => And.left

theorem fst_image_sigma (s : Set ι) (ht : ∀ i, (t i).Nonempty) : Sigma.fst '' s.Sigma t = s :=
  (fst_image_sigma_subset _ _).antisymm fun i hi =>
    let ⟨a, ha⟩ := ht i
    ⟨⟨i, a⟩, ⟨hi, ha⟩, rfl⟩

theorem sigma_diff_sigma : s₁.Sigma t₁ \ s₂.Sigma t₂ = s₁.Sigma (t₁ \ t₂) ∪ (s₁ \ s₂).Sigma t₁ :=
  ext fun x => by
    by_cases' h₁ : x.1 ∈ s₁ <;> by_cases' h₂ : x.2 ∈ t₁ x.1 <;> simp [*, imp_iff_or_not]

end Set

