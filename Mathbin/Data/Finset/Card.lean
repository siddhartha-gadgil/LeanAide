/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathbin.Data.Finset.Basic
import Mathbin.Tactic.ByContra

/-!
# Cardinality of a finite set

This defines the cardinality of a `finset` and provides induction principles for finsets.

## Main declarations

* `finset.card`: `s.card : ℕ` returns the cardinality of `s : finset α`.

### Induction principles

* `finset.strong_induction`: Strong induction
* `finset.strong_induction_on`
* `finset.strong_downward_induction`
* `finset.strong_downward_induction_on`
* `finset.case_strong_induction_on`

## TODO

Should we add a noncomputable version?
-/


open Function Multiset Nat

variable {α β : Type _}

namespace Finset

variable {s t : Finset α} {a b : α}

/-- `s.card` is the number of elements of `s`, aka its cardinality. -/
def card (s : Finset α) : ℕ :=
  s.1.card

theorem card_def (s : Finset α) : s.card = s.1.card :=
  rfl

@[simp]
theorem card_mk {m nodup} : (⟨m, nodup⟩ : Finset α).card = m.card :=
  rfl

@[simp]
theorem card_empty : card (∅ : Finset α) = 0 :=
  rfl

theorem card_le_of_subset : s ⊆ t → s.card ≤ t.card :=
  Multiset.card_le_of_le ∘ val_le_iff.mpr

@[mono]
theorem card_mono : Monotone (@card α) := by
  apply card_le_of_subset

@[simp]
theorem card_eq_zero : s.card = 0 ↔ s = ∅ :=
  card_eq_zero.trans val_eq_zero

theorem card_pos : 0 < s.card ↔ s.Nonempty :=
  pos_iff_ne_zero.trans <| (not_congr card_eq_zero).trans nonempty_iff_ne_empty.symm

alias card_pos ↔ _ nonempty.card_pos

theorem card_ne_zero_of_mem (h : a ∈ s) : s.card ≠ 0 :=
  (not_congr card_eq_zero).2 <| ne_empty_of_mem h

@[simp]
theorem card_singleton (a : α) : card ({a} : Finset α) = 1 :=
  card_singleton _

theorem card_singleton_inter [DecidableEq α] : ({a} ∩ s).card ≤ 1 := by
  cases Finset.decidableMem a s
  · simp [← Finset.singleton_inter_of_not_mem h]
    
  · simp [← Finset.singleton_inter_of_mem h]
    

@[simp]
theorem card_cons (h : a ∉ s) : (s.cons a h).card = s.card + 1 :=
  card_cons _ _

section InsertErase

variable [DecidableEq α]

@[simp]
theorem card_insert_of_not_mem (h : a ∉ s) : (insert a s).card = s.card + 1 := by
  rw [← cons_eq_insert _ _ h, card_cons]

theorem card_insert_of_mem (h : a ∈ s) : card (insert a s) = s.card := by
  rw [insert_eq_of_mem h]

theorem card_insert_le (a : α) (s : Finset α) : card (insert a s) ≤ s.card + 1 := by
  by_cases' a ∈ s <;>
    [· rw [insert_eq_of_mem h]
      exact Nat.le_succₓ _
      ,
    rw [card_insert_of_not_mem h]]

/-- If `a ∈ s` is known, see also `finset.card_insert_of_mem` and `finset.card_insert_of_not_mem`.
-/
theorem card_insert_eq_ite : card (insert a s) = if a ∈ s then s.card else s.card + 1 := by
  by_cases' h : a ∈ s
  · rw [card_insert_of_mem h, if_pos h]
    
  · rw [card_insert_of_not_mem h, if_neg h]
    

@[simp]
theorem card_doubleton (h : a ≠ b) : ({a, b} : Finset α).card = 2 := by
  rw [card_insert_of_not_mem (not_mem_singleton.2 h), card_singleton]

@[simp]
theorem card_erase_of_mem : a ∈ s → (s.erase a).card = s.card - 1 :=
  card_erase_of_mem

@[simp]
theorem card_erase_add_one : a ∈ s → (s.erase a).card + 1 = s.card :=
  card_erase_add_one

theorem card_erase_lt_of_mem : a ∈ s → (s.erase a).card < s.card :=
  card_erase_lt_of_mem

theorem card_erase_le : (s.erase a).card ≤ s.card :=
  card_erase_le

theorem pred_card_le_card_erase : s.card - 1 ≤ (s.erase a).card := by
  by_cases' h : a ∈ s
  · exact (card_erase_of_mem h).Ge
    
  · rw [erase_eq_of_not_mem h]
    exact Nat.sub_leₓ _ _
    

/-- If `a ∈ s` is known, see also `finset.card_erase_of_mem` and `finset.erase_eq_of_not_mem`. -/
theorem card_erase_eq_ite : (s.erase a).card = if a ∈ s then s.card - 1 else s.card :=
  card_erase_eq_ite

end InsertErase

@[simp]
theorem card_range (n : ℕ) : (range n).card = n :=
  card_range n

@[simp]
theorem card_attach : s.attach.card = s.card :=
  Multiset.card_attach

end Finset

section ToListMultiset

variable [DecidableEq α] (m : Multiset α) (l : List α)

theorem Multiset.card_to_finset : m.toFinset.card = m.dedup.card :=
  rfl

theorem Multiset.to_finset_card_le : m.toFinset.card ≤ m.card :=
  card_le_of_le <| dedup_le _

theorem Multiset.to_finset_card_of_nodup {m : Multiset α} (h : m.Nodup) : m.toFinset.card = m.card :=
  congr_arg card <| Multiset.dedup_eq_self.mpr h

theorem List.card_to_finset : l.toFinset.card = l.dedup.length :=
  rfl

theorem List.to_finset_card_le : l.toFinset.card ≤ l.length :=
  Multiset.to_finset_card_le ⟦l⟧

theorem List.to_finset_card_of_nodup {l : List α} (h : l.Nodup) : l.toFinset.card = l.length :=
  Multiset.to_finset_card_of_nodup h

end ToListMultiset

namespace Finset

variable {s t : Finset α} {f : α → β} {n : ℕ}

@[simp]
theorem length_to_list (s : Finset α) : s.toList.length = s.card := by
  rw [to_list, ← Multiset.coe_card, Multiset.coe_to_list]
  rfl

theorem card_image_le [DecidableEq β] : (s.Image f).card ≤ s.card := by
  simpa only [← card_map] using (s.1.map f).to_finset_card_le

theorem card_image_of_inj_on [DecidableEq β] (H : Set.InjOn f s) : (s.Image f).card = s.card := by
  simp only [← card, ← image_val_of_inj_on H, ← card_map]

theorem inj_on_of_card_image_eq [DecidableEq β] (H : (s.Image f).card = s.card) : Set.InjOn f s := by
  change (s.1.map f).dedup.card = s.1.card at H
  have : (s.1.map f).dedup = s.1.map f := by
    refine' Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) _
    rw [H]
    simp only [← Multiset.card_map]
  rw [Multiset.dedup_eq_self] at this
  exact inj_on_of_nodup_map this

theorem card_image_iff [DecidableEq β] : (s.Image f).card = s.card ↔ Set.InjOn f s :=
  ⟨inj_on_of_card_image_eq, card_image_of_inj_on⟩

theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) : (s.Image f).card = s.card :=
  card_image_of_inj_on fun x _ y _ h => H h

theorem fiber_card_ne_zero_iff_mem_image (s : Finset α) (f : α → β) [DecidableEq β] (y : β) :
    (s.filter fun x => f x = y).card ≠ 0 ↔ y ∈ s.Image f := by
  rw [← pos_iff_ne_zero, card_pos, fiber_nonempty_iff_mem_image]

@[simp]
theorem card_map (f : α ↪ β) : (s.map f).card = s.card :=
  Multiset.card_map _ _

@[simp]
theorem card_subtype (p : α → Prop) [DecidablePred p] (s : Finset α) : (s.Subtype p).card = (s.filter p).card := by
  simp [← Finset.subtype]

theorem card_filter_le (s : Finset α) (p : α → Prop) [DecidablePred p] : (s.filter p).card ≤ s.card :=
  card_le_of_subset <| filter_subset _ _

theorem eq_of_subset_of_card_le {s t : Finset α} (h : s ⊆ t) (h₂ : t.card ≤ s.card) : s = t :=
  eq_of_veq <| Multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

theorem map_eq_of_subset {f : α ↪ α} (hs : s.map f ⊆ s) : s.map f = s :=
  eq_of_subset_of_card_le hs (card_map _).Ge

theorem filter_card_eq {p : α → Prop} [DecidablePred p] (h : (s.filter p).card = s.card) (x : α) (hx : x ∈ s) : p x :=
  by
  rw [← eq_of_subset_of_card_le (s.filter_subset p) h.ge, mem_filter] at hx
  exact hx.2

theorem card_lt_card (h : s ⊂ t) : s.card < t.card :=
  card_lt_of_lt <| val_lt_iff.2 h

theorem card_eq_of_bijective (f : ∀ i, i < n → α) (hf : ∀, ∀ a ∈ s, ∀, ∃ i, ∃ h : i < n, f i h = a)
    (hf' : ∀ (i) (h : i < n), f i h ∈ s) (f_inj : ∀ (i j) (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) :
    s.card = n := by
  classical
  have : ∀ a : α, a ∈ s ↔ ∃ (i : _)(hi : i ∈ range n), f i (mem_range.1 hi) = a := fun a =>
    ⟨fun ha =>
      let ⟨i, hi, Eq⟩ := hf a ha
      ⟨i, mem_range.2 hi, Eq⟩,
      fun ⟨i, hi, Eq⟩ => Eq ▸ hf' i (mem_range.1 hi)⟩
  have : s = (range n).attach.Image fun i => f i.1 (mem_range.1 i.2) := by
    simpa only [← ext_iff, ← mem_image, ← exists_prop, ← Subtype.exists, ← mem_attach, ← true_andₓ]
  calc s.card = card ((range n).attach.Image fun i => f i.1 (mem_range.1 i.2)) := by
      rw [this]_ = card (range n).attach :=
      (card_image_of_injective _) fun ⟨i, hi⟩ ⟨j, hj⟩ eq =>
        Subtype.eq <| f_inj i j (mem_range.1 hi) (mem_range.1 hj) Eq _ = card (range n) :=
      card_attach _ = n := card_range n

theorem card_congr {t : Finset β} (f : ∀, ∀ a ∈ s, ∀, β) (h₁ : ∀ a ha, f a ha ∈ t)
    (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀, ∀ b ∈ t, ∀, ∃ a ha, f a ha = b) : s.card = t.card := by
  classical <;>
    calc s.card = s.attach.card := card_attach.symm _ = (s.attach.image fun a : { a // a ∈ s } => f a.1 a.2).card :=
        Eq.symm ((card_image_of_injective _) fun a b h => Subtype.eq <| h₂ _ _ _ _ h)_ = t.card :=
        congr_arg card
          (Finset.ext fun b =>
            ⟨fun h =>
              let ⟨a, ha₁, ha₂⟩ := mem_image.1 h
              ha₂ ▸ h₁ _ _,
              fun h =>
              let ⟨a, ha₁, ha₂⟩ := h₃ b h
              mem_image.2
                ⟨⟨a, ha₁⟩, by
                  simp [← ha₂]⟩⟩)

theorem card_le_card_of_inj_on {t : Finset β} (f : α → β) (hf : ∀, ∀ a ∈ s, ∀, f a ∈ t)
    (f_inj : ∀, ∀ a₁ ∈ s, ∀, ∀, ∀ a₂ ∈ s, ∀, f a₁ = f a₂ → a₁ = a₂) : s.card ≤ t.card := by
  classical <;>
    calc s.card = (s.image f).card := (card_image_of_inj_on f_inj).symm _ ≤ t.card :=
        card_le_of_subset <| image_subset_iff.2 hf

/-- If there are more pigeons than pigeonholes, then there are two pigeons in the same pigeonhole.
-/
theorem exists_ne_map_eq_of_card_lt_of_maps_to {t : Finset β} (hc : t.card < s.card) {f : α → β}
    (hf : ∀, ∀ a ∈ s, ∀, f a ∈ t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  classical
  by_contra' hz
  refine' hc.not_le (card_le_card_of_inj_on f hf _)
  intro x hx y hy
  contrapose
  exact hz x hx y hy

theorem le_card_of_inj_on_range (f : ℕ → α) (hf : ∀, ∀ i < n, ∀, f i ∈ s)
    (f_inj : ∀, ∀ i < n, ∀, ∀ j < n, ∀, f i = f j → i = j) : n ≤ s.card :=
  calc
    n = card (range n) := (card_range n).symm
    _ ≤ s.card :=
      card_le_card_of_inj_on f
        (by
          simpa only [← mem_range] )
        (by
          simpa only [← mem_range] )
    

theorem surj_on_of_inj_on_of_card_le {t : Finset β} (f : ∀, ∀ a ∈ s, ∀, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.card ≤ s.card) :
    ∀, ∀ b ∈ t, ∀, ∃ a ha, b = f a ha := by
  classical
  intro b hb
  have h : (s.attach.image fun a : { a // a ∈ s } => f a a.Prop).card = s.card :=
    @card_attach _ s ▸ card_image_of_injective _ fun ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ h => Subtype.eq <| hinj _ _ _ _ h
  have h' : image (fun a : { a // a ∈ s } => f a a.Prop) s.attach = t :=
    eq_of_subset_of_card_le
      (fun b h =>
        let ⟨a, ha₁, ha₂⟩ := mem_image.1 h
        ha₂ ▸ hf _ _)
      (by
        simp [← hst, ← h])
  rw [← h'] at hb
  obtain ⟨a, ha₁, ha₂⟩ := mem_image.1 hb
  exact ⟨a, a.2, ha₂.symm⟩

theorem inj_on_of_surj_on_of_card_le {t : Finset β} (f : ∀, ∀ a ∈ s, ∀, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀, ∀ b ∈ t, ∀, ∃ a ha, b = f a ha) (hst : s.card ≤ t.card) ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s)
    (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) : a₁ = a₂ :=
  have : Inhabited { x // x ∈ s } := ⟨⟨a₁, ha₁⟩⟩
  let f' : { x // x ∈ s } → { x // x ∈ t } := fun x => ⟨f x.1 x.2, hf x.1 x.2⟩
  let g : { x // x ∈ t } → { x // x ∈ s } :=
    @surj_inv _ _ f' fun x =>
      let ⟨y, hy₁, hy₂⟩ := hsurj x.1 x.2
      ⟨⟨y, hy₁⟩, Subtype.eq hy₂.symm⟩
  have hg : injective g := injective_surj_inv _
  have hsg : surjective g := fun x =>
    let ⟨y, hy⟩ :=
      surj_on_of_inj_on_of_card_le (fun (x : { x // x ∈ t }) (hx : x ∈ t.attach) => g x)
        (fun x _ => show g x ∈ s.attach from mem_attach _ _) (fun x y _ _ hxy => hg hxy)
        (by
          simpa)
        x (mem_attach _ _)
    ⟨y, hy.snd.symm⟩
  have hif : injective f' := (left_inverse_of_surjective_of_right_inverse hsg (right_inverse_surj_inv _)).Injective
  Subtype.ext_iff_val.1 (@hif ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ (Subtype.eq ha₁a₂))

@[simp]
theorem card_disj_union (s t : Finset α) (h) : (s.disjUnion t h).card = s.card + t.card :=
  Multiset.card_add _ _

/-! ### Lattice structure -/


section Lattice

variable [DecidableEq α]

theorem card_union_add_card_inter (s t : Finset α) : (s ∪ t).card + (s ∩ t).card = s.card + t.card :=
  (Finset.induction_on t
      (by
        simp ))
    fun a r har => by
    by_cases' a ∈ s <;> simp [*] <;> cc

theorem card_union_le (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card :=
  card_union_add_card_inter s t ▸ Nat.le_add_rightₓ _ _

theorem card_union_eq (h : Disjoint s t) : (s ∪ t).card = s.card + t.card := by
  rw [← disj_union_eq_union s t <| disjoint_left.mp h, card_disj_union _ _ _]

@[simp]
theorem card_disjoint_union (h : Disjoint s t) : card (s ∪ t) = s.card + t.card :=
  card_union_eq h

theorem card_sdiff (h : s ⊆ t) : card (t \ s) = t.card - s.card := by
  suffices card (t \ s) = card (t \ s ∪ s) - s.card by
    rwa [sdiff_union_of_subset h] at this
  rw [card_disjoint_union sdiff_disjoint, add_tsub_cancel_right]

theorem card_sdiff_add_card_eq_card {s t : Finset α} (h : s ⊆ t) : card (t \ s) + card s = card t :=
  ((Nat.sub_eq_iff_eq_addₓ (card_le_of_subset h)).mp (card_sdiff h).symm).symm

theorem le_card_sdiff (s t : Finset α) : t.card - s.card ≤ card (t \ s) :=
  calc
    card t - card s ≤ card t - card (s ∩ t) := tsub_le_tsub_left (card_le_of_subset (inter_subset_left s t)) _
    _ = card (t \ (s ∩ t)) := (card_sdiff (inter_subset_right s t)).symm
    _ ≤ card (t \ s) := by
      rw [sdiff_inter_self_right t s]
    

theorem card_sdiff_add_card : (s \ t).card + t.card = (s ∪ t).card := by
  rw [← card_disjoint_union sdiff_disjoint, sdiff_union_self_eq_union]

end Lattice

theorem filter_card_add_filter_neg_card_eq_card (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (Not ∘ p)).card = s.card := by
  classical
  simp [card_union_eq, ← filter_union_filter_neg_eq, ← disjoint_filter]

/-- Given a set `A` and a set `B` inside it, we can shrink `A` to any appropriate size, and keep `B`
inside it. -/
theorem exists_intermediate_set {A B : Finset α} (i : ℕ) (h₁ : i + card B ≤ card A) (h₂ : B ⊆ A) :
    ∃ C : Finset α, B ⊆ C ∧ C ⊆ A ∧ card C = i + card B := by
  classical
  rcases Nat.Le.dest h₁ with ⟨k, _⟩
  clear h₁
  induction' k with k ih generalizing A
  · exact ⟨A, h₂, subset.refl _, h.symm⟩
    
  have : (A \ B).Nonempty := by
    rw [← card_pos, card_sdiff h₂, ← h, Nat.add_right_comm, add_tsub_cancel_right, Nat.add_succ]
    apply Nat.succ_posₓ
  rcases this with ⟨a, ha⟩
  have z : i + card B + k = card (erase A a) := by
    rw [card_erase_of_mem (mem_sdiff.1 ha).1, ← h]
    rfl
  rcases ih _ z with ⟨B', hB', B'subA', cards⟩
  · exact ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩
    
  · rintro t th
    apply mem_erase_of_ne_of_mem _ (h₂ th)
    rintro rfl
    exact not_mem_sdiff_of_mem_right th ha
    

/-- We can shrink `A` to any smaller size. -/
theorem exists_smaller_set (A : Finset α) (i : ℕ) (h₁ : i ≤ card A) : ∃ B : Finset α, B ⊆ A ∧ card B = i :=
  let ⟨B, _, x₁, x₂⟩ :=
    exists_intermediate_set i
      (by
        simpa)
      (empty_subset A)
  ⟨B, x₁, x₂⟩

theorem exists_subset_or_subset_of_two_mul_lt_card [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < (X ∪ Y).card) : ∃ C : Finset α, n < C.card ∧ (C ⊆ X ∨ C ⊆ Y) := by
  have h₁ : (X ∩ (Y \ X)).card = 0 := finset.card_eq_zero.mpr (Finset.inter_sdiff_self X Y)
  have h₂ : (X ∪ Y).card = X.card + (Y \ X).card := by
    rw [← card_union_add_card_inter X (Y \ X), Finset.union_sdiff_self_eq_union, h₁, add_zeroₓ]
  rw [h₂, two_mul] at hXY
  rcases lt_or_lt_of_add_lt_add hXY with (h | h)
  · exact ⟨X, h, Or.inl (Finset.Subset.refl X)⟩
    
  · exact ⟨Y \ X, h, Or.inr (Finset.sdiff_subset Y X)⟩
    

/-! ### Explicit description of a finset from its card -/


theorem card_eq_one : s.card = 1 ↔ ∃ a, s = {a} := by
  cases s <;> simp only [← Multiset.card_eq_one, ← Finset.card, val_inj, ← singleton_val]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a «expr ∉ » s)
theorem exists_eq_insert_iff [DecidableEq α] {s t : Finset α} :
    (∃ (a : _)(_ : a ∉ s), insert a s = t) ↔ s ⊆ t ∧ s.card + 1 = t.card := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨subset_insert _ _, (card_insert_of_not_mem ha).symm⟩
    
  · rintro ⟨hst, h⟩
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a} :=
      card_eq_one.1
        (by
          rw [card_sdiff hst, ← h, add_tsub_cancel_left])
    refine'
      ⟨a, fun hs => (_ : a ∉ {a}) <| mem_singleton_self _, by
        rw [insert_eq, ← ha, sdiff_union_of_subset hst]⟩
    rw [← ha]
    exact not_mem_sdiff_of_mem_right hs
    

theorem card_le_one : s.card ≤ 1 ↔ ∀, ∀ a ∈ s, ∀, ∀ b ∈ s, ∀, a = b := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
    
  refine' (Nat.succ_le_of_ltₓ (card_pos.2 ⟨x, hx⟩)).le_iff_eq.trans (card_eq_one.trans ⟨_, _⟩)
  · rintro ⟨y, rfl⟩
    simp
    
  · exact fun h => ⟨x, eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => h _ hy _ hx⟩⟩
    

theorem card_le_one_iff : s.card ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  rw [card_le_one]
  tauto

theorem card_le_one_iff_subset_singleton [Nonempty α] : s.card ≤ 1 ↔ ∃ x : α, s ⊆ {x} := by
  refine' ⟨fun H => _, _⟩
  · obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
    · exact ⟨Classical.arbitrary α, empty_subset _⟩
      
    · exact
        ⟨x, fun y hy => by
          rw [card_le_one.1 H y hy x hx, mem_singleton]⟩
      
    
  · rintro ⟨x, hx⟩
    rw [← card_singleton x]
    exact card_le_of_subset hx
    

/-- A `finset` of a subsingleton type has cardinality at most one. -/
theorem card_le_one_of_subsingleton [Subsingleton α] (s : Finset α) : s.card ≤ 1 :=
  Finset.card_le_one_iff.2 fun _ _ _ _ => Subsingleton.elimₓ _ _

theorem one_lt_card : 1 < s.card ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  rw [← not_iff_not]
  push_neg
  exact card_le_one

theorem one_lt_card_iff : 1 < s.card ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  rw [one_lt_card]
  simp only [← exists_prop, ← exists_and_distrib_left]

theorem two_lt_card_iff : 2 < s.card ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  refine' ⟨fun h => _, _⟩
  · obtain ⟨c, hc⟩ := card_pos.mp (zero_lt_two.trans h)
    have : 1 < (s.erase c).card := by
      rwa [← add_lt_add_iff_right 1, card_erase_add_one hc]
    obtain ⟨a, b, ha, hb, hab⟩ := one_lt_card_iff.mp this
    exact ⟨a, b, c, mem_of_mem_erase ha, mem_of_mem_erase hb, hc, hab, ne_of_mem_erase ha, ne_of_mem_erase hb⟩
    
  · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
    rw [← card_erase_add_one hc, ← card_erase_add_one (mem_erase_of_ne_of_mem hbc hb), ←
      card_erase_add_one (mem_erase_of_ne_of_mem hab (mem_erase_of_ne_of_mem hac ha))]
    apply Nat.le_add_leftₓ
    

theorem two_lt_card : 2 < s.card ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [two_lt_card_iff, exists_prop, exists_and_distrib_left]

theorem exists_ne_of_one_lt_card (hs : 1 < s.card) (a : α) : ∃ b, b ∈ s ∧ b ≠ a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := finset.one_lt_card.mp hs
  by_cases' ha : y = a
  · exact ⟨x, hx, ne_of_ne_of_eq hxy ha⟩
    
  · exact ⟨y, hy, ha⟩
    

theorem card_eq_succ [DecidableEq α] : s.card = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.card = n :=
  ⟨fun h =>
    let ⟨a, has⟩ := card_pos.mp (h.symm ▸ Nat.zero_lt_succₓ _ : 0 < s.card)
    ⟨a, s.erase a, s.not_mem_erase a, insert_erase has, by
      simp only [← h, ← card_erase_of_mem has, ← add_tsub_cancel_right]⟩,
    fun ⟨a, t, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ card_insert_of_not_mem hat⟩

theorem card_eq_two [DecidableEq α] : s.card = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  constructor
  · rw [card_eq_succ]
    simp_rw [card_eq_one]
    rintro ⟨a, _, hab, rfl, b, rfl⟩
    exact ⟨a, b, not_mem_singleton.1 hab, rfl⟩
    
  · rintro ⟨x, y, h, rfl⟩
    exact card_doubleton h
    

theorem card_eq_three [DecidableEq α] : s.card = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  constructor
  · rw [card_eq_succ]
    simp_rw [card_eq_two]
    rintro ⟨a, _, abc, rfl, b, c, bc, rfl⟩
    rw [mem_insert, mem_singleton, not_or_distrib] at abc
    exact ⟨a, b, c, abc.1, abc.2, bc, rfl⟩
    
  · rintro ⟨x, y, z, xy, xz, yz, rfl⟩
    simp only [← xy, ← xz, ← yz, ← mem_insert, ← card_insert_of_not_mem, ← not_false_iff, ← mem_singleton, ← or_selfₓ, ←
      card_singleton]
    

/-! ### Inductions -/


-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊂ » s)
/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
def strongInductionₓ {p : Finset α → Sort _} (H : ∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s) : ∀ s : Finset α, p s
  | s =>
    H s fun t h =>
      have : t.card < s.card := card_lt_card h
      strong_induction t

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊂ » s)
theorem strong_induction_eq {p : Finset α → Sort _} (H : ∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s) (s : Finset α) :
    strongInductionₓ H s = H s fun t h => strongInductionₓ H t := by
  rw [strong_induction]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊂ » s)
/-- Analogue of `strong_induction` with order of arguments swapped. -/
@[elab_as_eliminator]
def strongInductionOn {p : Finset α → Sort _} (s : Finset α) : (∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s) → p s := fun H =>
  strongInductionₓ H s

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊂ » s)
theorem strong_induction_on_eq {p : Finset α → Sort _} (s : Finset α) (H : ∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s) :
    s.strong_induction_on H = H s fun t h => t.strong_induction_on H := by
  dunfold strong_induction_on
  rw [strong_induction]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
@[elab_as_eliminator]
theorem case_strong_induction_on [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h₀ : p ∅)
    (h₁ : ∀ a s, a ∉ s → (∀ (t) (_ : t ⊆ s), p t) → p (insert a s)) : p s :=
  (Finset.strongInductionOn s) fun s =>
    (Finset.induction_on s fun _ => h₀) fun a s n _ ih =>
      (h₁ a s n) fun t ss => ih _ (lt_of_le_of_ltₓ ss (ssubset_insert n) : t < _)

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all finsets `s` of
cardinality less than `n`, starting from finsets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strongDownwardInductionₓ {p : Finset α → Sort _} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    ∀ s : Finset α, s.card ≤ n → p s
  | s =>
    H s fun t ht h =>
      have : n - t.card < n - s.card := (tsub_lt_tsub_iff_left_of_le ht).2 (Finset.card_lt_card h)
      strong_downward_induction t ht

theorem strong_downward_induction_eq {p : Finset α → Sort _}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) (s : Finset α) :
    strongDownwardInductionₓ H s = H s fun t ht hst => strongDownwardInductionₓ H t ht := by
  rw [strong_downward_induction]

/-- Analogue of `strong_downward_induction` with order of arguments swapped. -/
@[elab_as_eliminator]
def strongDownwardInductionOn {p : Finset α → Sort _} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) : s.card ≤ n → p s :=
  strongDownwardInductionₓ H s

theorem strong_downward_induction_on_eq {p : Finset α → Sort _} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun t ht h => t.strongDownwardInductionOn H ht := by
  dunfold strong_downward_induction_on
  rw [strong_downward_induction]

theorem lt_wf {α} : WellFounded (@LT.lt (Finset α) _) :=
  have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) card) := fun x y hxy => card_lt_card hxy
  Subrelation.wfₓ H <| InvImage.wfₓ _ <| Nat.lt_wf

end Finset

