/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Patrick Massot
-/
import Mathbin.Data.Set.Basic

/-!
# Sets in product and pi types

This file defines the product of sets in `α × β` and in `Π i, α i` along with the diagonal of a
type.

## Main declarations

* `set.prod`: Binary product of sets. For `s : set α`, `t : set β`, we have
  `s.prod t : set (α × β)`.
* `set.diagonal`: Diagonal of a type. `set.diagonal α = {(x, x) | x : α}`.
* `set.pi`: Arbitrary product of sets.
-/


open Function

/-- Notation class for product of subobjects (sets, submonoids, subgroups, etc). -/
class HasSetProd (α β : Type _) (γ : outParam (Type _)) where
  Prod : α → β → γ

-- mathport name: «expr ×ˢ »
infixr:82
  " ×ˢ " =>-- This notation binds more strongly than (pre)images, unions and intersections.
  HasSetProd.prod

namespace Set

/-! ### Cartesian binary product of sets -/


section Prod

variable {α β γ δ : Type _} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

/-- The cartesian product `prod s t` is the set of `(a, b)`
  such that `a ∈ s` and `b ∈ t`. -/
instance : HasSetProd (Set α) (Set β) (Set (α × β)) :=
  ⟨fun s t => { p | p.1 ∈ s ∧ p.2 ∈ t }⟩

theorem prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t :=
  rfl

theorem mem_prod_eq {p : α × β} : (p ∈ s ×ˢ t) = (p.1 ∈ s ∧ p.2 ∈ t) :=
  rfl

@[simp]
theorem mem_prod {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[simp]
theorem prod_mk_mem_set_prod_eq : ((a, b) ∈ s ×ˢ t) = (a ∈ s ∧ b ∈ t) :=
  rfl

theorem mk_mem_prod (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t :=
  ⟨ha, hb⟩

theorem prod_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ×ˢ t₁ ⊆ s₂ ×ˢ t₂ := fun x ⟨h₁, h₂⟩ => ⟨hs h₁, ht h₂⟩

@[simp]
theorem prod_self_subset_prod_self : s₁ ×ˢ s₁ ⊆ s₂ ×ˢ s₂ ↔ s₁ ⊆ s₂ :=
  ⟨fun h x hx => (h (mk_mem_prod hx hx)).1, fun h x hx => ⟨h hx.1, h hx.2⟩⟩

@[simp]
theorem prod_self_ssubset_prod_self : s₁ ×ˢ s₁ ⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂ :=
  and_congr prod_self_subset_prod_self <| not_congr prod_self_subset_prod_self

theorem prod_subset_iff {P : Set (α × β)} : s ×ˢ t ⊆ P ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, (x, y) ∈ P :=
  ⟨fun h _ hx _ hy => h (mk_mem_prod hx hy), fun h ⟨_, _⟩ hp => h _ hp.1 _ hp.2⟩

theorem forall_prod_set {p : α × β → Prop} : (∀, ∀ x ∈ s ×ˢ t, ∀, p x) ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, p (x, y) :=
  prod_subset_iff

theorem exists_prod_set {p : α × β → Prop} : (∃ x ∈ s ×ˢ t, p x) ↔ ∃ x ∈ s, ∃ y ∈ t, p (x, y) := by
  simp [← and_assoc]

@[simp]
theorem prod_empty : s ×ˢ (∅ : Set β) = ∅ := by
  ext
  exact and_falseₓ _

@[simp]
theorem empty_prod : (∅ : Set α) ×ˢ t = ∅ := by
  ext
  exact false_andₓ _

@[simp]
theorem univ_prod_univ : @Univ α ×ˢ @Univ β = univ := by
  ext
  exact true_andₓ _

theorem univ_prod {t : Set β} : (Univ : Set α) ×ˢ t = Prod.snd ⁻¹' t := by
  simp [← prod_eq]

theorem prod_univ {s : Set α} : s ×ˢ (Univ : Set β) = Prod.fst ⁻¹' s := by
  simp [← prod_eq]

@[simp]
theorem singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t := by
  ext ⟨x, y⟩
  simp [← And.left_comm, ← eq_comm]

@[simp]
theorem prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, b)) '' s := by
  ext ⟨x, y⟩
  simp [← And.left_comm, ← eq_comm]

theorem singleton_prod_singleton : ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)} := by
  simp

@[simp]
theorem union_prod : (s₁ ∪ s₂) ×ˢ t = s₁ ×ˢ t ∪ s₂ ×ˢ t := by
  ext ⟨x, y⟩
  simp [← or_and_distrib_right]

@[simp]
theorem prod_union : s ×ˢ (t₁ ∪ t₂) = s ×ˢ t₁ ∪ s ×ˢ t₂ := by
  ext ⟨x, y⟩
  simp [← and_or_distrib_left]

theorem prod_inter_prod : s₁ ×ˢ t₁ ∩ s₂ ×ˢ t₂ = (s₁ ∩ s₂) ×ˢ (t₁ ∩ t₂) := by
  ext ⟨x, y⟩
  simp [← and_assoc, ← And.left_comm]

theorem insert_prod : insert a s ×ˢ t = Prod.mk a '' t ∪ s ×ˢ t := by
  ext ⟨x, y⟩
  simp (config := { contextual := true })[← image, ← iff_def, ← or_imp_distrib, ← Imp.swap]

theorem prod_insert : s ×ˢ insert b t = (fun a => (a, b)) '' s ∪ s ×ˢ t := by
  ext ⟨x, y⟩
  simp (config := { contextual := true })[← image, ← iff_def, ← or_imp_distrib, ← Imp.swap]

theorem prod_preimage_eq {f : γ → α} {g : δ → β} :
    (f ⁻¹' s) ×ˢ (g ⁻¹' t) = (fun p : γ × δ => (f p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl

theorem prod_preimage_left {f : γ → α} : (f ⁻¹' s) ×ˢ t = (fun p : γ × β => (f p.1, p.2)) ⁻¹' s ×ˢ t :=
  rfl

theorem prod_preimage_right {g : δ → β} : s ×ˢ (g ⁻¹' t) = (fun p : α × δ => (p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl

theorem preimage_prod_map_prod (f : α → β) (g : γ → δ) (s : Set β) (t : Set δ) :
    Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) :=
  rfl

theorem mk_preimage_prod (f : γ → α) (g : γ → β) : (fun x => (f x, g x)) ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl

@[simp]
theorem mk_preimage_prod_left (hb : b ∈ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = s := by
  ext a
  simp [← hb]

@[simp]
theorem mk_preimage_prod_right (ha : a ∈ s) : Prod.mk a ⁻¹' s ×ˢ t = t := by
  ext b
  simp [← ha]

@[simp]
theorem mk_preimage_prod_left_eq_empty (hb : b ∉ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = ∅ := by
  ext a
  simp [← hb]

@[simp]
theorem mk_preimage_prod_right_eq_empty (ha : a ∉ s) : Prod.mk a ⁻¹' s ×ˢ t = ∅ := by
  ext b
  simp [← ha]

theorem mk_preimage_prod_left_eq_if [DecidablePred (· ∈ t)] : (fun a => (a, b)) ⁻¹' s ×ˢ t = if b ∈ t then s else ∅ :=
  by
  split_ifs <;> simp [← h]

theorem mk_preimage_prod_right_eq_if [DecidablePred (· ∈ s)] : Prod.mk a ⁻¹' s ×ˢ t = if a ∈ s then t else ∅ := by
  split_ifs <;> simp [← h]

theorem mk_preimage_prod_left_fn_eq_if [DecidablePred (· ∈ t)] (f : γ → α) :
    (fun a => (f a, b)) ⁻¹' s ×ˢ t = if b ∈ t then f ⁻¹' s else ∅ := by
  rw [← mk_preimage_prod_left_eq_if, prod_preimage_left, preimage_preimage]

theorem mk_preimage_prod_right_fn_eq_if [DecidablePred (· ∈ s)] (g : δ → β) :
    (fun b => (a, g b)) ⁻¹' s ×ˢ t = if a ∈ s then g ⁻¹' t else ∅ := by
  rw [← mk_preimage_prod_right_eq_if, prod_preimage_right, preimage_preimage]

theorem preimage_swap_prod {s : Set α} {t : Set β} : Prod.swap ⁻¹' t ×ˢ s = s ×ˢ t := by
  ext ⟨x, y⟩
  simp [← and_comm]

theorem image_swap_prod : Prod.swap '' t ×ˢ s = s ×ˢ t := by
  rw [image_swap_eq_preimage_swap, preimage_swap_prod]

theorem prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
    (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t :=
  ext <| by
    simp [-exists_and_distrib_right, ← exists_and_distrib_right.symm, ← And.left_comm, ← And.assoc, ← And.comm]

theorem prod_range_range_eq {m₁ : α → γ} {m₂ : β → δ} :
    Range m₁ ×ˢ Range m₂ = Range fun p : α × β => (m₁ p.1, m₂ p.2) :=
  ext <| by
    simp [← range]

@[simp]
theorem range_prod_map {m₁ : α → γ} {m₂ : β → δ} : Range (Prod.map m₁ m₂) = Range m₁ ×ˢ Range m₂ :=
  prod_range_range_eq.symm

theorem prod_range_univ_eq {m₁ : α → γ} : Range m₁ ×ˢ (Univ : Set β) = Range fun p : α × β => (m₁ p.1, p.2) :=
  ext <| by
    simp [← range]

theorem prod_univ_range_eq {m₂ : β → δ} : (Univ : Set α) ×ˢ Range m₂ = Range fun p : α × β => (p.1, m₂ p.2) :=
  ext <| by
    simp [← range]

theorem range_pair_subset (f : α → β) (g : α → γ) : (Range fun x => (f x, g x)) ⊆ Range f ×ˢ Range g := by
  have : (fun x => (f x, g x)) = Prod.map f g ∘ fun x => (x, x) := funext fun x => rfl
  rw [this, ← range_prod_map]
  apply range_comp_subset_range

theorem Nonempty.prod : s.Nonempty → t.Nonempty → (s ×ˢ t : Set _).Nonempty := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨(x, y), ⟨hx, hy⟩⟩

theorem Nonempty.fst : (s ×ˢ t : Set _).Nonempty → s.Nonempty := fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩

theorem Nonempty.snd : (s ×ˢ t : Set _).Nonempty → t.Nonempty := fun ⟨x, hx⟩ => ⟨x.2, hx.2⟩

theorem prod_nonempty_iff : (s ×ˢ t : Set _).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.Prod h.2⟩

theorem prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp only [← not_nonempty_iff_eq_empty.symm, ← prod_nonempty_iff, ← not_and_distrib]

theorem prod_sub_preimage_iff {W : Set γ} {f : α × β → γ} : s ×ˢ t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W := by
  simp [← subset_def]

theorem image_prod_mk_subset_prod_left (hb : b ∈ t) : (fun a => (a, b)) '' s ⊆ s ×ˢ t := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨ha, hb⟩

theorem image_prod_mk_subset_prod_right (ha : a ∈ s) : Prod.mk a '' t ⊆ s ×ˢ t := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨ha, hb⟩

theorem prod_subset_preimage_fst (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.fst ⁻¹' s :=
  inter_subset_left _ _

theorem fst_image_prod_subset (s : Set α) (t : Set β) : Prod.fst '' s ×ˢ t ⊆ s :=
  image_subset_iff.2 <| prod_subset_preimage_fst s t

theorem fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonempty) : Prod.fst '' s ×ˢ t = s :=
  (fst_image_prod_subset _ _).antisymm fun y hy =>
    let ⟨x, hx⟩ := ht
    ⟨(y, x), ⟨hy, hx⟩, rfl⟩

theorem prod_subset_preimage_snd (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.snd ⁻¹' t :=
  inter_subset_right _ _

theorem snd_image_prod_subset (s : Set α) (t : Set β) : Prod.snd '' s ×ˢ t ⊆ t :=
  image_subset_iff.2 <| prod_subset_preimage_snd s t

theorem snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Set β) : Prod.snd '' s ×ˢ t = t :=
  (snd_image_prod_subset _ _).antisymm fun y y_in =>
    let ⟨x, x_in⟩ := hs
    ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩

theorem prod_diff_prod : s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁) ∪ (s \ s₁) ×ˢ t := by
  ext x
  by_cases' h₁ : x.1 ∈ s₁ <;> by_cases' h₂ : x.2 ∈ t₁ <;> simp [*]

/-- A product set is included in a product set if and only factors are included, or a factor of the
first set is empty. -/
theorem prod_subset_prod_iff : s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  cases' (s ×ˢ t : Set _).eq_empty_or_nonempty with h h
  · simp [← h, ← prod_eq_empty_iff.1 h]
    
  have st : s.nonempty ∧ t.nonempty := by
    rwa [prod_nonempty_iff] at h
  refine' ⟨fun H => Or.inl ⟨_, _⟩, _⟩
  · have := image_subset (Prod.fst : α × β → α) H
    rwa [fst_image_prod _ st.2, fst_image_prod _ (h.mono H).snd] at this
    
  · have := image_subset (Prod.snd : α × β → β) H
    rwa [snd_image_prod st.1, snd_image_prod (h.mono H).fst] at this
    
  · intro H
    simp only [← st.1.ne_empty, ← st.2.ne_empty, ← or_falseₓ] at H
    exact prod_mono H.1 H.2
    

theorem prod_eq_prod_iff_of_nonempty (h : (s ×ˢ t : Set _).Nonempty) : s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ := by
  constructor
  · intro heq
    have h₁ : (s₁ ×ˢ t₁ : Set _).Nonempty := by
      rwa [← HEq]
    rw [prod_nonempty_iff] at h h₁
    rw [← fst_image_prod s h.2, ← fst_image_prod s₁ h₁.2, HEq, eq_self_iff_true, true_andₓ, ← snd_image_prod h.1 t, ←
      snd_image_prod h₁.1 t₁, HEq]
    
  · rintro ⟨rfl, rfl⟩
    rfl
    

theorem prod_eq_prod_iff : s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧ (s₁ = ∅ ∨ t₁ = ∅) := by
  symm
  cases' eq_empty_or_nonempty (s ×ˢ t) with h h
  · simp_rw [h, @eq_comm _ ∅, prod_eq_empty_iff, prod_eq_empty_iff.mp h, true_andₓ, or_iff_right_iff_imp]
    rintro ⟨rfl, rfl⟩
    exact prod_eq_empty_iff.mp h
    
  rw [prod_eq_prod_iff_of_nonempty h]
  rw [← ne_empty_iff_nonempty, Ne.def, prod_eq_empty_iff] at h
  simp_rw [h, false_andₓ, or_falseₓ]

@[simp]
theorem prod_eq_iff_eq (ht : t.Nonempty) : s ×ˢ t = s₁ ×ˢ t ↔ s = s₁ := by
  simp_rw [prod_eq_prod_iff, ht.ne_empty, eq_self_iff_true, and_trueₓ, or_iff_left_iff_imp, or_falseₓ]
  rintro ⟨rfl, rfl⟩
  rfl

@[simp]
theorem image_prod (f : α → β → γ) : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = Image2 f s t :=
  Set.ext fun a =>
    ⟨by
      rintro ⟨_, _, rfl⟩
      exact ⟨_, _, (mem_prod.mp ‹_›).1, (mem_prod.mp ‹_›).2, rfl⟩, by
      rintro ⟨_, _, _, _, rfl⟩
      exact ⟨(_, _), mem_prod.mpr ⟨‹_›, ‹_›⟩, rfl⟩⟩

@[simp]
theorem image2_mk_eq_prod : Image2 Prod.mk s t = s ×ˢ t :=
  ext <| by
    simp

section Mono

variable [Preorderₓ α] {f : α → Set β} {g : α → Set γ}

theorem _root_.monotone.set_prod (hf : Monotone f) (hg : Monotone g) : Monotone fun x => f x ×ˢ g x := fun a b h =>
  prod_mono (hf h) (hg h)

theorem _root_.antitone.set_prod (hf : Antitone f) (hg : Antitone g) : Antitone fun x => f x ×ˢ g x := fun a b h =>
  prod_mono (hf h) (hg h)

theorem _root_.monotone_on.set_prod (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ×ˢ g x) s :=
  fun a ha b hb h => prod_mono (hf ha hb h) (hg ha hb h)

theorem _root_.antitone_on.set_prod (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ×ˢ g x) s :=
  fun a ha b hb h => prod_mono (hf ha hb h) (hg ha hb h)

end Mono

end Prod

/-! ### Diagonal -/


section Diagonal

variable {α : Type _} {s t : Set α}

/-- `diagonal α` is the set of `α × α` consisting of all pairs of the form `(a, a)`. -/
def Diagonal (α : Type _) : Set (α × α) :=
  { p | p.1 = p.2 }

theorem mem_diagonal (x : α) : (x, x) ∈ Diagonal α := by
  simp [← diagonal]

@[simp]
theorem mem_diagonal_iff {x : α × α} : x ∈ Diagonal α ↔ x.1 = x.2 :=
  Iff.rfl

theorem preimage_coe_coe_diagonal (s : Set α) : Prod.map coe coe ⁻¹' Diagonal α = Diagonal s := by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp [← Set.Diagonal]

theorem diagonal_eq_range : Diagonal α = Range fun x => (x, x) := by
  ext ⟨x, y⟩
  simp [← diagonal, ← eq_comm]

@[simp]
theorem prod_subset_compl_diagonal_iff_disjoint : s ×ˢ t ⊆ Diagonal αᶜ ↔ Disjoint s t :=
  subset_compl_comm.trans <| by
    simp_rw [diagonal_eq_range, range_subset_iff, disjoint_left, mem_compl_iff, prod_mk_mem_set_prod_eq, not_and]

end Diagonal

/-! ### Cartesian set-indexed product of sets -/


section Pi

variable {ι : Type _} {α β : ι → Type _} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)} {i : ι}

/-- Given an index set `ι` and a family of sets `t : Π i, set (α i)`, `pi s t`
is the set of dependent functions `f : Πa, π a` such that `f a` belongs to `t a`
whenever `a ∈ s`. -/
def Pi (s : Set ι) (t : ∀ i, Set (α i)) : Set (∀ i, α i) :=
  { f | ∀, ∀ i ∈ s, ∀, f i ∈ t i }

@[simp]
theorem mem_pi {f : ∀ i, α i} : f ∈ s.pi t ↔ ∀, ∀ i ∈ s, ∀, f i ∈ t i :=
  Iff.rfl

@[simp]
theorem mem_univ_pi {f : ∀ i, α i} : f ∈ Pi Univ t ↔ ∀ i, f i ∈ t i := by
  simp

@[simp]
theorem empty_pi (s : ∀ i, Set (α i)) : Pi ∅ s = univ := by
  ext
  simp [← pi]

@[simp]
theorem pi_univ (s : Set ι) : (Pi s fun i => (Univ : Set (α i))) = univ :=
  eq_univ_of_forall fun f i hi => mem_univ _

theorem pi_mono (h : ∀, ∀ i ∈ s, ∀, t₁ i ⊆ t₂ i) : Pi s t₁ ⊆ Pi s t₂ := fun x hx i hi => h i hi <| hx i hi

theorem pi_inter_distrib : (s.pi fun i => t i ∩ t₁ i) = s.pi t ∩ s.pi t₁ :=
  ext fun x => by
    simp only [← forall_and_distrib, ← mem_pi, ← mem_inter_eq]

theorem pi_congr (h : s₁ = s₂) (h' : ∀, ∀ i ∈ s₁, ∀, t₁ i = t₂ i) : s₁.pi t₁ = s₂.pi t₂ :=
  h ▸ ext fun x => forall₂_congrₓ fun i hi => h' i hi ▸ Iff.rfl

theorem pi_eq_empty (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ := by
  ext f
  simp only [← mem_empty_eq, ← not_forall, ← iff_falseₓ, ← mem_pi, ← not_imp]
  exact
    ⟨i, hs, by
      simp [← ht]⟩

theorem univ_pi_eq_empty (ht : t i = ∅) : Pi Univ t = ∅ :=
  pi_eq_empty (mem_univ i) ht

theorem pi_nonempty_iff : (s.pi t).Nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i := by
  simp [← Classical.skolem, ← Set.Nonempty]

theorem univ_pi_nonempty_iff : (Pi Univ t).Nonempty ↔ ∀ i, (t i).Nonempty := by
  simp [← Classical.skolem, ← Set.Nonempty]

theorem pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, IsEmpty (α i) ∨ i ∈ s ∧ t i = ∅ := by
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff]
  push_neg
  refine' exists_congr fun i => ⟨fun h => (is_empty_or_nonempty (α i)).imp_right _, _⟩
  · rintro ⟨x⟩
    exact
      ⟨(h x).1, by
        simp [← eq_empty_iff_forall_not_mem, ← h]⟩
    
  · rintro (h | h) x
    · exact h.elim' x
      
    · simp [← h]
      
    

theorem univ_pi_eq_empty_iff : Pi Univ t = ∅ ↔ ∃ i, t i = ∅ := by
  simp [not_nonempty_iff_eq_empty, ← univ_pi_nonempty_iff]

@[simp]
theorem univ_pi_empty [h : Nonempty ι] : Pi Univ (fun i => ∅ : ∀ i, Set (α i)) = ∅ :=
  univ_pi_eq_empty_iff.2 <| h.elim fun x => ⟨x, rfl⟩

@[simp]
theorem range_dcomp (f : ∀ i, α i → β i) :
    (Range fun g : ∀ i, α i => fun i => f i (g i)) = Pi Univ fun i => Range (f i) := by
  apply subset.antisymm _ fun x hx => _
  · rintro _ ⟨x, rfl⟩ i -
    exact ⟨x i, rfl⟩
    
  · choose y hy using hx
    exact ⟨fun i => y i trivialₓ, funext fun i => hy i trivialₓ⟩
    

@[simp]
theorem insert_pi (i : ι) (s : Set ι) (t : ∀ i, Set (α i)) : Pi (insert i s) t = eval i ⁻¹' t i ∩ Pi s t := by
  ext
  simp [← pi, ← or_imp_distrib, ← forall_and_distrib]

@[simp]
theorem singleton_pi (i : ι) (t : ∀ i, Set (α i)) : Pi {i} t = eval i ⁻¹' t i := by
  ext
  simp [← pi]

theorem singleton_pi' (i : ι) (t : ∀ i, Set (α i)) : Pi {i} t = { x | x i ∈ t i } :=
  singleton_pi i t

theorem univ_pi_singleton (f : ∀ i, α i) : (Pi Univ fun i => {f i}) = ({f} : Set (∀ i, α i)) :=
  ext fun g => by
    simp [← funext_iff]

theorem pi_if {p : ι → Prop} [h : DecidablePred p] (s : Set ι) (t₁ t₂ : ∀ i, Set (α i)) :
    (Pi s fun i => if p i then t₁ i else t₂ i) = Pi ({ i ∈ s | p i }) t₁ ∩ Pi ({ i ∈ s | ¬p i }) t₂ := by
  ext f
  refine' ⟨fun h => _, _⟩
  · constructor <;>
      · rintro i ⟨his, hpi⟩
        simpa [*] using h i
        
    
  · rintro ⟨ht₁, ht₂⟩ i his
    by_cases' p i <;> simp_all
    

theorem union_pi : (s₁ ∪ s₂).pi t = s₁.pi t ∩ s₂.pi t := by
  simp [← pi, ← or_imp_distrib, ← forall_and_distrib, ← set_of_and]

@[simp]
theorem pi_inter_compl (s : Set ι) : Pi s t ∩ Pi (sᶜ) t = Pi Univ t := by
  rw [← union_pi, union_compl_self]

theorem pi_update_of_not_mem [DecidableEq ι] (hi : i ∉ s) (f : ∀ j, α j) (a : α i) (t : ∀ j, α j → Set (β j)) :
    (s.pi fun j => t j (update f i a j)) = s.pi fun j => t j (f j) :=
  (pi_congr rfl) fun j hj => by
    rw [update_noteq]
    exact fun h => hi (h ▸ hj)

theorem pi_update_of_mem [DecidableEq ι] (hi : i ∈ s) (f : ∀ j, α j) (a : α i) (t : ∀ j, α j → Set (β j)) :
    (s.pi fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) :=
  calc
    (s.pi fun j => t j (update f i a j)) = ({i} ∪ s \ {i}).pi fun j => t j (update f i a j) := by
      rw [union_diff_self, union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
    _ = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) := by
      rw [union_pi, singleton_pi', update_same, pi_update_of_not_mem]
      simp
    

theorem univ_pi_update [DecidableEq ι] {β : ∀ i, Type _} (i : ι) (f : ∀ j, α j) (a : α i) (t : ∀ j, α j → Set (β j)) :
    (Pi Univ fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ Pi ({i}ᶜ) fun j => t j (f j) := by
  rw [compl_eq_univ_diff, ← pi_update_of_mem (mem_univ _)]

theorem univ_pi_update_univ [DecidableEq ι] (i : ι) (s : Set (α i)) :
    Pi Univ (update (fun j : ι => (Univ : Set (α j))) i s) = eval i ⁻¹' s := by
  rw [univ_pi_update i (fun j => (univ : Set (α j))) s fun j t => t, pi_univ, inter_univ, preimage]

theorem eval_image_pi_subset (hs : i ∈ s) : eval i '' s.pi t ⊆ t i :=
  image_subset_iff.2 fun f hf => hf i hs

theorem eval_image_univ_pi_subset : eval i '' Pi Univ t ⊆ t i :=
  eval_image_pi_subset (mem_univ i)

theorem eval_image_pi (hs : i ∈ s) (ht : (s.pi t).Nonempty) : eval i '' s.pi t = t i := by
  refine' (eval_image_pi_subset hs).antisymm _
  classical
  obtain ⟨f, hf⟩ := ht
  refine' fun y hy => ⟨update f i y, fun j hj => _, update_same _ _ _⟩
  obtain rfl | hji := eq_or_ne j i <;> simp [*, ← hf _ hj]

@[simp]
theorem eval_image_univ_pi (ht : (Pi Univ t).Nonempty) : (fun f : ∀ i, α i => f i) '' Pi Univ t = t i :=
  eval_image_pi (mem_univ i) ht

theorem eval_preimage [DecidableEq ι] {s : Set (α i)} : eval i ⁻¹' s = Pi Univ (update (fun i => Univ) i s) := by
  ext x
  simp [← @forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]

theorem eval_preimage' [DecidableEq ι] {s : Set (α i)} : eval i ⁻¹' s = Pi {i} (update (fun i => Univ) i s) := by
  ext
  simp

theorem update_preimage_pi [DecidableEq ι] {f : ∀ i, α i} (hi : i ∈ s) (hf : ∀, ∀ j ∈ s, ∀, j ≠ i → f j ∈ t j) :
    update f i ⁻¹' s.pi t = t i := by
  ext x
  refine' ⟨fun h => _, fun hx j hj => _⟩
  · convert h i hi
    simp
    
  · obtain rfl | h := eq_or_ne j i
    · simpa
      
    · rw [update_noteq h]
      exact hf j hj h
      
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
theorem update_preimage_univ_pi [DecidableEq ι] {f : ∀ i, α i} (hf : ∀ (j) (_ : j ≠ i), f j ∈ t j) :
    update f i ⁻¹' Pi Univ t = t i :=
  update_preimage_pi (mem_univ i) fun j _ => hf j

theorem subset_pi_eval_image (s : Set ι) (u : Set (∀ i, α i)) : u ⊆ Pi s fun i => eval i '' u := fun f hf i hi =>
  ⟨f, hf, rfl⟩

theorem univ_pi_ite (s : Set ι) [DecidablePred (· ∈ s)] (t : ∀ i, Set (α i)) :
    (Pi Univ fun i => if i ∈ s then t i else Univ) = s.pi t := by
  ext
  simp_rw [mem_univ_pi]
  refine' forall_congrₓ fun i => _
  split_ifs <;> simp [← h]

end Pi

end Set

