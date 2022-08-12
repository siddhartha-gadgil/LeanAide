/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Nat.Basic
import Mathbin.Order.CompleteBooleanAlgebra
import Mathbin.Order.Directed
import Mathbin.Order.GaloisConnection

/-!
# The set lattice

This file provides usual set notation for unions and intersections, a `complete_lattice` instance
for `set α`, and some more set constructions.

## Main declarations

* `set.Union`: Union of an indexed family of sets.
* `set.Inter`: Intersection of an indexed family of sets.
* `set.sInter`: **s**et **Inter**. Intersection of sets belonging to a set of sets.
* `set.sUnion`: **s**et **Union**. Union of sets belonging to a set of sets. This is actually
  defined in core Lean.
* `set.sInter_eq_bInter`, `set.sUnion_eq_bInter`: Shows that `⋂₀ s = ⋂ x ∈ s, x` and
  `⋃₀ s = ⋃ x ∈ s, x`.
* `set.complete_boolean_algebra`: `set α` is a `complete_boolean_algebra` with `≤ = ⊆`, `< = ⊂`,
  `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference. See `set.boolean_algebra`.
* `set.kern_image`: For a function `f : α → β`, `s.kern_image f` is the set of `y` such that
  `f ⁻¹ y ⊆ s`.
* `set.seq`: Union of the image of a set under a **seq**uence of functions. `seq s t` is the union
  of `f '' t` over all `f ∈ s`, where `t : set α` and `s : set (α → β)`.
* `set.Union_eq_sigma_of_disjoint`: Equivalence between `⋃ i, t i` and `Σ i, t i`, where `t` is an
  indexed family of disjoint sets.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `Union`
* `⋂ i, s i` is called `Inter`
* `⋃ i j, s i j` is called `Union₂`. This is a `Union` inside a `Union`.
* `⋂ i j, s i j` is called `Inter₂`. This is an `Inter` inside an `Inter`.
* `⋃ i ∈ s, t i` is called `bUnion` for "bounded `Union`". This is the special case of `Union₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `bInter` for "bounded `Inter`". This is the special case of `Inter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `set.Union`
* `⋂`: `set.Inter`
* `⋃₀`: `set.sUnion`
* `⋂₀`: `set.sInter`
-/


open Function Tactic Set

universe u

variable {α β γ : Type _} {ι ι' ι₂ : Sort _} {κ κ₁ κ₂ : ι → Sort _} {κ' : ι' → Sort _}

namespace Set

/-! ### Complete lattice and complete Boolean algebra instances -/


instance : HasInfₓ (Set α) :=
  ⟨fun s => { a | ∀, ∀ t ∈ s, ∀, a ∈ t }⟩

instance : HasSupₓ (Set α) :=
  ⟨fun s => { a | ∃ t ∈ s, a ∈ t }⟩

/-- Intersection of a set of sets. -/
def SInter (S : Set (Set α)) : Set α :=
  inf S

/-- Union of a set of sets. -/
def SUnion (S : Set (Set α)) : Set α :=
  sup S

-- mathport name: «expr⋂₀ »
prefix:110 "⋂₀ " => SInter

@[simp]
theorem mem_sInter {x : α} {S : Set (Set α)} : x ∈ ⋂₀ S ↔ ∀, ∀ t ∈ S, ∀, x ∈ t :=
  Iff.rfl

@[simp]
theorem mem_sUnion {x : α} {S : Set (Set α)} : x ∈ ⋃₀S ↔ ∃ t ∈ S, x ∈ t :=
  Iff.rfl

/-- Indexed union of a family of sets -/
def Union (s : ι → Set β) : Set β :=
  supr s

/-- Indexed intersection of a family of sets -/
def Inter (s : ι → Set β) : Set β :=
  infi s

-- mathport name: «expr⋃ , »
notation3"⋃ "(...)", "r:(scoped f => Union f) => r

-- mathport name: «expr⋂ , »
notation3"⋂ "(...)", "r:(scoped f => Inter f) => r

@[simp]
theorem Sup_eq_sUnion (S : Set (Set α)) : sup S = ⋃₀S :=
  rfl

@[simp]
theorem Inf_eq_sInter (S : Set (Set α)) : inf S = ⋂₀ S :=
  rfl

@[simp]
theorem supr_eq_Union (s : ι → Set α) : supr s = Union s :=
  rfl

@[simp]
theorem infi_eq_Inter (s : ι → Set α) : infi s = Inter s :=
  rfl

@[simp]
theorem mem_Union {x : α} {s : ι → Set α} : (x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i :=
  ⟨fun ⟨t, ⟨⟨a, (t_eq : s a = t)⟩, (h : x ∈ t)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ => ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩

@[simp]
theorem mem_Inter {x : α} {s : ι → Set α} : (x ∈ ⋂ i, s i) ↔ ∀ i, x ∈ s i :=
  ⟨fun (h : ∀, ∀ a ∈ { a : Set α | ∃ i, s i = a }, ∀, x ∈ a) a => h (s a) ⟨a, rfl⟩, fun h t ⟨a, (Eq : s a = t)⟩ =>
    Eq ▸ h a⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem mem_Union₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋃ (i) (j), s i j) ↔ ∃ i j, x ∈ s i j := by
  simp_rw [mem_Union]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem mem_Inter₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋂ (i) (j), s i j) ↔ ∀ i j, x ∈ s i j := by
  simp_rw [mem_Inter]

theorem mem_Union_of_mem {s : ι → Set α} {a : α} (i : ι) (ha : a ∈ s i) : a ∈ ⋃ i, s i :=
  mem_Union.2 ⟨i, ha⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem mem_Union₂_of_mem {s : ∀ i, κ i → Set α} {a : α} {i : ι} (j : κ i) (ha : a ∈ s i j) : a ∈ ⋃ (i) (j), s i j :=
  mem_Union₂.2 ⟨i, j, ha⟩

theorem mem_Inter_of_mem {s : ι → Set α} {a : α} (h : ∀ i, a ∈ s i) : a ∈ ⋂ i, s i :=
  mem_Inter.2 h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem mem_Inter₂_of_mem {s : ∀ i, κ i → Set α} {a : α} (h : ∀ i j, a ∈ s i j) : a ∈ ⋂ (i) (j), s i j :=
  mem_Inter₂.2 h

instance : CompleteBooleanAlgebra (Set α) :=
  { Set.booleanAlgebra with sup := sup, inf := inf, le_Sup := fun s t t_in a a_in => ⟨t, ⟨t_in, a_in⟩⟩,
    Sup_le := fun s t h a ⟨t', ⟨t'_in, a_in⟩⟩ => h t' t'_in a_in,
    le_Inf := fun s t h a a_in t' t'_in => h t' t'_in a_in, Inf_le := fun s t t_in a h => h _ t_in,
    infi_sup_le_sup_Inf := fun s S x =>
      Iff.mp <| by
        simp [← forall_or_distrib_left],
    inf_Sup_le_supr_inf := fun s S x =>
      Iff.mp <| by
        simp [← exists_and_distrib_left] }

/-- `set.image` is monotone. See `set.image_image` for the statement in terms of `⊆`. -/
theorem monotone_image {f : α → β} : Monotone (Image f) := fun s t => image_subset _

theorem _root_.monotone.inter [Preorderₓ β] {f g : β → Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ∩ g x :=
  hf.inf hg

theorem _root_.monotone_on.inter [Preorderₓ β] {f g : β → Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ∩ g x) s :=
  hf.inf hg

theorem _root_.antitone.inter [Preorderₓ β] {f g : β → Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ∩ g x :=
  hf.inf hg

theorem _root_.antitone_on.inter [Preorderₓ β] {f g : β → Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ∩ g x) s :=
  hf.inf hg

theorem _root_.monotone.union [Preorderₓ β] {f g : β → Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ∪ g x :=
  hf.sup hg

theorem _root_.monotone_on.union [Preorderₓ β] {f g : β → Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ∪ g x) s :=
  hf.sup hg

theorem _root_.antitone.union [Preorderₓ β] {f g : β → Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ∪ g x :=
  hf.sup hg

theorem _root_.antitone_on.union [Preorderₓ β] {f g : β → Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ∪ g x) s :=
  hf.sup hg

theorem monotone_set_of [Preorderₓ α] {p : α → β → Prop} (hp : ∀ b, Monotone fun a => p a b) :
    Monotone fun a => { b | p a b } := fun a a' h b => hp b h

theorem antitone_set_of [Preorderₓ α] {p : α → β → Prop} (hp : ∀ b, Antitone fun a => p a b) :
    Antitone fun a => { b | p a b } := fun a a' h b => hp b h

/-- Quantifying over a set is antitone in the set -/
theorem antitone_bforall {P : α → Prop} : Antitone fun s : Set α => ∀, ∀ x ∈ s, ∀, P x := fun s t hst h x hx =>
  h x <| hst hx

section GaloisConnection

variable {f : α → β}

protected theorem image_preimage : GaloisConnection (Image f) (Preimage f) := fun a b => image_subset_iff

/-- `kern_image f s` is the set of `y` such that `f ⁻¹ y ⊆ s`. -/
def KernImage (f : α → β) (s : Set α) : Set β :=
  { y | ∀ ⦃x⦄, f x = y → x ∈ s }

protected theorem preimage_kern_image : GaloisConnection (Preimage f) (KernImage f) := fun a b =>
  ⟨fun h x hx y hy =>
    have : f y ∈ a := hy.symm ▸ hx
    h this,
    fun h x (hx : f x ∈ a) => h hx rfl⟩

end GaloisConnection

/-! ### Union and intersection over an indexed family of sets -/


instance : OrderTop (Set α) where
  top := Univ
  le_top := by
    simp

@[congr]
theorem Union_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q) (f : ∀ x, f₁ (pq.mpr x) = f₂ x) :
    Union f₁ = Union f₂ :=
  supr_congr_Prop pq f

@[congr]
theorem Inter_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q) (f : ∀ x, f₁ (pq.mpr x) = f₂ x) :
    Inter f₁ = Inter f₂ :=
  infi_congr_Prop pq f

theorem Union_eq_if {p : Prop} [Decidable p] (s : Set α) : (⋃ h : p, s) = if p then s else ∅ :=
  supr_eq_if _

theorem Union_eq_dif {p : Prop} [Decidable p] (s : p → Set α) : (⋃ h : p, s h) = if h : p then s h else ∅ :=
  supr_eq_dif _

theorem Inter_eq_if {p : Prop} [Decidable p] (s : Set α) : (⋂ h : p, s) = if p then s else Univ :=
  infi_eq_if _

theorem Infi_eq_dif {p : Prop} [Decidable p] (s : p → Set α) : (⋂ h : p, s h) = if h : p then s h else Univ :=
  infi_eq_dif _

theorem exists_set_mem_of_union_eq_top {ι : Type _} (t : Set ι) (s : ι → Set β) (w : (⋃ i ∈ t, s i) = ⊤) (x : β) :
    ∃ i ∈ t, x ∈ s i := by
  have p : x ∈ ⊤ := Set.mem_univ x
  simpa only [w, ← Set.mem_Union] using p

theorem nonempty_of_union_eq_top_of_nonempty {ι : Type _} (t : Set ι) (s : ι → Set α) (H : Nonempty α)
    (w : (⋃ i ∈ t, s i) = ⊤) : t.Nonempty := by
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some
  exact ⟨x, m⟩

theorem set_of_exists (p : ι → β → Prop) : { x | ∃ i, p i x } = ⋃ i, { x | p i x } :=
  ext fun i => mem_Union.symm

theorem set_of_forall (p : ι → β → Prop) : { x | ∀ i, p i x } = ⋂ i, { x | p i x } :=
  ext fun i => mem_Inter.symm

theorem Union_subset {s : ι → Set α} {t : Set α} (h : ∀ i, s i ⊆ t) : (⋃ i, s i) ⊆ t :=
  @supr_le (Set α) _ _ _ _ h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Union₂_subset {s : ∀ i, κ i → Set α} {t : Set α} (h : ∀ i j, s i j ⊆ t) : (⋃ (i) (j), s i j) ⊆ t :=
  Union_subset fun x => Union_subset (h x)

theorem subset_Inter {t : Set β} {s : ι → Set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
  @le_infi (Set β) _ _ _ _ h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem subset_Inter₂ {s : Set α} {t : ∀ i, κ i → Set α} (h : ∀ i j, s ⊆ t i j) : s ⊆ ⋂ (i) (j), t i j :=
  subset_Inter fun x => subset_Inter <| h x

@[simp]
theorem Union_subset_iff {s : ι → Set α} {t : Set α} : (⋃ i, s i) ⊆ t ↔ ∀ i, s i ⊆ t :=
  ⟨fun h i => Subset.trans (le_supr s _) h, Union_subset⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Union₂_subset_iff {s : ∀ i, κ i → Set α} {t : Set α} : (⋃ (i) (j), s i j) ⊆ t ↔ ∀ i j, s i j ⊆ t := by
  simp_rw [Union_subset_iff]

@[simp]
theorem subset_Inter_iff {s : Set α} {t : ι → Set α} : (s ⊆ ⋂ i, t i) ↔ ∀ i, s ⊆ t i :=
  @le_infi_iff (Set α) _ _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem subset_Inter₂_iff {s : Set α} {t : ∀ i, κ i → Set α} : (s ⊆ ⋂ (i) (j), t i j) ↔ ∀ i j, s ⊆ t i j := by
  simp_rw [subset_Inter_iff]

theorem subset_Union : ∀ (s : ι → Set β) (i : ι), s i ⊆ ⋃ i, s i :=
  le_supr

theorem Inter_subset : ∀ (s : ι → Set β) (i : ι), (⋂ i, s i) ⊆ s i :=
  infi_le

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem subset_Union₂ {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : s i j ⊆ ⋃ (i) (j), s i j :=
  @le_supr₂ (Set α) _ _ _ _ i j

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Inter₂_subset {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : (⋂ (i) (j), s i j) ⊆ s i j :=
  @infi₂_le (Set α) _ _ _ _ i j

/-- This rather trivial consequence of `subset_Union`is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem subset_Union_of_subset {s : Set α} {t : ι → Set α} (i : ι) (h : s ⊆ t i) : s ⊆ ⋃ i, t i :=
  @le_supr_of_le (Set α) _ _ _ _ i h

/-- This rather trivial consequence of `Inter_subset`is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem Inter_subset_of_subset {s : ι → Set α} {t : Set α} (i : ι) (h : s i ⊆ t) : (⋂ i, s i) ⊆ t :=
  @infi_le_of_le (Set α) _ _ _ _ i h

theorem Union_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : (⋃ i, s i) ⊆ ⋃ i, t i :=
  @supr_mono (Set α) _ _ s t h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Union₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) : (⋃ (i) (j), s i j) ⊆ ⋃ (i) (j), t i j :=
  @supr₂_mono (Set α) _ _ _ s t h

theorem Inter_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : (⋂ i, s i) ⊆ ⋂ i, t i :=
  @infi_mono (Set α) _ _ s t h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Inter₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) : (⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), t i j :=
  @infi₂_mono (Set α) _ _ _ s t h

theorem Union_mono' {s : ι → Set α} {t : ι₂ → Set α} (h : ∀ i, ∃ j, s i ⊆ t j) : (⋃ i, s i) ⊆ ⋃ i, t i :=
  @supr_mono' (Set α) _ _ _ s t h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i' j')
theorem Union₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α} (h : ∀ i j, ∃ i' j', s i j ⊆ t i' j') :
    (⋃ (i) (j), s i j) ⊆ ⋃ (i') (j'), t i' j' :=
  @supr₂_mono' (Set α) _ _ _ _ _ s t h

theorem Inter_mono' {s : ι → Set α} {t : ι' → Set α} (h : ∀ j, ∃ i, s i ⊆ t j) : (⋂ i, s i) ⊆ ⋂ j, t j :=
  Set.subset_Inter fun j =>
    let ⟨i, hi⟩ := h j
    Inter_subset_of_subset i hi

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i' j')
theorem Inter₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α} (h : ∀ i' j', ∃ i j, s i j ⊆ t i' j') :
    (⋂ (i) (j), s i j) ⊆ ⋂ (i') (j'), t i' j' :=
  subset_Inter₂_iff.2 fun i' j' =>
    let ⟨i, j, hst⟩ := h i' j'
    (Inter₂_subset _ _).trans hst

theorem Union₂_subset_Union (κ : ι → Sort _) (s : ι → Set α) : (⋃ (i) (j : κ i), s i) ⊆ ⋃ i, s i :=
  Union_mono fun i => Union_subset fun h => Subset.rfl

theorem Inter_subset_Inter₂ (κ : ι → Sort _) (s : ι → Set α) : (⋂ i, s i) ⊆ ⋂ (i) (j : κ i), s i :=
  Inter_mono fun i => subset_Inter fun h => Subset.rfl

theorem Union_set_of (P : ι → α → Prop) : (⋃ i, { x : α | P i x }) = { x : α | ∃ i, P i x } := by
  ext
  exact mem_Union

theorem Inter_set_of (P : ι → α → Prop) : (⋂ i, { x : α | P i x }) = { x : α | ∀ i, P i x } := by
  ext
  exact mem_Inter

theorem Union_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⋃ x, f x) = ⋃ y, g y :=
  h1.supr_congr h h2

theorem Inter_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⋂ x, f x) = ⋂ y, g y :=
  h1.infi_congr h h2

theorem Union_const [Nonempty ι] (s : Set β) : (⋃ i : ι, s) = s :=
  supr_const

theorem Inter_const [Nonempty ι] (s : Set β) : (⋂ i : ι, s) = s :=
  infi_const

@[simp]
theorem compl_Union (s : ι → Set β) : (⋃ i, s i)ᶜ = ⋂ i, s iᶜ :=
  compl_supr

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem compl_Union₂ (s : ∀ i, κ i → Set α) : (⋃ (i) (j), s i j)ᶜ = ⋂ (i) (j), s i jᶜ := by
  simp_rw [compl_Union]

@[simp]
theorem compl_Inter (s : ι → Set β) : (⋂ i, s i)ᶜ = ⋃ i, s iᶜ :=
  compl_infi

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem compl_Inter₂ (s : ∀ i, κ i → Set α) : (⋂ (i) (j), s i j)ᶜ = ⋃ (i) (j), s i jᶜ := by
  simp_rw [compl_Inter]

-- classical -- complete_boolean_algebra
theorem Union_eq_compl_Inter_compl (s : ι → Set β) : (⋃ i, s i) = (⋂ i, s iᶜ)ᶜ := by
  simp only [← compl_Inter, ← compl_compl]

-- classical -- complete_boolean_algebra
theorem Inter_eq_compl_Union_compl (s : ι → Set β) : (⋂ i, s i) = (⋃ i, s iᶜ)ᶜ := by
  simp only [← compl_Union, ← compl_compl]

theorem inter_Union (s : Set β) (t : ι → Set β) : (s ∩ ⋃ i, t i) = ⋃ i, s ∩ t i :=
  inf_supr_eq _ _

theorem Union_inter (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s :=
  supr_inf_eq _ _

theorem Union_union_distrib (s : ι → Set β) (t : ι → Set β) : (⋃ i, s i ∪ t i) = (⋃ i, s i) ∪ ⋃ i, t i :=
  supr_sup_eq

theorem Inter_inter_distrib (s : ι → Set β) (t : ι → Set β) : (⋂ i, s i ∩ t i) = (⋂ i, s i) ∩ ⋂ i, t i :=
  infi_inf_eq

theorem union_Union [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∪ ⋃ i, t i) = ⋃ i, s ∪ t i :=
  sup_supr

theorem Union_union [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∪ s = ⋃ i, t i ∪ s :=
  supr_sup

theorem inter_Inter [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∩ ⋂ i, t i) = ⋂ i, s ∩ t i :=
  inf_infi

theorem Inter_inter [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋂ i, t i) ∩ s = ⋂ i, t i ∩ s :=
  infi_inf

-- classical
theorem union_Inter (s : Set β) (t : ι → Set β) : (s ∪ ⋂ i, t i) = ⋂ i, s ∪ t i :=
  sup_infi_eq _ _

theorem Inter_union (s : ι → Set β) (t : Set β) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  infi_sup_eq _ _

theorem Union_diff (s : Set β) (t : ι → Set β) : (⋃ i, t i) \ s = ⋃ i, t i \ s :=
  Union_inter _ _

theorem diff_Union [Nonempty ι] (s : Set β) (t : ι → Set β) : (s \ ⋃ i, t i) = ⋂ i, s \ t i := by
  rw [diff_eq, compl_Union, inter_Inter] <;> rfl

theorem diff_Inter (s : Set β) (t : ι → Set β) : (s \ ⋂ i, t i) = ⋃ i, s \ t i := by
  rw [diff_eq, compl_Inter, inter_Union] <;> rfl

theorem directed_on_Union {r} {f : ι → Set α} (hd : Directed (· ⊆ ·) f) (h : ∀ x, DirectedOn r (f x)) :
    DirectedOn r (⋃ x, f x) := by
  simp only [← DirectedOn, ← exists_prop, ← mem_Union, ← exists_imp_distrib] <;>
    exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
      let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
      let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
      ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩

theorem Union_inter_subset {ι α} {s t : ι → Set α} : (⋃ i, s i ∩ t i) ⊆ (⋃ i, s i) ∩ ⋃ i, t i :=
  le_supr_inf_supr s t

theorem Union_inter_of_monotone {ι α} [Preorderₓ ι] [IsDirected ι (· ≤ ·)] {s t : ι → Set α} (hs : Monotone s)
    (ht : Monotone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ ⋃ i, t i :=
  supr_inf_of_monotone hs ht

theorem Union_inter_of_antitone {ι α} [Preorderₓ ι] [IsDirected ι (swap (· ≤ ·))] {s t : ι → Set α} (hs : Antitone s)
    (ht : Antitone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ ⋃ i, t i :=
  supr_inf_of_antitone hs ht

theorem Inter_union_of_monotone {ι α} [Preorderₓ ι] [IsDirected ι (swap (· ≤ ·))] {s t : ι → Set α} (hs : Monotone s)
    (ht : Monotone t) : (⋂ i, s i ∪ t i) = (⋂ i, s i) ∪ ⋂ i, t i :=
  infi_sup_of_monotone hs ht

theorem Inter_union_of_antitone {ι α} [Preorderₓ ι] [IsDirected ι (· ≤ ·)] {s t : ι → Set α} (hs : Antitone s)
    (ht : Antitone t) : (⋂ i, s i ∪ t i) = (⋂ i, s i) ∪ ⋂ i, t i :=
  infi_sup_of_antitone hs ht

/-- An equality version of this lemma is `Union_Inter_of_monotone` in `data.set.finite`. -/
theorem Union_Inter_subset {s : ι → ι' → Set α} : (⋃ j, ⋂ i, s i j) ⊆ ⋂ i, ⋃ j, s i j :=
  supr_infi_le_infi_supr (flip s)

theorem Union_option {ι} (s : Option ι → Set α) : (⋃ o, s o) = s none ∪ ⋃ i, s (some i) :=
  supr_option s

theorem Inter_option {ι} (s : Option ι → Set α) : (⋂ o, s o) = s none ∩ ⋂ i, s (some i) :=
  infi_option s

section

variable (p : ι → Prop) [DecidablePred p]

theorem Union_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    (⋃ i, if h : p i then f i h else g i h) = (⋃ (i) (h : p i), f i h) ∪ ⋃ (i) (h : ¬p i), g i h :=
  supr_dite _ _ _

theorem Union_ite (f g : ι → Set α) :
    (⋃ i, if p i then f i else g i) = (⋃ (i) (h : p i), f i) ∪ ⋃ (i) (h : ¬p i), g i :=
  Union_dite _ _ _

theorem Inter_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    (⋂ i, if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f i h) ∩ ⋂ (i) (h : ¬p i), g i h :=
  infi_dite _ _ _

theorem Inter_ite (f g : ι → Set α) :
    (⋂ i, if p i then f i else g i) = (⋂ (i) (h : p i), f i) ∩ ⋂ (i) (h : ¬p i), g i :=
  Inter_dite _ _ _

end

theorem image_projection_prod {ι : Type _} {α : ι → Type _} {v : ∀ i : ι, Set (α i)} (hv : (Pi Univ v).Nonempty)
    (i : ι) : ((fun x : ∀ i : ι, α i => x i) '' ⋂ k, (fun x : ∀ j : ι, α j => x k) ⁻¹' v k) = v i := by
  classical
  apply subset.antisymm
  · simp [← Inter_subset]
    
  · intro y y_in
    simp only [← mem_image, ← mem_Inter, ← mem_preimage]
    rcases hv with ⟨z, hz⟩
    refine' ⟨Function.update z i y, _, update_same i y z⟩
    rw [@forall_update_iff ι α _ z i y fun i t => t ∈ v i]
    exact
      ⟨y_in, fun j hj => by
        simpa using hz j⟩
    

/-! ### Unions and intersections indexed by `Prop` -/


@[simp]
theorem Inter_false {s : False → Set α} : Inter s = univ :=
  infi_false

@[simp]
theorem Union_false {s : False → Set α} : Union s = ∅ :=
  supr_false

@[simp]
theorem Inter_true {s : True → Set α} : Inter s = s trivialₓ :=
  infi_true

@[simp]
theorem Union_true {s : True → Set α} : Union s = s trivialₓ :=
  supr_true

@[simp]
theorem Inter_exists {p : ι → Prop} {f : Exists p → Set α} : (⋂ x, f x) = ⋂ (i) (h : p i), f ⟨i, h⟩ :=
  infi_exists

@[simp]
theorem Union_exists {p : ι → Prop} {f : Exists p → Set α} : (⋃ x, f x) = ⋃ (i) (h : p i), f ⟨i, h⟩ :=
  supr_exists

@[simp]
theorem Union_empty : (⋃ i : ι, ∅ : Set α) = ∅ :=
  supr_bot

@[simp]
theorem Inter_univ : (⋂ i : ι, univ : Set α) = univ :=
  infi_top

section

variable {s : ι → Set α}

@[simp]
theorem Union_eq_empty : (⋃ i, s i) = ∅ ↔ ∀ i, s i = ∅ :=
  supr_eq_bot

@[simp]
theorem Inter_eq_univ : (⋂ i, s i) = univ ↔ ∀ i, s i = univ :=
  infi_eq_top

@[simp]
theorem nonempty_Union : (⋃ i, s i).Nonempty ↔ ∃ i, (s i).Nonempty := by
  simp [ne_empty_iff_nonempty]

@[simp]
theorem nonempty_bUnion {t : Set α} {s : α → Set β} : (⋃ i ∈ t, s i).Nonempty ↔ ∃ i ∈ t, (s i).Nonempty := by
  simp [ne_empty_iff_nonempty]

theorem Union_nonempty_index (s : Set α) (t : s.Nonempty → Set β) : (⋃ h, t h) = ⋃ x ∈ s, t ⟨x, ‹_›⟩ :=
  supr_exists

end

@[simp]
theorem Inter_Inter_eq_left {b : β} {s : ∀ x : β, x = b → Set α} : (⋂ (x) (h : x = b), s x h) = s b rfl :=
  infi_infi_eq_left

@[simp]
theorem Inter_Inter_eq_right {b : β} {s : ∀ x : β, b = x → Set α} : (⋂ (x) (h : b = x), s x h) = s b rfl :=
  infi_infi_eq_right

@[simp]
theorem Union_Union_eq_left {b : β} {s : ∀ x : β, x = b → Set α} : (⋃ (x) (h : x = b), s x h) = s b rfl :=
  supr_supr_eq_left

@[simp]
theorem Union_Union_eq_right {b : β} {s : ∀ x : β, b = x → Set α} : (⋃ (x) (h : b = x), s x h) = s b rfl :=
  supr_supr_eq_right

theorem Inter_or {p q : Prop} (s : p ∨ q → Set α) : (⋂ h, s h) = (⋂ h : p, s (Or.inl h)) ∩ ⋂ h : q, s (Or.inr h) :=
  infi_or

theorem Union_or {p q : Prop} (s : p ∨ q → Set α) : (⋃ h, s h) = (⋃ i, s (Or.inl i)) ∪ ⋃ j, s (Or.inr j) :=
  supr_or

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (hp hq)
theorem Union_and {p q : Prop} (s : p ∧ q → Set α) : (⋃ h, s h) = ⋃ (hp) (hq), s ⟨hp, hq⟩ :=
  supr_and

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (hp hq)
theorem Inter_and {p q : Prop} (s : p ∧ q → Set α) : (⋂ h, s h) = ⋂ (hp) (hq), s ⟨hp, hq⟩ :=
  infi_and

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i i')
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i' i)
theorem Union_comm (s : ι → ι' → Set α) : (⋃ (i) (i'), s i i') = ⋃ (i') (i), s i i' :=
  supr_comm

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i i')
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i' i)
theorem Inter_comm (s : ι → ι' → Set α) : (⋂ (i) (i'), s i i') = ⋂ (i') (i), s i i' :=
  infi_comm

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i₁ j₁ i₂ j₂)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i₂ j₂ i₁ j₁)
theorem Union₂_comm (s : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Set α) :
    (⋃ (i₁) (j₁) (i₂) (j₂), s i₁ j₁ i₂ j₂) = ⋃ (i₂) (j₂) (i₁) (j₁), s i₁ j₁ i₂ j₂ :=
  supr₂_comm _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i₁ j₁ i₂ j₂)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i₂ j₂ i₁ j₁)
theorem Inter₂_comm (s : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Set α) :
    (⋂ (i₁) (j₁) (i₂) (j₂), s i₁ j₁ i₂ j₂) = ⋂ (i₂) (j₂) (i₁) (j₁), s i₁ j₁ i₂ j₂ :=
  infi₂_comm _

@[simp]
theorem bUnion_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    (⋃ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h) = ⋃ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ := by
  simp only [← Union_and, ← @Union_comm _ ι']

@[simp]
theorem bUnion_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    (⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h) = ⋃ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ := by
  simp only [← Union_and, ← @Union_comm _ ι]

@[simp]
theorem bInter_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    (⋂ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h) = ⋂ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ := by
  simp only [← Inter_and, ← @Inter_comm _ ι']

@[simp]
theorem bInter_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    (⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h) = ⋂ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ := by
  simp only [← Inter_and, ← @Inter_comm _ ι]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (x h)
@[simp]
theorem Union_Union_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    (⋃ (x) (h), s x h) = s b (Or.inl rfl) ∪ ⋃ (x) (h : p x), s x (Or.inr h) := by
  simp only [← Union_or, ← Union_union_distrib, ← Union_Union_eq_left]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (x h)
@[simp]
theorem Inter_Inter_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    (⋂ (x) (h), s x h) = s b (Or.inl rfl) ∩ ⋂ (x) (h : p x), s x (Or.inr h) := by
  simp only [← Inter_or, ← Inter_inter_distrib, ← Inter_Inter_eq_left]

/-! ### Bounded unions and intersections -/


/-- A specialization of `mem_Union₂`. -/
theorem mem_bUnion {s : Set α} {t : α → Set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) : y ∈ ⋃ x ∈ s, t x :=
  mem_Union₂_of_mem xs ytx

/-- A specialization of `mem_Inter₂`. -/
theorem mem_bInter {s : Set α} {t : α → Set β} {y : β} (h : ∀, ∀ x ∈ s, ∀, y ∈ t x) : y ∈ ⋂ x ∈ s, t x :=
  mem_Inter₂_of_mem h

/-- A specialization of `subset_Union₂`. -/
theorem subset_bUnion_of_mem {s : Set α} {u : α → Set β} {x : α} (xs : x ∈ s) : u x ⊆ ⋃ x ∈ s, u x :=
  subset_Union₂ x xs

/-- A specialization of `Inter₂_subset`. -/
theorem bInter_subset_of_mem {s : Set α} {t : α → Set β} {x : α} (xs : x ∈ s) : (⋂ x ∈ s, t x) ⊆ t x :=
  Inter₂_subset x xs

theorem bUnion_subset_bUnion_left {s s' : Set α} {t : α → Set β} (h : s ⊆ s') : (⋃ x ∈ s, t x) ⊆ ⋃ x ∈ s', t x :=
  Union₂_subset fun x hx => subset_bUnion_of_mem <| h hx

theorem bInter_subset_bInter_left {s s' : Set α} {t : α → Set β} (h : s' ⊆ s) : (⋂ x ∈ s, t x) ⊆ ⋂ x ∈ s', t x :=
  subset_Inter₂ fun x hx => bInter_subset_of_mem <| h hx

theorem bUnion_mono {s s' : Set α} {t t' : α → Set β} (hs : s' ⊆ s) (h : ∀, ∀ x ∈ s, ∀, t x ⊆ t' x) :
    (⋃ x ∈ s', t x) ⊆ ⋃ x ∈ s, t' x :=
  (bUnion_subset_bUnion_left hs).trans <| Union₂_mono h

theorem bInter_mono {s s' : Set α} {t t' : α → Set β} (hs : s ⊆ s') (h : ∀, ∀ x ∈ s, ∀, t x ⊆ t' x) :
    (⋂ x ∈ s', t x) ⊆ ⋂ x ∈ s, t' x :=
  (bInter_subset_bInter_left hs).trans <| Inter₂_mono h

theorem Union_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : (⋃ i, s i) = ⋃ i, t i :=
  supr_congr h

theorem Inter_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : (⋂ i, s i) = ⋂ i, t i :=
  infi_congr h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Union₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) : (⋃ (i) (j), s i j) = ⋃ (i) (j), t i j :=
  Union_congr fun i => Union_congr <| h i

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Inter₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) : (⋂ (i) (j), s i j) = ⋂ (i) (j), t i j :=
  Inter_congr fun i => Inter_congr <| h i

theorem bUnion_eq_Union (s : Set α) (t : ∀, ∀ x ∈ s, ∀, Set β) : (⋃ x ∈ s, t x ‹_›) = ⋃ x : s, t x x.2 :=
  supr_subtype'

theorem bInter_eq_Inter (s : Set α) (t : ∀, ∀ x ∈ s, ∀, Set β) : (⋂ x ∈ s, t x ‹_›) = ⋂ x : s, t x x.2 :=
  infi_subtype'

theorem Union_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    (⋃ x : { x // p x }, s x) = ⋃ (x) (hx : p x), s ⟨x, hx⟩ :=
  supr_subtype

theorem Inter_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    (⋂ x : { x // p x }, s x) = ⋂ (x) (hx : p x), s ⟨x, hx⟩ :=
  infi_subtype

theorem bInter_empty (u : α → Set β) : (⋂ x ∈ (∅ : Set α), u x) = univ :=
  infi_emptyset

theorem bInter_univ (u : α → Set β) : (⋂ x ∈ @Univ α, u x) = ⋂ x, u x :=
  infi_univ

@[simp]
theorem bUnion_self (s : Set α) : (⋃ x ∈ s, s) = s :=
  Subset.antisymm (Union₂_subset fun x hx => Subset.refl s) fun x hx => mem_bUnion hx hx

@[simp]
theorem Union_nonempty_self (s : Set α) : (⋃ h : s.Nonempty, s) = s := by
  rw [Union_nonempty_index, bUnion_self]

-- TODO(Jeremy): here is an artifact of the encoding of bounded intersection:
-- without dsimp, the next theorem fails to type check, because there is a lambda
-- in a type that needs to be contracted. Using simp [eq_of_mem_singleton xa] also works.
theorem bInter_singleton (a : α) (s : α → Set β) : (⋂ x ∈ ({a} : Set α), s x) = s a :=
  infi_singleton

theorem bInter_union (s t : Set α) (u : α → Set β) : (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  infi_union

theorem bInter_insert (a : α) (s : Set α) (t : α → Set β) : (⋂ x ∈ insert a s, t x) = t a ∩ ⋂ x ∈ s, t x := by
  simp

-- TODO(Jeremy): another example of where an annotation is needed
theorem bInter_pair (a b : α) (s : α → Set β) : (⋂ x ∈ ({a, b} : Set α), s x) = s a ∩ s b := by
  rw [bInter_insert, bInter_singleton]

theorem bInter_inter {ι α : Type _} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    (⋂ i ∈ s, f i ∩ t) = (⋂ i ∈ s, f i) ∩ t := by
  have : Nonempty s := hs.to_subtype
  simp [← bInter_eq_Inter, Inter_inter]

theorem inter_bInter {ι α : Type _} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    (⋂ i ∈ s, t ∩ f i) = t ∩ ⋂ i ∈ s, f i := by
  rw [inter_comm, ← bInter_inter hs]
  simp [← inter_comm]

theorem bUnion_empty (s : α → Set β) : (⋃ x ∈ (∅ : Set α), s x) = ∅ :=
  supr_emptyset

theorem bUnion_univ (s : α → Set β) : (⋃ x ∈ @Univ α, s x) = ⋃ x, s x :=
  supr_univ

theorem bUnion_singleton (a : α) (s : α → Set β) : (⋃ x ∈ ({a} : Set α), s x) = s a :=
  supr_singleton

@[simp]
theorem bUnion_of_singleton (s : Set α) : (⋃ x ∈ s, {x}) = s :=
  ext <| by
    simp

theorem bUnion_union (s t : Set α) (u : α → Set β) : (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  supr_union

@[simp]
theorem Union_coe_set {α β : Type _} (s : Set α) (f : s → Set β) : (⋃ i, f i) = ⋃ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  Union_subtype _ _

@[simp]
theorem Inter_coe_set {α β : Type _} (s : Set α) (f : s → Set β) : (⋂ i, f i) = ⋂ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  Inter_subtype _ _

theorem bUnion_insert (a : α) (s : Set α) (t : α → Set β) : (⋃ x ∈ insert a s, t x) = t a ∪ ⋃ x ∈ s, t x := by
  simp

theorem bUnion_pair (a b : α) (s : α → Set β) : (⋃ x ∈ ({a, b} : Set α), s x) = s a ∪ s b := by
  simp

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem inter_Union₂ (s : Set α) (t : ∀ i, κ i → Set α) : (s ∩ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ∩ t i j := by
  simp only [← inter_Union]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Union₂_inter (s : ∀ i, κ i → Set α) (t : Set α) : (⋃ (i) (j), s i j) ∩ t = ⋃ (i) (j), s i j ∩ t := by
  simp_rw [Union_inter]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem union_Inter₂ (s : Set α) (t : ∀ i, κ i → Set α) : (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by
  simp_rw [union_Inter]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Inter₂_union (s : ∀ i, κ i → Set α) (t : Set α) : (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by
  simp_rw [Inter_union]

theorem mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∈ t) (ht : t ∈ S) : x ∈ ⋃₀S :=
  ⟨t, ht, hx⟩

-- is this theorem really necessary?
theorem not_mem_of_not_mem_sUnion {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀S) (ht : t ∈ S) : x ∉ t := fun h =>
  hx ⟨t, ht, h⟩

theorem sInter_subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
  Inf_le tS

theorem subset_sUnion_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : t ⊆ ⋃₀S :=
  le_Sup tS

theorem subset_sUnion_of_subset {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s ⊆ u) (h₂ : u ∈ t) : s ⊆ ⋃₀t :=
  Subset.trans h₁ (subset_sUnion_of_mem h₂)

theorem sUnion_subset {S : Set (Set α)} {t : Set α} (h : ∀, ∀ t' ∈ S, ∀, t' ⊆ t) : ⋃₀S ⊆ t :=
  Sup_le h

@[simp]
theorem sUnion_subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀s ⊆ t ↔ ∀, ∀ t' ∈ s, ∀, t' ⊆ t :=
  @Sup_le_iff (Set α) _ _ _

theorem subset_sInter {S : Set (Set α)} {t : Set α} (h : ∀, ∀ t' ∈ S, ∀, t ⊆ t') : t ⊆ ⋂₀ S :=
  le_Inf h

@[simp]
theorem subset_sInter_iff {S : Set (Set α)} {t : Set α} : t ⊆ ⋂₀ S ↔ ∀, ∀ t' ∈ S, ∀, t ⊆ t' :=
  @le_Inf_iff (Set α) _ _ _

theorem sUnion_subset_sUnion {S T : Set (Set α)} (h : S ⊆ T) : ⋃₀S ⊆ ⋃₀T :=
  sUnion_subset fun s hs => subset_sUnion_of_mem (h hs)

theorem sInter_subset_sInter {S T : Set (Set α)} (h : S ⊆ T) : ⋂₀ T ⊆ ⋂₀ S :=
  subset_sInter fun s hs => sInter_subset_of_mem (h hs)

@[simp]
theorem sUnion_empty : ⋃₀∅ = (∅ : Set α) :=
  Sup_empty

@[simp]
theorem sInter_empty : ⋂₀ ∅ = (Univ : Set α) :=
  Inf_empty

@[simp]
theorem sUnion_singleton (s : Set α) : ⋃₀{s} = s :=
  Sup_singleton

@[simp]
theorem sInter_singleton (s : Set α) : ⋂₀ {s} = s :=
  Inf_singleton

@[simp]
theorem sUnion_eq_empty {S : Set (Set α)} : ⋃₀S = ∅ ↔ ∀, ∀ s ∈ S, ∀, s = ∅ :=
  Sup_eq_bot

@[simp]
theorem sInter_eq_univ {S : Set (Set α)} : ⋂₀ S = univ ↔ ∀, ∀ s ∈ S, ∀, s = univ :=
  Inf_eq_top

@[simp]
theorem nonempty_sUnion {S : Set (Set α)} : (⋃₀S).Nonempty ↔ ∃ s ∈ S, Set.Nonempty s := by
  simp [ne_empty_iff_nonempty]

theorem Nonempty.of_sUnion {s : Set (Set α)} (h : (⋃₀s).Nonempty) : s.Nonempty :=
  let ⟨s, hs, _⟩ := nonempty_sUnion.1 h
  ⟨s, hs⟩

theorem Nonempty.of_sUnion_eq_univ [Nonempty α] {s : Set (Set α)} (h : ⋃₀s = univ) : s.Nonempty :=
  nonempty.of_sUnion <| h.symm ▸ univ_nonempty

theorem sUnion_union (S T : Set (Set α)) : ⋃₀(S ∪ T) = ⋃₀S ∪ ⋃₀T :=
  Sup_union

theorem sInter_union (S T : Set (Set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
  Inf_union

@[simp]
theorem sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀insert s T = s ∪ ⋃₀T :=
  Sup_insert

@[simp]
theorem sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ insert s T = s ∩ ⋂₀ T :=
  Inf_insert

@[simp]
theorem sUnion_diff_singleton_empty (s : Set (Set α)) : ⋃₀(s \ {∅}) = ⋃₀s :=
  Sup_diff_singleton_bot s

@[simp]
theorem sInter_diff_singleton_univ (s : Set (Set α)) : ⋂₀ (s \ {Univ}) = ⋂₀ s :=
  Inf_diff_singleton_top s

theorem sUnion_pair (s t : Set α) : ⋃₀{s, t} = s ∪ t :=
  Sup_pair

theorem sInter_pair (s t : Set α) : ⋂₀ {s, t} = s ∩ t :=
  Inf_pair

@[simp]
theorem sUnion_image (f : α → Set β) (s : Set α) : ⋃₀(f '' s) = ⋃ x ∈ s, f x :=
  Sup_image

@[simp]
theorem sInter_image (f : α → Set β) (s : Set α) : ⋂₀ (f '' s) = ⋂ x ∈ s, f x :=
  Inf_image

@[simp]
theorem sUnion_range (f : ι → Set β) : ⋃₀Range f = ⋃ x, f x :=
  rfl

@[simp]
theorem sInter_range (f : ι → Set β) : ⋂₀ Range f = ⋂ x, f x :=
  rfl

theorem Union_eq_univ_iff {f : ι → Set α} : (⋃ i, f i) = univ ↔ ∀ x, ∃ i, x ∈ f i := by
  simp only [← eq_univ_iff_forall, ← mem_Union]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Union₂_eq_univ_iff {s : ∀ i, κ i → Set α} : (⋃ (i) (j), s i j) = univ ↔ ∀ a, ∃ i j, a ∈ s i j := by
  simp only [← Union_eq_univ_iff, ← mem_Union]

theorem sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀c = univ ↔ ∀ a, ∃ b ∈ c, a ∈ b := by
  simp only [← eq_univ_iff_forall, ← mem_sUnion]

-- classical
theorem Inter_eq_empty_iff {f : ι → Set α} : (⋂ i, f i) = ∅ ↔ ∀ x, ∃ i, x ∉ f i := by
  simp [← Set.eq_empty_iff_forall_not_mem]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- classical
theorem Inter₂_eq_empty_iff {s : ∀ i, κ i → Set α} : (⋂ (i) (j), s i j) = ∅ ↔ ∀ a, ∃ i j, a ∉ s i j := by
  simp only [← eq_empty_iff_forall_not_mem, ← mem_Inter, ← not_forall]

-- classical
theorem sInter_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = ∅ ↔ ∀ a, ∃ b ∈ c, a ∉ b := by
  simp [← Set.eq_empty_iff_forall_not_mem]

-- classical
@[simp]
theorem nonempty_Inter {f : ι → Set α} : (⋂ i, f i).Nonempty ↔ ∃ x, ∀ i, x ∈ f i := by
  simp [ne_empty_iff_nonempty, ← Inter_eq_empty_iff]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- classical
@[simp]
theorem nonempty_Inter₂ {s : ∀ i, κ i → Set α} : (⋂ (i) (j), s i j).Nonempty ↔ ∃ a, ∀ i j, a ∈ s i j := by
  simp [ne_empty_iff_nonempty, ← Inter_eq_empty_iff]

-- classical
@[simp]
theorem nonempty_sInter {c : Set (Set α)} : (⋂₀ c).Nonempty ↔ ∃ a, ∀, ∀ b ∈ c, ∀, a ∈ b := by
  simp [ne_empty_iff_nonempty, ← sInter_eq_empty_iff]

-- classical
theorem compl_sUnion (S : Set (Set α)) : (⋃₀S)ᶜ = ⋂₀ (compl '' S) :=
  ext fun x => by
    simp

-- classical
theorem sUnion_eq_compl_sInter_compl (S : Set (Set α)) : ⋃₀S = (⋂₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋃₀S), compl_sUnion]

-- classical
theorem compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀(compl '' S) := by
  rw [sUnion_eq_compl_sInter_compl, compl_compl_image]

-- classical
theorem sInter_eq_compl_sUnion_compl (S : Set (Set α)) : ⋂₀ S = (⋃₀(compl '' S))ᶜ := by
  rw [← compl_compl (⋂₀ S), compl_sInter]

theorem inter_empty_of_inter_sUnion_empty {s t : Set α} {S : Set (Set α)} (hs : t ∈ S) (h : s ∩ ⋃₀S = ∅) : s ∩ t = ∅ :=
  eq_empty_of_subset_empty <| by
    rw [← h] <;> exact inter_subset_inter_right _ (subset_sUnion_of_mem hs)

theorem range_sigma_eq_Union_range {γ : α → Type _} (f : Sigma γ → β) : Range f = ⋃ a, Range fun b => f ⟨a, b⟩ :=
  Set.ext <| by
    simp

theorem Union_eq_range_sigma (s : α → Set β) : (⋃ i, s i) = Range fun a : Σi, s i => a.2 := by
  simp [← Set.ext_iff]

theorem Union_eq_range_psigma (s : ι → Set β) : (⋃ i, s i) = Range fun a : Σ'i, s i => a.2 := by
  simp [← Set.ext_iff]

theorem Union_image_preimage_sigma_mk_eq_self {ι : Type _} {σ : ι → Type _} (s : Set (Sigma σ)) :
    (⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s)) = s := by
  ext x
  simp only [← mem_Union, ← mem_image, ← mem_preimage]
  constructor
  · rintro ⟨i, a, h, rfl⟩
    exact h
    
  · intro h
    cases' x with i a
    exact ⟨i, a, h, rfl⟩
    

theorem Sigma.univ (X : α → Type _) : (Set.Univ : Set (Σa, X a)) = ⋃ a, Range (Sigma.mk a) :=
  Set.ext fun x => iff_of_true trivialₓ ⟨Range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩

theorem sUnion_mono {s t : Set (Set α)} (h : s ⊆ t) : ⋃₀s ⊆ ⋃₀t :=
  sUnion_subset fun t' ht' => subset_sUnion_of_mem <| h ht'

theorem Union_subset_Union_const {s : Set α} (h : ι → ι₂) : (⋃ i : ι, s) ⊆ ⋃ j : ι₂, s :=
  @supr_const_mono (Set α) ι ι₂ _ s h

@[simp]
theorem Union_singleton_eq_range {α β : Type _} (f : α → β) : (⋃ x : α, {f x}) = Range f := by
  ext x
  simp [← @eq_comm _ x]

theorem Union_of_singleton (α : Type _) : (⋃ x, {x} : Set α) = univ := by
  simp

theorem Union_of_singleton_coe (s : Set α) : (⋃ i : s, {i} : Set α) = s := by
  simp

theorem sUnion_eq_bUnion {s : Set (Set α)} : ⋃₀s = ⋃ (i : Set α) (h : i ∈ s), i := by
  rw [← sUnion_image, image_id']

theorem sInter_eq_bInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i : Set α) (h : i ∈ s), i := by
  rw [← sInter_image, image_id']

theorem sUnion_eq_Union {s : Set (Set α)} : ⋃₀s = ⋃ i : s, i := by
  simp only [sUnion_range, ← Subtype.range_coe]

theorem sInter_eq_Inter {s : Set (Set α)} : ⋂₀ s = ⋂ i : s, i := by
  simp only [sInter_range, ← Subtype.range_coe]

theorem union_eq_Union {s₁ s₂ : Set α} : s₁ ∪ s₂ = ⋃ b : Bool, cond b s₁ s₂ :=
  sup_eq_supr s₁ s₂

theorem inter_eq_Inter {s₁ s₂ : Set α} : s₁ ∩ s₂ = ⋂ b : Bool, cond b s₁ s₂ :=
  inf_eq_infi s₁ s₂

theorem sInter_union_sInter {S T : Set (Set α)} : ⋂₀ S ∪ ⋂₀ T = ⋂ p ∈ S ×ˢ T, (p : Set α × Set α).1 ∪ p.2 :=
  Inf_sup_Inf

theorem sUnion_inter_sUnion {s t : Set (Set α)} : ⋃₀s ∩ ⋃₀t = ⋃ p ∈ s ×ˢ t, (p : Set α × Set α).1 ∩ p.2 :=
  Sup_inf_Sup

theorem bUnion_Union (s : ι → Set α) (t : α → Set β) : (⋃ x ∈ ⋃ i, s i, t x) = ⋃ (i) (x ∈ s i), t x := by
  simp [← @Union_comm _ ι]

theorem bInter_Union (s : ι → Set α) (t : α → Set β) : (⋂ x ∈ ⋃ i, s i, t x) = ⋂ (i) (x ∈ s i), t x := by
  simp [← @Inter_comm _ ι]

theorem sUnion_Union (s : ι → Set (Set α)) : (⋃₀⋃ i, s i) = ⋃ i, ⋃₀s i := by
  simp only [← sUnion_eq_bUnion, ← bUnion_Union]

theorem sInter_Union (s : ι → Set (Set α)) : (⋂₀ ⋃ i, s i) = ⋂ i, ⋂₀ s i := by
  simp only [← sInter_eq_bInter, ← bInter_Union]

theorem Union_range_eq_sUnion {α β : Type _} (C : Set (Set α)) {f : ∀ s : C, β → s} (hf : ∀ s : C, Surjective (f s)) :
    (⋃ y : β, Range fun s : C => (f s y).val) = ⋃₀C := by
  ext x
  constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine' ⟨_, hs, _⟩
    exact (f ⟨s, hs⟩ y).2
    
  · rintro ⟨s, hs, hx⟩
    cases' hf ⟨s, hs⟩ ⟨x, hx⟩ with y hy
    refine' ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, _⟩
    exact congr_arg Subtype.val hy
    

theorem Union_range_eq_Union (C : ι → Set α) {f : ∀ x : ι, β → C x} (hf : ∀ x : ι, Surjective (f x)) :
    (⋃ y : β, Range fun x : ι => (f x y).val) = ⋃ x, C x := by
  ext x
  rw [mem_Union, mem_Union]
  constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
    
  · rintro ⟨i, hx⟩
    cases' hf i ⟨x, hx⟩ with y hy
    exact ⟨y, i, congr_arg Subtype.val hy⟩
    

theorem union_distrib_Inter_left (s : ι → Set α) (t : Set α) : (t ∪ ⋂ i, s i) = ⋂ i, t ∪ s i :=
  sup_infi_eq _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem union_distrib_Inter₂_left (s : Set α) (t : ∀ i, κ i → Set α) : (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j :=
  by
  simp_rw [union_distrib_Inter_left]

theorem union_distrib_Inter_right (s : ι → Set α) (t : Set α) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  infi_sup_eq _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem union_distrib_Inter₂_right (s : ∀ i, κ i → Set α) (t : Set α) : (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t :=
  by
  simp_rw [union_distrib_Inter_right]

section Function

/-! ### `maps_to` -/


theorem maps_to_sUnion {S : Set (Set α)} {t : Set β} {f : α → β} (H : ∀, ∀ s ∈ S, ∀, MapsTo f s t) : MapsTo f (⋃₀S) t :=
  fun x ⟨s, hs, hx⟩ => H s hs hx

theorem maps_to_Union {s : ι → Set α} {t : Set β} {f : α → β} (H : ∀ i, MapsTo f (s i) t) : MapsTo f (⋃ i, s i) t :=
  maps_to_sUnion <| forall_range_iff.2 H

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem maps_to_Union₂ {s : ∀ i, κ i → Set α} {t : Set β} {f : α → β} (H : ∀ i j, MapsTo f (s i j) t) :
    MapsTo f (⋃ (i) (j), s i j) t :=
  maps_to_Union fun i => maps_to_Union (H i)

theorem maps_to_Union_Union {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, MapsTo f (s i) (t i)) :
    MapsTo f (⋃ i, s i) (⋃ i, t i) :=
  maps_to_Union fun i => (H i).mono (Subset.refl _) (subset_Union t i)

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem maps_to_Union₂_Union₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  maps_to_Union_Union fun i => maps_to_Union_Union (H i)

theorem maps_to_sInter {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀, ∀ t ∈ T, ∀, MapsTo f s t) :
    MapsTo f s (⋂₀ T) := fun x hx t ht => H t ht hx

theorem maps_to_Inter {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, MapsTo f s (t i)) : MapsTo f s (⋂ i, t i) :=
  fun x hx => mem_Inter.2 fun i => H i hx

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem maps_to_Inter₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β} (H : ∀ i j, MapsTo f s (t i j)) :
    MapsTo f s (⋂ (i) (j), t i j) :=
  maps_to_Inter fun i => maps_to_Inter (H i)

theorem maps_to_Inter_Inter {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, MapsTo f (s i) (t i)) :
    MapsTo f (⋂ i, s i) (⋂ i, t i) :=
  maps_to_Inter fun i => (H i).mono (Inter_subset s i) (Subset.refl _)

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem maps_to_Inter₂_Inter₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋂ (i) (j), s i j) (⋂ (i) (j), t i j) :=
  maps_to_Inter_Inter fun i => maps_to_Inter_Inter (H i)

theorem image_Inter_subset (s : ι → Set α) (f : α → β) : (f '' ⋂ i, s i) ⊆ ⋂ i, f '' s i :=
  (maps_to_Inter_Inter fun i => maps_to_image f (s i)).image_subset

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem image_Inter₂_subset (s : ∀ i, κ i → Set α) (f : α → β) : (f '' ⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), f '' s i j :=
  (maps_to_Inter₂_Inter₂ fun i hi => maps_to_image f (s i hi)).image_subset

theorem image_sInter_subset (S : Set (Set α)) (f : α → β) : f '' ⋂₀ S ⊆ ⋂ s ∈ S, f '' s := by
  rw [sInter_eq_bInter]
  apply image_Inter₂_subset

/-! ### `inj_on` -/


theorem InjOn.image_inter {f : α → β} {s t u : Set α} (hf : InjOn f u) (hs : s ⊆ u) (ht : t ⊆ u) :
    f '' (s ∩ t) = f '' s ∩ f '' t := by
  apply subset.antisymm (image_inter_subset _ _ _)
  rintro x ⟨⟨y, ys, hy⟩, ⟨z, zt, hz⟩⟩
  have : y = z := by
    apply hf (hs ys) (ht zt)
    rwa [← hz] at hy
  rw [← this] at zt
  exact ⟨y, ⟨ys, zt⟩, hy⟩

theorem InjOn.image_Inter_eq [Nonempty ι] {s : ι → Set α} {f : α → β} (h : InjOn f (⋃ i, s i)) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  inhabit ι
  refine' subset.antisymm (image_Inter_subset s f) fun y hy => _
  simp only [← mem_Inter, ← mem_image_iff_bex] at hy
  choose x hx hy using hy
  refine' ⟨x default, mem_Inter.2 fun i => _, hy _⟩
  suffices x default = x i by
    rw [this]
    apply hx
  replace hx : ∀ i, x i ∈ ⋃ j, s j := fun i => (subset_Union _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [← hy]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem InjOn.image_bInter_eq {p : ι → Prop} {s : ∀ (i) (hi : p i), Set α} (hp : ∃ i, p i) {f : α → β}
    (h : InjOn f (⋃ (i) (hi), s i hi)) : (f '' ⋂ (i) (hi), s i hi) = ⋂ (i) (hi), f '' s i hi := by
  simp only [← Inter, ← infi_subtype']
  have : Nonempty { i // p i } := nonempty_subtype.2 hp
  apply inj_on.image_Inter_eq
  simpa only [← Union, ← supr_subtype'] using h

theorem inj_on_Union_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {f : α → β} (hf : ∀ i, InjOn f (s i)) :
    InjOn f (⋃ i, s i) := by
  intro x hx y hy hxy
  rcases mem_Union.1 hx with ⟨i, hx⟩
  rcases mem_Union.1 hy with ⟨j, hy⟩
  rcases hs i j with ⟨k, hi, hj⟩
  exact hf k (hi hx) (hj hy) hxy

/-! ### `surj_on` -/


theorem surj_on_sUnion {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀, ∀ t ∈ T, ∀, SurjOn f s t) : SurjOn f s (⋃₀T) :=
  fun x ⟨t, ht, hx⟩ => H t ht hx

theorem surj_on_Union {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, SurjOn f s (t i)) : SurjOn f s (⋃ i, t i) :=
  surj_on_sUnion <| forall_range_iff.2 H

theorem surj_on_Union_Union {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, SurjOn f (s i) (t i)) :
    SurjOn f (⋃ i, s i) (⋃ i, t i) :=
  surj_on_Union fun i => (H i).mono (subset_Union _ _) (Subset.refl _)

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem surj_on_Union₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β} (H : ∀ i j, SurjOn f s (t i j)) :
    SurjOn f s (⋃ (i) (j), t i j) :=
  surj_on_Union fun i => surj_on_Union (H i)

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem surj_on_Union₂_Union₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f (s i j) (t i j)) : SurjOn f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  surj_on_Union_Union fun i => surj_on_Union_Union (H i)

theorem surj_on_Inter [hi : Nonempty ι] {s : ι → Set α} {t : Set β} {f : α → β} (H : ∀ i, SurjOn f (s i) t)
    (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) t := by
  intro y hy
  rw [Hinj.image_Inter_eq, mem_Inter]
  exact fun i => H i hy

theorem surj_on_Inter_Inter [hi : Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) (⋂ i, t i) :=
  surj_on_Inter (fun i => (H i).mono (Subset.refl _) (Inter_subset _ _)) Hinj

/-! ### `bij_on` -/


theorem bij_on_Union {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i))
    (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  ⟨maps_to_Union_Union fun i => (H i).MapsTo, Hinj, surj_on_Union_Union fun i => (H i).SurjOn⟩

theorem bij_on_Inter [hi : Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i))
    (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  ⟨maps_to_Inter_Inter fun i => (H i).MapsTo, hi.elim fun i => (H i).InjOn.mono (Inter_subset _ _),
    surj_on_Inter_Inter (fun i => (H i).SurjOn) Hinj⟩

theorem bij_on_Union_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {t : ι → Set β} {f : α → β}
    (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  bij_on_Union H <| inj_on_Union_of_directed hs fun i => (H i).InjOn

theorem bij_on_Inter_of_directed [Nonempty ι] {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {t : ι → Set β} {f : α → β}
    (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  bij_on_Inter H <| inj_on_Union_of_directed hs fun i => (H i).InjOn

end Function

/-! ### `image`, `preimage` -/


section Image

theorem image_Union {f : α → β} {s : ι → Set α} : (f '' ⋃ i, s i) = ⋃ i, f '' s i := by
  ext1 x
  simp [← image, exists_and_distrib_right, ← @exists_swap α]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem image_Union₂ (f : α → β) (s : ∀ i, κ i → Set α) : (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j := by
  simp_rw [image_Union]

theorem univ_subtype {p : α → Prop} : (Univ : Set (Subtype p)) = ⋃ (x) (h : p x), {⟨x, h⟩} :=
  Set.ext fun ⟨x, h⟩ => by
    simp [← h]

theorem range_eq_Union {ι} (f : ι → α) : Range f = ⋃ i, {f i} :=
  Set.ext fun a => by
    simp [← @eq_comm α a]

theorem image_eq_Union (f : α → β) (s : Set α) : f '' s = ⋃ i ∈ s, {f i} :=
  Set.ext fun b => by
    simp [← @eq_comm β b]

theorem bUnion_range {f : ι → α} {g : α → Set β} : (⋃ x ∈ Range f, g x) = ⋃ y, g (f y) :=
  supr_range

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (x y)
@[simp]
theorem Union_Union_eq' {f : ι → α} {g : α → Set β} : (⋃ (x) (y) (h : f y = x), g x) = ⋃ y, g (f y) := by
  simpa using bUnion_range

theorem bInter_range {f : ι → α} {g : α → Set β} : (⋂ x ∈ Range f, g x) = ⋂ y, g (f y) :=
  infi_range

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (x y)
@[simp]
theorem Inter_Inter_eq' {f : ι → α} {g : α → Set β} : (⋂ (x) (y) (h : f y = x), g x) = ⋂ y, g (f y) := by
  simpa using bInter_range

variable {s : Set γ} {f : γ → α} {g : α → Set β}

theorem bUnion_image : (⋃ x ∈ f '' s, g x) = ⋃ y ∈ s, g (f y) :=
  supr_image

theorem bInter_image : (⋂ x ∈ f '' s, g x) = ⋂ y ∈ s, g (f y) :=
  infi_image

end Image

section Preimage

theorem monotone_preimage {f : α → β} : Monotone (Preimage f) := fun a b h => preimage_mono h

@[simp]
theorem preimage_Union {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i :=
  Set.ext <| by
    simp [← preimage]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem preimage_Union₂ {f : α → β} {s : ∀ i, κ i → Set β} : (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j := by
  simp_rw [preimage_Union]

@[simp]
theorem preimage_sUnion {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋃₀s = ⋃ t ∈ s, f ⁻¹' t := by
  rw [sUnion_eq_bUnion, preimage_Union₂]

theorem preimage_Inter {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i := by
  ext <;> simp

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem preimage_Inter₂ {f : α → β} {s : ∀ i, κ i → Set β} : (f ⁻¹' ⋂ (i) (j), s i j) = ⋂ (i) (j), f ⁻¹' s i j := by
  simp_rw [preimage_Inter]

@[simp]
theorem preimage_sInter {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋂₀ s = ⋂ t ∈ s, f ⁻¹' t := by
  rw [sInter_eq_bInter, preimage_Inter₂]

@[simp]
theorem bUnion_preimage_singleton (f : α → β) (s : Set β) : (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' s := by
  rw [← preimage_Union₂, bUnion_of_singleton]

theorem bUnion_range_preimage_singleton (f : α → β) : (⋃ y ∈ Range f, f ⁻¹' {y}) = univ := by
  rw [bUnion_preimage_singleton, preimage_range]

end Preimage

section Prod

theorem prod_Union {s : Set α} {t : ι → Set β} : (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i := by
  ext
  simp

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem prod_Union₂ {s : Set α} {t : ∀ i, κ i → Set β} : (s ×ˢ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ×ˢ t i j := by
  simp_rw [prod_Union]

theorem prod_sUnion {s : Set α} {C : Set (Set β)} : s ×ˢ ⋃₀C = ⋃₀((fun t => s ×ˢ t) '' C) := by
  simp_rw [sUnion_eq_bUnion, bUnion_image, prod_Union₂]

theorem Union_prod_const {s : ι → Set α} {t : Set β} : (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t := by
  ext
  simp

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Union₂_prod_const {s : ∀ i, κ i → Set α} {t : Set β} : (⋃ (i) (j), s i j) ×ˢ t = ⋃ (i) (j), s i j ×ˢ t := by
  simp_rw [Union_prod_const]

theorem sUnion_prod_const {C : Set (Set α)} {t : Set β} : ⋃₀C ×ˢ t = ⋃₀((fun s : Set α => s ×ˢ t) '' C) := by
  simp only [← sUnion_eq_bUnion, ← Union₂_prod_const, ← bUnion_image]

theorem Union_prod {ι ι' α β} (s : ι → Set α) (t : ι' → Set β) :
    (⋃ x : ι × ι', s x.1 ×ˢ t x.2) = (⋃ i : ι, s i) ×ˢ ⋃ i : ι', t i := by
  ext
  simp

theorem Union_prod_of_monotone [SemilatticeSup α] {s : α → Set β} {t : α → Set γ} (hs : Monotone s) (ht : Monotone t) :
    (⋃ x, s x ×ˢ t x) = (⋃ x, s x) ×ˢ ⋃ x, t x := by
  ext ⟨z, w⟩
  simp only [← mem_prod, ← mem_Union, ← exists_imp_distrib, ← and_imp, ← iff_def]
  constructor
  · intro x hz hw
    exact ⟨⟨x, hz⟩, x, hw⟩
    
  · intro x hz x' hw
    exact ⟨x⊔x', hs le_sup_left hz, ht le_sup_right hw⟩
    

end Prod

section Image2

variable (f : α → β → γ) {s : Set α} {t : Set β}

theorem Union_image_left : (⋃ a ∈ s, f a '' t) = Image2 f s t := by
  ext y
  constructor <;> simp only [← mem_Union] <;> rintro ⟨a, ha, x, hx, ax⟩ <;> exact ⟨a, x, ha, hx, ax⟩

theorem Union_image_right : (⋃ b ∈ t, (fun a => f a b) '' s) = Image2 f s t := by
  ext y
  constructor <;> simp only [← mem_Union] <;> rintro ⟨a, b, c, d, e⟩
  exact ⟨c, a, d, b, e⟩
  exact ⟨b, d, a, c, e⟩

theorem image2_Union_left (s : ι → Set α) (t : Set β) : Image2 f (⋃ i, s i) t = ⋃ i, Image2 f (s i) t := by
  simp only [image_prod, ← Union_prod_const, ← image_Union]

theorem image2_Union_right (s : Set α) (t : ι → Set β) : Image2 f s (⋃ i, t i) = ⋃ i, Image2 f s (t i) := by
  simp only [image_prod, ← prod_Union, ← image_Union]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem image2_Union₂_left (s : ∀ i, κ i → Set α) (t : Set β) :
    Image2 f (⋃ (i) (j), s i j) t = ⋃ (i) (j), Image2 f (s i j) t := by
  simp_rw [image2_Union_left]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem image2_Union₂_right (s : Set α) (t : ∀ i, κ i → Set β) :
    Image2 f s (⋃ (i) (j), t i j) = ⋃ (i) (j), Image2 f s (t i j) := by
  simp_rw [image2_Union_right]

theorem image2_Inter_subset_left (s : ι → Set α) (t : Set β) : Image2 f (⋂ i, s i) t ⊆ ⋂ i, Image2 f (s i) t := by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i => mem_image2_of_mem (hx _) hy

theorem image2_Inter_subset_right (s : Set α) (t : ι → Set β) : Image2 f s (⋂ i, t i) ⊆ ⋂ i, Image2 f s (t i) := by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i => mem_image2_of_mem hx (hy _)

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem image2_Inter₂_subset_left (s : ∀ i, κ i → Set α) (t : Set β) :
    Image2 f (⋂ (i) (j), s i j) t ⊆ ⋂ (i) (j), Image2 f (s i j) t := by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i j => mem_image2_of_mem (hx _ _) hy

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem image2_Inter₂_subset_right (s : Set α) (t : ∀ i, κ i → Set β) :
    Image2 f s (⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), Image2 f s (t i j) := by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i j => mem_image2_of_mem hx (hy _ _)

/-- The `set.image2` version of `set.image_eq_Union` -/
theorem image2_eq_Union (s : Set α) (t : Set β) : Image2 f s t = ⋃ (i ∈ s) (j ∈ t), {f i j} := by
  simp_rw [← image_eq_Union, Union_image_left]

theorem prod_eq_bUnion_left : s ×ˢ t = ⋃ a ∈ s, (fun b => (a, b)) '' t := by
  rw [Union_image_left, image2_mk_eq_prod]

theorem prod_eq_bUnion_right : s ×ˢ t = ⋃ b ∈ t, (fun a => (a, b)) '' s := by
  rw [Union_image_right, image2_mk_eq_prod]

end Image2

section Seq

/-- Given a set `s` of functions `α → β` and `t : set α`, `seq s t` is the union of `f '' t` over
all `f ∈ s`. -/
def Seq (s : Set (α → β)) (t : Set α) : Set β :=
  { b | ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b }

theorem seq_def {s : Set (α → β)} {t : Set α} : Seq s t = ⋃ f ∈ s, f '' t :=
  Set.ext <| by
    simp [← seq]

@[simp]
theorem mem_seq_iff {s : Set (α → β)} {t : Set α} {b : β} : b ∈ Seq s t ↔ ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b :=
  Iff.rfl

theorem seq_subset {s : Set (α → β)} {t : Set α} {u : Set β} :
    Seq s t ⊆ u ↔ ∀, ∀ f ∈ s, ∀, ∀, ∀ a ∈ t, ∀, (f : α → β) a ∈ u :=
  Iff.intro (fun h f hf a ha => h ⟨f, hf, a, ha, rfl⟩) fun h b ⟨f, hf, a, ha, Eq⟩ => Eq ▸ h f hf a ha

theorem seq_mono {s₀ s₁ : Set (α → β)} {t₀ t₁ : Set α} (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) : Seq s₀ t₀ ⊆ Seq s₁ t₁ :=
  fun b ⟨f, hf, a, ha, Eq⟩ => ⟨f, hs hf, a, ht ha, Eq⟩

theorem singleton_seq {f : α → β} {t : Set α} : Set.Seq {f} t = f '' t :=
  Set.ext <| by
    simp

theorem seq_singleton {s : Set (α → β)} {a : α} : Set.Seq s {a} = (fun f : α → β => f a) '' s :=
  Set.ext <| by
    simp

theorem seq_seq {s : Set (β → γ)} {t : Set (α → β)} {u : Set α} : Seq s (Seq t u) = Seq (Seq ((· ∘ ·) '' s) t) u := by
  refine' Set.ext fun c => Iff.intro _ _
  · rintro ⟨f, hfs, b, ⟨g, hg, a, hau, rfl⟩, rfl⟩
    exact ⟨f ∘ g, ⟨(· ∘ ·) f, mem_image_of_mem _ hfs, g, hg, rfl⟩, a, hau, rfl⟩
    
  · rintro ⟨fg, ⟨fc, ⟨f, hfs, rfl⟩, g, hgt, rfl⟩, a, ha, rfl⟩
    exact ⟨f, hfs, g a, ⟨g, hgt, a, ha, rfl⟩, rfl⟩
    

theorem image_seq {f : β → γ} {s : Set (α → β)} {t : Set α} : f '' Seq s t = Seq ((· ∘ ·) f '' s) t := by
  rw [← singleton_seq, ← singleton_seq, seq_seq, image_singleton]

theorem prod_eq_seq {s : Set α} {t : Set β} : s ×ˢ t = (Prod.mk '' s).seq t := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨Prod.mk a, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    
  · rintro ⟨f, ⟨x, hx, rfl⟩, y, hy, eq⟩
    rw [← Eq]
    exact ⟨hx, hy⟩
    

theorem prod_image_seq_comm (s : Set α) (t : Set β) : (Prod.mk '' s).seq t = Seq ((fun b a => (a, b)) '' t) s := by
  rw [← prod_eq_seq, ← image_swap_prod, prod_eq_seq, image_seq, ← image_comp, Prod.swap]

theorem image2_eq_seq (f : α → β → γ) (s : Set α) (t : Set β) : Image2 f s t = Seq (f '' s) t := by
  ext
  simp

end Seq

section Pi

variable {π : α → Type _}

theorem pi_def (i : Set α) (s : ∀ a, Set (π a)) : Pi i s = ⋂ a ∈ i, eval a ⁻¹' s a := by
  ext
  simp

theorem univ_pi_eq_Inter (t : ∀ i, Set (π i)) : Pi Univ t = ⋂ i, eval i ⁻¹' t i := by
  simp only [← pi_def, ← Inter_true, ← mem_univ]

theorem pi_diff_pi_subset (i : Set α) (s t : ∀ a, Set (π a)) : Pi i s \ Pi i t ⊆ ⋃ a ∈ i, eval a ⁻¹' (s a \ t a) := by
  refine' diff_subset_comm.2 fun x hx a ha => _
  simp only [← mem_diff, ← mem_pi, ← mem_Union, ← not_exists, ← mem_preimage, ← not_and, ← not_not, ← eval_apply] at hx
  exact hx.2 _ ha (hx.1 _ ha)

theorem Union_univ_pi (t : ∀ i, ι → Set (π i)) :
    (⋃ x : α → ι, Pi Univ fun i => t i (x i)) = Pi Univ fun i => ⋃ j : ι, t i j := by
  ext
  simp [← Classical.skolem]

end Pi

end Set

namespace Function

namespace Surjective

theorem Union_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : (⋃ x, g (f x)) = ⋃ y, g y :=
  hf.supr_comp g

theorem Inter_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : (⋂ x, g (f x)) = ⋂ y, g y :=
  hf.infi_comp g

end Surjective

end Function

/-!
### Disjoint sets

We define some lemmas in the `disjoint` namespace to be able to use projection notation.
-/


section Disjoint

variable {s t u : Set α} {f : α → β}

namespace Disjoint

theorem union_left (hs : Disjoint s u) (ht : Disjoint t u) : Disjoint (s ∪ t) u :=
  hs.sup_left ht

theorem union_right (ht : Disjoint s t) (hu : Disjoint s u) : Disjoint s (t ∪ u) :=
  ht.sup_right hu

theorem inter_left (u : Set α) (h : Disjoint s t) : Disjoint (s ∩ u) t :=
  inf_left _ h

theorem inter_left' (u : Set α) (h : Disjoint s t) : Disjoint (u ∩ s) t :=
  inf_left' _ h

theorem inter_right (u : Set α) (h : Disjoint s t) : Disjoint s (t ∩ u) :=
  inf_right _ h

theorem inter_right' (u : Set α) (h : Disjoint s t) : Disjoint s (u ∩ t) :=
  inf_right' _ h

theorem subset_left_of_subset_union (h : s ⊆ t ∪ u) (hac : Disjoint s u) : s ⊆ t :=
  hac.left_le_of_le_sup_right h

theorem subset_right_of_subset_union (h : s ⊆ t ∪ u) (hab : Disjoint s t) : s ⊆ u :=
  hab.left_le_of_le_sup_left h

theorem preimage {α β} (f : α → β) {s t : Set β} (h : Disjoint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t) := fun x hx => h hx

end Disjoint

namespace Set

protected theorem disjoint_iff : Disjoint s t ↔ s ∩ t ⊆ ∅ :=
  Iff.rfl

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

theorem not_disjoint_iff : ¬Disjoint s t ↔ ∃ x, x ∈ s ∧ x ∈ t :=
  not_forall.trans <| exists_congr fun x => not_not

theorem not_disjoint_iff_nonempty_inter : ¬Disjoint s t ↔ (s ∩ t).Nonempty :=
  not_disjoint_iff

alias not_disjoint_iff_nonempty_inter ↔ _ nonempty.not_disjoint

theorem disjoint_or_nonempty_inter (s t : Set α) : Disjoint s t ∨ (s ∩ t).Nonempty :=
  (em _).imp_right not_disjoint_iff_nonempty_inter.mp

theorem disjoint_iff_forall_ne : Disjoint s t ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, x ≠ y := by
  simp only [← Ne.def, ← disjoint_left, ← @imp_not_comm _ (_ = _), ← forall_eq']

theorem _root_.disjoint.ne_of_mem (h : Disjoint s t) {x y} (hx : x ∈ s) (hy : y ∈ t) : x ≠ y :=
  disjoint_iff_forall_ne.mp h x hx y hy

theorem disjoint_of_subset_left (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t :=
  d.mono_left h

theorem disjoint_of_subset_right (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t :=
  d.mono_right h

theorem disjoint_of_subset {s t u v : Set α} (h1 : s ⊆ u) (h2 : t ⊆ v) (d : Disjoint u v) : Disjoint s t :=
  d.mono h1 h2

@[simp]
theorem disjoint_union_left : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u :=
  disjoint_sup_left

@[simp]
theorem disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u :=
  disjoint_sup_right

@[simp]
theorem disjoint_Union_left {ι : Sort _} {s : ι → Set α} : Disjoint (⋃ i, s i) t ↔ ∀ i, Disjoint (s i) t :=
  supr_disjoint_iff

@[simp]
theorem disjoint_Union_right {ι : Sort _} {s : ι → Set α} : Disjoint t (⋃ i, s i) ↔ ∀ i, Disjoint t (s i) :=
  disjoint_supr_iff

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem disjoint_Union₂_left {s : ∀ i, κ i → Set α} {t : Set α} :
    Disjoint (⋃ (i) (j), s i j) t ↔ ∀ i j, Disjoint (s i j) t :=
  supr₂_disjoint_iff

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem disjoint_Union₂_right {s : Set α} {t : ∀ i, κ i → Set α} :
    Disjoint s (⋃ (i) (j), t i j) ↔ ∀ i j, Disjoint s (t i j) :=
  disjoint_supr₂_iff

@[simp]
theorem disjoint_sUnion_left {S : Set (Set α)} {t : Set α} : Disjoint (⋃₀S) t ↔ ∀, ∀ s ∈ S, ∀, Disjoint s t :=
  Sup_disjoint_iff

@[simp]
theorem disjoint_sUnion_right {s : Set α} {S : Set (Set α)} : Disjoint s (⋃₀S) ↔ ∀, ∀ t ∈ S, ∀, Disjoint s t :=
  disjoint_Sup_iff

theorem disjoint_diff {a b : Set α} : Disjoint a (b \ a) :=
  disjoint_iff.2 (inter_diff_self _ _)

@[simp]
theorem disjoint_empty (s : Set α) : Disjoint s ∅ :=
  disjoint_bot_right

@[simp]
theorem empty_disjoint (s : Set α) : Disjoint ∅ s :=
  disjoint_bot_left

@[simp]
theorem univ_disjoint {s : Set α} : Disjoint Univ s ↔ s = ∅ :=
  top_disjoint

@[simp]
theorem disjoint_univ {s : Set α} : Disjoint s Univ ↔ s = ∅ :=
  disjoint_top

@[simp]
theorem disjoint_singleton_left {a : α} {s : Set α} : Disjoint {a} s ↔ a ∉ s := by
  simp [← Set.disjoint_iff, ← subset_def] <;> exact Iff.rfl

@[simp]
theorem disjoint_singleton_right {a : α} {s : Set α} : Disjoint s {a} ↔ a ∉ s := by
  rw [Disjoint.comm] <;> exact disjoint_singleton_left

@[simp]
theorem disjoint_singleton {a b : α} : Disjoint ({a} : Set α) {b} ↔ a ≠ b := by
  rw [disjoint_singleton_left, mem_singleton_iff]

theorem disjoint_image_image {f : β → α} {g : γ → α} {s : Set β} {t : Set γ}
    (h : ∀, ∀ b ∈ s, ∀, ∀, ∀ c ∈ t, ∀, f b ≠ g c) : Disjoint (f '' s) (g '' t) := by
  rintro a ⟨⟨b, hb, eq⟩, c, hc, rfl⟩ <;> exact h b hb c hc Eq

theorem disjoint_image_of_injective {f : α → β} (hf : Injective f) {s t : Set α} (hd : Disjoint s t) :
    Disjoint (f '' s) (f '' t) :=
  disjoint_image_image fun x hx y hy => hf.Ne fun H => Set.disjoint_iff.1 hd ⟨hx, H.symm ▸ hy⟩

theorem _root_.disjoint.of_image (h : Disjoint (f '' s) (f '' t)) : Disjoint s t := fun x hx =>
  disjoint_left.1 h (mem_image_of_mem _ hx.1) (mem_image_of_mem _ hx.2)

theorem disjoint_image_iff (hf : Injective f) : Disjoint (f '' s) (f '' t) ↔ Disjoint s t :=
  ⟨Disjoint.of_image, disjoint_image_of_injective hf⟩

theorem _root_.disjoint.of_preimage (hf : Surjective f) {s t : Set β} (h : Disjoint (f ⁻¹' s) (f ⁻¹' t)) :
    Disjoint s t := by
  rw [disjoint_iff_inter_eq_empty, ← image_preimage_eq (_ ∩ _) hf, preimage_inter, h.inter_eq, image_empty]

theorem disjoint_preimage_iff (hf : Surjective f) {s t : Set β} : Disjoint (f ⁻¹' s) (f ⁻¹' t) ↔ Disjoint s t :=
  ⟨Disjoint.of_preimage hf, Disjoint.preimage _⟩

theorem preimage_eq_empty {f : α → β} {s : Set β} (h : Disjoint s (Range f)) : f ⁻¹' s = ∅ := by
  simpa using h.preimage f

theorem preimage_eq_empty_iff {s : Set β} : f ⁻¹' s = ∅ ↔ Disjoint s (Range f) :=
  ⟨fun h => by
    simp only [← eq_empty_iff_forall_not_mem, ← disjoint_iff_inter_eq_empty, ← not_exists, ← mem_inter_eq, ← not_and, ←
      mem_range, ← mem_preimage] at h⊢
    intro y hy x hx
    rw [← hx] at hy
    exact h x hy, preimage_eq_empty⟩

theorem _root_.disjoint.image {s t u : Set α} {f : α → β} (h : Disjoint s t) (hf : InjOn f u) (hs : s ⊆ u)
    (ht : t ⊆ u) : Disjoint (f '' s) (f '' t) := by
  rw [disjoint_iff_inter_eq_empty] at h⊢
  rw [← hf.image_inter hs ht, h, image_empty]

end Set

end Disjoint

/-! ### Intervals -/


namespace Set

variable [CompleteLattice α]

theorem Ici_supr (f : ι → α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  ext fun _ => by
    simp only [← mem_Ici, ← supr_le_iff, ← mem_Inter]

theorem Iic_infi (f : ι → α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i) :=
  ext fun _ => by
    simp only [← mem_Iic, ← le_infi_iff, ← mem_Inter]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Ici_supr₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⋂ (i) (j), Ici (f i j) := by
  simp_rw [Ici_supr]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Iic_infi₂ (f : ∀ i, κ i → α) : Iic (⨅ (i) (j), f i j) = ⋂ (i) (j), Iic (f i j) := by
  simp_rw [Iic_infi]

theorem Ici_Sup (s : Set α) : Ici (sup s) = ⋂ a ∈ s, Ici a := by
  rw [Sup_eq_supr, Ici_supr₂]

theorem Iic_Inf (s : Set α) : Iic (inf s) = ⋂ a ∈ s, Iic a := by
  rw [Inf_eq_infi, Iic_infi₂]

end Set

namespace Set

variable (t : α → Set β)

theorem subset_diff {s t u : Set α} : s ⊆ t \ u ↔ s ⊆ t ∧ Disjoint s u :=
  ⟨fun h => ⟨fun x hxs => (h hxs).1, fun x ⟨hxs, hxu⟩ => (h hxs).2 hxu⟩, fun ⟨h1, h2⟩ x hxs =>
    ⟨h1 hxs, fun hxu => h2 ⟨hxs, hxu⟩⟩⟩

theorem bUnion_diff_bUnion_subset (s₁ s₂ : Set α) : ((⋃ x ∈ s₁, t x) \ ⋃ x ∈ s₂, t x) ⊆ ⋃ x ∈ s₁ \ s₂, t x := by
  simp only [← diff_subset_iff, bUnion_union]
  apply bUnion_subset_bUnion_left
  rw [union_diff_self]
  apply subset_union_right

/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
def sigmaToUnion (x : Σi, t i) : ⋃ i, t i :=
  ⟨x.2, mem_Union.2 ⟨x.1, x.2.2⟩⟩

theorem sigma_to_Union_surjective : Surjective (sigmaToUnion t)
  | ⟨b, hb⟩ =>
    have : ∃ a, b ∈ t a := by
      simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩

theorem sigma_to_Union_injective (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) : Injective (sigmaToUnion t)
  | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, Eq =>
    have b_eq : b₁ = b₂ := congr_arg Subtype.val Eq
    have a_eq : a₁ = a₂ :=
      Classical.by_contradiction fun ne =>
        have : b₁ ∈ t a₁ ∩ t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        h _ _ Ne this
    Sigma.eq a_eq <|
      Subtype.eq <| by
        subst b_eq <;> subst a_eq

theorem sigma_to_Union_bijective (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) : Bijective (sigmaToUnion t) :=
  ⟨sigma_to_Union_injective t h, sigma_to_Union_surjective t⟩

/-- Equivalence between a disjoint union and a dependent sum. -/
noncomputable def unionEqSigmaOfDisjoint {t : α → Set β} (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    (⋃ i, t i) ≃ Σi, t i :=
  (Equivₓ.ofBijective _ <| sigma_to_Union_bijective t h).symm

theorem Union_ge_eq_Union_nat_add (u : ℕ → Set α) (n : ℕ) : (⋃ i ≥ n, u i) = ⋃ i, u (i + n) :=
  supr_ge_eq_supr_nat_add u n

theorem Inter_ge_eq_Inter_nat_add (u : ℕ → Set α) (n : ℕ) : (⋂ i ≥ n, u i) = ⋂ i, u (i + n) :=
  infi_ge_eq_infi_nat_add u n

theorem _root_.monotone.Union_nat_add {f : ℕ → Set α} (hf : Monotone f) (k : ℕ) : (⋃ n, f (n + k)) = ⋃ n, f n :=
  hf.supr_nat_add k

theorem _root_.antitone.Inter_nat_add {f : ℕ → Set α} (hf : Antitone f) (k : ℕ) : (⋂ n, f (n + k)) = ⋂ n, f n :=
  hf.infi_nat_add k

@[simp]
theorem Union_Inter_ge_nat_add (f : ℕ → Set α) (k : ℕ) : (⋃ n, ⋂ i ≥ n, f (i + k)) = ⋃ n, ⋂ i ≥ n, f i :=
  supr_infi_ge_nat_add f k

theorem union_Union_nat_succ (u : ℕ → Set α) : (u 0 ∪ ⋃ i, u (i + 1)) = ⋃ i, u i :=
  sup_supr_nat_succ u

theorem inter_Inter_nat_succ (u : ℕ → Set α) : (u 0 ∩ ⋂ i, u (i + 1)) = ⋂ i, u i :=
  inf_infi_nat_succ u

end Set

section SupClosed

/-- A set `s` is sup-closed if for all `x₁, x₂ ∈ s`, `x₁ ⊔ x₂ ∈ s`. -/
def SupClosed [HasSup α] (s : Set α) : Prop :=
  ∀ x1 x2, x1 ∈ s → x2 ∈ s → x1⊔x2 ∈ s

theorem sup_closed_singleton [SemilatticeSup α] (x : α) : SupClosed ({x} : Set α) := fun _ _ y1_mem y2_mem => by
  rw [Set.mem_singleton_iff] at *
  rw [y1_mem, y2_mem, sup_idem]

theorem SupClosed.inter [SemilatticeSup α] {s t : Set α} (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ∩ t) := by
  intro x y hx hy
  rw [Set.mem_inter_iff] at hx hy⊢
  exact ⟨hs x y hx.left hy.left, ht x y hx.right hy.right⟩

theorem sup_closed_of_totally_ordered [SemilatticeSup α] (s : Set α) (hs : ∀ x y : α, x ∈ s → y ∈ s → y ≤ x ∨ x ≤ y) :
    SupClosed s := by
  intro x y hxs hys
  cases hs x y hxs hys
  · rwa [sup_eq_left.mpr h]
    
  · rwa [sup_eq_right.mpr h]
    

theorem sup_closed_of_linear_order [LinearOrderₓ α] (s : Set α) : SupClosed s :=
  sup_closed_of_totally_ordered s fun x y hxs hys => le_totalₓ y x

end SupClosed

open Set

variable [CompleteLattice β]

theorem supr_Union (s : ι → Set α) (f : α → β) : (⨆ a ∈ ⋃ i, s i, f a) = ⨆ (i) (a ∈ s i), f a := by
  rw [supr_comm]
  simp_rw [mem_Union, supr_exists]

theorem infi_Union (s : ι → Set α) (f : α → β) : (⨅ a ∈ ⋃ i, s i, f a) = ⨅ (i) (a ∈ s i), f a :=
  @supr_Union α βᵒᵈ _ _ s f

theorem Sup_sUnion (s : Set (Set β)) : sup (⋃₀s) = ⨆ t ∈ s, sup t := by
  simp only [← sUnion_eq_bUnion, ← Sup_eq_supr, ← supr_Union]

theorem Inf_sUnion (s : Set (Set β)) : inf (⋃₀s) = ⨅ t ∈ s, inf t :=
  @Sup_sUnion βᵒᵈ _ _

