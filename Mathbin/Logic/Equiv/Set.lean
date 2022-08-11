/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Data.Set.Function
import Mathbin.Logic.Equiv.Basic

/-!
# Equivalences and sets

In this file we provide lemmas linking equivalences to sets.

Some notable definitions are:

* `equiv.of_injective`: an injective function is (noncomputably) equivalent to its range.
* `equiv.set_congr`: two equal sets are equivalent as types.
* `equiv.set.union`: a disjoint union of sets is equivalent to their `sum`.

This file is separate from `equiv/basic` such that we do not require the full lattice structure
on sets before defining what an equivalence is.
-/


open Function Set

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

namespace Equivₓ

@[simp]
theorem range_eq_univ {α : Type _} {β : Type _} (e : α ≃ β) : Range e = univ :=
  eq_univ_of_forall e.Surjective

protected theorem image_eq_preimage {α β} (e : α ≃ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  Set.ext fun x => mem_image_iff_of_inverse e.left_inv e.right_inv

theorem _root_.set.mem_image_equiv {α β} {S : Set α} {f : α ≃ β} {x : β} : x ∈ f '' S ↔ f.symm x ∈ S :=
  Set.ext_iff.mp (f.image_eq_preimage S) x

/-- Alias for `equiv.image_eq_preimage` -/
theorem _root_.set.image_equiv_eq_preimage_symm {α β} (S : Set α) (f : α ≃ β) : f '' S = f.symm ⁻¹' S :=
  f.image_eq_preimage S

/-- Alias for `equiv.image_eq_preimage` -/
theorem _root_.set.preimage_equiv_eq_image_symm {α β} (S : Set α) (f : β ≃ α) : f ⁻¹' S = f.symm '' S :=
  (f.symm.image_eq_preimage S).symm

@[simp]
protected theorem subset_image {α β} (e : α ≃ β) (s : Set α) (t : Set β) : e.symm '' t ⊆ s ↔ t ⊆ e '' s := by
  rw [image_subset_iff, e.image_eq_preimage]

@[simp]
protected theorem subset_image' {α β} (e : α ≃ β) (s : Set α) (t : Set β) : s ⊆ e.symm '' t ↔ e '' s ⊆ t :=
  calc
    s ⊆ e.symm '' t ↔ e.symm.symm '' s ⊆ t := by
      rw [e.symm.subset_image]
    _ ↔ e '' s ⊆ t := by
      rw [e.symm_symm]
    

@[simp]
theorem symm_image_image {α β} (e : α ≃ β) (s : Set α) : e.symm '' (e '' s) = s :=
  e.left_inverse_symm.image_image s

theorem eq_image_iff_symm_image_eq {α β} (e : α ≃ β) (s : Set α) (t : Set β) : t = e '' s ↔ e.symm '' t = s :=
  (e.symm.Injective.image_injective.eq_iff' (e.symm_image_image s)).symm

@[simp]
theorem image_symm_image {α β} (e : α ≃ β) (s : Set β) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image s

@[simp]
theorem image_preimage {α β} (e : α ≃ β) (s : Set β) : e '' (e ⁻¹' s) = s :=
  e.Surjective.image_preimage s

@[simp]
theorem preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' (e '' s) = s :=
  e.Injective.preimage_image s

protected theorem image_compl {α β} (f : Equivₓ α β) (s : Set α) : f '' sᶜ = (f '' s)ᶜ :=
  image_compl_eq f.Bijective

@[simp]
theorem symm_preimage_preimage {α β} (e : α ≃ β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.right_inverse_symm.preimage_preimage s

@[simp]
theorem preimage_symm_preimage {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.left_inverse_symm.preimage_preimage s

@[simp]
theorem preimage_subset {α β} (e : α ≃ β) (s t : Set β) : e ⁻¹' s ⊆ e ⁻¹' t ↔ s ⊆ t :=
  e.Surjective.preimage_subset_preimage_iff

@[simp]
theorem image_subset {α β} (e : α ≃ β) (s t : Set α) : e '' s ⊆ e '' t ↔ s ⊆ t :=
  image_subset_image_iff e.Injective

@[simp]
theorem image_eq_iff_eq {α β} (e : α ≃ β) (s t : Set α) : e '' s = e '' t ↔ s = t :=
  image_eq_image e.Injective

theorem preimage_eq_iff_eq_image {α β} (e : α ≃ β) (s t) : e ⁻¹' s = t ↔ s = e '' t :=
  preimage_eq_iff_eq_image e.Bijective

theorem eq_preimage_iff_image_eq {α β} (e : α ≃ β) (s t) : s = e ⁻¹' t ↔ e '' s = t :=
  eq_preimage_iff_image_eq e.Bijective

@[simp]
theorem prod_comm_preimage {α β} {s : Set α} {t : Set β} : Equivₓ.prodComm α β ⁻¹' t ×ˢ s = s ×ˢ t :=
  preimage_swap_prod

theorem prod_comm_image {α β} {s : Set α} {t : Set β} : Equivₓ.prodComm α β '' s ×ˢ t = t ×ˢ s :=
  image_swap_prod

@[simp]
theorem prod_assoc_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    Equivₓ.prodAssoc α β γ ⁻¹' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u := by
  ext
  simp [← and_assoc]

@[simp]
theorem prod_assoc_symm_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    (Equivₓ.prodAssoc α β γ).symm ⁻¹' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u := by
  ext
  simp [← and_assoc]

-- `@[simp]` doesn't like these lemmas, as it uses `set.image_congr'` to turn `equiv.prod_assoc`
-- into a lambda expression and then unfold it.
theorem prod_assoc_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    Equivₓ.prodAssoc α β γ '' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u := by
  simpa only [← Equivₓ.image_eq_preimage] using prod_assoc_symm_preimage

theorem prod_assoc_symm_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    (Equivₓ.prodAssoc α β γ).symm '' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u := by
  simpa only [← Equivₓ.image_eq_preimage] using prod_assoc_preimage

/-- A set `s` in `α × β` is equivalent to the sigma-type `Σ x, {y | (x, y) ∈ s}`. -/
def setProdEquivSigma {α β : Type _} (s : Set (α × β)) : s ≃ Σx : α, { y | (x, y) ∈ s } where
  toFun := fun x =>
    ⟨x.1.1, x.1.2, by
      simp ⟩
  invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
  left_inv := fun ⟨⟨x, y⟩, h⟩ => rfl
  right_inv := fun ⟨x, y, h⟩ => rfl

/-- The subtypes corresponding to equal sets are equivalent. -/
@[simps apply]
def setCongr {α : Type _} {s t : Set α} (h : s = t) : s ≃ t :=
  subtypeEquivProp h

/-- A set is equivalent to its image under an equivalence.
-/
-- We could construct this using `equiv.set.image e s e.injective`,
-- but this definition provides an explicit inverse.
@[simps]
def image {α β : Type _} (e : α ≃ β) (s : Set α) : s ≃ e '' s where
  toFun := fun x =>
    ⟨e x.1, by
      simp ⟩
  invFun := fun y =>
    ⟨e.symm y.1, by
      rcases y with ⟨-, ⟨a, ⟨m, rfl⟩⟩⟩
      simpa using m⟩
  left_inv := fun x => by
    simp
  right_inv := fun y => by
    simp

namespace Set

/-- `univ α` is equivalent to `α`. -/
@[simps apply symmApply]
protected def univ (α) : @Univ α ≃ α :=
  ⟨coe, fun a => ⟨a, trivialₓ⟩, fun ⟨a, _⟩ => rfl, fun a => rfl⟩

/-- An empty set is equivalent to the `empty` type. -/
protected def empty (α) : (∅ : Set α) ≃ Empty :=
  equivEmpty _

/-- An empty set is equivalent to a `pempty` type. -/
protected def pempty (α) : (∅ : Set α) ≃ Pempty :=
  equivPempty _

/-- If sets `s` and `t` are separated by a decidable predicate, then `s ∪ t` is equivalent to
`s ⊕ t`. -/
protected def union' {α} {s t : Set α} (p : α → Prop) [DecidablePred p] (hs : ∀, ∀ x ∈ s, ∀, p x)
    (ht : ∀, ∀ x ∈ t, ∀, ¬p x) : (s ∪ t : Set α) ≃ Sum s t where
  toFun := fun x =>
    if hp : p x then Sum.inl ⟨_, x.2.resolve_right fun xt => ht _ xt hp⟩
    else Sum.inr ⟨_, x.2.resolve_left fun xs => hp (hs _ xs)⟩
  invFun := fun o =>
    match o with
    | Sum.inl x => ⟨x, Or.inl x.2⟩
    | Sum.inr x => ⟨x, Or.inr x.2⟩
  left_inv := fun ⟨x, h'⟩ => by
    by_cases' p x <;> simp [← union'._match_1, ← h] <;> congr
  right_inv := fun o => by
    rcases o with (⟨x, h⟩ | ⟨x, h⟩) <;> dsimp' [← union'._match_1] <;> [simp [← hs _ h], simp [← ht _ h]]

/-- If sets `s` and `t` are disjoint, then `s ∪ t` is equivalent to `s ⊕ t`. -/
protected def union {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) : (s ∪ t : Set α) ≃ Sum s t :=
  Set.union' (fun x => x ∈ s) (fun _ => id) fun x xt xs => H ⟨xs, xt⟩

theorem union_apply_left {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) {a : (s ∪ t : Set α)}
    (ha : ↑a ∈ s) : Equivₓ.Set.union H a = Sum.inl ⟨a, ha⟩ :=
  dif_pos ha

theorem union_apply_right {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) {a : (s ∪ t : Set α)}
    (ha : ↑a ∈ t) : Equivₓ.Set.union H a = Sum.inr ⟨a, ha⟩ :=
  dif_neg fun h => H ⟨h, ha⟩

@[simp]
theorem union_symm_apply_left {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) (a : s) :
    (Equivₓ.Set.union H).symm (Sum.inl a) = ⟨a, subset_union_left _ _ a.2⟩ :=
  rfl

@[simp]
theorem union_symm_apply_right {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) (a : t) :
    (Equivₓ.Set.union H).symm (Sum.inr a) = ⟨a, subset_union_right _ _ a.2⟩ :=
  rfl

/-- A singleton set is equivalent to a `punit` type. -/
protected def singleton {α} (a : α) : ({a} : Set α) ≃ PUnit.{u} :=
  ⟨fun _ => PUnit.unit, fun _ => ⟨a, mem_singleton _⟩, fun ⟨x, h⟩ => by
    simp at h
    subst x, fun ⟨⟩ => rfl⟩

/-- Equal sets are equivalent.

TODO: this is the same as `equiv.set_congr`! -/
@[simps apply symmApply]
protected def ofEq {α : Type u} {s t : Set α} (h : s = t) : s ≃ t :=
  Equivₓ.setCongr h

/-- If `a ∉ s`, then `insert a s` is equivalent to `s ⊕ punit`. -/
protected def insert {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) :
    (insert a s : Set α) ≃ Sum s PUnit.{u + 1} :=
  calc
    (insert a s : Set α) ≃ ↥(s ∪ {a}) :=
      Equivₓ.Set.ofEq
        (by
          simp )
    _ ≃ Sum s ({a} : Set α) :=
      Equivₓ.Set.union fun x ⟨hx, hx'⟩ => by
        simp_all
    _ ≃ Sum s PUnit.{u + 1} := sumCongr (Equivₓ.refl _) (Equivₓ.Set.singleton _)
    

@[simp]
theorem insert_symm_apply_inl {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) (b : s) :
    (Equivₓ.Set.insert H).symm (Sum.inl b) = ⟨b, Or.inr b.2⟩ :=
  rfl

@[simp]
theorem insert_symm_apply_inr {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) (b : PUnit.{u + 1}) :
    (Equivₓ.Set.insert H).symm (Sum.inr b) = ⟨a, Or.inl rfl⟩ :=
  rfl

@[simp]
theorem insert_apply_left {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) :
    Equivₓ.Set.insert H ⟨a, Or.inl rfl⟩ = Sum.inr PUnit.unit :=
  (Equivₓ.Set.insert H).apply_eq_iff_eq_symm_apply.2 rfl

@[simp]
theorem insert_apply_right {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) (b : s) :
    Equivₓ.Set.insert H ⟨b, Or.inr b.2⟩ = Sum.inl b :=
  (Equivₓ.Set.insert H).apply_eq_iff_eq_symm_apply.2 rfl

/-- If `s : set α` is a set with decidable membership, then `s ⊕ sᶜ` is equivalent to `α`. -/
protected def sumCompl {α} (s : Set α) [DecidablePred (· ∈ s)] : Sum s (sᶜ : Set α) ≃ α :=
  calc
    Sum s (sᶜ : Set α) ≃ ↥(s ∪ sᶜ) :=
      (Equivₓ.Set.union
          (by
            simp [← Set.ext_iff])).symm
    _ ≃ @Univ α :=
      Equivₓ.Set.ofEq
        (by
          simp )
    _ ≃ α := Equivₓ.Set.univ _
    

@[simp]
theorem sum_compl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : s) :
    Equivₓ.Set.sumCompl s (Sum.inl x) = x :=
  rfl

@[simp]
theorem sum_compl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : sᶜ) :
    Equivₓ.Set.sumCompl s (Sum.inr x) = x :=
  rfl

theorem sum_compl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α} (hx : x ∈ s) :
    (Equivₓ.Set.sumCompl s).symm x = Sum.inl ⟨x, hx⟩ := by
  have : ↑(⟨x, Or.inl hx⟩ : (s ∪ sᶜ : Set α)) ∈ s := hx
  rw [Equivₓ.Set.sumCompl]
  simpa using set.union_apply_left _ this

theorem sum_compl_symm_apply_of_not_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α} (hx : x ∉ s) :
    (Equivₓ.Set.sumCompl s).symm x = Sum.inr ⟨x, hx⟩ := by
  have : ↑(⟨x, Or.inr hx⟩ : (s ∪ sᶜ : Set α)) ∈ sᶜ := hx
  rw [Equivₓ.Set.sumCompl]
  simpa using set.union_apply_right _ this

@[simp]
theorem sum_compl_symm_apply {α : Type _} {s : Set α} [DecidablePred (· ∈ s)] {x : s} :
    (Equivₓ.Set.sumCompl s).symm x = Sum.inl x := by
  cases' x with x hx <;> exact set.sum_compl_symm_apply_of_mem hx

@[simp]
theorem sum_compl_symm_apply_compl {α : Type _} {s : Set α} [DecidablePred (· ∈ s)] {x : sᶜ} :
    (Equivₓ.Set.sumCompl s).symm x = Sum.inr x := by
  cases' x with x hx <;> exact set.sum_compl_symm_apply_of_not_mem hx

/-- `sum_diff_subset s t` is the natural equivalence between
`s ⊕ (t \ s)` and `t`, where `s` and `t` are two sets. -/
protected def sumDiffSubset {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] : Sum s (t \ s : Set α) ≃ t :=
  calc
    Sum s (t \ s : Set α) ≃ (s ∪ t \ s : Set α) :=
      (Equivₓ.Set.union
          (by
            simp [← inter_diff_self])).symm
    _ ≃ t :=
      Equivₓ.Set.ofEq
        (by
          simp [← union_diff_self, ← union_eq_self_of_subset_left h])
    

@[simp]
theorem sum_diff_subset_apply_inl {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] (x : s) :
    Equivₓ.Set.sumDiffSubset h (Sum.inl x) = inclusion h x :=
  rfl

@[simp]
theorem sum_diff_subset_apply_inr {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] (x : t \ s) :
    Equivₓ.Set.sumDiffSubset h (Sum.inr x) = inclusion (diff_subset t s) x :=
  rfl

theorem sum_diff_subset_symm_apply_of_mem {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] {x : t} (hx : x.1 ∈ s) :
    (Equivₓ.Set.sumDiffSubset h).symm x = Sum.inl ⟨x, hx⟩ := by
  apply (Equivₓ.Set.sumDiffSubset h).Injective
  simp only [← apply_symm_apply, ← sum_diff_subset_apply_inl]
  exact Subtype.eq rfl

theorem sum_diff_subset_symm_apply_of_not_mem {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] {x : t}
    (hx : x.1 ∉ s) : (Equivₓ.Set.sumDiffSubset h).symm x = Sum.inr ⟨x, ⟨x.2, hx⟩⟩ := by
  apply (Equivₓ.Set.sumDiffSubset h).Injective
  simp only [← apply_symm_apply, ← sum_diff_subset_apply_inr]
  exact Subtype.eq rfl

/-- If `s` is a set with decidable membership, then the sum of `s ∪ t` and `s ∩ t` is equivalent
to `s ⊕ t`. -/
protected def unionSumInter {α : Type u} (s t : Set α) [DecidablePred (· ∈ s)] :
    Sum (s ∪ t : Set α) (s ∩ t : Set α) ≃ Sum s t :=
  calc
    Sum (s ∪ t : Set α) (s ∩ t : Set α) ≃ Sum (s ∪ t \ s : Set α) (s ∩ t : Set α) := by
      rw [union_diff_self]
    _ ≃ Sum (Sum s (t \ s : Set α)) (s ∩ t : Set α) :=
      sumCongr (set.union <| subset_empty_iff.2 (inter_diff_self _ _)) (Equivₓ.refl _)
    _ ≃ Sum s (Sum (t \ s : Set α) (s ∩ t : Set α)) := sumAssoc _ _ _
    _ ≃ Sum s (t \ s ∪ s ∩ t : Set α) :=
      sumCongr (Equivₓ.refl _)
        (by
          refine' (set.union' (· ∉ s) _ _).symm
          exacts[fun x hx => hx.2, fun x hx => not_not_intro hx.1])
    _ ≃ Sum s t := by
      rw [(_ : t \ s ∪ s ∩ t = t)]
      rw [union_comm, inter_comm, inter_union_diff]
    

/-- Given an equivalence `e₀` between sets `s : set α` and `t : set β`, the set of equivalences
`e : α ≃ β` such that `e ↑x = ↑(e₀ x)` for each `x : s` is equivalent to the set of equivalences
between `sᶜ` and `tᶜ`. -/
protected def compl {α : Type u} {β : Type v} {s : Set α} {t : Set β} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (e₀ : s ≃ t) : { e : α ≃ β // ∀ x : s, e x = e₀ x } ≃ ((sᶜ : Set α) ≃ (tᶜ : Set β)) where
  toFun := fun e =>
    subtypeEquiv e fun a =>
      not_congr <|
        Iff.symm <|
          MapsTo.mem_iff (maps_to_iff_exists_map_subtype.2 ⟨e₀, e.2⟩)
            (SurjOn.maps_to_compl (surj_on_iff_exists_map_subtype.2 ⟨t, e₀, Subset.refl t, e₀.Surjective, e.2⟩)
              e.1.Injective)
  invFun := fun e₁ =>
    Subtype.mk
      (calc
        α ≃ Sum s (sᶜ : Set α) := (Set.sumCompl s).symm
        _ ≃ Sum t (tᶜ : Set β) := e₀.sumCongr e₁
        _ ≃ β := Set.sumCompl t
        )
      fun x => by
      simp only [← Sum.map_inl, ← trans_apply, ← sum_congr_apply, ← set.sum_compl_apply_inl, ← set.sum_compl_symm_apply]
  left_inv := fun e => by
    ext x
    by_cases' hx : x ∈ s
    · simp only [← set.sum_compl_symm_apply_of_mem hx, e.prop ⟨x, hx⟩, ← Sum.map_inl, ← sum_congr_apply, ← trans_apply,
        ← Subtype.coe_mk, ← set.sum_compl_apply_inl]
      
    · simp only [← set.sum_compl_symm_apply_of_not_mem hx, ← Sum.map_inr, ← subtype_equiv_apply, ←
        set.sum_compl_apply_inr, ← trans_apply, ← sum_congr_apply, ← Subtype.coe_mk]
      
  right_inv := fun e =>
    Equivₓ.ext fun x => by
      simp only [← Sum.map_inr, ← subtype_equiv_apply, ← set.sum_compl_apply_inr, ← Function.comp_app, ←
        sum_congr_apply, ← Equivₓ.coe_trans, ← Subtype.coe_eta, ← Subtype.coe_mk, ← set.sum_compl_symm_apply_compl]

/-- The set product of two sets is equivalent to the type product of their coercions to types. -/
protected def prod {α β} (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ s × t :=
  @subtypeProdEquivProd α β s t

/-- The set `set.pi set.univ s` is equivalent to `Π a, s a`. -/
@[simps]
protected def univPi {α : Type _} {β : α → Type _} (s : ∀ a, Set (β a)) : Pi Univ s ≃ ∀ a, s a where
  toFun := fun f a => ⟨(f : ∀ a, β a) a, f.2 a (mem_univ a)⟩
  invFun := fun f => ⟨fun a => f a, fun a ha => (f a).2⟩
  left_inv := fun ⟨f, hf⟩ => by
    ext a
    rfl
  right_inv := fun f => by
    ext a
    rfl

/-- If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`. -/
protected noncomputable def imageOfInjOn {α β} (f : α → β) (s : Set α) (H : InjOn f s) : s ≃ f '' s :=
  ⟨fun p => ⟨f p, mem_image_of_mem f p.2⟩, fun p => ⟨Classical.some p.2, (Classical.some_spec p.2).1⟩, fun ⟨x, h⟩ =>
    Subtype.eq (H (Classical.some_spec (mem_image_of_mem f h)).1 h (Classical.some_spec (mem_image_of_mem f h)).2),
    fun ⟨y, h⟩ => Subtype.eq (Classical.some_spec h).2⟩

/-- If `f` is an injective function, then `s` is equivalent to `f '' s`. -/
@[simps apply]
protected noncomputable def image {α β} (f : α → β) (s : Set α) (H : Injective f) : s ≃ f '' s :=
  Equivₓ.Set.imageOfInjOn f s (H.InjOn s)

@[simp]
protected theorem image_symm_apply {α β} (f : α → β) (s : Set α) (H : Injective f) (x : α) (h : x ∈ s) :
    (Set.image f s H).symm ⟨f x, ⟨x, ⟨h, rfl⟩⟩⟩ = ⟨x, h⟩ := by
  apply (Set.Image f s H).Injective
  simp [← (Set.Image f s H).apply_symm_apply]

theorem image_symm_preimage {α β} {f : α → β} (hf : Injective f) (u s : Set α) :
    (fun x => (Set.image f s hf).symm x : f '' s → α) ⁻¹' u = coe ⁻¹' (f '' u) := by
  ext ⟨b, a, has, rfl⟩
  have : ∀ h : ∃ a', a' ∈ s ∧ a' = a, Classical.some h = a := fun h => (Classical.some_spec h).2
  simp [← Equivₓ.Set.image, ← Equivₓ.Set.imageOfInjOn, ← hf.eq_iff, ← this]

/-- If `α` is equivalent to `β`, then `set α` is equivalent to `set β`. -/
@[simps]
protected def congr {α β : Type _} (e : α ≃ β) : Set α ≃ Set β :=
  ⟨fun s => e '' s, fun t => e.symm '' t, symm_image_image e, symm_image_image e.symm⟩

/-- The set `{x ∈ s | t x}` is equivalent to the set of `x : s` such that `t x`. -/
protected def sep {α : Type u} (s : Set α) (t : α → Prop) : ({ x ∈ s | t x } : Set α) ≃ { x : s | t x } :=
  (Equivₓ.subtypeSubtypeEquivSubtypeInter s t).symm

/-- The set `𝒫 S := {x | x ⊆ S}` is equivalent to the type `set S`. -/
protected def powerset {α} (S : Set α) : 𝒫 S ≃ Set S where
  toFun := fun x : 𝒫 S => coe ⁻¹' (x : Set α)
  invFun := fun x : Set S =>
    ⟨coe '' x, by
      rintro _ ⟨a : S, _, rfl⟩ <;> exact a.2⟩
  left_inv := fun x => by
    ext y <;> exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨_, x.2 h⟩, h, rfl⟩⟩
  right_inv := fun x => by
    ext <;> simp

/-- If `s` is a set in `range f`,
then its image under `range_splitting f` is in bijection (via `f`) with `s`.
-/
@[simps]
noncomputable def rangeSplittingImageEquiv {α β : Type _} (f : α → β) (s : Set (Range f)) :
    rangeSplitting f '' s ≃ s where
  toFun := fun x =>
    ⟨⟨f x, by
        simp ⟩,
      by
      rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
      simpa [← apply_range_splitting f] using m⟩
  invFun := fun x => ⟨rangeSplitting f x, ⟨x, ⟨x.2, rfl⟩⟩⟩
  left_inv := fun x => by
    rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
    simp [← apply_range_splitting f]
  right_inv := fun x => by
    simp [← apply_range_splitting f]

end Set

/-- If `f : α → β` has a left-inverse when `α` is nonempty, then `α` is computably equivalent to the
range of `f`.

While awkward, the `nonempty α` hypothesis on `f_inv` and `hf` allows this to be used when `α` is
empty too. This hypothesis is absent on analogous definitions on stronger `equiv`s like
`linear_equiv.of_left_inverse` and `ring_equiv.of_left_inverse` as their typeclass assumptions
are already sufficient to ensure non-emptiness. -/
@[simps]
def ofLeftInverse {α β : Sort _} (f : α → β) (f_inv : Nonempty α → β → α)
    (hf : ∀ h : Nonempty α, LeftInverse (f_inv h) f) : α ≃ Range f where
  toFun := fun a => ⟨f a, a, rfl⟩
  invFun := fun b => f_inv (nonempty_of_exists b.2) b
  left_inv := fun a => hf ⟨a⟩ a
  right_inv := fun ⟨b, a, ha⟩ => Subtype.eq <| show f (f_inv ⟨a⟩ b) = b from Eq.trans (congr_arg f <| ha ▸ hf _ a) ha

/-- If `f : α → β` has a left-inverse, then `α` is computably equivalent to the range of `f`.

Note that if `α` is empty, no such `f_inv` exists and so this definition can't be used, unlike
the stronger but less convenient `of_left_inverse`. -/
abbrev ofLeftInverse' {α β : Sort _} (f : α → β) (f_inv : β → α) (hf : LeftInverse f_inv f) : α ≃ Range f :=
  ofLeftInverse f (fun _ => f_inv) fun _ => hf

/-- If `f : α → β` is an injective function, then domain `α` is equivalent to the range of `f`. -/
@[simps apply]
noncomputable def ofInjective {α β} (f : α → β) (hf : Injective f) : α ≃ Range f :=
  Equivₓ.ofLeftInverse f (fun h => Function.invFun f) fun h => Function.left_inverse_inv_fun hf

theorem apply_of_injective_symm {α β} {f : α → β} (hf : Injective f) (b : Range f) :
    f ((ofInjective f hf).symm b) = b :=
  Subtype.ext_iff.1 <| (ofInjective f hf).apply_symm_apply b

@[simp]
theorem of_injective_symm_apply {α β} {f : α → β} (hf : Injective f) (a : α) :
    (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a := by
  apply (of_injective f hf).Injective
  simp [← apply_of_injective_symm hf]

theorem coe_of_injective_symm {α β} {f : α → β} (hf : Injective f) :
    ((ofInjective f hf).symm : Range f → α) = rangeSplitting f := by
  ext ⟨y, x, rfl⟩
  apply hf
  simp [← apply_range_splitting f]

@[simp]
theorem self_comp_of_injective_symm {α β} {f : α → β} (hf : Injective f) : f ∘ (ofInjective f hf).symm = coe :=
  funext fun x => apply_of_injective_symm hf x

theorem of_left_inverse_eq_of_injective {α β : Type _} (f : α → β) (f_inv : Nonempty α → β → α)
    (hf : ∀ h : Nonempty α, LeftInverse (f_inv h) f) :
    ofLeftInverse f f_inv hf =
      ofInjective f
        ((em (Nonempty α)).elim (fun h => (hf h).Injective) fun h _ _ _ => by
          have : Subsingleton α := subsingleton_of_not_nonempty h
          simp ) :=
  by
  ext
  simp

theorem of_left_inverse'_eq_of_injective {α β : Type _} (f : α → β) (f_inv : β → α) (hf : LeftInverse f_inv f) :
    ofLeftInverse' f f_inv hf = ofInjective f hf.Injective := by
  ext
  simp

protected theorem set_forall_iff {α β} (e : α ≃ β) {p : Set α → Prop} : (∀ a, p a) ↔ ∀ a, p (e ⁻¹' a) :=
  e.Injective.preimage_surjective.forall

theorem preimage_pi_equiv_pi_subtype_prod_symm_pi {α : Type _} {β : α → Type _} (p : α → Prop) [DecidablePred p]
    (s : ∀ i, Set (β i)) :
    (piEquivPiSubtypeProd p β).symm ⁻¹' Pi Univ s =
      (Pi Univ fun i : { i // p i } => s i) ×ˢ Pi Univ fun i : { i // ¬p i } => s i :=
  by
  ext ⟨f, g⟩
  simp only [← mem_preimage, ← mem_univ_pi, ← prod_mk_mem_set_prod_eq, ← Subtype.forall, forall_and_distrib]
  refine' forall_congrₓ fun i => _
  dsimp' only [← Subtype.coe_mk]
  by_cases' hi : p i <;> simp [← hi]

/-- `sigma_fiber_equiv f` for `f : α → β` is the natural equivalence between
the type of all preimages of points under `f` and the total space `α`. -/
-- See also `equiv.sigma_fiber_equiv`.
@[simps]
def sigmaPreimageEquiv {α β} (f : α → β) : (Σb, f ⁻¹' {b}) ≃ α :=
  sigmaFiberEquiv f

/-- A family of equivalences between preimages of points gives an equivalence between domains. -/
-- See also `equiv.of_fiber_equiv`.
@[simps]
def ofPreimageEquiv {α β γ} {f : α → γ} {g : β → γ} (e : ∀ c, f ⁻¹' {c} ≃ g ⁻¹' {c}) : α ≃ β :=
  Equivₓ.ofFiberEquiv e

theorem of_preimage_equiv_map {α β γ} {f : α → γ} {g : β → γ} (e : ∀ c, f ⁻¹' {c} ≃ g ⁻¹' {c}) (a : α) :
    g (ofPreimageEquiv e a) = f a :=
  Equivₓ.of_fiber_equiv_map e a

end Equivₓ

/-- If a function is a bijection between two sets `s` and `t`, then it induces an
equivalence between the types `↥s` and `↥t`. -/
noncomputable def Set.BijOn.equiv {α : Type _} {β : Type _} {s : Set α} {t : Set β} (f : α → β) (h : BijOn f s t) :
    s ≃ t :=
  Equivₓ.ofBijective _ h.Bijective

/-- The composition of an updated function with an equiv on a subset can be expressed as an
updated function. -/
theorem dite_comp_equiv_update {α : Type _} {β : Sort _} {γ : Sort _} {s : Set α} (e : β ≃ s) (v : β → γ) (w : α → γ)
    (j : β) (x : γ) [DecidableEq β] [DecidableEq α] [∀ j, Decidable (j ∈ s)] :
    (fun i : α => if h : i ∈ s then (Function.update v j x) (e.symm ⟨i, h⟩) else w i) =
      Function.update (fun i : α => if h : i ∈ s then v (e.symm ⟨i, h⟩) else w i) (e j) x :=
  by
  ext i
  by_cases' h : i ∈ s
  · rw [dif_pos h, Function.update_apply_equiv_apply, Equivₓ.symm_symm, Function.comp, Function.update_apply,
      Function.update_apply, dif_pos h]
    have h_coe : (⟨i, h⟩ : s) = e j ↔ i = e j :=
      subtype.ext_iff.trans
        (by
          rw [Subtype.coe_mk])
    simp_rw [h_coe]
    
  · have : i ≠ e j := by
      contrapose! h
      have : (e j : α) ∈ s := (e j).2
      rwa [← h] at this
    simp [← h, ← this]
    

