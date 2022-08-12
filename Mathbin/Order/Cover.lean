/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Floris van Doorn
-/
import Mathbin.Data.Set.Intervals.OrdConnected

/-!
# The covering relation

This file defines the covering relation in an order. `b` is said to cover `a` if `a < b` and there
is no element in between. We say that `b` weakly covers `a` if `a ≤ b` and there is no element
between `a` and `b`. In a partial order this is equivalent to `a ⋖ b ∨ a = b`, in a preorder this
is equivalent to `a ⋖ b ∨ (a ≤ b ∧ b ≤ a)`

## Notation

* `a ⋖ b` means that `b` covers `a`.
* `a ⩿ b` means that `b` weakly covers `a`.
-/


open Set OrderDual

variable {α β : Type _}

section WeaklyCovers

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] {a b c : α}

/-- `wcovby a b` means that `a = b` or `b` covers `a`.
This means that `a ≤ b` and there is no element in between.
-/
def Wcovby (a b : α) : Prop :=
  a ≤ b ∧ ∀ ⦃c⦄, a < c → ¬c < b

-- mathport name: «expr ⩿ »
infixl:50 " ⩿ " => Wcovby

theorem Wcovby.le (h : a ⩿ b) : a ≤ b :=
  h.1

theorem Wcovby.refl (a : α) : a ⩿ a :=
  ⟨le_rfl, fun c hc => hc.not_lt⟩

theorem Wcovby.rfl : a ⩿ a :=
  Wcovby.refl a

protected theorem Eq.wcovby (h : a = b) : a ⩿ b :=
  h ▸ Wcovby.rfl

theorem wcovby_of_le_of_le (h1 : a ≤ b) (h2 : b ≤ a) : a ⩿ b :=
  ⟨h1, fun c hac hcb => (hac.trans hcb).not_le h2⟩

alias wcovby_of_le_of_le ← LE.le.wcovby_of_le

theorem Wcovby.wcovby_iff_le (hab : a ⩿ b) : b ⩿ a ↔ b ≤ a :=
  ⟨fun h => h.le, fun h => h.wcovby_of_le hab.le⟩

theorem wcovby_of_eq_or_eq (hab : a ≤ b) (h : ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b) : a ⩿ b :=
  ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.Ne⟩

/-- If `a ≤ b`, then `b` does not cover `a` iff there's an element in between. -/
theorem not_wcovby_iff (h : a ≤ b) : ¬a ⩿ b ↔ ∃ c, a < c ∧ c < b := by
  simp_rw [Wcovby, h, true_andₓ, not_forall, exists_prop, not_not]

instance Wcovby.is_refl : IsRefl α (· ⩿ ·) :=
  ⟨Wcovby.refl⟩

theorem Wcovby.Ioo_eq (h : a ⩿ b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun x hx => h.2 hx.1 hx.2

theorem Wcovby.of_image (f : α ↪o β) (h : f a ⩿ f b) : a ⩿ b :=
  ⟨f.le_iff_le.mp h.le, fun c hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

theorem Wcovby.image (f : α ↪o β) (hab : a ⩿ b) (h : (Range f).OrdConnected) : f a ⩿ f b := by
  refine' ⟨f.monotone hab.le, fun c ha hb => _⟩
  obtain ⟨c, rfl⟩ := h.out (mem_range_self _) (mem_range_self _) ⟨ha.le, hb.le⟩
  rw [f.lt_iff_lt] at ha hb
  exact hab.2 ha hb

theorem Set.OrdConnected.apply_wcovby_apply_iff (f : α ↪o β) (h : (Range f).OrdConnected) : f a ⩿ f b ↔ a ⩿ b :=
  ⟨fun h2 => h2.of_image f, fun hab => hab.Image f h⟩

@[simp]
theorem apply_wcovby_apply_iff {E : Type _} [OrderIsoClass E α β] (e : E) : e a ⩿ e b ↔ a ⩿ b :=
  (ord_connected_range (e : α ≃o β)).apply_wcovby_apply_iff ((e : α ≃o β) : α ↪o β)

@[simp]
theorem to_dual_wcovby_to_dual_iff : toDual b ⩿ toDual a ↔ a ⩿ b :=
  and_congr_right' <| forall_congrₓ fun c => forall_swap

@[simp]
theorem of_dual_wcovby_of_dual_iff {a b : αᵒᵈ} : ofDual a ⩿ ofDual b ↔ b ⩿ a :=
  and_congr_right' <| forall_congrₓ fun c => forall_swap

alias to_dual_wcovby_to_dual_iff ↔ _ Wcovby.to_dual

alias of_dual_wcovby_of_dual_iff ↔ _ Wcovby.of_dual

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] {a b c : α}

theorem Wcovby.eq_or_eq (h : a ⩿ b) (h2 : a ≤ c) (h3 : c ≤ b) : c = a ∨ c = b := by
  rcases h2.eq_or_lt with (h2 | h2)
  · exact Or.inl h2.symm
    
  rcases h3.eq_or_lt with (h3 | h3)
  · exact Or.inr h3
    
  exact (h.2 h2 h3).elim

theorem Wcovby.le_and_le_iff (h : a ⩿ b) : a ≤ c ∧ c ≤ b ↔ c = a ∨ c = b := by
  refine' ⟨fun h2 => h.eq_or_eq h2.1 h2.2, _⟩
  rintro (rfl | rfl)
  exacts[⟨le_rfl, h.le⟩, ⟨h.le, le_rfl⟩]

theorem Wcovby.Icc_eq (h : a ⩿ b) : Icc a b = {a, b} := by
  ext c
  exact h.le_and_le_iff

theorem Wcovby.Ico_subset (h : a ⩿ b) : Ico a b ⊆ {a} := by
  rw [← Icc_diff_right, h.Icc_eq, diff_singleton_subset_iff, pair_comm]

theorem Wcovby.Ioc_subset (h : a ⩿ b) : Ioc a b ⊆ {b} := by
  rw [← Icc_diff_left, h.Icc_eq, diff_singleton_subset_iff]

end PartialOrderₓ

end WeaklyCovers

section LT

variable [LT α] {a b : α}

/-- `covby a b` means that `b` covers `a`: `a < b` and there is no element in between. -/
def Covby (a b : α) : Prop :=
  a < b ∧ ∀ ⦃c⦄, a < c → ¬c < b

-- mathport name: «expr ⋖ »
infixl:50 " ⋖ " => Covby

theorem Covby.lt (h : a ⋖ b) : a < b :=
  h.1

/-- If `a < b`, then `b` does not cover `a` iff there's an element in between. -/
theorem not_covby_iff (h : a < b) : ¬a ⋖ b ↔ ∃ c, a < c ∧ c < b := by
  simp_rw [Covby, h, true_andₓ, not_forall, exists_prop, not_not]

alias not_covby_iff ↔ exists_lt_lt_of_not_covby _

alias exists_lt_lt_of_not_covby ← LT.lt.exists_lt_lt

/-- In a dense order, nothing covers anything. -/
theorem not_covby [DenselyOrdered α] : ¬a ⋖ b := fun h =>
  let ⟨c, hc⟩ := exists_between h.1
  h.2 hc.1 hc.2

theorem densely_ordered_iff_forall_not_covby : DenselyOrdered α ↔ ∀ a b : α, ¬a ⋖ b :=
  ⟨fun h a b => @not_covby _ _ _ _ h, fun h => ⟨fun a b hab => exists_lt_lt_of_not_covby hab <| h _ _⟩⟩

@[simp]
theorem to_dual_covby_to_dual_iff : toDual b ⋖ toDual a ↔ a ⋖ b :=
  and_congr_right' <| forall_congrₓ fun c => forall_swap

@[simp]
theorem of_dual_covby_of_dual_iff {a b : αᵒᵈ} : ofDual a ⋖ ofDual b ↔ b ⋖ a :=
  and_congr_right' <| forall_congrₓ fun c => forall_swap

alias to_dual_covby_to_dual_iff ↔ _ Covby.to_dual

alias of_dual_covby_of_dual_iff ↔ _ Covby.of_dual

end LT

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] {a b : α}

theorem Covby.le (h : a ⋖ b) : a ≤ b :=
  h.1.le

protected theorem Covby.ne (h : a ⋖ b) : a ≠ b :=
  h.lt.Ne

theorem Covby.ne' (h : a ⋖ b) : b ≠ a :=
  h.lt.ne'

protected theorem Covby.wcovby (h : a ⋖ b) : a ⩿ b :=
  ⟨h.le, h.2⟩

theorem Wcovby.covby_of_not_le (h : a ⩿ b) (h2 : ¬b ≤ a) : a ⋖ b :=
  ⟨h.le.lt_of_not_le h2, h.2⟩

theorem Wcovby.covby_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b :=
  ⟨h2, h.2⟩

theorem covby_iff_wcovby_and_lt : a ⋖ b ↔ a ⩿ b ∧ a < b :=
  ⟨fun h => ⟨h.Wcovby, h.lt⟩, fun h => h.1.covby_of_lt h.2⟩

theorem covby_iff_wcovby_and_not_le : a ⋖ b ↔ a ⩿ b ∧ ¬b ≤ a :=
  ⟨fun h => ⟨h.Wcovby, h.lt.not_le⟩, fun h => h.1.covby_of_not_le h.2⟩

theorem wcovby_iff_covby_or_le_and_le : a ⩿ b ↔ a ⋖ b ∨ a ≤ b ∧ b ≤ a :=
  ⟨fun h => or_iff_not_imp_right.mpr fun h' => h.covby_of_not_le fun hba => h' ⟨h.le, hba⟩, fun h' =>
    h'.elim (fun h => h.Wcovby) fun h => h.1.wcovby_of_le h.2⟩

instance : IsNonstrictStrictOrder α (· ⩿ ·) (· ⋖ ·) :=
  ⟨fun a b => covby_iff_wcovby_and_not_le.trans <| and_congr_right fun h => h.wcovby_iff_le.Not.symm⟩

instance Covby.is_irrefl : IsIrrefl α (· ⋖ ·) :=
  ⟨fun a ha => ha.Ne rfl⟩

theorem Covby.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
  h.Wcovby.Ioo_eq

theorem Covby.of_image (f : α ↪o β) (h : f a ⋖ f b) : a ⋖ b :=
  ⟨f.lt_iff_lt.mp h.lt, fun c hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

theorem Covby.image (f : α ↪o β) (hab : a ⋖ b) (h : (Range f).OrdConnected) : f a ⋖ f b :=
  (hab.Wcovby.Image f h).covby_of_lt <| f.StrictMono hab.lt

theorem Set.OrdConnected.apply_covby_apply_iff (f : α ↪o β) (h : (Range f).OrdConnected) : f a ⋖ f b ↔ a ⋖ b :=
  ⟨Covby.of_image f, fun hab => hab.Image f h⟩

@[simp]
theorem apply_covby_apply_iff {E : Type _} [OrderIsoClass E α β] (e : E) : e a ⋖ e b ↔ a ⋖ b :=
  (ord_connected_range (e : α ≃o β)).apply_covby_apply_iff ((e : α ≃o β) : α ↪o β)

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] {a b : α}

theorem Wcovby.covby_of_ne (h : a ⩿ b) (h2 : a ≠ b) : a ⋖ b :=
  ⟨h.le.lt_of_ne h2, h.2⟩

theorem covby_iff_wcovby_and_ne : a ⋖ b ↔ a ⩿ b ∧ a ≠ b :=
  ⟨fun h => ⟨h.Wcovby, h.Ne⟩, fun h => h.1.covby_of_ne h.2⟩

theorem wcovby_iff_covby_or_eq : a ⩿ b ↔ a ⋖ b ∨ a = b := by
  rw [le_antisymm_iffₓ, wcovby_iff_covby_or_le_and_le]

theorem Covby.Ico_eq (h : a ⋖ b) : Ico a b = {a} := by
  rw [← Ioo_union_left h.lt, h.Ioo_eq, empty_union]

theorem Covby.Ioc_eq (h : a ⋖ b) : Ioc a b = {b} := by
  rw [← Ioo_union_right h.lt, h.Ioo_eq, empty_union]

theorem Covby.Icc_eq (h : a ⋖ b) : Icc a b = {a, b} :=
  h.Wcovby.Icc_eq

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α] {a b c : α}

theorem Covby.Ioi_eq (h : a ⋖ b) : Ioi a = Ici b := by
  rw [← Ioo_union_Ici_eq_Ioi h.lt, h.Ioo_eq, empty_union]

theorem Covby.Iio_eq (h : a ⋖ b) : Iio b = Iic a := by
  rw [← Iic_union_Ioo_eq_Iio h.lt, h.Ioo_eq, union_empty]

theorem Wcovby.le_of_lt (hab : a ⩿ b) (hcb : c < b) : c ≤ a :=
  not_ltₓ.1 fun hac => hab.2 hac hcb

theorem Wcovby.ge_of_gt (hab : a ⩿ b) (hac : a < c) : b ≤ c :=
  not_ltₓ.1 <| hab.2 hac

theorem Covby.le_of_lt (hab : a ⋖ b) : c < b → c ≤ a :=
  hab.Wcovby.le_of_lt

theorem Covby.ge_of_gt (hab : a ⋖ b) : a < c → b ≤ c :=
  hab.Wcovby.ge_of_gt

theorem Covby.unique_left (ha : a ⋖ c) (hb : b ⋖ c) : a = b :=
  (hb.le_of_lt ha.lt).antisymm <| ha.le_of_lt hb.lt

theorem Covby.unique_right (hb : a ⋖ b) (hc : a ⋖ c) : b = c :=
  (hb.ge_of_gt hc.lt).antisymm <| hc.ge_of_gt hb.lt

end LinearOrderₓ

namespace Set

theorem wcovby_insert (x : α) (s : Set α) : s ⩿ insert x s := by
  refine' wcovby_of_eq_or_eq (subset_insert x s) fun t hst h2t => _
  by_cases' h : x ∈ t
  · exact Or.inr (subset_antisymm h2t <| insert_subset.mpr ⟨h, hst⟩)
    
  · refine' Or.inl (subset_antisymm _ hst)
    rwa [← diff_singleton_eq_self h, diff_singleton_subset_iff]
    

theorem covby_insert {x : α} {s : Set α} (hx : x ∉ s) : s ⋖ insert x s :=
  (wcovby_insert x s).covby_of_lt <| ssubset_insert hx

end Set

namespace Prod

variable [PartialOrderₓ α] [PartialOrderₓ β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

@[simp]
theorem swap_wcovby_swap : x.swap ⩿ y.swap ↔ x ⩿ y :=
  apply_wcovby_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

@[simp]
theorem swap_covby_swap : x.swap ⋖ y.swap ↔ x ⋖ y :=
  apply_covby_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

theorem fst_eq_or_snd_eq_of_wcovby : x ⩿ y → x.1 = y.1 ∨ x.2 = y.2 := by
  refine' fun h => of_not_not fun hab => _
  push_neg  at hab
  exact h.2 (mk_lt_mk.2 <| Or.inl ⟨hab.1.lt_of_le h.1.1, le_rfl⟩) (mk_lt_mk.2 <| Or.inr ⟨le_rfl, hab.2.lt_of_le h.1.2⟩)

theorem _root_.wcovby.fst (h : x ⩿ y) : x.1 ⩿ y.1 :=
  ⟨h.1.1, fun c h₁ h₂ => h.2 (mk_lt_mk_iff_left.2 h₁) ⟨⟨h₂.le, h.1.2⟩, fun hc => h₂.not_le hc.1⟩⟩

theorem _root_.wcovby.snd (h : x ⩿ y) : x.2 ⩿ y.2 :=
  ⟨h.1.2, fun c h₁ h₂ => h.2 (mk_lt_mk_iff_right.2 h₁) ⟨⟨h.1.1, h₂.le⟩, fun hc => h₂.not_le hc.2⟩⟩

theorem mk_wcovby_mk_iff_left : (a₁, b) ⩿ (a₂, b) ↔ a₁ ⩿ a₂ := by
  refine' ⟨Wcovby.fst, (And.imp mk_le_mk_iff_left.2) fun h c h₁ h₂ => _⟩
  have : c.2 = b := h₂.le.2.antisymm h₁.le.2
  rw [← @Prod.mk.eta _ _ c, this, mk_lt_mk_iff_left] at h₁ h₂
  exact h h₁ h₂

theorem mk_wcovby_mk_iff_right : (a, b₁) ⩿ (a, b₂) ↔ b₁ ⩿ b₂ :=
  swap_wcovby_swap.trans mk_wcovby_mk_iff_left

theorem mk_covby_mk_iff_left : (a₁, b) ⋖ (a₂, b) ↔ a₁ ⋖ a₂ := by
  simp_rw [covby_iff_wcovby_and_lt, mk_wcovby_mk_iff_left, mk_lt_mk_iff_left]

theorem mk_covby_mk_iff_right : (a, b₁) ⋖ (a, b₂) ↔ b₁ ⋖ b₂ := by
  simp_rw [covby_iff_wcovby_and_lt, mk_wcovby_mk_iff_right, mk_lt_mk_iff_right]

theorem mk_wcovby_mk_iff : (a₁, b₁) ⩿ (a₂, b₂) ↔ a₁ ⩿ a₂ ∧ b₁ = b₂ ∨ b₁ ⩿ b₂ ∧ a₁ = a₂ := by
  refine' ⟨fun h => _, _⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovby h
    · exact Or.inr ⟨mk_wcovby_mk_iff_right.1 h, rfl⟩
      
    · exact Or.inl ⟨mk_wcovby_mk_iff_left.1 h, rfl⟩
      
    
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_wcovby_mk_iff_left.2 h
      
    · exact mk_wcovby_mk_iff_right.2 h
      
    

theorem mk_covby_mk_iff : (a₁, b₁) ⋖ (a₂, b₂) ↔ a₁ ⋖ a₂ ∧ b₁ = b₂ ∨ b₁ ⋖ b₂ ∧ a₁ = a₂ := by
  refine' ⟨fun h => _, _⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovby h.wcovby
    · exact Or.inr ⟨mk_covby_mk_iff_right.1 h, rfl⟩
      
    · exact Or.inl ⟨mk_covby_mk_iff_left.1 h, rfl⟩
      
    
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_covby_mk_iff_left.2 h
      
    · exact mk_covby_mk_iff_right.2 h
      
    

theorem wcovby_iff : x ⩿ y ↔ x.1 ⩿ y.1 ∧ x.2 = y.2 ∨ x.2 ⩿ y.2 ∧ x.1 = y.1 := by
  cases x
  cases y
  exact mk_wcovby_mk_iff

theorem covby_iff : x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1 := by
  cases x
  cases y
  exact mk_covby_mk_iff

end Prod

