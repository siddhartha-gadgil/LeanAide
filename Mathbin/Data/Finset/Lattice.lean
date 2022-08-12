/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Finset.Fold
import Mathbin.Data.Finset.Option
import Mathbin.Data.Finset.Prod
import Mathbin.Data.Multiset.Lattice
import Mathbin.Order.CompleteLattice

/-!
# Lattice operations on finsets
-/


variable {α β γ ι : Type _}

namespace Finset

open Multiset OrderDual

/-! ### sup -/


section Sup

-- TODO: define with just `[has_bot α]` where some lemmas hold without requiring `[order_bot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def sup (s : Finset β) (f : β → α) : α :=
  s.fold (·⊔·) ⊥ f

variable {s s₁ s₂ : Finset β} {f g : β → α}

theorem sup_def : s.sup f = (s.1.map f).sup :=
  rfl

@[simp]
theorem sup_empty : (∅ : Finset β).sup f = ⊥ :=
  fold_empty

@[simp]
theorem sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b⊔s.sup f :=
  fold_cons h

@[simp]
theorem sup_insert [DecidableEq β] {b : β} : (insert b s : Finset β).sup f = f b⊔s.sup f :=
  fold_insert_idem

theorem sup_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) : (s.Image f).sup g = s.sup (g ∘ f) :=
  fold_image_idem

@[simp]
theorem sup_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).sup g = s.sup (g ∘ f) :=
  fold_map

@[simp]
theorem sup_singleton {b : β} : ({b} : Finset β).sup f = f b :=
  sup_singleton

theorem sup_union [DecidableEq β] : (s₁ ∪ s₂).sup f = s₁.sup f⊔s₂.sup f :=
  (Finset.induction_on s₁
      (by
        rw [empty_union, sup_empty, bot_sup_eq]))
    fun a s has ih => by
    rw [insert_union, sup_insert, sup_insert, ih, sup_assoc]

theorem sup_sup : s.sup (f⊔g) = s.sup f⊔s.sup g := by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  · rw [sup_empty, sup_empty, sup_empty, bot_sup_eq]
    
  · rw [sup_cons, sup_cons, sup_cons, h]
    exact sup_sup_sup_comm _ _ _ _
    

theorem sup_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀, ∀ a ∈ s₂, ∀, f a = g a) : s₁.sup f = s₂.sup g := by
  subst hs <;> exact Finset.fold_congr hfg

@[simp]
protected theorem sup_le_iff {a : α} : s.sup f ≤ a ↔ ∀, ∀ b ∈ s, ∀, f b ≤ a := by
  apply Iff.trans Multiset.sup_le
  simp only [← Multiset.mem_map, ← and_imp, ← exists_imp_distrib]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

@[simp]
theorem sup_bUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
    (s.bUnion t).sup f = s.sup fun x => (t x).sup f :=
  eq_of_forall_ge_iff fun c => by
    simp [← @forall_swap _ β]

theorem sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.sup fun _ => c) = c :=
  eq_of_forall_ge_iff fun b => Finset.sup_le_iff.trans h.forall_const

@[simp]
theorem sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact sup_empty
    
  · exact sup_const hs _
    

theorem sup_ite (p : β → Prop) [DecidablePred p] :
    (s.sup fun i => ite (p i) (f i) (g i)) = (s.filter p).sup f⊔(s.filter fun i => ¬p i).sup g :=
  fold_ite _

theorem sup_le {a : α} : (∀, ∀ b ∈ s, ∀, f b ≤ a) → s.sup f ≤ a :=
  Finset.sup_le_iff.2

theorem le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
  Finset.sup_le_iff.1 le_rfl _ hb

theorem sup_mono_fun {g : β → α} (h : ∀, ∀ b ∈ s, ∀, f b ≤ g b) : s.sup f ≤ s.sup g :=
  sup_le fun b hb => le_transₓ (h b hb) (le_sup hb)

theorem sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
  sup_le fun b hb => le_sup (h hb)

theorem sup_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.sup fun b => t.sup (f b)) = t.sup fun c => s.sup fun b => f b c := by
  refine' eq_of_forall_ge_iff fun a => _
  simp_rw [Finset.sup_le_iff]
  exact ⟨fun h c hc b hb => h b hb c hc, fun h b hb c hc => h c hc b hb⟩

@[simp]
theorem sup_attach (s : Finset β) (f : β → α) : (s.attach.sup fun x => f x) = s.sup f :=
  (s.attach.sup_map (Function.Embedding.subtype _) f).symm.trans <| congr_arg _ attach_map_val

/-- See also `finset.product_bUnion`. -/
theorem sup_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s.product t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩ := by
  refine' le_antisymmₓ _ (sup_le fun i hi => sup_le fun i' hi' => le_sup <| mem_product.2 ⟨hi, hi'⟩)
  refine' sup_le _
  rintro ⟨i, i'⟩ hi
  rw [mem_product] at hi
  refine' le_transₓ _ (le_sup hi.1)
  convert le_sup hi.2

theorem sup_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s.product t).sup f = t.sup fun i' => s.sup fun i => f ⟨i, i'⟩ := by
  rw [sup_product_left, sup_comm]

@[simp]
theorem sup_erase_bot [DecidableEq α] (s : Finset α) : (s.erase ⊥).sup id = s.sup id := by
  refine' (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2 fun a ha => _)
  obtain rfl | ha' := eq_or_ne a ⊥
  · exact bot_le
    
  · exact le_sup (mem_erase.2 ⟨ha', ha⟩)
    

theorem sup_sdiff_right {α β : Type _} [GeneralizedBooleanAlgebra α] (s : Finset β) (f : β → α) (a : α) :
    (s.sup fun b => f b \ a) = s.sup f \ a := by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  · rw [sup_empty, sup_empty, bot_sdiff]
    
  · rw [sup_cons, sup_cons, h, sup_sdiff]
    

theorem comp_sup_eq_sup_comp [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_sup : ∀ x y, g (x⊔y) = g x⊔g y) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  Finset.cons_induction_on s bot fun c t hc ih => by
    rw [sup_cons, sup_cons, g_sup, ih]

/-- Computing `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
theorem sup_coe {P : α → Prop} {Pbot : P ⊥} {Psup : ∀ ⦃x y⦄, P x → P y → P (x⊔y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    (@sup _ _ (Subtype.semilatticeSup Psup) (Subtype.orderBot Pbot) t f : α) = t.sup fun x => f x := by
  rw [comp_sup_eq_sup_comp coe] <;> intros <;> rfl

@[simp]
theorem sup_to_finset {α β} [DecidableEq β] (s : Finset α) (f : α → Multiset β) :
    (s.sup f).toFinset = s.sup fun x => (f x).toFinset :=
  comp_sup_eq_sup_comp Multiset.toFinset to_finset_union rfl

theorem subset_range_sup_succ (s : Finset ℕ) : s ⊆ range (s.sup id).succ := fun n hn =>
  mem_range.2 <| Nat.lt_succ_of_leₓ <| le_sup hn

theorem exists_nat_subset_range (s : Finset ℕ) : ∃ n : ℕ, s ⊆ range n :=
  ⟨_, s.subset_range_sup_succ⟩

theorem sup_induction {p : α → Prop} (hb : p ⊥) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁⊔a₂))
    (hs : ∀, ∀ b ∈ s, ∀, p (f b)) : p (s.sup f) := by
  induction' s using Finset.cons_induction with c s hc ih
  · exact hb
    
  · rw [sup_cons]
    apply hp
    · exact hs c (mem_cons.2 (Or.inl rfl))
      
    · exact ih fun b h => hs b (mem_cons.2 (Or.inr h))
      
    

theorem sup_le_of_le_directed {α : Type _} [SemilatticeSup α] [OrderBot α] (s : Set α) (hs : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) (t : Finset α) : (∀, ∀ x ∈ t, ∀, ∃ y ∈ s, x ≤ y) → ∃ x, x ∈ s ∧ t.sup id ≤ x := by
  classical
  apply Finset.induction_on t
  · simpa only [← forall_prop_of_true, ← and_trueₓ, ← forall_prop_of_false, ← bot_le, ← not_false_iff, ← sup_empty, ←
      forall_true_iff, ← not_mem_empty]
    
  · intro a r har ih h
    have incs : ↑r ⊆ ↑(insert a r) := by
      rw [Finset.coe_subset]
      apply Finset.subset_insert
    -- x ∈ s is above the sup of r
    obtain ⟨x, ⟨hxs, hsx_sup⟩⟩ := ih fun x hx => h x <| incs hx
    -- y ∈ s is above a
    obtain ⟨y, hys, hay⟩ := h a (Finset.mem_insert_self a r)
    -- z ∈ s is above x and y
    obtain ⟨z, hzs, ⟨hxz, hyz⟩⟩ := hdir x hxs y hys
    use z, hzs
    rw [sup_insert, id.def, sup_le_iff]
    exact ⟨le_transₓ hay hyz, le_transₓ hsx_sup hxz⟩
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » s)
-- If we acquire sublattices
-- the hypotheses should be reformulated as `s : subsemilattice_sup_bot`
theorem sup_mem (s : Set α) (w₁ : ⊥ ∈ s) (w₂ : ∀ (x y) (_ : x ∈ s) (_ : y ∈ s), x⊔y ∈ s) {ι : Type _} (t : Finset ι)
    (p : ι → α) (h : ∀, ∀ i ∈ t, ∀, p i ∈ s) : t.sup p ∈ s :=
  @sup_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h

@[simp]
theorem sup_eq_bot_iff (f : β → α) (S : Finset β) : S.sup f = ⊥ ↔ ∀, ∀ s ∈ S, ∀, f s = ⊥ := by
  classical
  induction' S using Finset.induction with a S haS hi <;> simp [*]

end Sup

theorem sup_eq_supr [CompleteLattice β] (s : Finset α) (f : α → β) : s.sup f = ⨆ a ∈ s, f a :=
  le_antisymmₓ (Finset.sup_le fun a ha => le_supr_of_le a <| le_supr _ ha)
    (supr_le fun a => supr_le fun ha => le_sup ha)

theorem sup_id_eq_Sup [CompleteLattice α] (s : Finset α) : s.sup id = sup s := by
  simp [← Sup_eq_supr, ← sup_eq_supr]

theorem sup_id_set_eq_sUnion (s : Finset (Set α)) : s.sup id = ⋃₀↑s :=
  sup_id_eq_Sup _

@[simp]
theorem sup_set_eq_bUnion (s : Finset α) (f : α → Set β) : s.sup f = ⋃ x ∈ s, f x :=
  sup_eq_supr _ _

theorem sup_eq_Sup_image [CompleteLattice β] (s : Finset α) (f : α → β) : s.sup f = sup (f '' s) := by
  classical
  rw [← Finset.coe_image, ← sup_id_eq_Sup, sup_image, Function.comp.left_id]

/-! ### inf -/


section Inf

-- TODO: define with just `[has_top α]` where some lemmas hold without requiring `[order_top α]`
variable [SemilatticeInf α] [OrderTop α]

/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def inf (s : Finset β) (f : β → α) : α :=
  s.fold (·⊓·) ⊤ f

variable {s s₁ s₂ : Finset β} {f g : β → α}

theorem inf_def : s.inf f = (s.1.map f).inf :=
  rfl

@[simp]
theorem inf_empty : (∅ : Finset β).inf f = ⊤ :=
  fold_empty

@[simp]
theorem inf_cons {b : β} (h : b ∉ s) : (cons b s h).inf f = f b⊓s.inf f :=
  @sup_cons αᵒᵈ _ _ _ _ _ _ h

@[simp]
theorem inf_insert [DecidableEq β] {b : β} : (insert b s : Finset β).inf f = f b⊓s.inf f :=
  fold_insert_idem

theorem inf_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) : (s.Image f).inf g = s.inf (g ∘ f) :=
  fold_image_idem

@[simp]
theorem inf_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).inf g = s.inf (g ∘ f) :=
  fold_map

@[simp]
theorem inf_singleton {b : β} : ({b} : Finset β).inf f = f b :=
  inf_singleton

theorem inf_union [DecidableEq β] : (s₁ ∪ s₂).inf f = s₁.inf f⊓s₂.inf f :=
  @sup_union αᵒᵈ _ _ _ _ _ _ _

theorem inf_inf : s.inf (f⊓g) = s.inf f⊓s.inf g :=
  @sup_sup αᵒᵈ _ _ _ _ _ _

theorem inf_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀, ∀ a ∈ s₂, ∀, f a = g a) : s₁.inf f = s₂.inf g := by
  subst hs <;> exact Finset.fold_congr hfg

@[simp]
theorem inf_bUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
    (s.bUnion t).inf f = s.inf fun x => (t x).inf f :=
  @sup_bUnion αᵒᵈ _ _ _ _ _ _ _ _

theorem inf_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.inf fun _ => c) = c :=
  @sup_const αᵒᵈ _ _ _ _ h _

@[simp]
theorem inf_top (s : Finset β) : (s.inf fun _ => ⊤) = (⊤ : α) :=
  @sup_bot αᵒᵈ _ _ _ _

theorem le_inf_iff {a : α} : a ≤ s.inf f ↔ ∀, ∀ b ∈ s, ∀, a ≤ f b :=
  @Finset.sup_le_iff αᵒᵈ _ _ _ _ _ _

theorem inf_le {b : β} (hb : b ∈ s) : s.inf f ≤ f b :=
  le_inf_iff.1 le_rfl _ hb

theorem le_inf {a : α} : (∀, ∀ b ∈ s, ∀, a ≤ f b) → a ≤ s.inf f :=
  le_inf_iff.2

theorem inf_mono_fun {g : β → α} (h : ∀, ∀ b ∈ s, ∀, f b ≤ g b) : s.inf f ≤ s.inf g :=
  le_inf fun b hb => le_transₓ (inf_le hb) (h b hb)

theorem inf_mono (h : s₁ ⊆ s₂) : s₂.inf f ≤ s₁.inf f :=
  le_inf fun b hb => inf_le (h hb)

theorem inf_attach (s : Finset β) (f : β → α) : (s.attach.inf fun x => f x) = s.inf f :=
  @sup_attach αᵒᵈ _ _ _ _ _

theorem inf_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.inf fun b => t.inf (f b)) = t.inf fun c => s.inf fun b => f b c :=
  @sup_comm αᵒᵈ _ _ _ _ _ _ _

theorem inf_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s.product t).inf f = s.inf fun i => t.inf fun i' => f ⟨i, i'⟩ :=
  @sup_product_left αᵒᵈ _ _ _ _ _ _ _

theorem inf_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s.product t).inf f = t.inf fun i' => s.inf fun i => f ⟨i, i'⟩ :=
  @sup_product_right αᵒᵈ _ _ _ _ _ _ _

@[simp]
theorem inf_erase_top [DecidableEq α] (s : Finset α) : (s.erase ⊤).inf id = s.inf id :=
  @sup_erase_bot αᵒᵈ _ _ _ _

theorem sup_sdiff_left {α β : Type _} [BooleanAlgebra α] (s : Finset β) (f : β → α) (a : α) :
    (s.sup fun b => a \ f b) = a \ s.inf f := by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  · rw [sup_empty, inf_empty, sdiff_top]
    
  · rw [sup_cons, inf_cons, h, sdiff_inf]
    

theorem inf_sdiff_left {α β : Type _} [BooleanAlgebra α] {s : Finset β} (hs : s.Nonempty) (f : β → α) (a : α) :
    (s.inf fun b => a \ f b) = a \ s.sup f := by
  induction' hs using Finset.Nonempty.cons_induction with b b t _ _ h
  · rw [sup_singleton, inf_singleton]
    
  · rw [sup_cons, inf_cons, h, sdiff_sup]
    

theorem inf_sdiff_right {α β : Type _} [BooleanAlgebra α] {s : Finset β} (hs : s.Nonempty) (f : β → α) (a : α) :
    (s.inf fun b => f b \ a) = s.inf f \ a := by
  induction' hs using Finset.Nonempty.cons_induction with b b t _ _ h
  · rw [inf_singleton, inf_singleton]
    
  · rw [inf_cons, inf_cons, h, inf_sdiff]
    

theorem comp_inf_eq_inf_comp [SemilatticeInf γ] [OrderTop γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_inf : ∀ x y, g (x⊓y) = g x⊓g y) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  @comp_sup_eq_sup_comp αᵒᵈ _ γᵒᵈ _ _ _ _ _ _ _ g_inf top

/-- Computing `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/
theorem inf_coe {P : α → Prop} {Ptop : P ⊤} {Pinf : ∀ ⦃x y⦄, P x → P y → P (x⊓y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    (@inf _ _ (Subtype.semilatticeInf Pinf) (Subtype.orderTop Ptop) t f : α) = t.inf fun x => f x :=
  @sup_coe αᵒᵈ _ _ _ _ Ptop Pinf t f

theorem inf_induction {p : α → Prop} (ht : p ⊤) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁⊓a₂))
    (hs : ∀, ∀ b ∈ s, ∀, p (f b)) : p (s.inf f) :=
  @sup_induction αᵒᵈ _ _ _ _ _ _ ht hp hs

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » s)
theorem inf_mem (s : Set α) (w₁ : ⊤ ∈ s) (w₂ : ∀ (x y) (_ : x ∈ s) (_ : y ∈ s), x⊓y ∈ s) {ι : Type _} (t : Finset ι)
    (p : ι → α) (h : ∀, ∀ i ∈ t, ∀, p i ∈ s) : t.inf p ∈ s :=
  @inf_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h

@[simp]
theorem inf_eq_top_iff (f : β → α) (S : Finset β) : S.inf f = ⊤ ↔ ∀, ∀ s ∈ S, ∀, f s = ⊤ :=
  @Finset.sup_eq_bot_iff αᵒᵈ _ _ _ _ _

end Inf

@[simp]
theorem to_dual_sup [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → α) :
    toDual (s.sup f) = s.inf (to_dual ∘ f) :=
  rfl

@[simp]
theorem to_dual_inf [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → α) :
    toDual (s.inf f) = s.sup (to_dual ∘ f) :=
  rfl

@[simp]
theorem of_dual_sup [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.sup f) = s.inf (of_dual ∘ f) :=
  rfl

@[simp]
theorem of_dual_inf [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.inf f) = s.sup (of_dual ∘ f) :=
  rfl

section DistribLattice

variable [DistribLattice α]

section OrderBot

variable [OrderBot α] {s : Finset β} {f : β → α} {a : α}

theorem sup_inf_distrib_left (s : Finset ι) (f : ι → α) (a : α) : a⊓s.sup f = s.sup fun i => a⊓f i := by
  induction' s using Finset.cons_induction with i s hi h
  · simp_rw [Finset.sup_empty, inf_bot_eq]
    
  · rw [sup_cons, sup_cons, inf_sup_left, h]
    

theorem sup_inf_distrib_right (s : Finset ι) (f : ι → α) (a : α) : s.sup f⊓a = s.sup fun i => f i⊓a := by
  rw [_root_.inf_comm, s.sup_inf_distrib_left]
  simp_rw [_root_.inf_comm]

theorem disjoint_sup_right : Disjoint a (s.sup f) ↔ ∀, ∀ i ∈ s, ∀, Disjoint a (f i) := by
  simp only [← disjoint_iff, ← sup_inf_distrib_left, ← sup_eq_bot_iff]

theorem disjoint_sup_left : Disjoint (s.sup f) a ↔ ∀, ∀ i ∈ s, ∀, Disjoint (f i) a := by
  simp only [← disjoint_iff, ← sup_inf_distrib_right, ← sup_eq_bot_iff]

end OrderBot

section OrderTop

variable [OrderTop α]

theorem inf_sup_distrib_left (s : Finset ι) (f : ι → α) (a : α) : a⊔s.inf f = s.inf fun i => a⊔f i :=
  @sup_inf_distrib_left αᵒᵈ _ _ _ _ _ _

theorem inf_sup_distrib_right (s : Finset ι) (f : ι → α) (a : α) : s.inf f⊔a = s.inf fun i => f i⊔a :=
  @sup_inf_distrib_right αᵒᵈ _ _ _ _ _ _

end OrderTop

end DistribLattice

section LinearOrderₓ

variable [LinearOrderₓ α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {f : ι → α} {a : α}

theorem comp_sup_eq_sup_comp_of_is_total [SemilatticeSup β] [OrderBot β] (g : α → β) (mono_g : Monotone g)
    (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  comp_sup_eq_sup_comp g mono_g.map_sup bot

@[simp]
protected theorem le_sup_iff (ha : ⊥ < a) : a ≤ s.sup f ↔ ∃ b ∈ s, a ≤ f b :=
  ⟨Finset.cons_induction_on s (fun h => absurd h (not_le_of_lt ha)) fun c t hc ih => by
      simpa using
        @Or.ndrec _ _ (∃ b, (b = c ∨ b ∈ t) ∧ a ≤ f b) (fun h => ⟨c, Or.inl rfl, h⟩) fun h =>
          let ⟨b, hb, hle⟩ := ih h
          ⟨b, Or.inr hb, hle⟩,
    fun ⟨b, hb, hle⟩ => trans hle (le_sup hb)⟩

@[simp]
protected theorem lt_sup_iff : a < s.sup f ↔ ∃ b ∈ s, a < f b :=
  ⟨Finset.cons_induction_on s (fun h => absurd h not_lt_bot) fun c t hc ih => by
      simpa using
        @Or.ndrec _ _ (∃ b, (b = c ∨ b ∈ t) ∧ a < f b) (fun h => ⟨c, Or.inl rfl, h⟩) fun h =>
          let ⟨b, hb, hlt⟩ := ih h
          ⟨b, Or.inr hb, hlt⟩,
    fun ⟨b, hb, hlt⟩ => lt_of_lt_of_leₓ hlt (le_sup hb)⟩

@[simp]
protected theorem sup_lt_iff (ha : ⊥ < a) : s.sup f < a ↔ ∀, ∀ b ∈ s, ∀, f b < a :=
  ⟨fun hs b hb => lt_of_le_of_ltₓ (le_sup hb) hs,
    Finset.cons_induction_on s (fun _ => ha) fun c t hc => by
      simpa only [← sup_cons, ← sup_lt_iff, ← mem_cons, ← forall_eq_or_imp] using And.imp_right⟩

end OrderBot

section OrderTop

variable [OrderTop α] {s : Finset ι} {f : ι → α} {a : α}

theorem comp_inf_eq_inf_comp_of_is_total [SemilatticeInf β] [OrderTop β] (g : α → β) (mono_g : Monotone g)
    (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  comp_inf_eq_inf_comp g mono_g.map_inf top

@[simp]
protected theorem inf_le_iff (ha : a < ⊤) : s.inf f ≤ a ↔ ∃ b ∈ s, f b ≤ a :=
  @Finset.le_sup_iff αᵒᵈ _ _ _ _ _ _ ha

@[simp]
protected theorem inf_lt_iff : s.inf f < a ↔ ∃ b ∈ s, f b < a :=
  @Finset.lt_sup_iff αᵒᵈ _ _ _ _ _ _

@[simp]
protected theorem lt_inf_iff (ha : a < ⊤) : a < s.inf f ↔ ∀, ∀ b ∈ s, ∀, a < f b :=
  @Finset.sup_lt_iff αᵒᵈ _ _ _ _ _ _ ha

end OrderTop

end LinearOrderₓ

theorem inf_eq_infi [CompleteLattice β] (s : Finset α) (f : α → β) : s.inf f = ⨅ a ∈ s, f a :=
  @sup_eq_supr _ βᵒᵈ _ _ _

theorem inf_id_eq_Inf [CompleteLattice α] (s : Finset α) : s.inf id = inf s :=
  @sup_id_eq_Sup αᵒᵈ _ _

theorem inf_id_set_eq_sInter (s : Finset (Set α)) : s.inf id = ⋂₀ ↑s :=
  inf_id_eq_Inf _

@[simp]
theorem inf_set_eq_bInter (s : Finset α) (f : α → Set β) : s.inf f = ⋂ x ∈ s, f x :=
  inf_eq_infi _ _

theorem inf_eq_Inf_image [CompleteLattice β] (s : Finset α) (f : α → β) : s.inf f = inf (f '' s) :=
  @sup_eq_Sup_image _ βᵒᵈ _ _ _

section Sup'

variable [SemilatticeSup α]

theorem sup_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) : ∃ a : α, s.sup (coe ∘ f : β → WithBot α) = ↑a :=
  Exists.imp (fun a => Exists.fst) (@le_sup (WithBot α) _ _ _ _ _ _ h (f b) rfl)

/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `finset.sup` which does not require `s` nonempty. -/
def sup' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  Option.getₓ <|
    let ⟨b, hb⟩ := H
    Option.is_some_iff_exists.2 (sup_of_mem f hb)

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

@[simp]
theorem coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup (coe ∘ f) := by
  rw [sup', ← WithBot.some_eq_coe, Option.some_getₓ]

@[simp]
theorem sup'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).Nonempty} : (cons b s hb).sup' h f = f b⊔s.sup' H f := by
  rw [← WithBot.coe_eq_coe]
  simp only [← coe_sup', ← sup_cons, ← WithBot.coe_sup]

@[simp]
theorem sup'_insert [DecidableEq β] {b : β} {h : (insert b s).Nonempty} : (insert b s).sup' h f = f b⊔s.sup' H f := by
  rw [← WithBot.coe_eq_coe]
  simp only [← coe_sup', ← sup_insert, ← WithBot.coe_sup]

@[simp]
theorem sup'_singleton {b : β} {h : ({b} : Finset β).Nonempty} : ({b} : Finset β).sup' h f = f b :=
  rfl

theorem sup'_le {a : α} (hs : ∀, ∀ b ∈ s, ∀, f b ≤ a) : s.sup' H f ≤ a := by
  rw [← WithBot.coe_le_coe, coe_sup']
  exact sup_le fun b h => WithBot.coe_le_coe.2 <| hs b h

theorem le_sup' {b : β} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f := by
  rw [← WithBot.coe_le_coe, coe_sup']
  exact le_sup h

@[simp]
theorem sup'_const (a : α) : (s.sup' H fun b => a) = a := by
  apply le_antisymmₓ
  · apply sup'_le
    intros
    exact le_rfl
    
  · apply le_sup' (fun b => a) H.some_spec
    

@[simp]
theorem sup'_le_iff {a : α} : s.sup' H f ≤ a ↔ ∀, ∀ b ∈ s, ∀, f b ≤ a :=
  Iff.intro (fun h b hb => trans (le_sup' f hb) h) (sup'_le H f)

theorem sup'_bUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ → Finset β} (Ht : ∀ b, (t b).Nonempty) :
    (s.bUnion t).sup' (Hs.bUnion fun b _ => Ht b) f = s.sup' Hs fun b => (t b).sup' (Ht b) f :=
  eq_of_forall_ge_iff fun c => by
    simp [← @forall_swap _ β]

theorem comp_sup'_eq_sup'_comp [SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β → α} (g : α → γ)
    (g_sup : ∀ x y, g (x⊔y) = g x⊔g y) : g (s.sup' H f) = s.sup' H (g ∘ f) := by
  rw [← WithBot.coe_eq_coe, coe_sup']
  let g' : WithBot α → WithBot γ := WithBot.recBotCoe ⊥ fun x => ↑(g x)
  show g' ↑(s.sup' H f) = s.sup fun a => g' ↑(f a)
  rw [coe_sup']
  refine' comp_sup_eq_sup_comp g' _ rfl
  intro f₁ f₂
  cases f₁
  · rw [WithBot.none_eq_bot, bot_sup_eq]
    exact bot_sup_eq.symm
    
  · cases f₂
    rfl
    exact congr_arg coe (g_sup f₁ f₂)
    

theorem sup'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁⊔a₂)) (hs : ∀, ∀ b ∈ s, ∀, p (f b)) :
    p (s.sup' H f) := by
  show @WithBot.recBotCoe α (fun _ => Prop) True p ↑(s.sup' H f)
  rw [coe_sup']
  refine' sup_induction trivialₓ _ hs
  rintro (_ | a₁) h₁ a₂ h₂
  · rw [WithBot.none_eq_bot, bot_sup_eq]
    exact h₂
    
  cases a₂
  exacts[h₁, hp a₁ h₁ a₂ h₂]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » s)
theorem sup'_mem (s : Set α) (w : ∀ (x y) (_ : x ∈ s) (_ : y ∈ s), x⊔y ∈ s) {ι : Type _} (t : Finset ι) (H : t.Nonempty)
    (p : ι → α) (h : ∀, ∀ i ∈ t, ∀, p i ∈ s) : t.sup' H p ∈ s :=
  sup'_induction H p w h

@[congr]
theorem sup'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀, ∀ x ∈ s, ∀, f x = g x) :
    s.sup' H f = t.sup' (h₁ ▸ H) g := by
  subst s
  refine' eq_of_forall_ge_iff fun c => _
  simp (config := { contextual := true })only [← sup'_le_iff, ← h₂]

end Sup'

section Inf'

variable [SemilatticeInf α]

theorem inf_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) : ∃ a : α, s.inf (coe ∘ f : β → WithTop α) = ↑a :=
  @sup_of_mem αᵒᵈ _ _ _ f _ h

/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `finset.inf` which does not require `s` nonempty. -/
def inf' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  @sup' αᵒᵈ _ _ s H f

variable {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α} {b : β}

@[simp]
theorem coe_inf' : ((s.inf' H f : α) : WithTop α) = s.inf (coe ∘ f) :=
  @coe_sup' αᵒᵈ _ _ _ H f

@[simp]
theorem inf'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).Nonempty} : (cons b s hb).inf' h f = f b⊓s.inf' H f :=
  @sup'_cons αᵒᵈ _ _ _ H f _ _ _

@[simp]
theorem inf'_insert [DecidableEq β] {b : β} {h : (insert b s).Nonempty} : (insert b s).inf' h f = f b⊓s.inf' H f :=
  @sup'_insert αᵒᵈ _ _ _ H f _ _ _

@[simp]
theorem inf'_singleton {b : β} {h : ({b} : Finset β).Nonempty} : ({b} : Finset β).inf' h f = f b :=
  rfl

theorem le_inf' (hs : ∀, ∀ b ∈ s, ∀, a ≤ f b) : a ≤ s.inf' H f :=
  @sup'_le αᵒᵈ _ _ _ H f _ hs

theorem inf'_le (h : b ∈ s) : s.inf' ⟨b, h⟩ f ≤ f b :=
  @le_sup' αᵒᵈ _ _ _ f _ h

@[simp]
theorem inf'_const (a : α) : (s.inf' H fun b => a) = a :=
  @sup'_const αᵒᵈ _ _ _ _ _

@[simp]
theorem le_inf'_iff : a ≤ s.inf' H f ↔ ∀, ∀ b ∈ s, ∀, a ≤ f b :=
  @sup'_le_iff αᵒᵈ _ _ _ H f _

theorem inf'_bUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ → Finset β} (Ht : ∀ b, (t b).Nonempty) :
    (s.bUnion t).inf' (Hs.bUnion fun b _ => Ht b) f = s.inf' Hs fun b => (t b).inf' (Ht b) f :=
  @sup'_bUnion αᵒᵈ _ _ _ _ _ _ Hs _ Ht

theorem comp_inf'_eq_inf'_comp [SemilatticeInf γ] {s : Finset β} (H : s.Nonempty) {f : β → α} (g : α → γ)
    (g_inf : ∀ x y, g (x⊓y) = g x⊓g y) : g (s.inf' H f) = s.inf' H (g ∘ f) :=
  @comp_sup'_eq_sup'_comp αᵒᵈ _ γᵒᵈ _ _ _ H f g g_inf

theorem inf'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁⊓a₂)) (hs : ∀, ∀ b ∈ s, ∀, p (f b)) :
    p (s.inf' H f) :=
  @sup'_induction αᵒᵈ _ _ _ H f _ hp hs

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » s)
theorem inf'_mem (s : Set α) (w : ∀ (x y) (_ : x ∈ s) (_ : y ∈ s), x⊓y ∈ s) {ι : Type _} (t : Finset ι) (H : t.Nonempty)
    (p : ι → α) (h : ∀, ∀ i ∈ t, ∀, p i ∈ s) : t.inf' H p ∈ s :=
  inf'_induction H p w h

@[congr]
theorem inf'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀, ∀ x ∈ s, ∀, f x = g x) :
    s.inf' H f = t.inf' (h₁ ▸ H) g :=
  @sup'_congr αᵒᵈ _ _ _ H _ _ _ h₁ h₂

end Inf'

section Sup

variable [SemilatticeSup α] [OrderBot α]

theorem sup'_eq_sup {s : Finset β} (H : s.Nonempty) (f : β → α) : s.sup' H f = s.sup f :=
  le_antisymmₓ (sup'_le H f fun b => le_sup) (sup_le fun b => le_sup' f)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a b «expr ∈ » s)
theorem sup_closed_of_sup_closed {s : Set α} (t : Finset α) (htne : t.Nonempty) (h_subset : ↑t ⊆ s)
    (h : ∀ (a b) (_ : a ∈ s) (_ : b ∈ s), a⊔b ∈ s) : t.sup id ∈ s :=
  sup'_eq_sup htne id ▸ sup'_induction _ _ h h_subset

theorem coe_sup_of_nonempty {s : Finset β} (h : s.Nonempty) (f : β → α) : (↑(s.sup f) : WithBot α) = s.sup (coe ∘ f) :=
  by
  simp only [sup'_eq_sup h, ← coe_sup' h]

end Sup

section Inf

variable [SemilatticeInf α] [OrderTop α]

theorem inf'_eq_inf {s : Finset β} (H : s.Nonempty) (f : β → α) : s.inf' H f = s.inf f :=
  @sup'_eq_sup αᵒᵈ _ _ _ _ H f

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a b «expr ∈ » s)
theorem inf_closed_of_inf_closed {s : Set α} (t : Finset α) (htne : t.Nonempty) (h_subset : ↑t ⊆ s)
    (h : ∀ (a b) (_ : a ∈ s) (_ : b ∈ s), a⊓b ∈ s) : t.inf id ∈ s :=
  @sup_closed_of_sup_closed αᵒᵈ _ _ _ t htne h_subset h

theorem coe_inf_of_nonempty {s : Finset β} (h : s.Nonempty) (f : β → α) :
    (↑(s.inf f) : WithTop α) = s.inf fun i => f i :=
  @coe_sup_of_nonempty αᵒᵈ _ _ _ _ h f

end Inf

section Sup

variable {C : β → Type _} [∀ b : β, SemilatticeSup (C b)] [∀ b : β, OrderBot (C b)]

@[simp]
protected theorem sup_apply (s : Finset α) (f : α → ∀ b : β, C b) (b : β) : s.sup f b = s.sup fun a => f a b :=
  comp_sup_eq_sup_comp (fun x : ∀ b : β, C b => x b) (fun i j => rfl) rfl

end Sup

section Inf

variable {C : β → Type _} [∀ b : β, SemilatticeInf (C b)] [∀ b : β, OrderTop (C b)]

@[simp]
protected theorem inf_apply (s : Finset α) (f : α → ∀ b : β, C b) (b : β) : s.inf f b = s.inf fun a => f a b :=
  @Finset.sup_apply _ _ (fun b => (C b)ᵒᵈ) _ _ s f b

end Inf

section Sup'

variable {C : β → Type _} [∀ b : β, SemilatticeSup (C b)]

@[simp]
protected theorem sup'_apply {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  comp_sup'_eq_sup'_comp H (fun x : ∀ b : β, C b => x b) fun i j => rfl

end Sup'

section Inf'

variable {C : β → Type _} [∀ b : β, SemilatticeInf (C b)]

@[simp]
protected theorem inf'_apply {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.inf' H f b = s.inf' H fun a => f a b :=
  @Finset.sup'_apply _ _ (fun b => (C b)ᵒᵈ) _ _ H f b

end Inf'

@[simp]
theorem to_dual_sup' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.sup' hs f) = s.inf' hs (to_dual ∘ f) :=
  rfl

@[simp]
theorem to_dual_inf' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.inf' hs f) = s.sup' hs (to_dual ∘ f) :=
  rfl

@[simp]
theorem of_dual_sup' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.sup' hs f) = s.inf' hs (of_dual ∘ f) :=
  rfl

@[simp]
theorem of_dual_inf' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.inf' hs f) = s.sup' hs (of_dual ∘ f) :=
  rfl

section LinearOrderₓ

variable [LinearOrderₓ α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α}

@[simp]
theorem le_sup'_iff : a ≤ s.sup' H f ↔ ∃ b ∈ s, a ≤ f b := by
  rw [← WithBot.coe_le_coe, coe_sup', Finset.le_sup_iff (WithBot.bot_lt_coe a)]
  exact bex_congr fun b hb => WithBot.coe_le_coe

@[simp]
theorem lt_sup'_iff : a < s.sup' H f ↔ ∃ b ∈ s, a < f b := by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.lt_sup_iff]
  exact bex_congr fun b hb => WithBot.coe_lt_coe

@[simp]
theorem sup'_lt_iff : s.sup' H f < a ↔ ∀, ∀ i ∈ s, ∀, f i < a := by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.sup_lt_iff (WithBot.bot_lt_coe a)]
  exact ball_congr fun b hb => WithBot.coe_lt_coe

@[simp]
theorem inf'_le_iff : s.inf' H f ≤ a ↔ ∃ i ∈ s, f i ≤ a :=
  @le_sup'_iff αᵒᵈ _ _ _ H f _

@[simp]
theorem inf'_lt_iff : s.inf' H f < a ↔ ∃ i ∈ s, f i < a :=
  @lt_sup'_iff αᵒᵈ _ _ _ H f _

@[simp]
theorem lt_inf'_iff : a < s.inf' H f ↔ ∀, ∀ i ∈ s, ∀, a < f i :=
  @sup'_lt_iff αᵒᵈ _ _ _ H f _

theorem exists_mem_eq_sup' (f : ι → α) : ∃ i, i ∈ s ∧ s.sup' H f = f i := by
  refine' H.cons_induction (fun c => _) fun c s hc hs ih => _
  · exact ⟨c, mem_singleton_self c, rfl⟩
    
  · rcases ih with ⟨b, hb, h'⟩
    rw [sup'_cons hs, h']
    cases' total_of (· ≤ ·) (f b) (f c) with h h
    · exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left.2 h⟩
      
    · exact ⟨b, mem_cons.2 (Or.inr hb), sup_eq_right.2 h⟩
      
    

theorem exists_mem_eq_inf' (f : ι → α) : ∃ i, i ∈ s ∧ s.inf' H f = f i :=
  @exists_mem_eq_sup' αᵒᵈ _ _ _ H f

theorem exists_mem_eq_sup [OrderBot α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) : ∃ i, i ∈ s ∧ s.sup f = f i :=
  sup'_eq_sup h f ▸ exists_mem_eq_sup' h f

theorem exists_mem_eq_inf [OrderTop α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) : ∃ i, i ∈ s ∧ s.inf f = f i :=
  @exists_mem_eq_sup αᵒᵈ _ _ _ _ h f

end LinearOrderₓ

/-! ### max and min of finite sets -/


section MaxMin

variable [LinearOrderₓ α]

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `⊥` otherwise. It belongs to `with_bot α`. If you want to get an element of `α`, see
`s.max'`. -/
protected def max (s : Finset α) : WithBot α :=
  sup s coe

theorem max_eq_sup_with_bot (s : Finset α) : s.max = sup s coe :=
  rfl

@[simp]
theorem max_empty : (∅ : Finset α).max = ⊥ :=
  rfl

@[simp]
theorem max_insert {a : α} {s : Finset α} : (insert a s).max = max a s.max :=
  fold_insert_idem

@[simp]
theorem max_singleton {a : α} : Finset.max {a} = (a : WithBot α) := by
  rw [← insert_emptyc_eq]
  exact max_insert

theorem max_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.max = b :=
  (@le_sup (WithBot α) _ _ _ _ _ _ h _ rfl).imp fun b => Exists.fst

theorem max_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.max = a :=
  let ⟨a, ha⟩ := h
  max_of_mem ha

theorem max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅ :=
  ⟨fun h =>
    s.eq_empty_or_nonempty.elim id fun H => by
      let ⟨a, ha⟩ := max_of_nonempty H
      rw [h] at ha <;> cases ha,
    fun h => h.symm ▸ max_empty⟩

theorem mem_of_max {s : Finset α} : ∀ {a : α}, s.max = a → a ∈ s :=
  Finset.induction_on s
    (fun _ H => by
      cases H)
    fun b s _ (ih : ∀ {a : α}, s.max = a → a ∈ s) a (h : (insert b s).max = a) => by
    by_cases' p : b = a
    · induction p
      exact mem_insert_self b s
      
    · cases' max_choice (↑b) s.max with q q <;> rw [max_insert, q] at h
      · cases h
        cases p rfl
        
      · exact mem_insert_of_mem (ih h)
        
      

theorem coe_le_max_of_mem {a : α} {s : Finset α} (as : a ∈ s) : ↑a ≤ s.max :=
  le_sup as

theorem le_max_of_mem {s : Finset α} {a b : α} (h₁ : a ∈ s) (h₂ : s.max = b) : a ≤ b :=
  WithBot.coe_le_coe.mp <| (coe_le_max_of_mem h₁).trans h₂.le

theorem max_mono {s t : Finset α} (st : s ⊆ t) : s.max ≤ t.max :=
  sup_mono st

theorem max_le {M : WithBot α} {s : Finset α} (st : ∀ a : α, a ∈ s → (a : WithBot α) ≤ M) : s.max ≤ M :=
  sup_le st

/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `⊤` otherwise. It belongs to `with_top α`. If you want to get an element of `α`, see
`s.min'`. -/
protected def min (s : Finset α) : WithTop α :=
  inf s coe

theorem min_eq_inf_with_top (s : Finset α) : s.min = inf s coe :=
  rfl

@[simp]
theorem min_empty : (∅ : Finset α).min = ⊤ :=
  rfl

@[simp]
theorem min_insert {a : α} {s : Finset α} : (insert a s).min = min (↑a) s.min :=
  fold_insert_idem

@[simp]
theorem min_singleton {a : α} : Finset.min {a} = (a : WithTop α) := by
  rw [← insert_emptyc_eq]
  exact min_insert

theorem min_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.min = b :=
  (@inf_le (WithTop α) _ _ _ _ _ _ h _ rfl).imp fun b => Exists.fst

theorem min_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.min = a :=
  let ⟨a, ha⟩ := h
  min_of_mem ha

theorem min_eq_top {s : Finset α} : s.min = ⊤ ↔ s = ∅ :=
  ⟨fun h =>
    s.eq_empty_or_nonempty.elim id fun H => by
      let ⟨a, ha⟩ := min_of_nonempty H
      rw [h] at ha <;> cases ha,
    fun h => h.symm ▸ min_empty⟩

theorem mem_of_min {s : Finset α} : ∀ {a : α}, s.min = a → a ∈ s :=
  @mem_of_max αᵒᵈ _ s

theorem min_le_coe_of_mem {a : α} {s : Finset α} (as : a ∈ s) : s.min ≤ a :=
  inf_le as

theorem min_le_of_mem {s : Finset α} {a b : α} (h₁ : b ∈ s) (h₂ : s.min = a) : a ≤ b :=
  WithTop.coe_le_coe.mp <| h₂.Ge.trans (min_le_coe_of_mem h₁)

theorem min_mono {s t : Finset α} (st : s ⊆ t) : t.min ≤ s.min :=
  inf_mono st

theorem le_min {m : WithTop α} {s : Finset α} (st : ∀ a : α, a ∈ s → m ≤ a) : m ≤ s.min :=
  le_inf st

/-- Given a nonempty finset `s` in a linear order `α `, then `s.min' h` is its minimum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `with_top α`. -/
def min' (s : Finset α) (H : s.Nonempty) : α :=
  WithTop.untop s.min <| mt min_eq_top.1 H.ne_empty

/-- Given a nonempty finset `s` in a linear order `α `, then `s.max' h` is its maximum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `with_bot α`. -/
def max' (s : Finset α) (H : s.Nonempty) : α :=
  WithBot.unbot s.max <| by
    let ⟨k, hk⟩ := H
    let ⟨b, hb⟩ := max_of_mem hk
    simp [← hb]

variable (s : Finset α) (H : s.Nonempty) {x : α}

theorem min'_mem : s.min' H ∈ s :=
  mem_of_min <| by
    simp [← min']

theorem min'_le (x) (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x :=
  min_le_of_mem H2 (WithTop.coe_untop _ _).symm

theorem le_min' (x) (H2 : ∀, ∀ y ∈ s, ∀, x ≤ y) : x ≤ s.min' H :=
  H2 _ <| min'_mem _ _

theorem is_least_min' : IsLeast (↑s) (s.min' H) :=
  ⟨min'_mem _ _, min'_le _⟩

@[simp]
theorem le_min'_iff {x} : x ≤ s.min' H ↔ ∀, ∀ y ∈ s, ∀, x ≤ y :=
  le_is_glb_iff (is_least_min' s H).IsGlb

/-- `{a}.min' _` is `a`. -/
@[simp]
theorem min'_singleton (a : α) : ({a} : Finset α).min' (singleton_nonempty _) = a := by
  simp [← min']

theorem max'_mem : s.max' H ∈ s :=
  mem_of_max <| by
    simp [← max']

theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_mem H2 (WithBot.coe_unbot _ _).symm

theorem max'_le (x) (H2 : ∀, ∀ y ∈ s, ∀, y ≤ x) : s.max' H ≤ x :=
  H2 _ <| max'_mem _ _

theorem is_greatest_max' : IsGreatest (↑s) (s.max' H) :=
  ⟨max'_mem _ _, le_max' _⟩

@[simp]
theorem max'_le_iff {x} : s.max' H ≤ x ↔ ∀, ∀ y ∈ s, ∀, y ≤ x :=
  is_lub_le_iff (is_greatest_max' s H).IsLub

@[simp]
theorem max'_lt_iff {x} : s.max' H < x ↔ ∀, ∀ y ∈ s, ∀, y < x :=
  ⟨fun Hlt y hy => (s.le_max' y hy).trans_lt Hlt, fun H => H _ <| s.max'_mem _⟩

@[simp]
theorem lt_min'_iff : x < s.min' H ↔ ∀, ∀ y ∈ s, ∀, x < y :=
  @max'_lt_iff αᵒᵈ _ _ H _

theorem max'_eq_sup' : s.max' H = s.sup' H id :=
  eq_of_forall_ge_iff fun a => (max'_le_iff _ _).trans (sup'_le_iff _ _).symm

theorem min'_eq_inf' : s.min' H = s.inf' H id :=
  @max'_eq_sup' αᵒᵈ _ s H

/-- `{a}.max' _` is `a`. -/
@[simp]
theorem max'_singleton (a : α) : ({a} : Finset α).max' (singleton_nonempty _) = a := by
  simp [← max']

theorem min'_lt_max' {i j} (H1 : i ∈ s) (H2 : j ∈ s) (H3 : i ≠ j) : s.min' ⟨i, H1⟩ < s.max' ⟨i, H1⟩ :=
  is_glb_lt_is_lub_of_ne (s.is_least_min' _).IsGlb (s.is_greatest_max' _).IsLub H1 H2 H3

/-- If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
theorem min'_lt_max'_of_card (h₂ : 1 < card s) :
    s.min' (Finset.card_pos.mp <| lt_transₓ zero_lt_one h₂) < s.max' (Finset.card_pos.mp <| lt_transₓ zero_lt_one h₂) :=
  by
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
  exact s.min'_lt_max' ha hb hab

theorem map_of_dual_min (s : Finset αᵒᵈ) : s.min.map ofDual = (s.Image ofDual).max := by
  rw [max_eq_sup_with_bot, sup_image]
  exact congr_fun Option.map_id _

theorem map_of_dual_max (s : Finset αᵒᵈ) : s.max.map ofDual = (s.Image ofDual).min := by
  rw [min_eq_inf_with_top, inf_image]
  exact congr_fun Option.map_id _

theorem map_to_dual_min (s : Finset α) : s.min.map toDual = (s.Image toDual).max := by
  rw [max_eq_sup_with_bot, sup_image]
  exact congr_fun Option.map_id _

theorem map_to_dual_max (s : Finset α) : s.max.map toDual = (s.Image toDual).min := by
  rw [min_eq_inf_with_top, inf_image]
  exact congr_fun Option.map_id _

theorem of_dual_min' {s : Finset αᵒᵈ} (hs : s.Nonempty) : ofDual (min' s hs) = max' (s.Image ofDual) (hs.Image _) := by
  convert rfl
  exact image_id

theorem of_dual_max' {s : Finset αᵒᵈ} (hs : s.Nonempty) : ofDual (max' s hs) = min' (s.Image ofDual) (hs.Image _) := by
  convert rfl
  exact image_id

theorem to_dual_min' {s : Finset α} (hs : s.Nonempty) : toDual (min' s hs) = max' (s.Image toDual) (hs.Image _) := by
  convert rfl
  exact image_id

theorem to_dual_max' {s : Finset α} (hs : s.Nonempty) : toDual (max' s hs) = min' (s.Image toDual) (hs.Image _) := by
  convert rfl
  exact image_id

theorem max'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) : s.max' H ≤ t.max' (H.mono hst) :=
  le_max' _ _ (hst (s.max'_mem H))

theorem min'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) : t.min' (H.mono hst) ≤ s.min' H :=
  min'_le _ _ (hst (s.min'_mem H))

theorem max'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).max' (s.insert_nonempty a) = max (s.max' H) a :=
  (is_greatest_max' _ _).unique <| by
    rw [coe_insert, max_commₓ]
    exact (is_greatest_max' _ _).insert _

theorem min'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).min' (s.insert_nonempty a) = min (s.min' H) a :=
  (is_least_min' _ _).unique <| by
    rw [coe_insert, min_commₓ]
    exact (is_least_min' _ _).insert _

theorem lt_max'_of_mem_erase_max' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.max' H)) : a < s.max' H :=
  lt_of_le_of_neₓ (le_max' _ _ (mem_of_mem_erase ha)) <| ne_of_mem_of_not_mem ha <| not_mem_erase _ _

theorem min'_lt_of_mem_erase_min' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.min' H)) : s.min' H < a :=
  @lt_max'_of_mem_erase_max' αᵒᵈ _ s H _ a ha

@[simp]
theorem max'_image [LinearOrderₓ β] {f : α → β} (hf : Monotone f) (s : Finset α) (h : (s.Image f).Nonempty) :
    (s.Image f).max' h = f (s.max' ((Nonempty.image_iff f).mp h)) := by
  refine' le_antisymmₓ (max'_le _ _ _ fun y hy => _) (le_max' _ _ (mem_image.mpr ⟨_, max'_mem _ _, rfl⟩))
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact hf (le_max' _ _ hx)

@[simp]
theorem min'_image [LinearOrderₓ β] {f : α → β} (hf : Monotone f) (s : Finset α) (h : (s.Image f).Nonempty) :
    (s.Image f).min' h = f (s.min' ((Nonempty.image_iff f).mp h)) := by
  refine' le_antisymmₓ (min'_le _ _ (mem_image.mpr ⟨_, min'_mem _ _, rfl⟩)) (le_min' _ _ _ fun y hy => _)
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact hf (min'_le _ _ hx)

/-- Induction principle for `finset`s in a linearly ordered type: a predicate is true on all
`s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` strictly greater than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_eliminator]
theorem induction_on_max [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
    (step : ∀ a s, (∀, ∀ x ∈ s, ∀, x < a) → p s → p (insert a s)) : p s := by
  induction' s using Finset.strongInductionOn with s ihs
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · exact h0
    
  · have H : s.max' hne ∈ s := max'_mem s hne
    rw [← insert_erase H]
    exact step _ _ (fun x => s.lt_max'_of_mem_erase_max' hne) (ihs _ <| erase_ssubset H)
    

/-- Induction principle for `finset`s in a linearly ordered type: a predicate is true on all
`s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` strictly less than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_eliminator]
theorem induction_on_min [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
    (step : ∀ a s, (∀, ∀ x ∈ s, ∀, a < x) → p s → p (insert a s)) : p s :=
  @induction_on_max αᵒᵈ _ _ _ s h0 step

end MaxMin

section MaxMinInductionValue

variable [LinearOrderₓ α] [LinearOrderₓ β]

/-- Induction principle for `finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f x ≤ f a`, `p s` implies `p (insert a s)`. -/
@[elab_as_eliminator]
theorem induction_on_max_value [DecidableEq ι] (f : ι → α) {p : Finset ι → Prop} (s : Finset ι) (h0 : p ∅)
    (step : ∀ a s, a ∉ s → (∀, ∀ x ∈ s, ∀, f x ≤ f a) → p s → p (insert a s)) : p s := by
  induction' s using Finset.strongInductionOn with s ihs
  rcases(s.image f).eq_empty_or_nonempty with (hne | hne)
  · simp only [← image_eq_empty] at hne
    simp only [← hne, ← h0]
    
  · have H : (s.image f).max' hne ∈ s.image f := max'_mem (s.image f) hne
    simp only [← mem_image, ← exists_prop] at H
    rcases H with ⟨a, has, hfa⟩
    rw [← insert_erase has]
    refine' step _ _ (not_mem_erase a s) (fun x hx => _) (ihs _ <| erase_ssubset has)
    rw [hfa]
    exact le_max' _ _ (mem_image_of_mem _ <| mem_of_mem_erase hx)
    

/-- Induction principle for `finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f a ≤ f x`, `p s` implies `p (insert a s)`. -/
@[elab_as_eliminator]
theorem induction_on_min_value [DecidableEq ι] (f : ι → α) {p : Finset ι → Prop} (s : Finset ι) (h0 : p ∅)
    (step : ∀ a s, a ∉ s → (∀, ∀ x ∈ s, ∀, f a ≤ f x) → p s → p (insert a s)) : p s :=
  @induction_on_max_value αᵒᵈ ι _ _ _ _ s h0 step

end MaxMinInductionValue

section ExistsMaxMin

variable [LinearOrderₓ α]

theorem exists_max_image (s : Finset β) (f : β → α) (h : s.Nonempty) : ∃ x ∈ s, ∀, ∀ x' ∈ s, ∀, f x' ≤ f x := by
  cases' max_of_nonempty (h.image f) with y hy
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
  exact ⟨x, hx, fun x' hx' => le_max_of_mem (mem_image_of_mem f hx') hy⟩

theorem exists_min_image (s : Finset β) (f : β → α) (h : s.Nonempty) : ∃ x ∈ s, ∀, ∀ x' ∈ s, ∀, f x ≤ f x' :=
  @exists_max_image αᵒᵈ β _ s f h

end ExistsMaxMin

end Finset

namespace Multiset

theorem map_finset_sup [DecidableEq α] [DecidableEq β] (s : Finset γ) (f : γ → Multiset β) (g : β → α)
    (hg : Function.Injective g) : map g (s.sup f) = s.sup (map g ∘ f) :=
  Finset.comp_sup_eq_sup_comp _ (fun _ _ => map_union hg) (map_zero _)

theorem count_finset_sup [DecidableEq β] (s : Finset α) (f : α → Multiset β) (b : β) :
    count b (s.sup f) = s.sup fun a => count b (f a) := by
  let this := Classical.decEq α
  refine' s.induction _ _
  · exact count_zero _
    
  · intro i s his ih
    rw [Finset.sup_insert, sup_eq_union, count_union, Finset.sup_insert, ih]
    rfl
    

theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Multiset β} {x : β} : x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v := by
  classical
  apply s.induction_on
  · simp
    
  · intro a s has hxs
    rw [Finset.sup_insert, Multiset.sup_eq_union, Multiset.mem_union]
    constructor
    · intro hxi
      cases' hxi with hf hf
      · refine' ⟨a, _, hf⟩
        simp only [← true_orₓ, ← eq_self_iff_true, ← Finset.mem_insert]
        
      · rcases hxs.mp hf with ⟨v, hv, hfv⟩
        refine' ⟨v, _, hfv⟩
        simp only [← hv, ← or_trueₓ, ← Finset.mem_insert]
        
      
    · rintro ⟨v, hv, hfv⟩
      rw [Finset.mem_insert] at hv
      rcases hv with (rfl | hv)
      · exact Or.inl hfv
        
      · refine' Or.inr (hxs.mpr ⟨v, hv, hfv⟩)
        
      
    

end Multiset

namespace Finset

theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Finset β} {x : β} : x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v := by
  change _ ↔ ∃ v ∈ s, x ∈ (f v).val
  rw [← Multiset.mem_sup, ← Multiset.mem_to_finset, sup_to_finset]
  simp_rw [val_to_finset]

theorem sup_eq_bUnion {α β} [DecidableEq β] (s : Finset α) (t : α → Finset β) : s.sup t = s.bUnion t := by
  ext
  rw [mem_sup, mem_bUnion]

@[simp]
theorem sup_singleton'' [DecidableEq α] (s : Finset β) (f : β → α) : (s.sup fun b => {f b}) = s.Image f := by
  ext a
  rw [mem_sup, mem_image]
  simp only [← mem_singleton, ← eq_comm]

@[simp]
theorem sup_singleton' [DecidableEq α] (s : Finset α) : s.sup singleton = s :=
  (s.sup_singleton'' _).trans image_id

end Finset

section Lattice

variable {ι' : Sort _} [CompleteLattice α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `supr_eq_supr_finset'` for a version
that works for `ι : Sort*`. -/
theorem supr_eq_supr_finset (s : ι → α) : (⨆ i, s i) = ⨆ t : Finset ι, ⨆ i ∈ t, s i := by
  classical
  exact
    le_antisymmₓ
      (supr_le fun b =>
        le_supr_of_le {b} <|
          le_supr_of_le b <|
            le_supr_of_le
                (by
                  simp ) <|
              le_rfl)
      (supr_le fun t => supr_le fun b => supr_le fun hb => le_supr _ _)

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `supr_eq_supr_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
theorem supr_eq_supr_finset' (s : ι' → α) : (⨆ i, s i) = ⨆ t : Finset (Plift ι'), ⨆ i ∈ t, s (Plift.down i) := by
  rw [← supr_eq_supr_finset, ← equiv.plift.surjective.supr_comp] <;> rfl

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `infi_eq_infi_finset'` for a version
that works for `ι : Sort*`. -/
theorem infi_eq_infi_finset (s : ι → α) : (⨅ i, s i) = ⨅ (t : Finset ι) (i ∈ t), s i :=
  @supr_eq_supr_finset αᵒᵈ _ _ _

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `infi_eq_infi_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
theorem infi_eq_infi_finset' (s : ι' → α) : (⨅ i, s i) = ⨅ t : Finset (Plift ι'), ⨅ i ∈ t, s (Plift.down i) :=
  @supr_eq_supr_finset' αᵒᵈ _ _ _

end Lattice

namespace Set

variable {ι' : Sort _}

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `Union_eq_Union_finset'` for
a version that works for `ι : Sort*`. -/
theorem Union_eq_Union_finset (s : ι → Set α) : (⋃ i, s i) = ⋃ t : Finset ι, ⋃ i ∈ t, s i :=
  supr_eq_supr_finset s

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `Union_eq_Union_finset` for
a version that assumes `ι : Type*` but avoids `plift`s in the right hand side. -/
theorem Union_eq_Union_finset' (s : ι' → Set α) : (⋃ i, s i) = ⋃ t : Finset (Plift ι'), ⋃ i ∈ t, s (Plift.down i) :=
  supr_eq_supr_finset' s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`Inter_eq_Inter_finset'` for a version that works for `ι : Sort*`. -/
theorem Inter_eq_Inter_finset (s : ι → Set α) : (⋂ i, s i) = ⋂ t : Finset ι, ⋂ i ∈ t, s i :=
  infi_eq_infi_finset s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`Inter_eq_Inter_finset` for a version that assumes `ι : Type*` but avoids `plift`s in the right
hand side. -/
theorem Inter_eq_Inter_finset' (s : ι' → Set α) : (⋂ i, s i) = ⋂ t : Finset (Plift ι'), ⋂ i ∈ t, s (Plift.down i) :=
  infi_eq_infi_finset' s

end Set

namespace Finset

/-! ### Interaction with ordered algebra structures -/


theorem sup_mul_le_mul_sup_of_nonneg [LinearOrderedSemiring α] [OrderBot α] {a b : ι → α} (s : Finset ι)
    (ha : ∀, ∀ i ∈ s, ∀, 0 ≤ a i) (hb : ∀, ∀ i ∈ s, ∀, 0 ≤ b i) : s.sup (a * b) ≤ s.sup a * s.sup b :=
  Finset.sup_le fun i hi => mul_le_mul (le_sup hi) (le_sup hi) (hb _ hi) ((ha _ hi).trans <| le_sup hi)

theorem mul_inf_le_inf_mul_of_nonneg [LinearOrderedSemiring α] [OrderTop α] {a b : ι → α} (s : Finset ι)
    (ha : ∀, ∀ i ∈ s, ∀, 0 ≤ a i) (hb : ∀, ∀ i ∈ s, ∀, 0 ≤ b i) : s.inf a * s.inf b ≤ s.inf (a * b) :=
  Finset.le_inf fun i hi => mul_le_mul (inf_le hi) (inf_le hi) (Finset.le_inf hb) (ha i hi)

theorem sup'_mul_le_mul_sup'_of_nonneg [LinearOrderedSemiring α] {a b : ι → α} (s : Finset ι) (H : s.Nonempty)
    (ha : ∀, ∀ i ∈ s, ∀, 0 ≤ a i) (hb : ∀, ∀ i ∈ s, ∀, 0 ≤ b i) : s.sup' H (a * b) ≤ s.sup' H a * s.sup' H b :=
  (sup'_le _ _) fun i hi => mul_le_mul (le_sup' _ hi) (le_sup' _ hi) (hb _ hi) ((ha _ hi).trans <| le_sup' _ hi)

theorem inf'_mul_le_mul_inf'_of_nonneg [LinearOrderedSemiring α] {a b : ι → α} (s : Finset ι) (H : s.Nonempty)
    (ha : ∀, ∀ i ∈ s, ∀, 0 ≤ a i) (hb : ∀, ∀ i ∈ s, ∀, 0 ≤ b i) : s.inf' H a * s.inf' H b ≤ s.inf' H (a * b) :=
  (le_inf' _ _) fun i hi => mul_le_mul (inf'_le _ hi) (inf'_le _ hi) (le_inf' _ _ hb) (ha _ hi)

open Function

/-! ### Interaction with big lattice/set operations -/


section Lattice

theorem supr_coe [HasSupₓ β] (f : α → β) (s : Finset α) : (⨆ x ∈ (↑s : Set α), f x) = ⨆ x ∈ s, f x :=
  rfl

theorem infi_coe [HasInfₓ β] (f : α → β) (s : Finset α) : (⨅ x ∈ (↑s : Set α), f x) = ⨅ x ∈ s, f x :=
  rfl

variable [CompleteLattice β]

theorem supr_singleton (a : α) (s : α → β) : (⨆ x ∈ ({a} : Finset α), s x) = s a := by
  simp

theorem infi_singleton (a : α) (s : α → β) : (⨅ x ∈ ({a} : Finset α), s x) = s a := by
  simp

theorem supr_option_to_finset (o : Option α) (f : α → β) : (⨆ x ∈ o.toFinset, f x) = ⨆ x ∈ o, f x := by
  simp

theorem infi_option_to_finset (o : Option α) (f : α → β) : (⨅ x ∈ o.toFinset, f x) = ⨅ x ∈ o, f x :=
  @supr_option_to_finset _ βᵒᵈ _ _ _

variable [DecidableEq α]

theorem supr_union {f : α → β} {s t : Finset α} : (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x)⊔⨆ x ∈ t, f x := by
  simp [← supr_or, ← supr_sup_eq]

theorem infi_union {f : α → β} {s t : Finset α} : (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x)⊓⨅ x ∈ t, f x :=
  @supr_union α βᵒᵈ _ _ _ _ _

theorem supr_insert (a : α) (s : Finset α) (t : α → β) : (⨆ x ∈ insert a s, t x) = t a⊔⨆ x ∈ s, t x := by
  rw [insert_eq]
  simp only [← supr_union, ← Finset.supr_singleton]

theorem infi_insert (a : α) (s : Finset α) (t : α → β) : (⨅ x ∈ insert a s, t x) = t a⊓⨅ x ∈ s, t x :=
  @supr_insert α βᵒᵈ _ _ _ _ _

theorem supr_finset_image {f : γ → α} {g : α → β} {s : Finset γ} : (⨆ x ∈ s.Image f, g x) = ⨆ y ∈ s, g (f y) := by
  rw [← supr_coe, coe_image, supr_image, supr_coe]

theorem sup_finset_image {β γ : Type _} [SemilatticeSup β] [OrderBot β] (f : γ → α) (g : α → β) (s : Finset γ) :
    (s.Image f).sup g = s.sup (g ∘ f) := by
  classical
  induction' s using Finset.induction_on with a s' ha ih <;> simp [*]

theorem infi_finset_image {f : γ → α} {g : α → β} {s : Finset γ} : (⨅ x ∈ s.Image f, g x) = ⨅ y ∈ s, g (f y) := by
  rw [← infi_coe, coe_image, infi_image, infi_coe]

theorem supr_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    (⨆ i ∈ insert x t, Function.update f x s i) = s⊔⨆ i ∈ t, f i := by
  simp only [← Finset.supr_insert, ← update_same]
  rcongr i hi
  apply update_noteq
  rintro rfl
  exact hx hi

theorem infi_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    (⨅ i ∈ insert x t, update f x s i) = s⊓⨅ i ∈ t, f i :=
  @supr_insert_update α βᵒᵈ _ _ _ _ f _ hx

theorem supr_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    (⨆ y ∈ s.bUnion t, f y) = ⨆ (x ∈ s) (y ∈ t x), f y := by
  simp [← @supr_comm _ α, ← supr_and]

theorem infi_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    (⨅ y ∈ s.bUnion t, f y) = ⨅ (x ∈ s) (y ∈ t x), f y :=
  @supr_bUnion _ βᵒᵈ _ _ _ _ _ _

end Lattice

theorem set_bUnion_coe (s : Finset α) (t : α → Set β) : (⋃ x ∈ (↑s : Set α), t x) = ⋃ x ∈ s, t x :=
  rfl

theorem set_bInter_coe (s : Finset α) (t : α → Set β) : (⋂ x ∈ (↑s : Set α), t x) = ⋂ x ∈ s, t x :=
  rfl

theorem set_bUnion_singleton (a : α) (s : α → Set β) : (⋃ x ∈ ({a} : Finset α), s x) = s a :=
  supr_singleton a s

theorem set_bInter_singleton (a : α) (s : α → Set β) : (⋂ x ∈ ({a} : Finset α), s x) = s a :=
  infi_singleton a s

@[simp]
theorem set_bUnion_preimage_singleton (f : α → β) (s : Finset β) : (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' s :=
  Set.bUnion_preimage_singleton f s

theorem set_bUnion_option_to_finset (o : Option α) (f : α → Set β) : (⋃ x ∈ o.toFinset, f x) = ⋃ x ∈ o, f x :=
  supr_option_to_finset o f

theorem set_bInter_option_to_finset (o : Option α) (f : α → Set β) : (⋂ x ∈ o.toFinset, f x) = ⋂ x ∈ o, f x :=
  infi_option_to_finset o f

theorem subset_set_bUnion_of_mem {s : Finset α} {f : α → Set β} {x : α} (h : x ∈ s) : f x ⊆ ⋃ y ∈ s, f y :=
  show f x ≤ ⨆ y ∈ s, f y from le_supr_of_le x <| le_supr _ h

variable [DecidableEq α]

theorem set_bUnion_union (s t : Finset α) (u : α → Set β) : (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  supr_union

theorem set_bInter_inter (s t : Finset α) (u : α → Set β) : (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  infi_union

theorem set_bUnion_insert (a : α) (s : Finset α) (t : α → Set β) : (⋃ x ∈ insert a s, t x) = t a ∪ ⋃ x ∈ s, t x :=
  supr_insert a s t

theorem set_bInter_insert (a : α) (s : Finset α) (t : α → Set β) : (⋂ x ∈ insert a s, t x) = t a ∩ ⋂ x ∈ s, t x :=
  infi_insert a s t

theorem set_bUnion_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    (⋃ x ∈ s.Image f, g x) = ⋃ y ∈ s, g (f y) :=
  supr_finset_image

theorem set_bInter_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    (⋂ x ∈ s.Image f, g x) = ⋂ y ∈ s, g (f y) :=
  infi_finset_image

theorem set_bUnion_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    (⋃ i ∈ insert x t, @update _ _ _ f x s i) = s ∪ ⋃ i ∈ t, f i :=
  supr_insert_update f hx

theorem set_bInter_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    (⋂ i ∈ insert x t, @update _ _ _ f x s i) = s ∩ ⋂ i ∈ t, f i :=
  infi_insert_update f hx

theorem set_bUnion_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    (⋃ y ∈ s.bUnion t, f y) = ⋃ (x ∈ s) (y ∈ t x), f y :=
  supr_bUnion s t f

theorem set_bInter_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    (⋂ y ∈ s.bUnion t, f y) = ⋂ (x ∈ s) (y ∈ t x), f y :=
  infi_bUnion s t f

end Finset

