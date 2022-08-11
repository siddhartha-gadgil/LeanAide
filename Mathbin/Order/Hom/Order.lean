/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Anne Baanen
-/
import Mathbin.Logic.Function.Iterate
import Mathbin.Order.GaloisConnection
import Mathbin.Order.Hom.Basic

/-!
# Lattice structure on order homomorphisms

This file defines the lattice structure on order homomorphisms, which are bundled
monotone functions.

## Main definitions

 * `order_hom.complete_lattice`: if `β` is a complete lattice, so is `α →o β`

## Tags

monotone map, bundled morphism
-/


namespace OrderHom

variable {α β : Type _}

section Preorderₓ

variable [Preorderₓ α]

@[simps]
instance [SemilatticeSup β] : HasSup (α →o β) where sup := fun f g => ⟨fun a => f a⊔g a, f.mono.sup g.mono⟩

instance [SemilatticeSup β] : SemilatticeSup (α →o β) :=
  { (_ : PartialOrderₓ (α →o β)) with sup := HasSup.sup, le_sup_left := fun a b x => le_sup_left,
    le_sup_right := fun a b x => le_sup_right, sup_le := fun a b c h₀ h₁ x => sup_le (h₀ x) (h₁ x) }

@[simps]
instance [SemilatticeInf β] : HasInf (α →o β) where inf := fun f g => ⟨fun a => f a⊓g a, f.mono.inf g.mono⟩

instance [SemilatticeInf β] : SemilatticeInf (α →o β) :=
  { (_ : PartialOrderₓ (α →o β)), (dualIso α β).symm.toGaloisInsertion.liftSemilatticeInf with inf := (·⊓·) }

instance [Lattice β] : Lattice (α →o β) :=
  { (_ : SemilatticeSup (α →o β)), (_ : SemilatticeInf (α →o β)) with }

@[simps]
instance [Preorderₓ β] [OrderBot β] : HasBot (α →o β) where bot := const α ⊥

instance [Preorderₓ β] [OrderBot β] : OrderBot (α →o β) where
  bot := ⊥
  bot_le := fun a x => bot_le

@[simps]
instance [Preorderₓ β] [OrderTop β] : HasTop (α →o β) where top := const α ⊤

instance [Preorderₓ β] [OrderTop β] : OrderTop (α →o β) where
  top := ⊤
  le_top := fun a x => le_top

instance [CompleteLattice β] :
    HasInfₓ (α →o β) where inf := fun s => ⟨fun x => ⨅ f ∈ s, (f : _) x, fun x y h => infi₂_mono fun f _ => f.mono h⟩

@[simp]
theorem Inf_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) : inf s x = ⨅ f ∈ s, (f : _) x :=
  rfl

theorem infi_apply {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) (x : α) : (⨅ i, f i) x = ⨅ i, f i x :=
  (Inf_apply _ _).trans infi_range

@[simp, norm_cast]
theorem coe_infi {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) : ((⨅ i, f i : α →o β) : α → β) = ⨅ i, f i :=
  funext fun x => (infi_apply f x).trans (@infi_apply _ _ _ _ (fun i => f i) _).symm

instance [CompleteLattice β] :
    HasSupₓ (α →o β) where sup := fun s => ⟨fun x => ⨆ f ∈ s, (f : _) x, fun x y h => supr₂_mono fun f _ => f.mono h⟩

@[simp]
theorem Sup_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) : sup s x = ⨆ f ∈ s, (f : _) x :=
  rfl

theorem supr_apply {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) (x : α) : (⨆ i, f i) x = ⨆ i, f i x :=
  (Sup_apply _ _).trans supr_range

@[simp, norm_cast]
theorem coe_supr {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) : ((⨆ i, f i : α →o β) : α → β) = ⨆ i, f i :=
  funext fun x => (supr_apply f x).trans (@supr_apply _ _ _ _ (fun i => f i) _).symm

instance [CompleteLattice β] : CompleteLattice (α →o β) :=
  { (_ : Lattice (α →o β)), OrderHom.orderTop, OrderHom.orderBot with sup := sup,
    le_Sup := fun s f hf x => le_supr_of_le f (le_supr _ hf), Sup_le := fun s f hf x => supr₂_le fun g hg => hf g hg x,
    inf := inf, le_Inf := fun s f hf x => le_infi₂ fun g hg => hf g hg x,
    Inf_le := fun s f hf x => infi_le_of_le f (infi_le _ hf) }

theorem iterate_sup_le_sup_iff {α : Type _} [SemilatticeSup α] (f : α →o α) :
    (∀ n₁ n₂ a₁ a₂, (f^[n₁ + n₂]) (a₁⊔a₂) ≤ (f^[n₁]) a₁⊔(f^[n₂]) a₂) ↔ ∀ a₁ a₂, f (a₁⊔a₂) ≤ f a₁⊔a₂ := by
  constructor <;> intro h
  · exact h 1 0
    
  · intro n₁ n₂ a₁ a₂
    have h' : ∀ n a₁ a₂, (f^[n]) (a₁⊔a₂) ≤ (f^[n]) a₁⊔a₂ := by
      intro n
      induction' n with n ih <;> intro a₁ a₂
      · rfl
        
      · calc (f^[n + 1]) (a₁⊔a₂) = (f^[n]) (f (a₁⊔a₂)) := Function.iterate_succ_apply f n _ _ ≤ (f^[n]) (f a₁⊔a₂) :=
            f.mono.iterate n (h a₁ a₂)_ ≤ (f^[n]) (f a₁)⊔a₂ := ih _ _ _ = (f^[n + 1]) a₁⊔a₂ := by
            rw [← Function.iterate_succ_apply]
        
    calc (f^[n₁ + n₂]) (a₁⊔a₂) = (f^[n₁]) ((f^[n₂]) (a₁⊔a₂)) :=
        Function.iterate_add_apply f n₁ n₂ _ _ = (f^[n₁]) ((f^[n₂]) (a₂⊔a₁)) := by
        rw [sup_comm]_ ≤ (f^[n₁]) ((f^[n₂]) a₂⊔a₁) := f.mono.iterate n₁ (h' n₂ _ _)_ = (f^[n₁]) (a₁⊔(f^[n₂]) a₂) := by
        rw [sup_comm]_ ≤ (f^[n₁]) a₁⊔(f^[n₂]) a₂ := h' n₁ a₁ _
    

end Preorderₓ

end OrderHom

