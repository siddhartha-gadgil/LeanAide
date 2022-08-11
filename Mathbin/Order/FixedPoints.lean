/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Yury Kudryashov
-/
import Mathbin.Dynamics.FixedPoints.Basic
import Mathbin.Order.Hom.Order

/-!
# Fixed point construction on complete lattices

This file sets up the basic theory of fixed points of a monotone function in a complete lattice.

## Main definitions

* `order_hom.lfp`: The least fixed point of a bundled monotone function.
* `order_hom.gfp`: The greatest fixed point of a bundled monotone function.
* `order_hom.prev_fixed`: The greatest fixed point of a bundled monotone function smaller than or
  equal to a given element.
* `order_hom.next_fixed`: The least fixed point of a bundled monotone function greater than or
  equal to a given element.
* `fixed_points.complete_lattice`: The Knaster-Tarski theorem: fixed points of a monotone
  self-map of a complete lattice form themselves a complete lattice.

## Tags

fixed point, complete lattice, monotone function
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function (FixedPoints IsFixedPt)

namespace OrderHom

section Basic

variable [CompleteLattice α] (f : α →o α)

/-- Least fixed point of a monotone function -/
def lfp : (α →o α) →o α where
  toFun := fun f => inf { a | f a ≤ a }
  monotone' := fun f g hle => Inf_le_Inf fun a ha => (hle a).trans ha

/-- Greatest fixed point of a monotone function -/
def gfp : (α →o α) →o α where
  toFun := fun f => sup { a | a ≤ f a }
  monotone' := fun f g hle => Sup_le_Sup fun a ha => le_transₓ ha (hle a)

theorem lfp_le {a : α} (h : f a ≤ a) : lfp f ≤ a :=
  Inf_le h

theorem lfp_le_fixed {a : α} (h : f a = a) : lfp f ≤ a :=
  f.lfp_le h.le

theorem le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ lfp f :=
  le_Inf h

theorem map_le_lfp {a : α} (ha : a ≤ f.lfp) : f a ≤ f.lfp :=
  f.le_lfp fun b hb => (f.mono <| le_Inf_iff.1 ha _ hb).trans hb

@[simp]
theorem map_lfp : f (lfp f) = lfp f :=
  have h : f (lfp f) ≤ lfp f := f.map_le_lfp le_rfl
  h.antisymm <| f.lfp_le <| f.mono h

theorem is_fixed_pt_lfp : IsFixedPt f f.lfp :=
  f.map_lfp

theorem lfp_le_map {a : α} (ha : lfp f ≤ a) : lfp f ≤ f a :=
  calc
    lfp f = f (lfp f) := f.map_lfp.symm
    _ ≤ f a := f.mono ha
    

theorem is_least_lfp_le : IsLeast { a | f a ≤ a } (lfp f) :=
  ⟨f.map_lfp.le, fun a => f.lfp_le⟩

theorem is_least_lfp : IsLeast (FixedPoints f) (lfp f) :=
  ⟨f.is_fixed_pt_lfp, fun a => f.lfp_le_fixed⟩

theorem lfp_induction {p : α → Prop} (step : ∀ a, p a → a ≤ lfp f → p (f a))
    (hSup : ∀ s, (∀, ∀ a ∈ s, ∀, p a) → p (sup s)) : p (lfp f) := by
  set s := { a | a ≤ lfp f ∧ p a }
  specialize hSup s fun a => And.right
  suffices : Sup s = lfp f
  exact this ▸ hSup
  have h : Sup s ≤ lfp f := Sup_le fun b => And.left
  have hmem : f (Sup s) ∈ s := ⟨f.map_le_lfp h, step _ hSup h⟩
  exact h.antisymm (f.lfp_le <| le_Sup hmem)

theorem le_gfp {a : α} (h : a ≤ f a) : a ≤ gfp f :=
  le_Sup h

theorem gfp_le {a : α} (h : ∀ b, b ≤ f b → b ≤ a) : gfp f ≤ a :=
  Sup_le h

theorem is_fixed_pt_gfp : IsFixedPt f (gfp f) :=
  f.dual.is_fixed_pt_lfp

@[simp]
theorem map_gfp : f (gfp f) = gfp f :=
  f.dual.map_lfp

theorem map_le_gfp {a : α} (ha : a ≤ gfp f) : f a ≤ gfp f :=
  f.dual.lfp_le_map ha

theorem gfp_le_map {a : α} (ha : gfp f ≤ a) : gfp f ≤ f a :=
  f.dual.map_le_lfp ha

theorem is_greatest_gfp_le : IsGreatest { a | a ≤ f a } (gfp f) :=
  f.dual.is_least_lfp_le

theorem is_greatest_gfp : IsGreatest (FixedPoints f) (gfp f) :=
  f.dual.is_least_lfp

theorem gfp_induction {p : α → Prop} (step : ∀ a, p a → gfp f ≤ a → p (f a))
    (hInf : ∀ s, (∀, ∀ a ∈ s, ∀, p a) → p (inf s)) : p (gfp f) :=
  f.dual.lfp_induction step hInf

end Basic

section Eqn

variable [CompleteLattice α] [CompleteLattice β] (f : β →o α) (g : α →o β)

-- Rolling rule
theorem map_lfp_comp : f (lfp (g.comp f)) = lfp (f.comp g) :=
  le_antisymmₓ ((f.comp g).map_lfp ▸ f.mono (lfp_le_fixed _ <| congr_arg g (f.comp g).map_lfp)) <|
    lfp_le _ (congr_arg f (g.comp f).map_lfp).le

theorem map_gfp_comp : f (g.comp f).gfp = (f.comp g).gfp :=
  f.dual.map_lfp_comp g.dual

-- Diagonal rule
theorem lfp_lfp (h : α →o α →o α) : lfp (lfp.comp h) = lfp h.onDiag := by
  let a := lfp (lfp.comp h)
  refine' (lfp_le _ _).antisymm (lfp_le _ (Eq.le _))
  · exact lfp_le _ h.on_diag.map_lfp.le
    
  have ha : (lfp ∘ h) a = a := (lfp.comp h).map_lfp
  calc h a a = h a (lfp (h a)) := congr_arg (h a) ha.symm _ = lfp (h a) := (h a).map_lfp _ = a := ha

theorem gfp_gfp (h : α →o α →o α) : gfp (gfp.comp h) = gfp h.onDiag :=
  @lfp_lfp αᵒᵈ _ <| (OrderHom.dualIso αᵒᵈ αᵒᵈ).symm.toOrderEmbedding.toOrderHom.comp h.dual

end Eqn

section PrevNext

variable [CompleteLattice α] (f : α →o α)

theorem gfp_const_inf_le (x : α) : gfp (const α x⊓f) ≤ x :=
  (gfp_le _) fun b hb => hb.trans inf_le_left

/-- Previous fixed point of a monotone map. If `f` is a monotone self-map of a complete lattice and
`x` is a point such that `f x ≤ x`, then `f.prev_fixed x hx` is the greatest fixed point of `f`
that is less than or equal to `x`. -/
def prevFixed (x : α) (hx : f x ≤ x) : FixedPoints f :=
  ⟨gfp (const α x⊓f),
    calc
      f (gfp (const α x⊓f)) = x⊓f (gfp (const α x⊓f)) :=
        Eq.symm <| inf_of_le_right <| (f.mono <| f.gfp_const_inf_le x).trans hx
      _ = gfp (const α x⊓f) := (const α x⊓f).map_gfp
      ⟩

/-- Next fixed point of a monotone map. If `f` is a monotone self-map of a complete lattice and
`x` is a point such that `x ≤ f x`, then `f.next_fixed x hx` is the least fixed point of `f`
that is greater than or equal to `x`. -/
def nextFixed (x : α) (hx : x ≤ f x) : FixedPoints f :=
  { f.dual.prevFixed x hx with val := (const α x⊔f).lfp }

theorem prev_fixed_le {x : α} (hx : f x ≤ x) : ↑(f.prevFixed x hx) ≤ x :=
  f.gfp_const_inf_le x

theorem le_next_fixed {x : α} (hx : x ≤ f x) : x ≤ f.nextFixed x hx :=
  f.dual.prev_fixed_le hx

theorem next_fixed_le {x : α} (hx : x ≤ f x) {y : FixedPoints f} (h : x ≤ y) : f.nextFixed x hx ≤ y :=
  Subtype.coe_le_coe.1 <| lfp_le _ <| sup_le h y.2.le

@[simp]
theorem next_fixed_le_iff {x : α} (hx : x ≤ f x) {y : FixedPoints f} : f.nextFixed x hx ≤ y ↔ x ≤ y :=
  ⟨fun h => (f.le_next_fixed hx).trans h, f.next_fixed_le hx⟩

@[simp]
theorem le_prev_fixed_iff {x : α} (hx : f x ≤ x) {y : FixedPoints f} : y ≤ f.prevFixed x hx ↔ ↑y ≤ x :=
  f.dual.next_fixed_le_iff hx

theorem le_prev_fixed {x : α} (hx : f x ≤ x) {y : FixedPoints f} (h : ↑y ≤ x) : y ≤ f.prevFixed x hx :=
  (f.le_prev_fixed_iff hx).2 h

theorem le_map_sup_fixed_points (x y : FixedPoints f) : (x⊔y : α) ≤ f (x⊔y) :=
  calc
    (x⊔y : α) = f x⊔f y := congr_arg2ₓ (·⊔·) x.2.symm y.2.symm
    _ ≤ f (x⊔y) := f.mono.le_map_sup x y
    

theorem map_inf_fixed_points_le (x y : FixedPoints f) : f (x⊓y) ≤ x⊓y :=
  f.dual.le_map_sup_fixed_points x y

theorem le_map_Sup_subset_fixed_points (A : Set α) (hA : A ⊆ FixedPoints f) : sup A ≤ f (sup A) :=
  Sup_le fun x hx => hA hx ▸ (f.mono <| le_Sup hx)

theorem map_Inf_subset_fixed_points_le (A : Set α) (hA : A ⊆ FixedPoints f) : f (inf A) ≤ inf A :=
  le_Inf fun x hx => hA hx ▸ (f.mono <| Inf_le hx)

end PrevNext

end OrderHom

namespace FixedPoints

open OrderHom

variable [CompleteLattice α] (f : α →o α)

instance : SemilatticeSup (FixedPoints f) :=
  { Subtype.partialOrder _ with sup := fun x y => f.nextFixed (x⊔y) (f.le_map_sup_fixed_points x y),
    le_sup_left := fun x y => Subtype.coe_le_coe.1 <| le_sup_left.trans (f.le_next_fixed _),
    le_sup_right := fun x y => Subtype.coe_le_coe.1 <| le_sup_right.trans (f.le_next_fixed _),
    sup_le := fun x y z hxz hyz => f.next_fixed_le _ <| sup_le hxz hyz }

instance : SemilatticeInf (FixedPoints f) :=
  { Subtype.partialOrder _, OrderDual.semilatticeInf (FixedPoints f.dual) with
    inf := fun x y => f.prevFixed (x⊓y) (f.map_inf_fixed_points_le x y) }

instance : CompleteSemilatticeSup (FixedPoints f) :=
  { Subtype.partialOrder _ with
    sup := fun s =>
      f.nextFixed (sup (coe '' s)) (f.le_map_Sup_subset_fixed_points (coe '' s) fun z ⟨x, hx⟩ => hx.2 ▸ x.2),
    le_Sup := fun s x hx => Subtype.coe_le_coe.1 <| le_transₓ (le_Sup <| Set.mem_image_of_mem _ hx) (f.le_next_fixed _),
    Sup_le := fun s x hx => f.next_fixed_le _ <| Sup_le <| Set.ball_image_iff.2 hx }

instance : CompleteSemilatticeInf (FixedPoints f) :=
  { Subtype.partialOrder _ with
    inf := fun s =>
      f.prevFixed (inf (coe '' s)) (f.map_Inf_subset_fixed_points_le (coe '' s) fun z ⟨x, hx⟩ => hx.2 ▸ x.2),
    le_Inf := fun s x hx => f.le_prev_fixed _ <| le_Inf <| Set.ball_image_iff.2 hx,
    Inf_le := fun s x hx =>
      Subtype.coe_le_coe.1 <| le_transₓ (f.prev_fixed_le _) (Inf_le <| Set.mem_image_of_mem _ hx) }

/-- **Knaster-Tarski Theorem**: The fixed points of `f` form a complete lattice. -/
instance : CompleteLattice (FixedPoints f) :=
  { Subtype.partialOrder _, FixedPoints.semilatticeSup f, FixedPoints.semilatticeInf f,
    FixedPoints.completeSemilatticeSup f, FixedPoints.completeSemilatticeInf f with top := ⟨f.gfp, f.is_fixed_pt_gfp⟩,
    bot := ⟨f.lfp, f.is_fixed_pt_lfp⟩, le_top := fun x => f.le_gfp x.2.Ge, bot_le := fun x => f.lfp_le x.2.le }

end FixedPoints

