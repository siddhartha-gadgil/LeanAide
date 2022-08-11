/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Johannes Hölzl
-/
import Mathbin.Order.ConditionallyCompleteLattice
import Mathbin.Logic.Function.Iterate
import Mathbin.Order.RelIso

/-!
# Order continuity

We say that a function is *left order continuous* if it sends all least upper bounds
to least upper bounds. The order dual notion is called *right order continuity*.

For monotone functions `ℝ → ℝ` these notions correspond to the usual left and right continuity.

We prove some basic lemmas (`map_sup`, `map_Sup` etc) and prove that an `rel_iso` is both left
and right order continuous.
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open Function OrderDual Set

/-!
### Definitions
-/


/-- A function `f` between preorders is left order continuous if it preserves all suprema.  We
define it using `is_lub` instead of `Sup` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def LeftOrdContinuous [Preorderₓ α] [Preorderₓ β] (f : α → β) :=
  ∀ ⦃s : Set α⦄ ⦃x⦄, IsLub s x → IsLub (f '' s) (f x)

/-- A function `f` between preorders is right order continuous if it preserves all infima.  We
define it using `is_glb` instead of `Inf` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def RightOrdContinuous [Preorderₓ α] [Preorderₓ β] (f : α → β) :=
  ∀ ⦃s : Set α⦄ ⦃x⦄, IsGlb s x → IsGlb (f '' s) (f x)

namespace LeftOrdContinuous

section Preorderₓ

variable (α) [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β}

protected theorem id : LeftOrdContinuous (id : α → α) := fun s x h => by
  simpa only [← image_id] using h

variable {α}

protected theorem order_dual : LeftOrdContinuous f → RightOrdContinuous (to_dual ∘ f ∘ of_dual) :=
  id

theorem map_is_greatest (hf : LeftOrdContinuous f) {s : Set α} {x : α} (h : IsGreatest s x) :
    IsGreatest (f '' s) (f x) :=
  ⟨mem_image_of_mem f h.1, (hf h.IsLub).1⟩

theorem mono (hf : LeftOrdContinuous f) : Monotone f := fun a₁ a₂ h =>
  have : IsGreatest {a₁, a₂} a₂ :=
    ⟨Or.inr rfl, by
      simp [*]⟩
  (hf.map_is_greatest this).2 <| mem_image_of_mem _ (Or.inl rfl)

theorem comp (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f) : LeftOrdContinuous (g ∘ f) := fun s x h => by
  simpa only [← image_image] using hg (hf h)

protected theorem iterate {f : α → α} (hf : LeftOrdContinuous f) (n : ℕ) : LeftOrdContinuous (f^[n]) :=
  (Nat.recOn n (LeftOrdContinuous.id α)) fun n ihn => ihn.comp hf

end Preorderₓ

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {f : α → β}

theorem map_sup (hf : LeftOrdContinuous f) (x y : α) : f (x⊔y) = f x⊔f y :=
  (hf is_lub_pair).unique <| by
    simp only [← image_pair, ← is_lub_pair]

theorem le_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x ≤ f y ↔ x ≤ y := by
  simp only [sup_eq_right, hf.map_sup, ← h.eq_iff]

theorem lt_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x < y := by
  simp only [← lt_iff_le_not_leₓ, ← hf.le_iff h]

variable (f)

/-- Convert an injective left order continuous function to an order embedding. -/
def toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, fun x y => hf.le_iff h⟩

variable {f}

@[simp]
theorem coe_to_order_embedding (hf : LeftOrdContinuous f) (h : Injective f) : ⇑(hf.toOrderEmbedding f h) = f :=
  rfl

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

theorem map_Sup' (hf : LeftOrdContinuous f) (s : Set α) : f (sup s) = sup (f '' s) :=
  (hf <| is_lub_Sup s).Sup_eq.symm

theorem map_Sup (hf : LeftOrdContinuous f) (s : Set α) : f (sup s) = ⨆ x ∈ s, f x := by
  rw [hf.map_Sup', Sup_image]

theorem map_supr (hf : LeftOrdContinuous f) (g : ι → α) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [← supr, ← hf.map_Sup', range_comp]

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

theorem map_cSup (hf : LeftOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddAbove s) :
    f (sup s) = sup (f '' s) :=
  ((hf <| is_lub_cSup sne sbdd).cSup_eq <| sne.Image f).symm

theorem map_csupr (hf : LeftOrdContinuous f) {g : ι → α} (hg : BddAbove (Range g)) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [← supr, ← hf.map_cSup (range_nonempty _) hg, range_comp]

end ConditionallyCompleteLattice

end LeftOrdContinuous

namespace RightOrdContinuous

section Preorderₓ

variable (α) [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β}

protected theorem id : RightOrdContinuous (id : α → α) := fun s x h => by
  simpa only [← image_id] using h

variable {α}

protected theorem order_dual : RightOrdContinuous f → LeftOrdContinuous (to_dual ∘ f ∘ of_dual) :=
  id

theorem map_is_least (hf : RightOrdContinuous f) {s : Set α} {x : α} (h : IsLeast s x) : IsLeast (f '' s) (f x) :=
  hf.OrderDual.map_is_greatest h

theorem mono (hf : RightOrdContinuous f) : Monotone f :=
  hf.OrderDual.mono.dual

theorem comp (hg : RightOrdContinuous g) (hf : RightOrdContinuous f) : RightOrdContinuous (g ∘ f) :=
  hg.OrderDual.comp hf.OrderDual

protected theorem iterate {f : α → α} (hf : RightOrdContinuous f) (n : ℕ) : RightOrdContinuous (f^[n]) :=
  hf.OrderDual.iterate n

end Preorderₓ

section SemilatticeInf

variable [SemilatticeInf α] [SemilatticeInf β] {f : α → β}

theorem map_inf (hf : RightOrdContinuous f) (x y : α) : f (x⊓y) = f x⊓f y :=
  hf.OrderDual.map_sup x y

theorem le_iff (hf : RightOrdContinuous f) (h : Injective f) {x y} : f x ≤ f y ↔ x ≤ y :=
  hf.OrderDual.le_iff h

theorem lt_iff (hf : RightOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x < y :=
  hf.OrderDual.lt_iff h

variable (f)

/-- Convert an injective left order continuous function to a `order_embedding`. -/
def toOrderEmbedding (hf : RightOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, fun x y => hf.le_iff h⟩

variable {f}

@[simp]
theorem coe_to_order_embedding (hf : RightOrdContinuous f) (h : Injective f) : ⇑(hf.toOrderEmbedding f h) = f :=
  rfl

end SemilatticeInf

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

theorem map_Inf' (hf : RightOrdContinuous f) (s : Set α) : f (inf s) = inf (f '' s) :=
  hf.OrderDual.map_Sup' s

theorem map_Inf (hf : RightOrdContinuous f) (s : Set α) : f (inf s) = ⨅ x ∈ s, f x :=
  hf.OrderDual.map_Sup s

theorem map_infi (hf : RightOrdContinuous f) (g : ι → α) : f (⨅ i, g i) = ⨅ i, f (g i) :=
  hf.OrderDual.map_supr g

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

theorem map_cInf (hf : RightOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddBelow s) :
    f (inf s) = inf (f '' s) :=
  hf.OrderDual.map_cSup sne sbdd

theorem map_cinfi (hf : RightOrdContinuous f) {g : ι → α} (hg : BddBelow (Range g)) : f (⨅ i, g i) = ⨅ i, f (g i) :=
  hf.OrderDual.map_csupr hg

end ConditionallyCompleteLattice

end RightOrdContinuous

namespace OrderIso

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] (e : α ≃o β) {s : Set α} {x : α}

protected theorem left_ord_continuous : LeftOrdContinuous e := fun s x hx =>
  ⟨Monotone.mem_upper_bounds_image (fun x y => e.map_rel_iff.2) hx.1, fun y hy =>
    e.rel_symm_apply.1 <| (is_lub_le_iff hx).2 fun x' hx' => e.rel_symm_apply.2 <| hy <| mem_image_of_mem _ hx'⟩

protected theorem right_ord_continuous : RightOrdContinuous e :=
  OrderIso.left_ord_continuous e.dual

end Preorderₓ

end OrderIso

