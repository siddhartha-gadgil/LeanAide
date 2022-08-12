/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathbin.Order.GaloisConnection

/-!
# Relations

This file defines bundled relations. A relation between `α` and `β` is a function `α → β → Prop`.
Relations are also known as set-valued functions, or partial multifunctions.

## Main declarations

* `rel α β`: Relation between `α` and `β`.
* `rel.inv`: `r.inv` is the `rel β α` obtained by swapping the arguments of `r`.
* `rel.dom`: Domain of a relation. `x ∈ r.dom` iff there exists `y` such that `r x y`.
* `rel.codom`: Codomain, aka range, of a relation. `y ∈ r.codom` iff there exists `x` such that
  `r x y`.
* `rel.comp`: Relation composition. Note that the arguments order follows the `category_theory/`
  one, so `r.comp s x z ↔ ∃ y, r x y ∧ s y z`.
* `rel.image`: Image of a set under a relation. `r.image s` is the set of `f x` over all `x ∈ s`.
* `rel.preimage`: Preimage of a set under a relation. Note that `r.preimage = r.inv.image`.
* `rel.core`: Core of a set. For `s : set β`, `r.core s` is the set of `x : α` such that all `y`
  related to `x` are in `s`.
* `rel.restrict_domain`: Domain-restriction of a relation to a subtype.
* `function.graph`: Graph of a function as a relation.
-/


variable {α β γ : Type _}

/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction --/
def Rel (α β : Type _) :=
  α → β → Prop deriving CompleteLattice, Inhabited

namespace Rel

variable {δ : Type _} (r : Rel α β)

/-- The inverse relation : `r.inv x y ↔ r y x`. Note that this is *not* a groupoid inverse. -/
def Inv : Rel β α :=
  flip r

theorem inv_def (x : α) (y : β) : r.inv y x ↔ r x y :=
  Iff.rfl

theorem inv_inv : Inv (Inv r) = r := by
  ext x y
  rfl

/-- Domain of a relation -/
def Dom :=
  { x | ∃ y, r x y }

theorem dom_mono {r s : Rel α β} (h : r ≤ s) : Dom r ⊆ Dom s := fun a ⟨b, hx⟩ => ⟨b, h a b hx⟩

/-- Codomain aka range of a relation -/
def Codom :=
  { y | ∃ x, r x y }

theorem codom_inv : r.inv.Codom = r.Dom := by
  ext x y
  rfl

theorem dom_inv : r.inv.Dom = r.Codom := by
  ext x y
  rfl

/-- Composition of relation; note that it follows the `category_theory/` order of arguments. -/
def Comp (r : Rel α β) (s : Rel β γ) : Rel α γ := fun x z => ∃ y, r x y ∧ s y z

-- mathport name: «expr ∘ »
local infixr:0 " ∘ " => Rel.Comp

theorem comp_assoc (r : Rel α β) (s : Rel β γ) (t : Rel γ δ) : ((r ∘ s) ∘ t) = (r ∘ s ∘ t) := by
  unfold comp
  ext x w
  constructor
  · rintro ⟨z, ⟨y, rxy, syz⟩, tzw⟩
    exact ⟨y, rxy, z, syz, tzw⟩
    
  rintro ⟨y, rxy, z, syz, tzw⟩
  exact ⟨z, ⟨y, rxy, syz⟩, tzw⟩

@[simp]
theorem comp_right_id (r : Rel α β) : (r ∘ @Eq β) = r := by
  unfold comp
  ext y
  simp

@[simp]
theorem comp_left_id (r : Rel α β) : (@Eq α ∘ r) = r := by
  unfold comp
  ext x
  simp

theorem inv_id : Inv (@Eq α) = @Eq α := by
  ext x y
  constructor <;> apply Eq.symm

theorem inv_comp (r : Rel α β) (s : Rel β γ) : Inv (r ∘ s) = (Inv s ∘ Inv r) := by
  ext x z
  simp [← comp, ← inv, ← flip, ← And.comm]

/-- Image of a set under a relation -/
def Image (s : Set α) : Set β :=
  { y | ∃ x ∈ s, r x y }

theorem mem_image (y : β) (s : Set α) : y ∈ Image r s ↔ ∃ x ∈ s, r x y :=
  Iff.rfl

theorem image_subset : ((· ⊆ ·)⇒(· ⊆ ·)) r.Image r.Image := fun s t h y ⟨x, xs, rxy⟩ => ⟨x, h xs, rxy⟩

theorem image_mono : Monotone r.Image :=
  r.image_subset

theorem image_inter (s t : Set α) : r.Image (s ∩ t) ⊆ r.Image s ∩ r.Image t :=
  r.image_mono.map_inf_le s t

theorem image_union (s t : Set α) : r.Image (s ∪ t) = r.Image s ∪ r.Image t :=
  le_antisymmₓ (fun y ⟨x, xst, rxy⟩ => xst.elim (fun xs => Or.inl ⟨x, ⟨xs, rxy⟩⟩) fun xt => Or.inr ⟨x, ⟨xt, rxy⟩⟩)
    (r.image_mono.le_map_sup s t)

@[simp]
theorem image_id (s : Set α) : Image (@Eq α) s = s := by
  ext x
  simp [← mem_image]

theorem image_comp (s : Rel β γ) (t : Set α) : Image (r ∘ s) t = Image s (Image r t) := by
  ext z
  simp only [← mem_image, ← comp]
  constructor
  · rintro ⟨x, xt, y, rxy, syz⟩
    exact ⟨y, ⟨x, xt, rxy⟩, syz⟩
    
  rintro ⟨y, ⟨x, xt, rxy⟩, syz⟩
  exact ⟨x, xt, y, rxy, syz⟩

theorem image_univ : r.Image Set.Univ = r.Codom := by
  ext y
  simp [← mem_image, ← codom]

/-- Preimage of a set under a relation `r`. Same as the image of `s` under `r.inv` -/
def Preimage (s : Set β) : Set α :=
  r.inv.Image s

theorem mem_preimage (x : α) (s : Set β) : x ∈ r.Preimage s ↔ ∃ y ∈ s, r x y :=
  Iff.rfl

theorem preimage_def (s : Set β) : Preimage r s = { x | ∃ y ∈ s, r x y } :=
  Set.ext fun x => mem_preimage _ _ _

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : r.Preimage s ⊆ r.Preimage t :=
  image_mono _ h

theorem preimage_inter (s t : Set β) : r.Preimage (s ∩ t) ⊆ r.Preimage s ∩ r.Preimage t :=
  image_inter _ s t

theorem preimage_union (s t : Set β) : r.Preimage (s ∪ t) = r.Preimage s ∪ r.Preimage t :=
  image_union _ s t

theorem preimage_id (s : Set α) : Preimage (@Eq α) s = s := by
  simp only [← preimage, ← inv_id, ← image_id]

theorem preimage_comp (s : Rel β γ) (t : Set γ) : Preimage (r ∘ s) t = Preimage r (Preimage s t) := by
  simp only [← preimage, ← inv_comp, ← image_comp]

theorem preimage_univ : r.Preimage Set.Univ = r.Dom := by
  rw [preimage, image_univ, codom_inv]

/-- Core of a set `s : set β` w.r.t `r : rel α β` is the set of `x : α` that are related *only*
to elements of `s`. Other generalization of `function.preimage`. -/
def Core (s : Set β) :=
  { x | ∀ y, r x y → y ∈ s }

theorem mem_core (x : α) (s : Set β) : x ∈ r.Core s ↔ ∀ y, r x y → y ∈ s :=
  Iff.rfl

theorem core_subset : ((· ⊆ ·)⇒(· ⊆ ·)) r.Core r.Core := fun s t h x h' y rxy => h (h' y rxy)

theorem core_mono : Monotone r.Core :=
  r.core_subset

theorem core_inter (s t : Set β) : r.Core (s ∩ t) = r.Core s ∩ r.Core t :=
  Set.ext
    (by
      simp [← mem_core, ← imp_and_distrib, ← forall_and_distrib])

theorem core_union (s t : Set β) : r.Core s ∪ r.Core t ⊆ r.Core (s ∪ t) :=
  r.core_mono.le_map_sup s t

@[simp]
theorem core_univ : r.Core Set.Univ = Set.Univ :=
  Set.ext
    (by
      simp [← mem_core])

theorem core_id (s : Set α) : Core (@Eq α) s = s := by
  simp [← core]

theorem core_comp (s : Rel β γ) (t : Set γ) : Core (r ∘ s) t = Core r (Core s t) := by
  ext x
  simp [← core, ← comp]
  constructor
  · exact fun h y rxy z => h z y rxy
    
  · exact fun h z y rzy => h y rzy z
    

/-- Restrict the domain of a relation to a subtype. -/
def RestrictDomain (s : Set α) : Rel { x // x ∈ s } β := fun x y => r x.val y

theorem image_subset_iff (s : Set α) (t : Set β) : Image r s ⊆ t ↔ s ⊆ Core r t :=
  Iff.intro (fun h x xs y rxy => h ⟨x, xs, rxy⟩) fun h y ⟨x, xs, rxy⟩ => h xs y rxy

theorem image_core_gc : GaloisConnection r.Image r.Core :=
  image_subset_iff _

end Rel

namespace Function

/-- The graph of a function as a relation. -/
def Graph (f : α → β) : Rel α β := fun x y => f x = y

end Function

namespace Set

-- TODO: if image were defined with bounded quantification in corelib, the next two would
-- be definitional
theorem image_eq (f : α → β) (s : Set α) : f '' s = (Function.Graph f).Image s := by
  simp [← Set.Image, ← Function.Graph, ← Rel.Image]

theorem preimage_eq (f : α → β) (s : Set β) : f ⁻¹' s = (Function.Graph f).Preimage s := by
  simp [← Set.Preimage, ← Function.Graph, ← Rel.Preimage, ← Rel.Inv, ← flip, ← Rel.Image]

theorem preimage_eq_core (f : α → β) (s : Set β) : f ⁻¹' s = (Function.Graph f).Core s := by
  simp [← Set.Preimage, ← Function.Graph, ← Rel.Core]

end Set

