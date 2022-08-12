/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Hom.Bounded
import Mathbin.Order.Hom.Order
import Mathbin.Topology.Order.Hom.Basic

/-!
# Esakia morphisms

This file defines pseudo-epimorphisms and Esakia morphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `pseudo_epimorphism`: Pseudo-epimorphisms. Maps `f` such that `f a ≤ b` implies the existence of
  `a'` such that `a ≤ a'` and `f a' = b`.
* `esakia_hom`: Esakia morphisms. Continuous pseudo-epimorphisms.

## Typeclasses

* `pseudo_epimorphism_class`
* `esakia_hom_class`

## References

* [Wikipedia, *Esakia space*](https://en.wikipedia.org/wiki/Esakia_space)
-/


open Function

variable {F α β γ δ : Type _}

/-- The type of pseudo-epimorphisms, aka p-morphisms, aka bounded maps, from `α` to `β`. -/
structure PseudoEpimorphism (α β : Type _) [Preorderₓ α] [Preorderₓ β] extends α →o β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : to_fun a ≤ b → ∃ c, a ≤ c ∧ to_fun c = b

/-- The type of Esakia morphisms, aka continuous pseudo-epimorphisms, from `α` to `β`. -/
structure EsakiaHom (α β : Type _) [TopologicalSpace α] [Preorderₓ α] [TopologicalSpace β] [Preorderₓ β] extends
  α →Co β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : to_fun a ≤ b → ∃ c, a ≤ c ∧ to_fun c = b

/-- `pseudo_epimorphism_class F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `pseudo_epimorphism`. -/
class PseudoEpimorphismClass (F : Type _) (α β : outParam <| Type _) [Preorderₓ α] [Preorderₓ β] extends
  RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop) where
  exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a ≤ b → ∃ c, a ≤ c ∧ f c = b

/-- `esakia_hom_class F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `esakia_hom`. -/
class EsakiaHomClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α] [Preorderₓ α] [TopologicalSpace β]
  [Preorderₓ β] extends ContinuousOrderHomClass F α β where
  exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a ≤ b → ∃ c, a ≤ c ∧ f c = b

export PseudoEpimorphismClass (exists_map_eq_of_map_le)

-- See note [lower instance priority]
instance (priority := 100) PseudoEpimorphismClass.toTopHomClass [PartialOrderₓ α] [OrderTop α] [Preorderₓ β]
    [OrderTop β] [PseudoEpimorphismClass F α β] : TopHomClass F α β :=
  ⟨fun f => by
    let ⟨b, h⟩ := exists_map_eq_of_map_le f (@le_top _ _ _ <| f ⊤)
    rw [← top_le_iff.1 h.1, h.2]⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toPseudoEpimorphismClass [Preorderₓ α] [Preorderₓ β] [OrderIsoClass F α β] :
    PseudoEpimorphismClass F α β :=
  ⟨fun f a b h => ⟨EquivLike.inv f b, (le_map_inv_iff f).2 h, EquivLike.right_inv _ _⟩⟩

-- See note [lower instance priority]
instance (priority := 100) EsakiaHomClass.toPseudoEpimorphismClass [TopologicalSpace α] [Preorderₓ α]
    [TopologicalSpace β] [Preorderₓ β] [EsakiaHomClass F α β] : PseudoEpimorphismClass F α β :=
  { ‹EsakiaHomClass F α β› with }

instance [Preorderₓ α] [Preorderₓ β] [PseudoEpimorphismClass F α β] : CoeTₓ F (PseudoEpimorphism α β) :=
  ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

instance [TopologicalSpace α] [Preorderₓ α] [TopologicalSpace β] [Preorderₓ β] [EsakiaHomClass F α β] :
    CoeTₓ F (EsakiaHom α β) :=
  ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

/-! ### Pseudo-epimorphisms -/


namespace PseudoEpimorphism

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] [Preorderₓ δ]

instance : PseudoEpimorphismClass (PseudoEpimorphism α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_rel := fun f => f.monotone'
  exists_map_eq_of_map_le := PseudoEpimorphism.exists_map_eq_of_map_le'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (PseudoEpimorphism α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : PseudoEpimorphism α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : PseudoEpimorphism α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `pseudo_epimorphism` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : PseudoEpimorphism α β) (f' : α → β) (h : f' = f) : PseudoEpimorphism α β :=
  ⟨f.toOrderHom.copy f' h, by
    simpa only [← h.symm, ← to_fun_eq_coe] using f.exists_map_eq_of_map_le'⟩

variable (α)

/-- `id` as a `pseudo_epimorphism`. -/
protected def id : PseudoEpimorphism α α :=
  ⟨OrderHom.id, fun a b h => ⟨b, h, rfl⟩⟩

instance : Inhabited (PseudoEpimorphism α α) :=
  ⟨PseudoEpimorphism.id α⟩

@[simp]
theorem coe_id : ⇑(PseudoEpimorphism.id α) = id :=
  rfl

@[simp]
theorem coe_id_order_hom : (PseudoEpimorphism.id α : α →o α) = OrderHom.id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : PseudoEpimorphism.id α a = a :=
  rfl

/-- Composition of `pseudo_epimorphism`s as a `pseudo_epimorphism`. -/
def comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) : PseudoEpimorphism α γ :=
  ⟨g.toOrderHom.comp f.toOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩

@[simp]
theorem coe_comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) : (g.comp f : α → γ) = g ∘ f :=
  rfl

@[simp]
theorem coe_comp_order_hom (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) :
    (g.comp f : α →o γ) = (g : β →o γ).comp f :=
  rfl

@[simp]
theorem comp_apply (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) (a : α) : (g.comp f) a = g (f a) :=
  rfl

@[simp]
theorem comp_assoc (h : PseudoEpimorphism γ δ) (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem comp_id (f : PseudoEpimorphism α β) : f.comp (PseudoEpimorphism.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : PseudoEpimorphism α β) : (PseudoEpimorphism.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : PseudoEpimorphism β γ} {f : PseudoEpimorphism α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : PseudoEpimorphism β γ} {f₁ f₂ : PseudoEpimorphism α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end PseudoEpimorphism

/-! ### Esakia morphisms -/


namespace EsakiaHom

variable [TopologicalSpace α] [Preorderₓ α] [TopologicalSpace β] [Preorderₓ β] [TopologicalSpace γ] [Preorderₓ γ]
  [TopologicalSpace δ] [Preorderₓ δ]

/-- Reinterpret an `esakia_hom` as a `pseudo_epimorphism`. -/
def toPseudoEpimorphism (f : EsakiaHom α β) : PseudoEpimorphism α β :=
  { f with }

instance : EsakiaHomClass (EsakiaHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
  map_rel := fun f => f.monotone'
  map_continuous := fun f => f.continuous_to_fun
  exists_map_eq_of_map_le := fun f => f.exists_map_eq_of_map_le'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (EsakiaHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : EsakiaHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : EsakiaHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of an `esakia_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : EsakiaHom α β) (f' : α → β) (h : f' = f) : EsakiaHom α β :=
  ⟨f.toContinuousOrderHom.copy f' h, by
    simpa only [← h.symm, ← to_fun_eq_coe] using f.exists_map_eq_of_map_le'⟩

variable (α)

/-- `id` as an `esakia_hom`. -/
protected def id : EsakiaHom α α :=
  ⟨ContinuousOrderHom.id α, fun a b h => ⟨b, h, rfl⟩⟩

instance : Inhabited (EsakiaHom α α) :=
  ⟨EsakiaHom.id α⟩

@[simp]
theorem coe_id : ⇑(EsakiaHom.id α) = id :=
  rfl

@[simp]
theorem coe_id_continuous_order_hom : (EsakiaHom.id α : α →Co α) = ContinuousOrderHom.id α :=
  rfl

@[simp]
theorem coe_id_pseudo_epimorphism : (EsakiaHom.id α : PseudoEpimorphism α α) = PseudoEpimorphism.id α :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : EsakiaHom.id α a = a :=
  rfl

/-- Composition of `esakia_hom`s as an `esakia_hom`. -/
def comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : EsakiaHom α γ :=
  ⟨g.toContinuousOrderHom.comp f.toContinuousOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩

@[simp]
theorem coe_comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : (g.comp f : α → γ) = g ∘ f :=
  rfl

@[simp]
theorem comp_apply (g : EsakiaHom β γ) (f : EsakiaHom α β) (a : α) : (g.comp f) a = g (f a) :=
  rfl

@[simp]
theorem coe_comp_continuous_order_hom (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (g.comp f : α →Co γ) = (g : β →Co γ).comp f :=
  rfl

@[simp]
theorem coe_comp_pseudo_epimorphism (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (g.comp f : PseudoEpimorphism α γ) = (g : PseudoEpimorphism β γ).comp f :=
  rfl

@[simp]
theorem comp_assoc (h : EsakiaHom γ δ) (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem comp_id (f : EsakiaHom α β) : f.comp (EsakiaHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : EsakiaHom α β) : (EsakiaHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : EsakiaHom β γ} {f : EsakiaHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : EsakiaHom β γ} {f₁ f₂ : EsakiaHom α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end EsakiaHom

