/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Continuous order homomorphisms

This file defines continuous order homomorphisms, that is maps which are both continuous and
monotone. They are also called Priestley homomorphisms because they are the morphisms of the
category of Priestley spaces.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `continuous_order_hom`: Continuous monotone functions, aka Priestley homomorphisms.

## Typeclasses

* `continuous_order_hom_class`
-/


open Function

variable {F α β γ δ : Type _}

/-- The type of continuous monotone maps from `α` to `β`, aka Priestley homomorphisms. -/
structure ContinuousOrderHom (α β : Type _) [Preorderₓ α] [Preorderₓ β] [TopologicalSpace α]
  [TopologicalSpace β] extends OrderHom α β where
  continuous_to_fun : Continuous to_fun

-- mathport name: «expr →Co »
infixr:25 " →Co " => ContinuousOrderHom

/-- `continuous_order_hom_class F α β` states that `F` is a type of continuous monotone maps.

You should extend this class when you extend `continuous_order_hom`. -/
class ContinuousOrderHomClass (F : Type _) (α β : outParam <| Type _) [Preorderₓ α] [Preorderₓ β] [TopologicalSpace α]
  [TopologicalSpace β] extends RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop) where
  map_continuous (f : F) : Continuous f

-- See note [lower instance priority]
instance (priority := 100) ContinuousOrderHomClass.toContinuousMapClass [Preorderₓ α] [Preorderₓ β] [TopologicalSpace α]
    [TopologicalSpace β] [ContinuousOrderHomClass F α β] : ContinuousMapClass F α β :=
  { ‹ContinuousOrderHomClass F α β› with }

instance [Preorderₓ α] [Preorderₓ β] [TopologicalSpace α] [TopologicalSpace β] [ContinuousOrderHomClass F α β] :
    CoeTₓ F (α →Co β) :=
  ⟨fun f => { toFun := f, monotone' := OrderHomClass.mono f, continuous_to_fun := map_continuous f }⟩

/-! ### Top homomorphisms -/


namespace ContinuousOrderHom

variable [TopologicalSpace α] [Preorderₓ α] [TopologicalSpace β]

section Preorderₓ

variable [Preorderₓ β] [TopologicalSpace γ] [Preorderₓ γ] [TopologicalSpace δ] [Preorderₓ δ]

/-- Reinterpret a `continuous_order_hom` as a `continuous_map`. -/
def toContinuousMap (f : α →Co β) : C(α, β) :=
  { f with }

instance : ContinuousOrderHomClass (α →Co β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_rel := fun f => f.monotone'
  map_continuous := fun f => f.continuous_to_fun

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →Co β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : α →Co β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : α →Co β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `continuous_order_hom` with a new `continuous_map` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →Co β) (f' : α → β) (h : f' = f) : α →Co β :=
  ⟨f.toOrderHom.copy f' <| h, h.symm.subst f.continuous_to_fun⟩

variable (α)

/-- `id` as a `continuous_order_hom`. -/
protected def id : α →Co α :=
  ⟨OrderHom.id, continuous_id⟩

instance : Inhabited (α →Co α) :=
  ⟨ContinuousOrderHom.id _⟩

@[simp]
theorem coe_id : ⇑(ContinuousOrderHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : ContinuousOrderHom.id α a = a :=
  rfl

/-- Composition of `continuous_order_hom`s as a `continuous_order_hom`. -/
def comp (f : β →Co γ) (g : α →Co β) : ContinuousOrderHom α γ :=
  ⟨f.toOrderHom.comp g.toOrderHom, f.continuous_to_fun.comp g.continuous_to_fun⟩

@[simp]
theorem coe_comp (f : β →Co γ) (g : α →Co β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : β →Co γ) (g : α →Co β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : γ →Co δ) (g : β →Co γ) (h : α →Co β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : α →Co β) : f.comp (ContinuousOrderHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : α →Co β) : (ContinuousOrderHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : β →Co γ} {f : α →Co β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : β →Co γ} {f₁ f₂ : α →Co β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

instance : Preorderₓ (α →Co β) :=
  Preorderₓ.lift (coeFn : (α →Co β) → α → β)

end Preorderₓ

instance [PartialOrderₓ β] : PartialOrderₓ (α →Co β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

end ContinuousOrderHom

