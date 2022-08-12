/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Order.BoundedOrder

/-!
# Bounded order homomorphisms

This file defines (bounded) order homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `top_hom`: Maps which preserve `⊤`.
* `bot_hom`: Maps which preserve `⊥`.
* `bounded_order_hom`: Bounded order homomorphisms. Monotone maps which preserve `⊤` and `⊥`.

## Typeclasses

* `top_hom_class`
* `bot_hom_class`
* `bounded_order_hom_class`
-/


open Function OrderDual

variable {F α β γ δ : Type _}

/-- The type of `⊤`-preserving functions from `α` to `β`. -/
structure TopHom (α β : Type _) [HasTop α] [HasTop β] where
  toFun : α → β
  map_top' : to_fun ⊤ = ⊤

/-- The type of `⊥`-preserving functions from `α` to `β`. -/
structure BotHom (α β : Type _) [HasBot α] [HasBot β] where
  toFun : α → β
  map_bot' : to_fun ⊥ = ⊥

/-- The type of bounded order homomorphisms from `α` to `β`. -/
structure BoundedOrderHom (α β : Type _) [Preorderₓ α] [Preorderₓ β] [BoundedOrder α] [BoundedOrder β] extends
  OrderHom α β where
  map_top' : to_fun ⊤ = ⊤
  map_bot' : to_fun ⊥ = ⊥

/-- `top_hom_class F α β` states that `F` is a type of `⊤`-preserving morphisms.

You should extend this class when you extend `top_hom`. -/
class TopHomClass (F : Type _) (α β : outParam <| Type _) [HasTop α] [HasTop β] extends FunLike F α fun _ => β where
  map_top (f : F) : f ⊤ = ⊤

/-- `bot_hom_class F α β` states that `F` is a type of `⊥`-preserving morphisms.

You should extend this class when you extend `bot_hom`. -/
class BotHomClass (F : Type _) (α β : outParam <| Type _) [HasBot α] [HasBot β] extends FunLike F α fun _ => β where
  map_bot (f : F) : f ⊥ = ⊥

/-- `bounded_order_hom_class F α β` states that `F` is a type of bounded order morphisms.

You should extend this class when you extend `bounded_order_hom`. -/
class BoundedOrderHomClass (F : Type _) (α β : outParam <| Type _) [LE α] [LE β] [BoundedOrder α]
  [BoundedOrder β] extends RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop) where
  map_top (f : F) : f ⊤ = ⊤
  map_bot (f : F) : f ⊥ = ⊥

export TopHomClass (map_top)

export BotHomClass (map_bot)

attribute [simp] map_top map_bot

-- See note [lower instance priority]
instance (priority := 100) BoundedOrderHomClass.toTopHomClass [LE α] [LE β] [BoundedOrder α] [BoundedOrder β]
    [BoundedOrderHomClass F α β] : TopHomClass F α β :=
  { ‹BoundedOrderHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) BoundedOrderHomClass.toBotHomClass [LE α] [LE β] [BoundedOrder α] [BoundedOrder β]
    [BoundedOrderHomClass F α β] : BotHomClass F α β :=
  { ‹BoundedOrderHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toTopHomClass [LE α] [OrderTop α] [PartialOrderₓ β] [OrderTop β]
    [OrderIsoClass F α β] : TopHomClass F α β :=
  ⟨fun f => top_le_iff.1 <| (map_inv_le_iff f).1 le_top⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBotHomClass [LE α] [OrderBot α] [PartialOrderₓ β] [OrderBot β]
    [OrderIsoClass F α β] : BotHomClass F α β :=
  ⟨fun f => le_bot_iff.1 <| (le_map_inv_iff f).1 bot_le⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBoundedOrderHomClass [LE α] [BoundedOrder α] [PartialOrderₓ β]
    [BoundedOrder β] [OrderIsoClass F α β] : BoundedOrderHomClass F α β :=
  { OrderIsoClass.toTopHomClass, OrderIsoClass.toBotHomClass with }

@[simp]
theorem map_eq_top_iff [LE α] [OrderTop α] [PartialOrderₓ β] [OrderTop β] [OrderIsoClass F α β] (f : F) {a : α} :
    f a = ⊤ ↔ a = ⊤ := by
  rw [← map_top f, (EquivLike.injective f).eq_iff]

@[simp]
theorem map_eq_bot_iff [LE α] [OrderBot α] [PartialOrderₓ β] [OrderBot β] [OrderIsoClass F α β] (f : F) {a : α} :
    f a = ⊥ ↔ a = ⊥ := by
  rw [← map_bot f, (EquivLike.injective f).eq_iff]

instance [HasTop α] [HasTop β] [TopHomClass F α β] : CoeTₓ F (TopHom α β) :=
  ⟨fun f => ⟨f, map_top f⟩⟩

instance [HasBot α] [HasBot β] [BotHomClass F α β] : CoeTₓ F (BotHom α β) :=
  ⟨fun f => ⟨f, map_bot f⟩⟩

instance [Preorderₓ α] [Preorderₓ β] [BoundedOrder α] [BoundedOrder β] [BoundedOrderHomClass F α β] :
    CoeTₓ F (BoundedOrderHom α β) :=
  ⟨fun f => { (f : α →o β) with toFun := f, map_top' := map_top f, map_bot' := map_bot f }⟩

/-! ### Top homomorphisms -/


namespace TopHom

variable [HasTop α]

section HasTop

variable [HasTop β] [HasTop γ] [HasTop δ]

instance : TopHomClass (TopHom α β) α β where
  coe := TopHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_top := TopHom.map_top'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (TopHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : TopHom α β} : f.toFun = (f : α → β) :=
  rfl

-- this must come after the coe_to_fun definition
initialize_simps_projections TopHom (toFun → apply)

@[ext]
theorem ext {f g : TopHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `top_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : TopHom α β) (f' : α → β) (h : f' = f) : TopHom α β where
  toFun := f'
  map_top' := h.symm ▸ f.map_top'

instance : Inhabited (TopHom α β) :=
  ⟨⟨fun _ => ⊤, rfl⟩⟩

variable (α)

/-- `id` as a `top_hom`. -/
protected def id : TopHom α α :=
  ⟨id, rfl⟩

@[simp]
theorem coe_id : ⇑(TopHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : TopHom.id α a = a :=
  rfl

/-- Composition of `top_hom`s as a `top_hom`. -/
def comp (f : TopHom β γ) (g : TopHom α β) : TopHom α γ where
  toFun := f ∘ g
  map_top' := by
    rw [comp_apply, map_top, map_top]

@[simp]
theorem coe_comp (f : TopHom β γ) (g : TopHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : TopHom β γ) (g : TopHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : TopHom γ δ) (g : TopHom β γ) (h : TopHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : TopHom α β) : f.comp (TopHom.id α) = f :=
  TopHom.ext fun a => rfl

@[simp]
theorem id_comp (f : TopHom α β) : (TopHom.id β).comp f = f :=
  TopHom.ext fun a => rfl

theorem cancel_right {g₁ g₂ : TopHom β γ} {f : TopHom α β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => TopHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : TopHom β γ} {f₁ f₂ : TopHom α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    TopHom.ext fun a =>
      hg <| by
        rw [← TopHom.comp_apply, h, TopHom.comp_apply],
    congr_arg _⟩

end HasTop

instance [Preorderₓ β] [HasTop β] : Preorderₓ (TopHom α β) :=
  Preorderₓ.lift (coeFn : TopHom α β → α → β)

instance [PartialOrderₓ β] [HasTop β] : PartialOrderₓ (TopHom α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

section OrderTop

variable [Preorderₓ β] [OrderTop β]

instance : OrderTop (TopHom α β) :=
  ⟨⟨⊤, rfl⟩, fun _ => le_top⟩

@[simp]
theorem coe_top : ⇑(⊤ : TopHom α β) = ⊤ :=
  rfl

@[simp]
theorem top_apply (a : α) : (⊤ : TopHom α β) a = ⊤ :=
  rfl

end OrderTop

section SemilatticeInf

variable [SemilatticeInf β] [OrderTop β] (f g : TopHom α β)

instance : HasInf (TopHom α β) :=
  ⟨fun f g =>
    ⟨f⊓g, by
      rw [Pi.inf_apply, map_top, map_top, inf_top_eq]⟩⟩

instance : SemilatticeInf (TopHom α β) :=
  (FunLike.coe_injective.SemilatticeInf _) fun _ _ => rfl

@[simp]
theorem coe_inf : ⇑(f⊓g) = f⊓g :=
  rfl

@[simp]
theorem inf_apply (a : α) : (f⊓g) a = f a⊓g a :=
  rfl

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup β] [OrderTop β] (f g : TopHom α β)

instance : HasSup (TopHom α β) :=
  ⟨fun f g =>
    ⟨f⊔g, by
      rw [Pi.sup_apply, map_top, map_top, sup_top_eq]⟩⟩

instance : SemilatticeSup (TopHom α β) :=
  (FunLike.coe_injective.SemilatticeSup _) fun _ _ => rfl

@[simp]
theorem coe_sup : ⇑(f⊔g) = f⊔g :=
  rfl

@[simp]
theorem sup_apply (a : α) : (f⊔g) a = f a⊔g a :=
  rfl

end SemilatticeSup

instance [Lattice β] [OrderTop β] : Lattice (TopHom α β) :=
  FunLike.coe_injective.Lattice _ (fun _ _ => rfl) fun _ _ => rfl

instance [DistribLattice β] [OrderTop β] : DistribLattice (TopHom α β) :=
  FunLike.coe_injective.DistribLattice _ (fun _ _ => rfl) fun _ _ => rfl

end TopHom

/-! ### Bot homomorphisms -/


namespace BotHom

variable [HasBot α]

section HasBot

variable [HasBot β] [HasBot γ] [HasBot δ]

instance : BotHomClass (BotHom α β) α β where
  coe := BotHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_bot := BotHom.map_bot'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (BotHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : BotHom α β} : f.toFun = (f : α → β) :=
  rfl

-- this must come after the coe_to_fun definition
initialize_simps_projections BotHom (toFun → apply)

@[ext]
theorem ext {f g : BotHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `bot_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : BotHom α β) (f' : α → β) (h : f' = f) : BotHom α β where
  toFun := f'
  map_bot' := h.symm ▸ f.map_bot'

instance : Inhabited (BotHom α β) :=
  ⟨⟨fun _ => ⊥, rfl⟩⟩

variable (α)

/-- `id` as a `bot_hom`. -/
protected def id : BotHom α α :=
  ⟨id, rfl⟩

@[simp]
theorem coe_id : ⇑(BotHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : BotHom.id α a = a :=
  rfl

/-- Composition of `bot_hom`s as a `bot_hom`. -/
def comp (f : BotHom β γ) (g : BotHom α β) : BotHom α γ where
  toFun := f ∘ g
  map_bot' := by
    rw [comp_apply, map_bot, map_bot]

@[simp]
theorem coe_comp (f : BotHom β γ) (g : BotHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : BotHom β γ) (g : BotHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : BotHom γ δ) (g : BotHom β γ) (h : BotHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : BotHom α β) : f.comp (BotHom.id α) = f :=
  BotHom.ext fun a => rfl

@[simp]
theorem id_comp (f : BotHom α β) : (BotHom.id β).comp f = f :=
  BotHom.ext fun a => rfl

theorem cancel_right {g₁ g₂ : BotHom β γ} {f : BotHom α β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BotHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : BotHom β γ} {f₁ f₂ : BotHom α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    BotHom.ext fun a =>
      hg <| by
        rw [← BotHom.comp_apply, h, BotHom.comp_apply],
    congr_arg _⟩

end HasBot

instance [Preorderₓ β] [HasBot β] : Preorderₓ (BotHom α β) :=
  Preorderₓ.lift (coeFn : BotHom α β → α → β)

instance [PartialOrderₓ β] [HasBot β] : PartialOrderₓ (BotHom α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

section OrderBot

variable [Preorderₓ β] [OrderBot β]

instance : OrderBot (BotHom α β) :=
  ⟨⟨⊥, rfl⟩, fun _ => bot_le⟩

@[simp]
theorem coe_bot : ⇑(⊥ : BotHom α β) = ⊥ :=
  rfl

@[simp]
theorem bot_apply (a : α) : (⊥ : BotHom α β) a = ⊥ :=
  rfl

end OrderBot

section SemilatticeInf

variable [SemilatticeInf β] [OrderBot β] (f g : BotHom α β)

instance : HasInf (BotHom α β) :=
  ⟨fun f g =>
    ⟨f⊓g, by
      rw [Pi.inf_apply, map_bot, map_bot, inf_bot_eq]⟩⟩

instance : SemilatticeInf (BotHom α β) :=
  (FunLike.coe_injective.SemilatticeInf _) fun _ _ => rfl

@[simp]
theorem coe_inf : ⇑(f⊓g) = f⊓g :=
  rfl

@[simp]
theorem inf_apply (a : α) : (f⊓g) a = f a⊓g a :=
  rfl

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup β] [OrderBot β] (f g : BotHom α β)

instance : HasSup (BotHom α β) :=
  ⟨fun f g =>
    ⟨f⊔g, by
      rw [Pi.sup_apply, map_bot, map_bot, sup_bot_eq]⟩⟩

instance : SemilatticeSup (BotHom α β) :=
  (FunLike.coe_injective.SemilatticeSup _) fun _ _ => rfl

@[simp]
theorem coe_sup : ⇑(f⊔g) = f⊔g :=
  rfl

@[simp]
theorem sup_apply (a : α) : (f⊔g) a = f a⊔g a :=
  rfl

end SemilatticeSup

instance [Lattice β] [OrderBot β] : Lattice (BotHom α β) :=
  FunLike.coe_injective.Lattice _ (fun _ _ => rfl) fun _ _ => rfl

instance [DistribLattice β] [OrderBot β] : DistribLattice (BotHom α β) :=
  FunLike.coe_injective.DistribLattice _ (fun _ _ => rfl) fun _ _ => rfl

end BotHom

/-! ### Bounded order homomorphisms -/


namespace BoundedOrderHom

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] [Preorderₓ δ] [BoundedOrder α] [BoundedOrder β] [BoundedOrder γ]
  [BoundedOrder δ]

/-- Reinterpret a `bounded_order_hom` as a `top_hom`. -/
def toTopHom (f : BoundedOrderHom α β) : TopHom α β :=
  { f with }

/-- Reinterpret a `bounded_order_hom` as a `bot_hom`. -/
def toBotHom (f : BoundedOrderHom α β) : BotHom α β :=
  { f with }

instance : BoundedOrderHomClass (BoundedOrderHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_rel := fun f => f.monotone'
  map_top := fun f => f.map_top'
  map_bot := fun f => f.map_bot'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (BoundedOrderHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : BoundedOrderHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : BoundedOrderHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `bounded_order_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : BoundedOrderHom α β) (f' : α → β) (h : f' = f) : BoundedOrderHom α β :=
  { f.toOrderHom.copy f' h, f.toTopHom.copy f' h, f.toBotHom.copy f' h with }

variable (α)

/-- `id` as a `bounded_order_hom`. -/
protected def id : BoundedOrderHom α α :=
  { OrderHom.id, TopHom.id α, BotHom.id α with }

instance : Inhabited (BoundedOrderHom α α) :=
  ⟨BoundedOrderHom.id α⟩

@[simp]
theorem coe_id : ⇑(BoundedOrderHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : BoundedOrderHom.id α a = a :=
  rfl

/-- Composition of `bounded_order_hom`s as a `bounded_order_hom`. -/
def comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : BoundedOrderHom α γ :=
  { f.toOrderHom.comp g.toOrderHom, f.toTopHom.comp g.toTopHom, f.toBotHom.comp g.toBotHom with }

@[simp]
theorem coe_comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem coe_comp_order_hom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) :
    (f.comp g : OrderHom α γ) = (f : OrderHom β γ).comp g :=
  rfl

@[simp]
theorem coe_comp_top_hom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) :
    (f.comp g : TopHom α γ) = (f : TopHom β γ).comp g :=
  rfl

@[simp]
theorem coe_comp_bot_hom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) :
    (f.comp g : BotHom α γ) = (f : BotHom β γ).comp g :=
  rfl

@[simp]
theorem comp_assoc (f : BoundedOrderHom γ δ) (g : BoundedOrderHom β γ) (h : BoundedOrderHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : BoundedOrderHom α β) : f.comp (BoundedOrderHom.id α) = f :=
  BoundedOrderHom.ext fun a => rfl

@[simp]
theorem id_comp (f : BoundedOrderHom α β) : (BoundedOrderHom.id β).comp f = f :=
  BoundedOrderHom.ext fun a => rfl

theorem cancel_right {g₁ g₂ : BoundedOrderHom β γ} {f : BoundedOrderHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BoundedOrderHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : BoundedOrderHom β γ} {f₁ f₂ : BoundedOrderHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    BoundedOrderHom.ext fun a =>
      hg <| by
        rw [← BoundedOrderHom.comp_apply, h, BoundedOrderHom.comp_apply],
    congr_arg _⟩

end BoundedOrderHom

/-! ### Dual homs -/


namespace TopHom

variable [LE α] [OrderTop α] [LE β] [OrderTop β] [LE γ] [OrderTop γ]

/-- Reinterpret a top homomorphism as a bot homomorphism between the dual lattices. -/
@[simps]
protected def dual : TopHom α β ≃ BotHom αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨f, f.map_top'⟩
  invFun := fun f => ⟨f, f.map_bot'⟩
  left_inv := fun f => TopHom.ext fun _ => rfl
  right_inv := fun f => BotHom.ext fun _ => rfl

@[simp]
theorem dual_id : (TopHom.id α).dual = BotHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : TopHom β γ) (f : TopHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : TopHom.dual.symm (BotHom.id _) = TopHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : BotHom βᵒᵈ γᵒᵈ) (f : BotHom αᵒᵈ βᵒᵈ) :
    TopHom.dual.symm (g.comp f) = (TopHom.dual.symm g).comp (TopHom.dual.symm f) :=
  rfl

end TopHom

namespace BotHom

variable [LE α] [OrderBot α] [LE β] [OrderBot β] [LE γ] [OrderBot γ]

/-- Reinterpret a bot homomorphism as a top homomorphism between the dual lattices. -/
@[simps]
protected def dual : BotHom α β ≃ TopHom αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨f, f.map_bot'⟩
  invFun := fun f => ⟨f, f.map_top'⟩
  left_inv := fun f => BotHom.ext fun _ => rfl
  right_inv := fun f => TopHom.ext fun _ => rfl

@[simp]
theorem dual_id : (BotHom.id α).dual = TopHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : BotHom β γ) (f : BotHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : BotHom.dual.symm (TopHom.id _) = BotHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : TopHom βᵒᵈ γᵒᵈ) (f : TopHom αᵒᵈ βᵒᵈ) :
    BotHom.dual.symm (g.comp f) = (BotHom.dual.symm g).comp (BotHom.dual.symm f) :=
  rfl

end BotHom

namespace BoundedOrderHom

variable [Preorderₓ α] [BoundedOrder α] [Preorderₓ β] [BoundedOrder β] [Preorderₓ γ] [BoundedOrder γ]

/-- Reinterpret a bounded order homomorphism as a bounded order homomorphism between the dual
orders. -/
@[simps]
protected def dual : BoundedOrderHom α β ≃ BoundedOrderHom αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨f.toOrderHom.dual, f.map_bot', f.map_top'⟩
  invFun := fun f => ⟨OrderHom.dual.symm f.toOrderHom, f.map_bot', f.map_top'⟩
  left_inv := fun f => ext fun a => rfl
  right_inv := fun f => ext fun a => rfl

@[simp]
theorem dual_id : (BoundedOrderHom.id α).dual = BoundedOrderHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : BoundedOrderHom β γ) (f : BoundedOrderHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : BoundedOrderHom.dual.symm (BoundedOrderHom.id _) = BoundedOrderHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : BoundedOrderHom βᵒᵈ γᵒᵈ) (f : BoundedOrderHom αᵒᵈ βᵒᵈ) :
    BoundedOrderHom.dual.symm (g.comp f) = (BoundedOrderHom.dual.symm g).comp (BoundedOrderHom.dual.symm f) :=
  rfl

end BoundedOrderHom

