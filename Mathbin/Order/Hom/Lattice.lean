/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.Lattice
import Mathbin.Order.Hom.Bounded
import Mathbin.Order.SymmDiff

/-!
# Lattice homomorphisms

This file defines (bounded) lattice homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `sup_hom`: Maps which preserve `⊔`.
* `inf_hom`: Maps which preserve `⊓`.
* `sup_bot_hom`: Finitary supremum homomorphisms. Maps which preserve `⊔` and `⊥`.
* `inf_top_hom`: Finitary infimum homomorphisms. Maps which preserve `⊓` and `⊤`.
* `lattice_hom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.
* `bounded_lattice_hom`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `sup_hom_class`
* `inf_hom_class`
* `sup_bot_hom_class`
* `inf_top_hom_class`
* `lattice_hom_class`
* `bounded_lattice_hom_class`

## TODO

Do we need more intersections between `bot_hom`, `top_hom` and lattice homomorphisms?
-/


open Function OrderDual

variable {F ι α β γ δ : Type _}

/-- The type of `⊔`-preserving functions from `α` to `β`. -/
structure SupHom (α β : Type _) [HasSup α] [HasSup β] where
  toFun : α → β
  map_sup' (a b : α) : to_fun (a⊔b) = to_fun a⊔to_fun b

/-- The type of `⊓`-preserving functions from `α` to `β`. -/
structure InfHom (α β : Type _) [HasInf α] [HasInf β] where
  toFun : α → β
  map_inf' (a b : α) : to_fun (a⊓b) = to_fun a⊓to_fun b

/-- The type of finitary supremum-preserving homomorphisms from `α` to `β`. -/
structure SupBotHom (α β : Type _) [HasSup α] [HasSup β] [HasBot α] [HasBot β] extends SupHom α β where
  map_bot' : to_fun ⊥ = ⊥

/-- The type of finitary infimum-preserving homomorphisms from `α` to `β`. -/
structure InfTopHom (α β : Type _) [HasInf α] [HasInf β] [HasTop α] [HasTop β] extends InfHom α β where
  map_top' : to_fun ⊤ = ⊤

/-- The type of lattice homomorphisms from `α` to `β`. -/
structure LatticeHom (α β : Type _) [Lattice α] [Lattice β] extends SupHom α β where
  map_inf' (a b : α) : to_fun (a⊓b) = to_fun a⊓to_fun b

/-- The type of bounded lattice homomorphisms from `α` to `β`. -/
structure BoundedLatticeHom (α β : Type _) [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] extends
  LatticeHom α β where
  map_top' : to_fun ⊤ = ⊤
  map_bot' : to_fun ⊥ = ⊥

/-- `sup_hom_class F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `sup_hom`. -/
class SupHomClass (F : Type _) (α β : outParam <| Type _) [HasSup α] [HasSup β] extends FunLike F α fun _ => β where
  map_sup (f : F) (a b : α) : f (a⊔b) = f a⊔f b

/-- `inf_hom_class F α β` states that `F` is a type of `⊓`-preserving morphisms.

You should extend this class when you extend `inf_hom`. -/
class InfHomClass (F : Type _) (α β : outParam <| Type _) [HasInf α] [HasInf β] extends FunLike F α fun _ => β where
  map_inf (f : F) (a b : α) : f (a⊓b) = f a⊓f b

/-- `sup_bot_hom_class F α β` states that `F` is a type of finitary supremum-preserving morphisms.

You should extend this class when you extend `sup_bot_hom`. -/
class SupBotHomClass (F : Type _) (α β : outParam <| Type _) [HasSup α] [HasSup β] [HasBot α] [HasBot β] extends
  SupHomClass F α β where
  map_bot (f : F) : f ⊥ = ⊥

/-- `inf_top_hom_class F α β` states that `F` is a type of finitary infimum-preserving morphisms.

You should extend this class when you extend `sup_bot_hom`. -/
class InfTopHomClass (F : Type _) (α β : outParam <| Type _) [HasInf α] [HasInf β] [HasTop α] [HasTop β] extends
  InfHomClass F α β where
  map_top (f : F) : f ⊤ = ⊤

/-- `lattice_hom_class F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `lattice_hom`. -/
class LatticeHomClass (F : Type _) (α β : outParam <| Type _) [Lattice α] [Lattice β] extends SupHomClass F α β where
  map_inf (f : F) (a b : α) : f (a⊓b) = f a⊓f b

/-- `bounded_lattice_hom_class F α β` states that `F` is a type of bounded lattice morphisms.

You should extend this class when you extend `bounded_lattice_hom`. -/
class BoundedLatticeHomClass (F : Type _) (α β : outParam <| Type _) [Lattice α] [Lattice β] [BoundedOrder α]
  [BoundedOrder β] extends LatticeHomClass F α β where
  map_top (f : F) : f ⊤ = ⊤
  map_bot (f : F) : f ⊥ = ⊥

export SupHomClass (map_sup)

export InfHomClass (map_inf)

attribute [simp] map_top map_bot map_sup map_inf

-- See note [lower instance priority]
instance (priority := 100) SupHomClass.toOrderHomClass [SemilatticeSup α] [SemilatticeSup β] [SupHomClass F α β] :
    OrderHomClass F α β :=
  ⟨fun f a b h => by
    rw [← sup_eq_right, ← map_sup, sup_eq_right.2 h]⟩

-- See note [lower instance priority]
instance (priority := 100) InfHomClass.toOrderHomClass [SemilatticeInf α] [SemilatticeInf β] [InfHomClass F α β] :
    OrderHomClass F α β :=
  ⟨fun f a b h => by
    rw [← inf_eq_left, ← map_inf, inf_eq_left.2 h]⟩

-- See note [lower instance priority]
instance (priority := 100) SupBotHomClass.toBotHomClass [HasSup α] [HasSup β] [HasBot α] [HasBot β]
    [SupBotHomClass F α β] : BotHomClass F α β :=
  { ‹SupBotHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) InfTopHomClass.toTopHomClass [HasInf α] [HasInf β] [HasTop α] [HasTop β]
    [InfTopHomClass F α β] : TopHomClass F α β :=
  { ‹InfTopHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) LatticeHomClass.toInfHomClass [Lattice α] [Lattice β] [LatticeHomClass F α β] :
    InfHomClass F α β :=
  { ‹LatticeHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toSupBotHomClass [Lattice α] [Lattice β] [BoundedOrder α]
    [BoundedOrder β] [BoundedLatticeHomClass F α β] : SupBotHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toInfTopHomClass [Lattice α] [Lattice β] [BoundedOrder α]
    [BoundedOrder β] [BoundedLatticeHomClass F α β] : InfTopHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toBoundedOrderHomClass [Lattice α] [Lattice β] [BoundedOrder α]
    [BoundedOrder β] [BoundedLatticeHomClass F α β] : BoundedOrderHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupHomClass [SemilatticeSup α] [SemilatticeSup β] [OrderIsoClass F α β] :
    SupHomClass F α β :=
  ⟨fun f a b =>
    eq_of_forall_ge_iff fun c => by
      simp only [le_map_inv_iff, ← sup_le_iff]⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfHomClass [SemilatticeInf α] [SemilatticeInf β] [OrderIsoClass F α β] :
    InfHomClass F α β :=
  ⟨fun f a b =>
    eq_of_forall_le_iff fun c => by
      simp only [map_inv_le_iff, ← le_inf_iff]⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupBotHomClass [SemilatticeSup α] [OrderBot α] [SemilatticeSup β]
    [OrderBot β] [OrderIsoClass F α β] : SupBotHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toBotHomClass with }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfTopHomClass [SemilatticeInf α] [OrderTop α] [SemilatticeInf β]
    [OrderTop β] [OrderIsoClass F α β] : InfTopHomClass F α β :=
  { OrderIsoClass.toInfHomClass, OrderIsoClass.toTopHomClass with }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toLatticeHomClass [Lattice α] [Lattice β] [OrderIsoClass F α β] :
    LatticeHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toInfHomClass with }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBoundedLatticeHomClass [Lattice α] [Lattice β] [BoundedOrder α]
    [BoundedOrder β] [OrderIsoClass F α β] : BoundedLatticeHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass, OrderIsoClass.toBoundedOrderHomClass with }

@[simp]
theorem map_finset_sup [SemilatticeSup α] [OrderBot α] [SemilatticeSup β] [OrderBot β] [SupBotHomClass F α β] (f : F)
    (s : Finset ι) (g : ι → α) : f (s.sup g) = s.sup (f ∘ g) :=
  (Finset.cons_induction_on s (map_bot f)) fun i s _ h => by
    rw [Finset.sup_cons, Finset.sup_cons, map_sup, h]

@[simp]
theorem map_finset_inf [SemilatticeInf α] [OrderTop α] [SemilatticeInf β] [OrderTop β] [InfTopHomClass F α β] (f : F)
    (s : Finset ι) (g : ι → α) : f (s.inf g) = s.inf (f ∘ g) :=
  (Finset.cons_induction_on s (map_top f)) fun i s _ h => by
    rw [Finset.inf_cons, Finset.inf_cons, map_inf, h]

section BoundedLattice

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [BoundedLatticeHomClass F α β] (f : F) {a b : α}

include β

theorem Disjoint.map (h : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff, ← map_inf, h.eq_bot, map_bot]

theorem Codisjoint.map (h : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [codisjoint_iff, ← map_sup, h.eq_top, map_top]

theorem IsCompl.map (h : IsCompl a b) : IsCompl (f a) (f b) :=
  ⟨h.1.map _, h.2.map _⟩

end BoundedLattice

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [BoundedLatticeHomClass F α β] (f : F)

include β

theorem map_compl (a : α) : f (aᶜ) = f aᶜ :=
  (is_compl_compl.map _).compl_eq.symm

theorem map_sdiff (a b : α) : f (a \ b) = f a \ f b := by
  rw [sdiff_eq, sdiff_eq, map_inf, map_compl]

theorem map_symm_diff (a b : α) : f (a ∆ b) = f a ∆ f b := by
  rw [symmDiff, symmDiff, map_sup, map_sdiff, map_sdiff]

end BooleanAlgebra

instance [HasSup α] [HasSup β] [SupHomClass F α β] : CoeTₓ F (SupHom α β) :=
  ⟨fun f => ⟨f, map_sup f⟩⟩

instance [HasInf α] [HasInf β] [InfHomClass F α β] : CoeTₓ F (InfHom α β) :=
  ⟨fun f => ⟨f, map_inf f⟩⟩

instance [HasSup α] [HasSup β] [HasBot α] [HasBot β] [SupBotHomClass F α β] : CoeTₓ F (SupBotHom α β) :=
  ⟨fun f => ⟨f, map_bot f⟩⟩

instance [HasInf α] [HasInf β] [HasTop α] [HasTop β] [InfTopHomClass F α β] : CoeTₓ F (InfTopHom α β) :=
  ⟨fun f => ⟨f, map_top f⟩⟩

instance [Lattice α] [Lattice β] [LatticeHomClass F α β] : CoeTₓ F (LatticeHom α β) :=
  ⟨fun f => { toFun := f, map_sup' := map_sup f, map_inf' := map_inf f }⟩

instance [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    CoeTₓ F (BoundedLatticeHom α β) :=
  ⟨fun f => { (f : LatticeHom α β) with toFun := f, map_top' := map_top f, map_bot' := map_bot f }⟩

/-! ### Supremum homomorphisms -/


namespace SupHom

variable [HasSup α]

section HasSup

variable [HasSup β] [HasSup γ] [HasSup δ]

instance : SupHomClass (SupHom α β) α β where
  coe := SupHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_sup := SupHom.map_sup'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (SupHom α β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem to_fun_eq_coe {f : SupHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : SupHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupHom α β) (f' : α → β) (h : f' = f) : SupHom α β where
  toFun := f'
  map_sup' := h.symm ▸ f.map_sup'

variable (α)

/-- `id` as a `sup_hom`. -/
protected def id : SupHom α α :=
  ⟨id, fun a b => rfl⟩

instance : Inhabited (SupHom α α) :=
  ⟨SupHom.id α⟩

@[simp]
theorem coe_id : ⇑(SupHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : SupHom.id α a = a :=
  rfl

/-- Composition of `sup_hom`s as a `sup_hom`. -/
def comp (f : SupHom β γ) (g : SupHom α β) : SupHom α γ where
  toFun := f ∘ g
  map_sup' := fun a b => by
    rw [comp_apply, map_sup, map_sup]

@[simp]
theorem coe_comp (f : SupHom β γ) (g : SupHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : SupHom β γ) (g : SupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : SupHom γ δ) (g : SupHom β γ) (h : SupHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : SupHom α β) : f.comp (SupHom.id α) = f :=
  SupHom.ext fun a => rfl

@[simp]
theorem id_comp (f : SupHom α β) : (SupHom.id β).comp f = f :=
  SupHom.ext fun a => rfl

theorem cancel_right {g₁ g₂ : SupHom β γ} {f : SupHom α β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => SupHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : SupHom β γ} {f₁ f₂ : SupHom α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    SupHom.ext fun a =>
      hg <| by
        rw [← SupHom.comp_apply, h, SupHom.comp_apply],
    congr_arg _⟩

end HasSup

variable (α) [SemilatticeSup β]

/-- The constant function as a `sup_hom`. -/
def const (b : β) : SupHom α β :=
  ⟨fun _ => b, fun _ _ => sup_idem.symm⟩

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

variable {α}

instance : HasSup (SupHom α β) :=
  ⟨fun f g =>
    ⟨f⊔g, fun a b => by
      rw [Pi.sup_apply, map_sup, map_sup]
      exact sup_sup_sup_comm _ _ _ _⟩⟩

instance : SemilatticeSup (SupHom α β) :=
  (FunLike.coe_injective.SemilatticeSup _) fun f g => rfl

instance [HasBot β] : HasBot (SupHom α β) :=
  ⟨SupHom.const α ⊥⟩

instance [HasTop β] : HasTop (SupHom α β) :=
  ⟨SupHom.const α ⊤⟩

instance [OrderBot β] : OrderBot (SupHom α β) :=
  OrderBot.lift (coeFn : _ → α → β) (fun _ _ => id) rfl

instance [OrderTop β] : OrderTop (SupHom α β) :=
  OrderTop.lift (coeFn : _ → α → β) (fun _ _ => id) rfl

instance [BoundedOrder β] : BoundedOrder (SupHom α β) :=
  BoundedOrder.lift (coeFn : _ → α → β) (fun _ _ => id) rfl rfl

@[simp]
theorem coe_sup (f g : SupHom α β) : ⇑(f⊔g) = f⊔g :=
  rfl

@[simp]
theorem coe_bot [HasBot β] : ⇑(⊥ : SupHom α β) = ⊥ :=
  rfl

@[simp]
theorem coe_top [HasTop β] : ⇑(⊤ : SupHom α β) = ⊤ :=
  rfl

@[simp]
theorem sup_apply (f g : SupHom α β) (a : α) : (f⊔g) a = f a⊔g a :=
  rfl

@[simp]
theorem bot_apply [HasBot β] (a : α) : (⊥ : SupHom α β) a = ⊥ :=
  rfl

@[simp]
theorem top_apply [HasTop β] (a : α) : (⊤ : SupHom α β) a = ⊤ :=
  rfl

end SupHom

/-! ### Infimum homomorphisms -/


namespace InfHom

variable [HasInf α]

section HasInf

variable [HasInf β] [HasInf γ] [HasInf δ]

instance : InfHomClass (InfHom α β) α β where
  coe := InfHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_inf := InfHom.map_inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (InfHom α β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem to_fun_eq_coe {f : InfHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : InfHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of an `inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfHom α β) (f' : α → β) (h : f' = f) : InfHom α β where
  toFun := f'
  map_inf' := h.symm ▸ f.map_inf'

variable (α)

/-- `id` as an `inf_hom`. -/
protected def id : InfHom α α :=
  ⟨id, fun a b => rfl⟩

instance : Inhabited (InfHom α α) :=
  ⟨InfHom.id α⟩

@[simp]
theorem coe_id : ⇑(InfHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : InfHom.id α a = a :=
  rfl

/-- Composition of `inf_hom`s as an `inf_hom`. -/
def comp (f : InfHom β γ) (g : InfHom α β) : InfHom α γ where
  toFun := f ∘ g
  map_inf' := fun a b => by
    rw [comp_apply, map_inf, map_inf]

@[simp]
theorem coe_comp (f : InfHom β γ) (g : InfHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : InfHom β γ) (g : InfHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : InfHom γ δ) (g : InfHom β γ) (h : InfHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : InfHom α β) : f.comp (InfHom.id α) = f :=
  InfHom.ext fun a => rfl

@[simp]
theorem id_comp (f : InfHom α β) : (InfHom.id β).comp f = f :=
  InfHom.ext fun a => rfl

theorem cancel_right {g₁ g₂ : InfHom β γ} {f : InfHom α β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => InfHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : InfHom β γ} {f₁ f₂ : InfHom α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    InfHom.ext fun a =>
      hg <| by
        rw [← InfHom.comp_apply, h, InfHom.comp_apply],
    congr_arg _⟩

end HasInf

variable (α) [SemilatticeInf β]

/-- The constant function as an `inf_hom`. -/
def const (b : β) : InfHom α β :=
  ⟨fun _ => b, fun _ _ => inf_idem.symm⟩

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

variable {α}

instance : HasInf (InfHom α β) :=
  ⟨fun f g =>
    ⟨f⊓g, fun a b => by
      rw [Pi.inf_apply, map_inf, map_inf]
      exact inf_inf_inf_comm _ _ _ _⟩⟩

instance : SemilatticeInf (InfHom α β) :=
  (FunLike.coe_injective.SemilatticeInf _) fun f g => rfl

instance [HasBot β] : HasBot (InfHom α β) :=
  ⟨InfHom.const α ⊥⟩

instance [HasTop β] : HasTop (InfHom α β) :=
  ⟨InfHom.const α ⊤⟩

instance [OrderBot β] : OrderBot (InfHom α β) :=
  OrderBot.lift (coeFn : _ → α → β) (fun _ _ => id) rfl

instance [OrderTop β] : OrderTop (InfHom α β) :=
  OrderTop.lift (coeFn : _ → α → β) (fun _ _ => id) rfl

instance [BoundedOrder β] : BoundedOrder (InfHom α β) :=
  BoundedOrder.lift (coeFn : _ → α → β) (fun _ _ => id) rfl rfl

@[simp]
theorem coe_inf (f g : InfHom α β) : ⇑(f⊓g) = f⊓g :=
  rfl

@[simp]
theorem coe_bot [HasBot β] : ⇑(⊥ : InfHom α β) = ⊥ :=
  rfl

@[simp]
theorem coe_top [HasTop β] : ⇑(⊤ : InfHom α β) = ⊤ :=
  rfl

@[simp]
theorem inf_apply (f g : InfHom α β) (a : α) : (f⊓g) a = f a⊓g a :=
  rfl

@[simp]
theorem bot_apply [HasBot β] (a : α) : (⊥ : InfHom α β) a = ⊥ :=
  rfl

@[simp]
theorem top_apply [HasTop β] (a : α) : (⊤ : InfHom α β) a = ⊤ :=
  rfl

end InfHom

/-! ### Finitary supremum homomorphisms -/


namespace SupBotHom

variable [HasSup α] [HasBot α]

section HasSup

variable [HasSup β] [HasBot β] [HasSup γ] [HasBot γ] [HasSup δ] [HasBot δ]

/-- Reinterpret a `sup_bot_hom` as a `bot_hom`. -/
def toBotHom (f : SupBotHom α β) : BotHom α β :=
  { f with }

instance : SupBotHomClass (SupBotHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_sup := fun f => f.map_sup'
  map_bot := fun f => f.map_bot'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (SupBotHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : SupBotHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : SupBotHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `sup_bot_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupBotHom α β) (f' : α → β) (h : f' = f) : SupBotHom α β :=
  { f.toBotHom.copy f' h with toSupHom := f.toSupHom.copy f' h }

variable (α)

/-- `id` as a `sup_bot_hom`. -/
@[simps]
protected def id : SupBotHom α α :=
  ⟨SupHom.id α, rfl⟩

instance : Inhabited (SupBotHom α α) :=
  ⟨SupBotHom.id α⟩

@[simp]
theorem coe_id : ⇑(SupBotHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : SupBotHom.id α a = a :=
  rfl

/-- Composition of `sup_bot_hom`s as a `sup_bot_hom`. -/
def comp (f : SupBotHom β γ) (g : SupBotHom α β) : SupBotHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toBotHom.comp g.toBotHom with }

@[simp]
theorem coe_comp (f : SupBotHom β γ) (g : SupBotHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : SupBotHom β γ) (g : SupBotHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : SupBotHom γ δ) (g : SupBotHom β γ) (h : SupBotHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : SupBotHom α β) : f.comp (SupBotHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : SupBotHom α β) : (SupBotHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : SupBotHom β γ} {f : SupBotHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : SupBotHom β γ} {f₁ f₂ : SupBotHom α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    SupBotHom.ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end HasSup

variable [SemilatticeSup β] [OrderBot β]

instance : HasSup (SupBotHom α β) :=
  ⟨fun f g => { f.toBotHom⊔g.toBotHom with toSupHom := f.toSupHom⊔g.toSupHom }⟩

instance : SemilatticeSup (SupBotHom α β) :=
  (FunLike.coe_injective.SemilatticeSup _) fun f g => rfl

instance : OrderBot (SupBotHom α β) where
  bot := ⟨⊥, rfl⟩
  bot_le := fun f => bot_le

@[simp]
theorem coe_sup (f g : SupBotHom α β) : ⇑(f⊔g) = f⊔g :=
  rfl

@[simp]
theorem coe_bot : ⇑(⊥ : SupBotHom α β) = ⊥ :=
  rfl

@[simp]
theorem sup_apply (f g : SupBotHom α β) (a : α) : (f⊔g) a = f a⊔g a :=
  rfl

@[simp]
theorem bot_apply (a : α) : (⊥ : SupBotHom α β) a = ⊥ :=
  rfl

end SupBotHom

/-! ### Finitary infimum homomorphisms -/


namespace InfTopHom

variable [HasInf α] [HasTop α]

section HasInf

variable [HasInf β] [HasTop β] [HasInf γ] [HasTop γ] [HasInf δ] [HasTop δ]

/-- Reinterpret an `inf_top_hom` as a `top_hom`. -/
def toTopHom (f : InfTopHom α β) : TopHom α β :=
  { f with }

instance : InfTopHomClass (InfTopHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_inf := fun f => f.map_inf'
  map_top := fun f => f.map_top'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (InfTopHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : InfTopHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : InfTopHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of an `inf_top_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfTopHom α β) (f' : α → β) (h : f' = f) : InfTopHom α β :=
  { f.toTopHom.copy f' h with toInfHom := f.toInfHom.copy f' h }

variable (α)

/-- `id` as an `inf_top_hom`. -/
@[simps]
protected def id : InfTopHom α α :=
  ⟨InfHom.id α, rfl⟩

instance : Inhabited (InfTopHom α α) :=
  ⟨InfTopHom.id α⟩

@[simp]
theorem coe_id : ⇑(InfTopHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : InfTopHom.id α a = a :=
  rfl

/-- Composition of `inf_top_hom`s as an `inf_top_hom`. -/
def comp (f : InfTopHom β γ) (g : InfTopHom α β) : InfTopHom α γ :=
  { f.toInfHom.comp g.toInfHom, f.toTopHom.comp g.toTopHom with }

@[simp]
theorem coe_comp (f : InfTopHom β γ) (g : InfTopHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : InfTopHom β γ) (g : InfTopHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : InfTopHom γ δ) (g : InfTopHom β γ) (h : InfTopHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : InfTopHom α β) : f.comp (InfTopHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : InfTopHom α β) : (InfTopHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : InfTopHom β γ} {f : InfTopHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : InfTopHom β γ} {f₁ f₂ : InfTopHom α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    InfTopHom.ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end HasInf

variable [SemilatticeInf β] [OrderTop β]

instance : HasInf (InfTopHom α β) :=
  ⟨fun f g => { f.toTopHom⊓g.toTopHom with toInfHom := f.toInfHom⊓g.toInfHom }⟩

instance : SemilatticeInf (InfTopHom α β) :=
  (FunLike.coe_injective.SemilatticeInf _) fun f g => rfl

instance : OrderTop (InfTopHom α β) where
  top := ⟨⊤, rfl⟩
  le_top := fun f => le_top

@[simp]
theorem coe_inf (f g : InfTopHom α β) : ⇑(f⊓g) = f⊓g :=
  rfl

@[simp]
theorem coe_top : ⇑(⊤ : InfTopHom α β) = ⊤ :=
  rfl

@[simp]
theorem inf_apply (f g : InfTopHom α β) (a : α) : (f⊓g) a = f a⊓g a :=
  rfl

@[simp]
theorem top_apply (a : α) : (⊤ : InfTopHom α β) a = ⊤ :=
  rfl

end InfTopHom

/-! ### Lattice homomorphisms -/


namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ]

/-- Reinterpret a `lattice_hom` as an `inf_hom`. -/
def toInfHom (f : LatticeHom α β) : InfHom α β :=
  { f with }

instance : LatticeHomClass (LatticeHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_sup := fun f => f.map_sup'
  map_inf := fun f => f.map_inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (LatticeHom α β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem to_fun_eq_coe {f : LatticeHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : LatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `lattice_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : LatticeHom α β :=
  { f.toSupHom.copy f' h, f.toInfHom.copy f' h with }

variable (α)

/-- `id` as a `lattice_hom`. -/
protected def id : LatticeHom α α where
  toFun := id
  map_sup' := fun _ _ => rfl
  map_inf' := fun _ _ => rfl

instance : Inhabited (LatticeHom α α) :=
  ⟨LatticeHom.id α⟩

@[simp]
theorem coe_id : ⇑(LatticeHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : LatticeHom.id α a = a :=
  rfl

/-- Composition of `lattice_hom`s as a `lattice_hom`. -/
def comp (f : LatticeHom β γ) (g : LatticeHom α β) : LatticeHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toInfHom.comp g.toInfHom with }

@[simp]
theorem coe_comp (f : LatticeHom β γ) (g : LatticeHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : LatticeHom β γ) (g : LatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem coe_comp_sup_hom (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl

@[simp]
theorem coe_comp_inf_hom (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g : InfHom α γ) = (f : InfHom β γ).comp g :=
  rfl

@[simp]
theorem comp_assoc (f : LatticeHom γ δ) (g : LatticeHom β γ) (h : LatticeHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : LatticeHom α β) : f.comp (LatticeHom.id α) = f :=
  LatticeHom.ext fun a => rfl

@[simp]
theorem id_comp (f : LatticeHom α β) : (LatticeHom.id β).comp f = f :=
  LatticeHom.ext fun a => rfl

theorem cancel_right {g₁ g₂ : LatticeHom β γ} {f : LatticeHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => LatticeHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : LatticeHom β γ} {f₁ f₂ : LatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    LatticeHom.ext fun a =>
      hg <| by
        rw [← LatticeHom.comp_apply, h, LatticeHom.comp_apply],
    congr_arg _⟩

end LatticeHom

namespace OrderHomClass

variable (α β) [LinearOrderₓ α] [Lattice β] [OrderHomClass F α β]

/-- An order homomorphism from a linear order is a lattice homomorphism. -/
@[reducible]
def toLatticeHomClass : LatticeHomClass F α β :=
  { ‹OrderHomClass F α β› with
    map_sup := fun f a b => by
      obtain h | h := le_totalₓ a b
      · rw [sup_eq_right.2 h, sup_eq_right.2 (OrderHomClass.mono f h : f a ≤ f b)]
        
      · rw [sup_eq_left.2 h, sup_eq_left.2 (OrderHomClass.mono f h : f b ≤ f a)]
        ,
    map_inf := fun f a b => by
      obtain h | h := le_totalₓ a b
      · rw [inf_eq_left.2 h, inf_eq_left.2 (OrderHomClass.mono f h : f a ≤ f b)]
        
      · rw [inf_eq_right.2 h, inf_eq_right.2 (OrderHomClass.mono f h : f b ≤ f a)]
         }

/-- Reinterpret an order homomorphism to a linear order as a `lattice_hom`. -/
def toLatticeHom (f : F) : LatticeHom α β := by
  have : LatticeHomClass F α β := OrderHomClass.toLatticeHomClass α β
  exact f

@[simp]
theorem coe_to_lattice_hom (f : F) : ⇑(toLatticeHom α β f) = f :=
  rfl

@[simp]
theorem to_lattice_hom_apply (f : F) (a : α) : toLatticeHom α β f a = f a :=
  rfl

end OrderHomClass

/-! ### Bounded lattice homomorphisms -/


namespace BoundedLatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ] [BoundedOrder α] [BoundedOrder β] [BoundedOrder γ]
  [BoundedOrder δ]

/-- Reinterpret a `bounded_lattice_hom` as a `sup_bot_hom`. -/
def toSupBotHom (f : BoundedLatticeHom α β) : SupBotHom α β :=
  { f with }

/-- Reinterpret a `bounded_lattice_hom` as an `inf_top_hom`. -/
def toInfTopHom (f : BoundedLatticeHom α β) : InfTopHom α β :=
  { f with }

/-- Reinterpret a `bounded_lattice_hom` as a `bounded_order_hom`. -/
def toBoundedOrderHom (f : BoundedLatticeHom α β) : BoundedOrderHom α β :=
  { f, (f.toLatticeHom : α →o β) with }

instance : BoundedLatticeHomClass (BoundedLatticeHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f <;> obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g <;> congr
  map_sup := fun f => f.map_sup'
  map_inf := fun f => f.map_inf'
  map_top := fun f => f.map_top'
  map_bot := fun f => f.map_bot'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (BoundedLatticeHom α β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem to_fun_eq_coe {f : BoundedLatticeHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : BoundedLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `bounded_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : BoundedLatticeHom α β :=
  { f.toLatticeHom.copy f' h, f.toBoundedOrderHom.copy f' h with }

variable (α)

/-- `id` as a `bounded_lattice_hom`. -/
protected def id : BoundedLatticeHom α α :=
  { LatticeHom.id α, BoundedOrderHom.id α with }

instance : Inhabited (BoundedLatticeHom α α) :=
  ⟨BoundedLatticeHom.id α⟩

@[simp]
theorem coe_id : ⇑(BoundedLatticeHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : BoundedLatticeHom.id α a = a :=
  rfl

/-- Composition of `bounded_lattice_hom`s as a `bounded_lattice_hom`. -/
def comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : BoundedLatticeHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom, f.toBoundedOrderHom.comp g.toBoundedOrderHom with }

@[simp]
theorem coe_comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem coe_comp_lattice_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : LatticeHom α γ) = (f : LatticeHom β γ).comp g :=
  rfl

@[simp]
theorem coe_comp_sup_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl

@[simp]
theorem coe_comp_inf_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : InfHom α γ) = (f : InfHom β γ).comp g :=
  rfl

@[simp]
theorem comp_assoc (f : BoundedLatticeHom γ δ) (g : BoundedLatticeHom β γ) (h : BoundedLatticeHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : BoundedLatticeHom α β) : f.comp (BoundedLatticeHom.id α) = f :=
  BoundedLatticeHom.ext fun a => rfl

@[simp]
theorem id_comp (f : BoundedLatticeHom α β) : (BoundedLatticeHom.id β).comp f = f :=
  BoundedLatticeHom.ext fun a => rfl

theorem cancel_right {g₁ g₂ : BoundedLatticeHom β γ} {f : BoundedLatticeHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BoundedLatticeHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : BoundedLatticeHom β γ} {f₁ f₂ : BoundedLatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end BoundedLatticeHom

/-! ### Dual homs -/


namespace SupHom

variable [HasSup α] [HasSup β] [HasSup γ]

/-- Reinterpret a supremum homomorphism as an infimum homomorphism between the dual lattices. -/
@[simps]
protected def dual : SupHom α β ≃ InfHom αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨f, f.map_sup'⟩
  invFun := fun f => ⟨f, f.map_inf'⟩
  left_inv := fun f => SupHom.ext fun _ => rfl
  right_inv := fun f => InfHom.ext fun _ => rfl

@[simp]
theorem dual_id : (SupHom.id α).dual = InfHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : SupHom β γ) (f : SupHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : SupHom.dual.symm (InfHom.id _) = SupHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ) :
    SupHom.dual.symm (g.comp f) = (SupHom.dual.symm g).comp (SupHom.dual.symm f) :=
  rfl

end SupHom

namespace InfHom

variable [HasInf α] [HasInf β] [HasInf γ]

/-- Reinterpret an infimum homomorphism as a supremum homomorphism between the dual lattices. -/
@[simps]
protected def dual : InfHom α β ≃ SupHom αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨f, f.map_inf'⟩
  invFun := fun f => ⟨f, f.map_sup'⟩
  left_inv := fun f => InfHom.ext fun _ => rfl
  right_inv := fun f => SupHom.ext fun _ => rfl

@[simp]
theorem dual_id : (InfHom.id α).dual = SupHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : InfHom β γ) (f : InfHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : InfHom.dual.symm (SupHom.id _) = InfHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : SupHom βᵒᵈ γᵒᵈ) (f : SupHom αᵒᵈ βᵒᵈ) :
    InfHom.dual.symm (g.comp f) = (InfHom.dual.symm g).comp (InfHom.dual.symm f) :=
  rfl

end InfHom

namespace SupBotHom

variable [HasSup α] [HasBot α] [HasSup β] [HasBot β] [HasSup γ] [HasBot γ]

/-- Reinterpret a finitary supremum homomorphism as a finitary infimum homomorphism between the dual
lattices. -/
def dual : SupBotHom α β ≃ InfTopHom αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨f.toSupHom.dual, f.map_bot'⟩
  invFun := fun f => ⟨SupHom.dual.symm f.toInfHom, f.map_top'⟩
  left_inv := fun f => SupBotHom.ext fun _ => rfl
  right_inv := fun f => InfTopHom.ext fun _ => rfl

@[simp]
theorem dual_id : (SupBotHom.id α).dual = InfTopHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : SupBotHom β γ) (f : SupBotHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : SupBotHom.dual.symm (InfTopHom.id _) = SupBotHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : InfTopHom βᵒᵈ γᵒᵈ) (f : InfTopHom αᵒᵈ βᵒᵈ) :
    SupBotHom.dual.symm (g.comp f) = (SupBotHom.dual.symm g).comp (SupBotHom.dual.symm f) :=
  rfl

end SupBotHom

namespace InfTopHom

variable [HasInf α] [HasTop α] [HasInf β] [HasTop β] [HasInf γ] [HasTop γ]

/-- Reinterpret a finitary infimum homomorphism as a finitary supremum homomorphism between the dual
lattices. -/
@[simps]
protected def dual : InfTopHom α β ≃ SupBotHom αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨f.toInfHom.dual, f.map_top'⟩
  invFun := fun f => ⟨InfHom.dual.symm f.toSupHom, f.map_bot'⟩
  left_inv := fun f => InfTopHom.ext fun _ => rfl
  right_inv := fun f => SupBotHom.ext fun _ => rfl

@[simp]
theorem dual_id : (InfTopHom.id α).dual = SupBotHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : InfTopHom β γ) (f : InfTopHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : InfTopHom.dual.symm (SupBotHom.id _) = InfTopHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : SupBotHom βᵒᵈ γᵒᵈ) (f : SupBotHom αᵒᵈ βᵒᵈ) :
    InfTopHom.dual.symm (g.comp f) = (InfTopHom.dual.symm g).comp (InfTopHom.dual.symm f) :=
  rfl

end InfTopHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Reinterpret a lattice homomorphism as a lattice homomorphism between the dual lattices. -/
@[simps]
protected def dual : LatticeHom α β ≃ LatticeHom αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨f.toInfHom.dual, f.map_sup'⟩
  invFun := fun f => ⟨f.toInfHom.dual, f.map_sup'⟩
  left_inv := fun f => ext fun a => rfl
  right_inv := fun f => ext fun a => rfl

@[simp]
theorem dual_id : (LatticeHom.id α).dual = LatticeHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : LatticeHom β γ) (f : LatticeHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : LatticeHom.dual.symm (LatticeHom.id _) = LatticeHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : LatticeHom βᵒᵈ γᵒᵈ) (f : LatticeHom αᵒᵈ βᵒᵈ) :
    LatticeHom.dual.symm (g.comp f) = (LatticeHom.dual.symm g).comp (LatticeHom.dual.symm f) :=
  rfl

end LatticeHom

namespace BoundedLatticeHom

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- Reinterpret a bounded lattice homomorphism as a bounded lattice homomorphism between the dual
bounded lattices. -/
@[simps]
protected def dual : BoundedLatticeHom α β ≃ BoundedLatticeHom αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨f.toLatticeHom.dual, f.map_bot', f.map_top'⟩
  invFun := fun f => ⟨LatticeHom.dual.symm f.toLatticeHom, f.map_bot', f.map_top'⟩
  left_inv := fun f => ext fun a => rfl
  right_inv := fun f => ext fun a => rfl

@[simp]
theorem dual_id : (BoundedLatticeHom.id α).dual = BoundedLatticeHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : BoundedLatticeHom.dual.symm (BoundedLatticeHom.id _) = BoundedLatticeHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : BoundedLatticeHom βᵒᵈ γᵒᵈ) (f : BoundedLatticeHom αᵒᵈ βᵒᵈ) :
    BoundedLatticeHom.dual.symm (g.comp f) = (BoundedLatticeHom.dual.symm g).comp (BoundedLatticeHom.dual.symm f) :=
  rfl

end BoundedLatticeHom

