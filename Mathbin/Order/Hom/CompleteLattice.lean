/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Order.Hom.Lattice

/-!
# Complete lattice homomorphisms

This file defines frame homorphisms and complete lattice homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `Sup_hom`: Maps which preserve `⨆`.
* `Inf_hom`: Maps which preserve `⨅`.
* `frame_hom`: Frame homomorphisms. Maps which preserve `⨆`, `⊓` and `⊤`.
* `complete_lattice_hom`: Complete lattice homomorphisms. Maps which preserve `⨆` and `⨅`.

## Typeclasses

* `Sup_hom_class`
* `Inf_hom_class`
* `frame_hom_class`
* `complete_lattice_hom_class`

## Concrete homs

* `complete_lattice.set_preimage`: `set.preimage` as a complete lattice homomorphism.
-/


open Function OrderDual Set

variable {F α β γ δ : Type _} {ι : Sort _} {κ : ι → Sort _}

/-- The type of `⨆`-preserving functions from `α` to `β`. -/
structure SupHomₓ (α β : Type _) [HasSupₓ α] [HasSupₓ β] where
  toFun : α → β
  map_Sup' (s : Set α) : to_fun (sup s) = sup (to_fun '' s)

/-- The type of `⨅`-preserving functions from `α` to `β`. -/
structure InfHomₓ (α β : Type _) [HasInfₓ α] [HasInfₓ β] where
  toFun : α → β
  map_Inf' (s : Set α) : to_fun (inf s) = inf (to_fun '' s)

/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
structure FrameHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends InfTopHom α β where
  map_Sup' (s : Set α) : to_fun (sup s) = sup (to_fun '' s)

/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure CompleteLatticeHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends InfHomₓ α β where
  map_Sup' (s : Set α) : to_fun (sup s) = sup (to_fun '' s)

/-- `Sup_hom_class F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `Sup_hom`. -/
class SupHomClassₓ (F : Type _) (α β : outParam <| Type _) [HasSupₓ α] [HasSupₓ β] extends FunLike F α fun _ => β where
  map_Sup (f : F) (s : Set α) : f (sup s) = sup (f '' s)

/-- `Inf_hom_class F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `Inf_hom`. -/
class InfHomClassₓ (F : Type _) (α β : outParam <| Type _) [HasInfₓ α] [HasInfₓ β] extends FunLike F α fun _ => β where
  map_Inf (f : F) (s : Set α) : f (inf s) = inf (f '' s)

/-- `frame_hom_class F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `frame_hom`. -/
class FrameHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHomClass F α β where
  map_Sup (f : F) (s : Set α) : f (sup s) = sup (f '' s)

/-- `complete_lattice_hom_class F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `complete_lattice_hom`. -/
class CompleteLatticeHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfHomClassₓ F α β where
  map_Sup (f : F) (s : Set α) : f (sup s) = sup (f '' s)

export SupHomClassₓ (map_Sup)

export InfHomClassₓ (map_Inf)

attribute [simp] map_Sup map_Inf

theorem map_supr [HasSupₓ α] [HasSupₓ β] [SupHomClassₓ F α β] (f : F) (g : ι → α) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [supr, supr, map_Sup, Set.range_comp]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem map_supr₂ [HasSupₓ α] [HasSupₓ β] [SupHomClassₓ F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by
  simp_rw [map_supr]

theorem map_infi [HasInfₓ α] [HasInfₓ β] [InfHomClassₓ F α β] (f : F) (g : ι → α) : f (⨅ i, g i) = ⨅ i, f (g i) := by
  rw [infi, infi, map_Inf, Set.range_comp]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem map_infi₂ [HasInfₓ α] [HasInfₓ β] [InfHomClassₓ F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨅ (i) (j), g i j) = ⨅ (i) (j), f (g i j) := by
  simp_rw [map_infi]

-- See note [lower instance priority]
instance (priority := 100) SupHomClassₓ.toSupBotHomClass [CompleteLattice α] [CompleteLattice β] [SupHomClassₓ F α β] :
    SupBotHomClass F α β where
  map_sup := fun f a b => by
    rw [← Sup_pair, map_Sup, Set.image_pair, Sup_pair]
  map_bot := fun f => by
    rw [← Sup_empty, map_Sup, Set.image_empty, Sup_empty]

-- See note [lower instance priority]
instance (priority := 100) InfHomClassₓ.toInfTopHomClass [CompleteLattice α] [CompleteLattice β] [InfHomClassₓ F α β] :
    InfTopHomClass F α β where
  map_inf := fun f a b => by
    rw [← Inf_pair, map_Inf, Set.image_pair, Inf_pair]
  map_top := fun f => by
    rw [← Inf_empty, map_Inf, Set.image_empty, Inf_empty]

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toSupHomClass [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] :
    SupHomClassₓ F α β :=
  { ‹FrameHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α] [CompleteLattice β]
    [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, SupHomClassₓ.toSupBotHomClass with }

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α] [CompleteLattice β]
    [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, InfHomClassₓ.toInfTopHomClass with }

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α] [CompleteLattice β]
    [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { SupHomClassₓ.toSupBotHomClass, InfHomClassₓ.toInfTopHomClass with }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupHomClassₓ [CompleteLattice α] [CompleteLattice β] [OrderIsoClass F α β] :
    SupHomClassₓ F α β :=
  ⟨fun f s =>
    eq_of_forall_ge_iff fun c => by
      simp only [le_map_inv_iff, ← Sup_le_iff, ← Set.ball_image_iff]⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfHomClassₓ [CompleteLattice α] [CompleteLattice β] [OrderIsoClass F α β] :
    InfHomClassₓ F α β :=
  ⟨fun f s =>
    eq_of_forall_le_iff fun c => by
      simp only [map_inv_le_iff, ← le_Inf_iff, ← Set.ball_image_iff]⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α] [CompleteLattice β]
    [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  { OrderIsoClass.toSupHomClassₓ, OrderIsoClass.toLatticeHomClass with }

instance [HasSupₓ α] [HasSupₓ β] [SupHomClassₓ F α β] : CoeTₓ F (SupHomₓ α β) :=
  ⟨fun f => ⟨f, map_Sup f⟩⟩

instance [HasInfₓ α] [HasInfₓ β] [InfHomClassₓ F α β] : CoeTₓ F (InfHomₓ α β) :=
  ⟨fun f => ⟨f, map_Inf f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTₓ F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_Sup f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] : CoeTₓ F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_Sup f⟩⟩

/-! ### Supremum homomorphisms -/


namespace SupHomₓ

variable [HasSupₓ α]

section HasSupₓ

variable [HasSupₓ β] [HasSupₓ γ] [HasSupₓ δ]

instance : SupHomClassₓ (SupHomₓ α β) α β where
  coe := SupHomₓ.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_Sup := SupHomₓ.map_Sup'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (SupHomₓ α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : SupHomₓ α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : SupHomₓ α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `Sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupHomₓ α β) (f' : α → β) (h : f' = f) : SupHomₓ α β where
  toFun := f'
  map_Sup' := h.symm ▸ f.map_Sup'

variable (α)

/-- `id` as a `Sup_hom`. -/
protected def id : SupHomₓ α α :=
  ⟨id, fun s => by
    rw [id, Set.image_id]⟩

instance : Inhabited (SupHomₓ α α) :=
  ⟨SupHomₓ.id α⟩

@[simp]
theorem coe_id : ⇑(SupHomₓ.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : SupHomₓ.id α a = a :=
  rfl

/-- Composition of `Sup_hom`s as a `Sup_hom`. -/
def comp (f : SupHomₓ β γ) (g : SupHomₓ α β) : SupHomₓ α γ where
  toFun := f ∘ g
  map_Sup' := fun s => by
    rw [comp_apply, map_Sup, map_Sup, Set.image_image]

@[simp]
theorem coe_comp (f : SupHomₓ β γ) (g : SupHomₓ α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : SupHomₓ β γ) (g : SupHomₓ α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : SupHomₓ γ δ) (g : SupHomₓ β γ) (h : SupHomₓ α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : SupHomₓ α β) : f.comp (SupHomₓ.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : SupHomₓ α β) : (SupHomₓ.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : SupHomₓ β γ} {f : SupHomₓ α β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : SupHomₓ β γ} {f₁ f₂ : SupHomₓ α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end HasSupₓ

variable [CompleteLattice β]

instance : PartialOrderₓ (SupHomₓ α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

instance : HasBot (SupHomₓ α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, Sup_empty]
        
      · rw [hs.image_const, Sup_singleton]
        ⟩⟩

instance : OrderBot (SupHomₓ α β) :=
  ⟨⊥, fun f a => bot_le⟩

@[simp]
theorem coe_bot : ⇑(⊥ : SupHomₓ α β) = ⊥ :=
  rfl

@[simp]
theorem bot_apply (a : α) : (⊥ : SupHomₓ α β) a = ⊥ :=
  rfl

end SupHomₓ

/-! ### Infimum homomorphisms -/


namespace InfHomₓ

variable [HasInfₓ α]

section HasInfₓ

variable [HasInfₓ β] [HasInfₓ γ] [HasInfₓ δ]

instance : InfHomClassₓ (InfHomₓ α β) α β where
  coe := InfHomₓ.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_Inf := InfHomₓ.map_Inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (InfHomₓ α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : InfHomₓ α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : InfHomₓ α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `Inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfHomₓ α β) (f' : α → β) (h : f' = f) : InfHomₓ α β where
  toFun := f'
  map_Inf' := h.symm ▸ f.map_Inf'

variable (α)

/-- `id` as an `Inf_hom`. -/
protected def id : InfHomₓ α α :=
  ⟨id, fun s => by
    rw [id, Set.image_id]⟩

instance : Inhabited (InfHomₓ α α) :=
  ⟨InfHomₓ.id α⟩

@[simp]
theorem coe_id : ⇑(InfHomₓ.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : InfHomₓ.id α a = a :=
  rfl

/-- Composition of `Inf_hom`s as a `Inf_hom`. -/
def comp (f : InfHomₓ β γ) (g : InfHomₓ α β) : InfHomₓ α γ where
  toFun := f ∘ g
  map_Inf' := fun s => by
    rw [comp_apply, map_Inf, map_Inf, Set.image_image]

@[simp]
theorem coe_comp (f : InfHomₓ β γ) (g : InfHomₓ α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : InfHomₓ β γ) (g : InfHomₓ α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : InfHomₓ γ δ) (g : InfHomₓ β γ) (h : InfHomₓ α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : InfHomₓ α β) : f.comp (InfHomₓ.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : InfHomₓ α β) : (InfHomₓ.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : InfHomₓ β γ} {f : InfHomₓ α β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : InfHomₓ β γ} {f₁ f₂ : InfHomₓ α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end HasInfₓ

variable [CompleteLattice β]

instance : PartialOrderₓ (InfHomₓ α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

instance : HasTop (InfHomₓ α β) :=
  ⟨⟨fun _ => ⊤, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, Inf_empty]
        
      · rw [hs.image_const, Inf_singleton]
        ⟩⟩

instance : OrderTop (InfHomₓ α β) :=
  ⟨⊤, fun f a => le_top⟩

@[simp]
theorem coe_top : ⇑(⊤ : InfHomₓ α β) = ⊤ :=
  rfl

@[simp]
theorem top_apply (a : α) : (⊤ : InfHomₓ α β) a = ⊤ :=
  rfl

end InfHomₓ

/-! ### Frame homomorphisms -/


namespace FrameHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : FrameHomClass (FrameHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
  map_Sup := fun f => f.map_Sup'
  map_inf := fun f => f.map_inf'
  map_top := fun f => f.map_top'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (FrameHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/-- Reinterpret a `frame_hom` as a `lattice_hom`. -/
def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f

@[simp]
theorem to_fun_eq_coe {f : FrameHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `frame_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : SupHomₓ α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }

variable (α)

/-- `id` as a `frame_hom`. -/
protected def id : FrameHom α α :=
  { SupHomₓ.id α with toInfTopHom := InfTopHom.id α }

instance : Inhabited (FrameHom α α) :=
  ⟨FrameHom.id α⟩

@[simp]
theorem coe_id : ⇑(FrameHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : FrameHom.id α a = a :=
  rfl

/-- Composition of `frame_hom`s as a `frame_hom`. -/
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : SupHomₓ β γ).comp (g : SupHomₓ α β) with toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }

@[simp]
theorem coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : FrameHom α β) : f.comp (FrameHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

instance : PartialOrderₓ (FrameHom α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

end FrameHom

/-! ### Complete lattice homomorphisms -/


namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : CompleteLatticeHomClass (CompleteLatticeHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_Sup := fun f => f.map_Sup'
  map_Inf := fun f => f.map_Inf'

/-- Reinterpret a `complete_lattice_hom` as a `Sup_hom`. -/
def toSupHom (f : CompleteLatticeHom α β) : SupHomₓ α β :=
  f

/-- Reinterpret a `complete_lattice_hom` as a `bounded_lattice_hom`. -/
def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (CompleteLatticeHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : CompleteLatticeHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `complete_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : CompleteLatticeHom α β :=
  { f.toSupHom.copy f' h with toInfHom := f.toInfHom.copy f' h }

variable (α)

/-- `id` as a `complete_lattice_hom`. -/
protected def id : CompleteLatticeHom α α :=
  { SupHomₓ.id α, InfHomₓ.id α with toFun := id }

instance : Inhabited (CompleteLatticeHom α α) :=
  ⟨CompleteLatticeHom.id α⟩

@[simp]
theorem coe_id : ⇑(CompleteLatticeHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : CompleteLatticeHom.id α a = a :=
  rfl

/-- Composition of `complete_lattice_hom`s as a `complete_lattice_hom`. -/
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.toSupHom.comp g.toSupHom with toInfHom := f.toInfHom.comp g.toInfHom }

@[simp]
theorem coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ) (h : CompleteLatticeHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : CompleteLatticeHom α β) : f.comp (CompleteLatticeHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end CompleteLatticeHom

/-! ### Dual homs -/


namespace SupHomₓ

variable [HasSupₓ α] [HasSupₓ β] [HasSupₓ γ]

/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[simps]
protected def dual : SupHomₓ α β ≃ InfHomₓ αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨to_dual ∘ f ∘ of_dual, f.map_Sup'⟩
  invFun := fun f => ⟨of_dual ∘ f ∘ to_dual, f.map_Inf'⟩
  left_inv := fun f => SupHomₓ.ext fun a => rfl
  right_inv := fun f => InfHomₓ.ext fun a => rfl

@[simp]
theorem dual_id : (SupHomₓ.id α).dual = InfHomₓ.id _ :=
  rfl

@[simp]
theorem dual_comp (g : SupHomₓ β γ) (f : SupHomₓ α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : SupHomₓ.dual.symm (InfHomₓ.id _) = SupHomₓ.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : InfHomₓ βᵒᵈ γᵒᵈ) (f : InfHomₓ αᵒᵈ βᵒᵈ) :
    SupHomₓ.dual.symm (g.comp f) = (SupHomₓ.dual.symm g).comp (SupHomₓ.dual.symm f) :=
  rfl

end SupHomₓ

namespace InfHomₓ

variable [HasInfₓ α] [HasInfₓ β] [HasInfₓ γ]

/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/
@[simps]
protected def dual : InfHomₓ α β ≃ SupHomₓ αᵒᵈ βᵒᵈ where
  toFun := fun f => { toFun := to_dual ∘ f ∘ of_dual, map_Sup' := fun _ => congr_arg toDual (map_Inf f _) }
  invFun := fun f => { toFun := of_dual ∘ f ∘ to_dual, map_Inf' := fun _ => congr_arg ofDual (map_Sup f _) }
  left_inv := fun f => InfHomₓ.ext fun a => rfl
  right_inv := fun f => SupHomₓ.ext fun a => rfl

@[simp]
theorem dual_id : (InfHomₓ.id α).dual = SupHomₓ.id _ :=
  rfl

@[simp]
theorem dual_comp (g : InfHomₓ β γ) (f : InfHomₓ α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : InfHomₓ.dual.symm (SupHomₓ.id _) = InfHomₓ.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : SupHomₓ βᵒᵈ γᵒᵈ) (f : SupHomₓ αᵒᵈ βᵒᵈ) :
    InfHomₓ.dual.symm (g.comp f) = (InfHomₓ.dual.symm g).comp (InfHomₓ.dual.symm f) :=
  rfl

end InfHomₓ

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps]
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ where
  toFun := fun f => ⟨f.toSupHom.dual, f.map_Inf'⟩
  invFun := fun f => ⟨f.toSupHom.dual, f.map_Inf'⟩
  left_inv := fun f => ext fun a => rfl
  right_inv := fun f => ext fun a => rfl

@[simp]
theorem dual_id : (CompleteLatticeHom.id α).dual = CompleteLatticeHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : CompleteLatticeHom.dual.symm (CompleteLatticeHom.id _) = CompleteLatticeHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒᵈ βᵒᵈ) :
    CompleteLatticeHom.dual.symm (g.comp f) = (CompleteLatticeHom.dual.symm g).comp (CompleteLatticeHom.dual.symm f) :=
  rfl

end CompleteLatticeHom

/-! ### Concrete homs -/


namespace CompleteLatticeHom

/-- `set.preimage` as a complete lattice homomorphism. -/
def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α) where
  toFun := Preimage f
  map_Sup' := fun s =>
    preimage_sUnion.trans <| by
      simp only [← Set.Sup_eq_sUnion, ← Set.sUnion_image]
  map_Inf' := fun s =>
    preimage_sInter.trans <| by
      simp only [← Set.Inf_eq_sInter, ← Set.sInter_image]

@[simp]
theorem coe_set_preimage (f : α → β) : ⇑(setPreimage f) = Preimage f :=
  rfl

@[simp]
theorem set_preimage_apply (f : α → β) (s : Set β) : setPreimage f s = s.Preimage f :=
  rfl

@[simp]
theorem set_preimage_id : setPreimage (id : α → α) = CompleteLatticeHom.id _ :=
  rfl

-- This lemma can't be `simp` because `g ∘ f` matches anything (`id ∘ f = f` synctatically)
theorem set_preimage_comp (g : β → γ) (f : α → β) : setPreimage (g ∘ f) = (setPreimage f).comp (setPreimage g) :=
  rfl

end CompleteLatticeHom

