/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Algebra.Order.Hom.Monoid
import Mathbin.Algebra.Order.Ring
import Mathbin.Algebra.Ring.Equiv

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered (semi)rings that respect the ordering.

## Main definitions

* `order_ring_hom` : Monotone semiring homomorphisms.
* `order_ring_iso` : Monotone semiring isomorphisms.

## Notation

* `→+*o`: Ordered ring homomorphisms.
* `≃+*o`: Ordered ring isomorphisms.

## Tags

ordered ring homomorphism, order homomorphism
-/


open Function

variable {F α β γ δ : Type _}

/-- `order_ring_hom α β` is the type of monotone semiring homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : order_ring_hom α β)`,
you should parametrize over `(F : Type*) [order_ring_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_ring_hom_class`. -/
structure OrderRingHom (α β : Type _) [NonAssocSemiringₓ α] [Preorderₓ α] [NonAssocSemiringₓ β] [Preorderₓ β] extends
  α →+* β where
  monotone' : Monotone to_fun

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc OrderRingHom.toRingHom

-- mathport name: «expr →+*o »
infixl:25 " →+*o " => OrderRingHom

/-- `order_ring_hom α β` is the type of order-preserving semiring isomorphisms between `α` and `β`.

When possible, instead of parametrizing results over `(f : order_ring_iso α β)`,
you should parametrize over `(F : Type*) [order_ring_iso_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_ring_iso_class`. -/
structure OrderRingIso (α β : Type _) [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] extends α ≃+* β where
  map_le_map_iff' {a b : α} : to_fun a ≤ to_fun b ↔ a ≤ b

-- mathport name: «expr ≃+*o »
infixl:25 " ≃+*o " => OrderRingIso

/-- `order_ring_hom_class F α β` states that `F` is a type of ordered semiring homomorphisms.
You should extend this typeclass when you extend `order_ring_hom`. -/
class OrderRingHomClass (F : Type _) (α β : outParam <| Type _) [NonAssocSemiringₓ α] [Preorderₓ α]
  [NonAssocSemiringₓ β] [Preorderₓ β] extends RingHomClass F α β where
  Monotone (f : F) : Monotone f

/-- `order_ring_iso_class F α β` states that `F` is a type of ordered semiring isomorphisms.
You should extend this class when you extend `order_ring_iso`. -/
class OrderRingIsoClass (F : Type _) (α β : outParam (Type _)) [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] extends
  RingEquivClass F α β where
  map_le_map_iff (f : F) {a b : α} : f a ≤ f b ↔ a ≤ b

-- See note [lower priority instance]
instance (priority := 100) OrderRingHomClass.toOrderAddMonoidHomClass [NonAssocSemiringₓ α] [Preorderₓ α]
    [NonAssocSemiringₓ β] [Preorderₓ β] [OrderRingHomClass F α β] : OrderAddMonoidHomClass F α β :=
  { ‹OrderRingHomClass F α β› with }

-- See note [lower priority instance]
instance (priority := 100) OrderRingHomClass.toOrderMonoidWithZeroHomClass [NonAssocSemiringₓ α] [Preorderₓ α]
    [NonAssocSemiringₓ β] [Preorderₓ β] [OrderRingHomClass F α β] : OrderMonoidWithZeroHomClass F α β :=
  { ‹OrderRingHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) OrderRingIsoClass.toOrderIsoClass [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β]
    [OrderRingIsoClass F α β] : OrderIsoClass F α β :=
  { ‹OrderRingIsoClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) OrderRingIsoClass.toOrderRingHomClass [NonAssocSemiringₓ α] [Preorderₓ α]
    [NonAssocSemiringₓ β] [Preorderₓ β] [OrderRingIsoClass F α β] : OrderRingHomClass F α β :=
  { ‹OrderRingIsoClass F α β› with Monotone := fun f => OrderHomClass.mono f }

instance [NonAssocSemiringₓ α] [Preorderₓ α] [NonAssocSemiringₓ β] [Preorderₓ β] [OrderRingHomClass F α β] :
    CoeTₓ F (α →+*o β) :=
  ⟨fun f => ⟨f, OrderHomClass.mono f⟩⟩

instance [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [OrderRingIsoClass F α β] : CoeTₓ F (α ≃+*o β) :=
  ⟨fun f => ⟨f, fun a b => map_le_map_iff f⟩⟩

/-! ### Ordered ring homomorphisms -/


namespace OrderRingHom

variable [NonAssocSemiringₓ α] [Preorderₓ α]

section Preorderₓ

variable [NonAssocSemiringₓ β] [Preorderₓ β] [NonAssocSemiringₓ γ] [Preorderₓ γ] [NonAssocSemiringₓ δ] [Preorderₓ δ]

/-- Reinterpret an ordered ring homomorphism as an ordered additive monoid homomorphism. -/
def toOrderAddMonoidHom (f : α →+*o β) : α →+o β :=
  { f with }

/-- Reinterpret an ordered ring homomorphism as an order homomorphism. -/
def toOrderMonoidWithZeroHom (f : α →+*o β) : α →*₀o β :=
  { f with }

instance : OrderRingHomClass (α →+*o β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_mul := fun f => f.map_mul'
  map_one := fun f => f.map_one'
  map_add := fun f => f.map_add'
  map_zero := fun f => f.map_zero'
  Monotone := fun f => f.monotone'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →+*o β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

theorem to_fun_eq_coe (f : α →+*o β) : f.toFun = ⇑f :=
  rfl

@[ext]
theorem ext {f g : α →+*o β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

@[simp]
theorem to_ring_hom_eq_coe (f : α →+*o β) : f.toRingHom = f :=
  RingHom.ext fun _ => rfl

@[simp]
theorem to_order_add_monoid_hom_eq_coe (f : α →+*o β) : f.toOrderAddMonoidHom = f :=
  rfl

@[simp]
theorem to_order_monoid_with_zero_hom_eq_coe (f : α →+*o β) : f.toOrderMonoidWithZeroHom = f :=
  rfl

@[simp]
theorem coe_coe_ring_hom (f : α →+*o β) : ⇑(f : α →+* β) = f :=
  rfl

@[simp]
theorem coe_coe_order_add_monoid_hom (f : α →+*o β) : ⇑(f : α →+o β) = f :=
  rfl

@[simp]
theorem coe_coe_order_monoid_with_zero_hom (f : α →+*o β) : ⇑(f : α →*₀o β) = f :=
  rfl

@[norm_cast]
theorem coe_ring_hom_apply (f : α →+*o β) (a : α) : (f : α →+* β) a = f a :=
  rfl

@[norm_cast]
theorem coe_order_add_monoid_hom_apply (f : α →+*o β) (a : α) : (f : α →+o β) a = f a :=
  rfl

@[norm_cast]
theorem coe_order_monoid_with_zero_hom_apply (f : α →+*o β) (a : α) : (f : α →*₀o β) a = f a :=
  rfl

/-- Copy of a `order_ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →+*o β) (f' : α → β) (h : f' = f) : α →+*o β :=
  { f.toRingHom.copy f' h, f.toOrderAddMonoidHom.copy f' h with }

variable (α)

/-- The identity as an ordered ring homomorphism. -/
protected def id : α →+*o α :=
  { RingHom.id _, OrderHom.id with }

instance : Inhabited (α →+*o α) :=
  ⟨OrderRingHom.id α⟩

@[simp]
theorem coe_id : ⇑(OrderRingHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : OrderRingHom.id α a = a :=
  rfl

@[simp]
theorem coe_ring_hom_id : (OrderRingHom.id α : α →+* α) = RingHom.id α :=
  rfl

@[simp]
theorem coe_order_add_monoid_hom_id : (OrderRingHom.id α : α →+o α) = OrderAddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_order_monoid_with_zero_hom_id : (OrderRingHom.id α : α →*₀o α) = OrderMonoidWithZeroHom.id α :=
  rfl

/-- Composition of two `order_ring_hom`s as an `order_ring_hom`. -/
protected def comp (f : β →+*o γ) (g : α →+*o β) : α →+*o γ :=
  { f.toRingHom.comp g.toRingHom, f.toOrderAddMonoidHom.comp g.toOrderAddMonoidHom with }

@[simp]
theorem coe_comp (f : β →+*o γ) (g : α →+*o β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : β →+*o γ) (g : α →+*o β) (a : α) : f.comp g a = f (g a) :=
  rfl

theorem comp_assoc (f : γ →+*o δ) (g : β →+*o γ) (h : α →+*o β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : α →+*o β) : f.comp (OrderRingHom.id α) = f :=
  ext fun x => rfl

@[simp]
theorem id_comp (f : α →+*o β) : (OrderRingHom.id β).comp f = f :=
  ext fun x => rfl

theorem cancel_right {f₁ f₂ : β →+*o γ} {g : α →+*o β} (hg : Surjective g) : f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {f : β →+*o γ} {g₁ g₂ : α →+*o β} (hf : Injective f) : f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h =>
    ext fun a =>
      hf <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end Preorderₓ

variable [NonAssocSemiringₓ β]

instance [Preorderₓ β] : Preorderₓ (OrderRingHom α β) :=
  Preorderₓ.lift (coeFn : _ → α → β)

instance [PartialOrderₓ β] : PartialOrderₓ (OrderRingHom α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

end OrderRingHom

/-! ### Ordered ring isomorphisms -/


namespace OrderRingIso

section LE

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ] [Mul δ] [Add δ] [LE δ]

/-- Reinterpret an ordered ring isomorphism as an order isomorphism. -/
def toOrderIso (f : α ≃+*o β) : α ≃o β :=
  ⟨f.toRingEquiv.toEquiv, f.map_le_map_iff'⟩

instance : OrderRingIsoClass (α ≃+*o β) α β where
  coe := fun f => f.toFun
  inv := fun f => f.invFun
  coe_injective' := fun f g h₁ h₂ => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_add := fun f => f.map_add'
  map_mul := fun f => f.map_mul'
  map_le_map_iff := fun f => f.map_le_map_iff'
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α ≃+*o β) fun _ => α → β :=
  FunLike.hasCoeToFun

theorem to_fun_eq_coe (f : α ≃+*o β) : f.toFun = f :=
  rfl

@[ext]
theorem ext {f g : α ≃+*o β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

@[simp]
theorem coe_mk (e : α ≃+* β) (h) : ⇑(⟨e, h⟩ : α ≃+*o β) = e :=
  rfl

@[simp]
theorem mk_coe (e : α ≃+*o β) (h) : (⟨e, h⟩ : α ≃+*o β) = e :=
  ext fun _ => rfl

@[simp]
theorem to_ring_equiv_eq_coe (f : α ≃+*o β) : f.toRingEquiv = f :=
  RingEquiv.ext fun _ => rfl

@[simp]
theorem to_order_iso_eq_coe (f : α ≃+*o β) : f.toOrderIso = f :=
  OrderIso.ext rfl

@[simp, norm_cast]
theorem coe_to_ring_equiv (f : α ≃+*o β) : ⇑(f : α ≃+* β) = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_order_iso (f : α ≃+*o β) : ⇑(f : α ≃o β) = f :=
  rfl

variable (α)

/-- The identity map as an ordered ring isomorphism. -/
@[refl]
protected def refl : α ≃+*o α :=
  ⟨RingEquiv.refl α, fun _ _ => Iff.rfl⟩

instance : Inhabited (α ≃+*o α) :=
  ⟨OrderRingIso.refl α⟩

@[simp]
theorem refl_apply (x : α) : OrderRingIso.refl α x = x :=
  rfl

@[simp]
theorem coe_ring_equiv_refl : (OrderRingIso.refl α : α ≃+* α) = RingEquiv.refl α :=
  rfl

@[simp]
theorem coe_order_iso_refl : (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α :=
  rfl

variable {α}

/-- The inverse of an ordered ring isomorphism as an ordered ring isomorphism. -/
@[symm]
protected def symm (e : α ≃+*o β) : β ≃+*o α :=
  ⟨e.toRingEquiv.symm, fun a b => by
    erw [← map_le_map_iff e, e.1.apply_symm_apply, e.1.apply_symm_apply]⟩

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : α ≃+*o β) : β → α :=
  e.symm

@[simp]
theorem symm_symm (e : α ≃+*o β) : e.symm.symm = e :=
  ext fun _ => rfl

/-- Composition of `order_ring_iso`s as an `order_ring_iso`. -/
@[trans, simps]
protected def trans (f : α ≃+*o β) (g : β ≃+*o γ) : α ≃+*o γ :=
  ⟨f.toRingEquiv.trans g.toRingEquiv, fun a b => (map_le_map_iff g).trans (map_le_map_iff f)⟩

@[simp]
theorem trans_apply (f : α ≃+*o β) (g : β ≃+*o γ) (a : α) : f.trans g a = g (f a) :=
  rfl

@[simp]
theorem self_trans_symm (e : α ≃+*o β) : e.trans e.symm = OrderRingIso.refl α :=
  ext e.left_inv

@[simp]
theorem symm_trans_self (e : α ≃+*o β) : e.symm.trans e = OrderRingIso.refl β :=
  ext e.right_inv

theorem symm_bijective : Bijective (OrderRingIso.symm : α ≃+*o β → β ≃+*o α) :=
  ⟨fun f g h => f.symm_symm.symm.trans <| (congr_arg OrderRingIso.symm h).trans g.symm_symm, fun f =>
    ⟨f.symm, f.symm_symm⟩⟩

end LE

section NonAssocSemiringₓ

variable [NonAssocSemiringₓ α] [Preorderₓ α] [NonAssocSemiringₓ β] [Preorderₓ β] [NonAssocSemiringₓ γ] [Preorderₓ γ]

/-- Reinterpret an ordered ring isomorphism as an ordered ring homomorphism. -/
def toOrderRingHom (f : α ≃+*o β) : α →+*o β :=
  ⟨f.toRingEquiv.toRingHom, fun a b => (map_le_map_iff f).2⟩

@[simp]
theorem to_order_ring_hom_eq_coe (f : α ≃+*o β) : f.toOrderRingHom = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_order_ring_hom (f : α ≃+*o β) : ⇑(f : α →+*o β) = f :=
  rfl

@[simp]
theorem coe_to_order_ring_hom_refl : (OrderRingIso.refl α : α →+*o α) = OrderRingHom.id α :=
  rfl

theorem to_order_ring_hom_injective : Injective (toOrderRingHom : α ≃+*o β → α →+*o β) := fun f g h =>
  FunLike.coe_injective <| by
    convert FunLike.ext'_iff.1 h

end NonAssocSemiringₓ

end OrderRingIso

/-!
### Uniqueness

There is at most one ordered ring homomorphism from a linear ordered field to an archimedean linear
ordered field. Reciprocally, such an ordered ring homomorphism exists when the codomain is further
conditionally complete.
-/


/-- There is at most one ordered ring homomorphism from a linear ordered field to an archimedean
linear ordered field. -/
-- TODO[gh-6025]: make this an instance once safe to do so
theorem OrderRingHom.subsingleton [LinearOrderedField α] [LinearOrderedField β] [Archimedean β] :
    Subsingleton (α →+*o β) :=
  ⟨fun f g => by
    ext x
    by_contra' h
    wlog h : f x < g x using f g, g f
    · exact Ne.lt_or_lt h
      
    obtain ⟨q, hf, hg⟩ := exists_rat_btwn h
    rw [← map_rat_cast f] at hf
    rw [← map_rat_cast g] at hg
    exact (lt_asymmₓ ((OrderHomClass.mono g).reflect_lt hg) <| (OrderHomClass.mono f).reflect_lt hf).elim⟩

attribute [local instance] OrderRingHom.subsingleton

/-- There is at most one ordered ring isomorphism between a linear ordered field and an archimedean
linear ordered field. -/
-- TODO[gh-6025]: make this an instance once safe to do so
theorem OrderRingIso.subsingleton_right [LinearOrderedField α] [LinearOrderedField β] [Archimedean β] :
    Subsingleton (α ≃+*o β) :=
  OrderRingIso.to_order_ring_hom_injective.Subsingleton

attribute [local instance] OrderRingIso.subsingleton_right

/-- There is at most one ordered ring isomorphism between an archimedean linear ordered field and a
linear ordered field. -/
-- TODO[gh-6025]: make this an instance once safe to do so
theorem OrderRingIso.subsingleton_left [LinearOrderedField α] [Archimedean α] [LinearOrderedField β] :
    Subsingleton (α ≃+*o β) :=
  OrderRingIso.symm_bijective.Injective.Subsingleton

