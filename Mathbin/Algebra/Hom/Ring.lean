/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
import Mathbin.Algebra.Ring.Basic

/-!
# Homomorphisms of semirings and rings

This file defines bundled homomorphisms of (non-unital) semirings and rings. As with monoid and
groups, we use the same structure `ring_hom a β`, a.k.a. `α →+* β`, for both types of homomorphisms.

The unbundled homomorphisms are defined in `deprecated.ring`. They are deprecated and the plan is to
slowly remove them from mathlib.

## Main definitions

* `non_unital_ring_hom`: Non-unital (semi)ring homomorphisms. Additive monoid homomorphism which
  preserve multiplication.
* `ring_hom`: (Semi)ring homomorphisms. Monoid homomorphisms which are also additive monoid
  homomorphism.

## Notations

* `→ₙ+*`: Non-unital (semi)ring homs
* `→+*`: (Semi)ring homs

## Implementation notes

* There's a coercion from bundled homs to fun, and the canonical notation is to
  use the bundled hom as a function via this coercion.

* There is no `semiring_hom` -- the idea is that `ring_hom` is used.
  The constructor for a `ring_hom` between semirings needs a proof of `map_zero`,
  `map_one` and `map_add` as well as `map_mul`; a separate constructor
  `ring_hom.mk'` will construct ring homs between rings from monoid homs given
  only a proof that addition is preserved.

## Tags

`ring_hom`, `semiring_hom`
-/


open Function

variable {F α β γ : Type _}

/-- Bundled non-unital semiring homomorphisms `α →ₙ+* β`; use this for bundled non-unital ring
homomorphisms too.

When possible, instead of parametrizing results over `(f : α →ₙ+* β)`,
you should parametrize over `(F : Type*) [non_unital_ring_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `non_unital_ring_hom_class`. -/
structure NonUnitalRingHom (α β : Type _) [NonUnitalNonAssocSemiringₓ α] [NonUnitalNonAssocSemiringₓ β] extends α →ₙ* β,
  α →+ β

-- mathport name: «expr →ₙ+* »
infixr:25 " →ₙ+* " => NonUnitalRingHom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as a semigroup
homomorphism `α →ₙ* β`. The `simp`-normal form is `(f : α →ₙ* β)`. -/
add_decl_doc NonUnitalRingHom.toMulHom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as an additive
monoid homomorphism `α →+ β`. The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc NonUnitalRingHom.toAddMonoidHom

section NonUnitalRingHomClass

/-- `non_unital_ring_hom_class F α β` states that `F` is a type of non-unital (semi)ring
homomorphisms. You should extend this class when you extend `non_unital_ring_hom`. -/
class NonUnitalRingHomClass (F : Type _) (α β : outParam (Type _)) [NonUnitalNonAssocSemiringₓ α]
  [NonUnitalNonAssocSemiringₓ β] extends MulHomClass F α β, AddMonoidHomClass F α β

variable [NonUnitalNonAssocSemiringₓ α] [NonUnitalNonAssocSemiringₓ β] [NonUnitalRingHomClass F α β]

instance : CoeTₓ F (α →ₙ+* β) :=
  ⟨fun f => { toFun := f, map_zero' := map_zero f, map_mul' := map_mul f, map_add' := map_add f }⟩

end NonUnitalRingHomClass

namespace NonUnitalRingHom

section coe

/-!
Throughout this section, some `semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/


variable {rα : NonUnitalNonAssocSemiringₓ α} {rβ : NonUnitalNonAssocSemiringₓ β}

include rα rβ

instance : NonUnitalRingHomClass (α →ₙ+* β) α β where
  coe := NonUnitalRingHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_add := NonUnitalRingHom.map_add'
  map_zero := NonUnitalRingHom.map_zero'
  map_mul := NonUnitalRingHom.map_mul'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →ₙ+* β) fun _ => α → β :=
  ⟨NonUnitalRingHom.toFun⟩

@[simp]
theorem to_fun_eq_coe (f : α →ₙ+* β) : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : α → β) (h₁ h₂ h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : α →ₙ+* β) = f :=
  rfl

@[simp]
theorem coe_coe [NonUnitalRingHomClass F α β] (f : F) : ((f : α →ₙ+* β) : α → β) = f :=
  rfl

@[simp]
theorem coe_to_mul_hom (f : α →ₙ+* β) : ⇑f.toMulHom = f :=
  rfl

@[simp]
theorem coe_mul_hom_mk (f : α → β) (h₁ h₂ h₃) : ((⟨f, h₁, h₂, h₃⟩ : α →ₙ+* β) : α →ₙ* β) = ⟨f, h₁⟩ :=
  rfl

@[simp]
theorem coe_to_add_monoid_hom (f : α →ₙ+* β) : ⇑f.toAddMonoidHom = f :=
  rfl

@[simp]
theorem coe_add_monoid_hom_mk (f : α → β) (h₁ h₂ h₃) : ((⟨f, h₁, h₂, h₃⟩ : α →ₙ+* β) : α →+ β) = ⟨f, h₂, h₃⟩ :=
  rfl

/-- Copy of a `ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : α →ₙ+* β :=
  { f.toMulHom.copy f' h, f.toAddMonoidHom.copy f' h with }

end coe

variable [rα : NonUnitalNonAssocSemiringₓ α] [rβ : NonUnitalNonAssocSemiringₓ β]

section

include rα rβ

variable (f : α →ₙ+* β) {x y : α} {rα rβ}

@[ext]
theorem ext ⦃f g : α →ₙ+* β⦄ : (∀ x, f x = g x) → f = g :=
  FunLike.ext _ _

theorem ext_iff {f g : α →ₙ+* β} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

@[simp]
theorem mk_coe (f : α →ₙ+* β) (h₁ h₂ h₃) : NonUnitalRingHom.mk f h₁ h₂ h₃ = f :=
  ext fun _ => rfl

theorem coe_add_monoid_hom_injective : Injective (coe : (α →ₙ+* β) → α →+ β) := fun f g h =>
  ext <| AddMonoidHom.congr_fun h

theorem coe_mul_hom_injective : Injective (coe : (α →ₙ+* β) → α →ₙ* β) := fun f g h => ext <| MulHom.congr_fun h

end

/-- The identity non-unital ring homomorphism from a non-unital semiring to itself. -/
protected def id (α : Type _) [NonUnitalNonAssocSemiringₓ α] : α →ₙ+* α := by
  refine' { toFun := id.. } <;> intros <;> rfl

include rα rβ

instance : Zero (α →ₙ+* β) :=
  ⟨{ toFun := 0, map_mul' := fun x y => (mul_zero (0 : β)).symm, map_zero' := rfl,
      map_add' := fun x y => (add_zeroₓ (0 : β)).symm }⟩

instance : Inhabited (α →ₙ+* β) :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : α →ₙ+* β) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : α) : (0 : α →ₙ+* β) x = 0 :=
  rfl

omit rβ

@[simp]
theorem id_apply (x : α) : NonUnitalRingHom.id α x = x :=
  rfl

@[simp]
theorem coe_add_monoid_hom_id : (NonUnitalRingHom.id α : α →+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_mul_hom_id : (NonUnitalRingHom.id α : α →ₙ* α) = MulHom.id α :=
  rfl

variable {rγ : NonUnitalNonAssocSemiringₓ γ}

include rβ rγ

/-- Composition of non-unital ring homomorphisms is a non-unital ring homomorphism. -/
def comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : α →ₙ+* γ :=
  { g.toMulHom.comp f.toMulHom, g.toAddMonoidHom.comp f.toAddMonoidHom with }

/-- Composition of non-unital ring homomorphisms is associative. -/
theorem comp_assoc {δ} {rδ : NonUnitalNonAssocSemiringₓ δ} (f : α →ₙ+* β) (g : β →ₙ+* γ) (h : γ →ₙ+* δ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem coe_comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
theorem comp_apply (g : β →ₙ+* γ) (f : α →ₙ+* β) (x : α) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem coe_comp_add_monoid_hom (g : β →ₙ+* γ) (f : α →ₙ+* β) : (g.comp f : α →+ γ) = (g : β →+ γ).comp f :=
  rfl

@[simp]
theorem coe_comp_mul_hom (g : β →ₙ+* γ) (f : α →ₙ+* β) : (g.comp f : α →ₙ* γ) = (g : β →ₙ* γ).comp f :=
  rfl

@[simp]
theorem comp_zero (g : β →ₙ+* γ) : g.comp (0 : α →ₙ+* β) = 0 := by
  ext
  simp

@[simp]
theorem zero_comp (f : α →ₙ+* β) : (0 : β →ₙ+* γ).comp f = 0 := by
  ext
  rfl

omit rγ

@[simp]
theorem comp_id (f : α →ₙ+* β) : f.comp (NonUnitalRingHom.id α) = f :=
  ext fun x => rfl

@[simp]
theorem id_comp (f : α →ₙ+* β) : (NonUnitalRingHom.id β).comp f = f :=
  ext fun x => rfl

omit rβ

instance : MonoidWithZeroₓ (α →ₙ+* α) where
  one := NonUnitalRingHom.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc := fun f g h => comp_assoc _ _ _
  zero := 0
  mul_zero := comp_zero
  zero_mul := zero_comp

theorem one_def : (1 : α →ₙ+* α) = NonUnitalRingHom.id α :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : α →ₙ+* α) = id :=
  rfl

theorem mul_def (f g : α →ₙ+* α) : f * g = f.comp g :=
  rfl

@[simp]
theorem coe_mul (f g : α →ₙ+* α) : ⇑(f * g) = f ∘ g :=
  rfl

include rβ rγ

theorem cancel_right {g₁ g₂ : β →ₙ+* γ} {f : α →ₙ+* β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 (ext_iff.1 h), fun h => h ▸ rfl⟩

theorem cancel_left {g : β →ₙ+* γ} {f₁ f₂ : α →ₙ+* β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun x =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    fun h => h ▸ rfl⟩

omit rα rβ rγ

end NonUnitalRingHom

/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.

This extends from both `monoid_hom` and `monoid_with_zero_hom` in order to put the fields in a
sensible order, even though `monoid_with_zero_hom` already extends `monoid_hom`. -/
structure RingHom (α : Type _) (β : Type _) [NonAssocSemiringₓ α] [NonAssocSemiringₓ β] extends α →* β, α →+ β,
  α →ₙ+* β, α →*₀ β

-- mathport name: «expr →+* »
infixr:25 " →+* " => RingHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a monoid with zero homomorphism `α →*₀ β`.
The `simp`-normal form is `(f : α →*₀ β)`. -/
add_decl_doc RingHom.toMonoidWithZeroHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a monoid homomorphism `α →* β`.
The `simp`-normal form is `(f : α →* β)`. -/
add_decl_doc RingHom.toMonoidHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as an additive monoid homomorphism `α →+ β`.
The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc RingHom.toAddMonoidHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a non-unital ring homomorphism `α →ₙ+* β`. The
`simp`-normal form is `(f : α →ₙ+* β)`. -/
add_decl_doc RingHom.toNonUnitalRingHom

section RingHomClass

/-- `ring_hom_class F α β` states that `F` is a type of (semi)ring homomorphisms.
You should extend this class when you extend `ring_hom`.

This extends from both `monoid_hom_class` and `monoid_with_zero_hom_class` in
order to put the fields in a sensible order, even though
`monoid_with_zero_hom_class` already extends `monoid_hom_class`. -/
class RingHomClass (F : Type _) (α β : outParam (Type _)) [NonAssocSemiringₓ α] [NonAssocSemiringₓ β] extends
  MonoidHomClass F α β, AddMonoidHomClass F α β, MonoidWithZeroHomClass F α β

variable [NonAssocSemiringₓ α] [NonAssocSemiringₓ β] [RingHomClass F α β]

/-- Ring homomorphisms preserve `bit1`. -/
@[simp]
theorem map_bit1 (f : F) (a : α) : (f (bit1 a) : β) = bit1 (f a) := by
  simp [← bit1]

instance : CoeTₓ F (α →+* β) :=
  ⟨fun f =>
    { toFun := f, map_zero' := map_zero f, map_one' := map_one f, map_mul' := map_mul f, map_add' := map_add f }⟩

instance (priority := 100) RingHomClass.toNonUnitalRingHomClass : NonUnitalRingHomClass F α β :=
  { ‹RingHomClass F α β› with }

end RingHomClass

namespace RingHom

section coe

/-!
Throughout this section, some `semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/


variable {rα : NonAssocSemiringₓ α} {rβ : NonAssocSemiringₓ β}

include rα rβ

instance : RingHomClass (α →+* β) α β where
  coe := RingHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_add := RingHom.map_add'
  map_zero := RingHom.map_zero'
  map_mul := RingHom.map_mul'
  map_one := RingHom.map_one'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly.
-/
instance : CoeFun (α →+* β) fun _ => α → β :=
  ⟨RingHom.toFun⟩

initialize_simps_projections RingHom (toFun → apply)

@[simp]
theorem to_fun_eq_coe (f : α →+* β) : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : α → β) (h₁ h₂ h₃ h₄) : ⇑(⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) = f :=
  rfl

@[simp]
theorem coe_coe {F : Type _} [RingHomClass F α β] (f : F) : ((f : α →+* β) : α → β) = f :=
  rfl

instance hasCoeMonoidHom : Coe (α →+* β) (α →* β) :=
  ⟨RingHom.toMonoidHom⟩

@[simp, norm_cast]
theorem coe_monoid_hom (f : α →+* β) : ⇑(f : α →* β) = f :=
  rfl

@[simp]
theorem to_monoid_hom_eq_coe (f : α →+* β) : f.toMonoidHom = f :=
  rfl

@[simp]
theorem to_monoid_with_zero_hom_eq_coe (f : α →+* β) : (f.toMonoidWithZeroHom : α → β) = f :=
  rfl

@[simp]
theorem coe_monoid_hom_mk (f : α → β) (h₁ h₂ h₃ h₄) : ((⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) : α →* β) = ⟨f, h₁, h₂⟩ :=
  rfl

@[simp, norm_cast]
theorem coe_add_monoid_hom (f : α →+* β) : ⇑(f : α →+ β) = f :=
  rfl

@[simp]
theorem to_add_monoid_hom_eq_coe (f : α →+* β) : f.toAddMonoidHom = f :=
  rfl

@[simp]
theorem coe_add_monoid_hom_mk (f : α → β) (h₁ h₂ h₃ h₄) : ((⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) : α →+ β) = ⟨f, h₃, h₄⟩ :=
  rfl

/-- Copy of a `ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
def copy (f : α →+* β) (f' : α → β) (h : f' = f) : α →+* β :=
  { f.toMonoidWithZeroHom.copy f' h, f.toAddMonoidHom.copy f' h with }

end coe

variable [rα : NonAssocSemiringₓ α] [rβ : NonAssocSemiringₓ β]

section

include rα rβ

variable (f : α →+* β) {x y : α} {rα rβ}

theorem congr_fun {f g : α →+* β} (h : f = g) (x : α) : f x = g x :=
  FunLike.congr_fun h x

theorem congr_arg (f : α →+* β) {x y : α} (h : x = y) : f x = f y :=
  FunLike.congr_arg f h

theorem coe_inj ⦃f g : α →+* β⦄ (h : (f : α → β) = g) : f = g :=
  FunLike.coe_injective h

@[ext]
theorem ext ⦃f g : α →+* β⦄ : (∀ x, f x = g x) → f = g :=
  FunLike.ext _ _

theorem ext_iff {f g : α →+* β} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

@[simp]
theorem mk_coe (f : α →+* β) (h₁ h₂ h₃ h₄) : RingHom.mk f h₁ h₂ h₃ h₄ = f :=
  ext fun _ => rfl

theorem coe_add_monoid_hom_injective : Injective (coe : (α →+* β) → α →+ β) := fun f g h =>
  ext <| AddMonoidHom.congr_fun h

theorem coe_monoid_hom_injective : Injective (coe : (α →+* β) → α →* β) := fun f g h => ext <| MonoidHom.congr_fun h

/-- Ring homomorphisms map zero to zero. -/
protected theorem map_zero (f : α →+* β) : f 0 = 0 :=
  map_zero f

/-- Ring homomorphisms map one to one. -/
protected theorem map_one (f : α →+* β) : f 1 = 1 :=
  map_one f

/-- Ring homomorphisms preserve addition. -/
protected theorem map_add (f : α →+* β) : ∀ a b, f (a + b) = f a + f b :=
  map_add f

/-- Ring homomorphisms preserve multiplication. -/
protected theorem map_mul (f : α →+* β) : ∀ a b, f (a * b) = f a * f b :=
  map_mul f

/-- Ring homomorphisms preserve `bit0`. -/
protected theorem map_bit0 (f : α →+* β) : ∀ a, f (bit0 a) = bit0 (f a) :=
  map_bit0 f

/-- Ring homomorphisms preserve `bit1`. -/
protected theorem map_bit1 (f : α →+* β) : ∀ a, f (bit1 a) = bit1 (f a) :=
  map_bit1 f

/-- `f : α →+* β` has a trivial codomain iff `f 1 = 0`. -/
theorem codomain_trivial_iff_map_one_eq_zero : (0 : β) = 1 ↔ f 1 = 0 := by
  rw [map_one, eq_comm]

/-- `f : α →+* β` has a trivial codomain iff it has a trivial range. -/
theorem codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ ∀ x, f x = 0 :=
  f.codomain_trivial_iff_map_one_eq_zero.trans
    ⟨fun h x => by
      rw [← mul_oneₓ x, map_mul, h, mul_zero], fun h => h 1⟩

/-- `f : α →+* β` has a trivial codomain iff its range is `{0}`. -/
theorem codomain_trivial_iff_range_eq_singleton_zero : (0 : β) = 1 ↔ Set.Range f = {0} :=
  f.codomain_trivial_iff_range_trivial.trans
    ⟨fun h =>
      Set.ext fun y =>
        ⟨fun ⟨x, hx⟩ => by
          simp [hx, ← h x], fun hy =>
          ⟨0, by
            simpa using hy.symm⟩⟩,
      fun h x => Set.mem_singleton_iff.mp (h ▸ Set.mem_range_self x)⟩

/-- `f : α →+* β` doesn't map `1` to `0` if `β` is nontrivial -/
theorem map_one_ne_zero [Nontrivial β] : f 1 ≠ 0 :=
  mt f.codomain_trivial_iff_map_one_eq_zero.mpr zero_ne_one

/-- If there is a homomorphism `f : α →+* β` and `β` is nontrivial, then `α` is nontrivial. -/
theorem domain_nontrivial [Nontrivial β] : Nontrivial α :=
  ⟨⟨1, 0,
      mt
        (fun h =>
          show f 1 = 0 by
            rw [h, map_zero])
        f.map_one_ne_zero⟩⟩

end

/-- Ring homomorphisms preserve additive inverse. -/
protected theorem map_neg [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x : α) : f (-x) = -f x :=
  map_neg f x

/-- Ring homomorphisms preserve subtraction. -/
protected theorem map_sub [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x y : α) : f (x - y) = f x - f y :=
  map_sub f x y

/-- Makes a ring homomorphism from a monoid homomorphism of rings which preserves addition. -/
def mk' [NonAssocSemiringₓ α] [NonAssocRing β] (f : α →* β) (map_add : ∀ a b, f (a + b) = f a + f b) : α →+* β :=
  { AddMonoidHom.mk' f map_add, f with }

section Semiringₓ

variable [Semiringₓ α] [Semiringₓ β]

theorem is_unit_map (f : α →+* β) {a : α} : IsUnit a → IsUnit (f a) :=
  IsUnit.map f

protected theorem map_dvd (f : α →+* β) {a b : α} : a ∣ b → f a ∣ f b :=
  map_dvd f

end Semiringₓ

/-- The identity ring homomorphism from a semiring to itself. -/
def id (α : Type _) [NonAssocSemiringₓ α] : α →+* α := by
  refine' { toFun := id.. } <;> intros <;> rfl

include rα

instance : Inhabited (α →+* α) :=
  ⟨id α⟩

@[simp]
theorem id_apply (x : α) : RingHom.id α x = x :=
  rfl

@[simp]
theorem coe_add_monoid_hom_id : (id α : α →+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_monoid_hom_id : (id α : α →* α) = MonoidHom.id α :=
  rfl

variable {rγ : NonAssocSemiringₓ γ}

include rβ rγ

/-- Composition of ring homomorphisms is a ring homomorphism. -/
def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
  { g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with toFun := g ∘ f,
    map_one' := by
      simp }

/-- Composition of semiring homomorphisms is associative. -/
theorem comp_assoc {δ} {rδ : NonAssocSemiringₓ δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem coe_comp (hnp : β →+* γ) (hmn : α →+* β) : (hnp.comp hmn : α → γ) = hnp ∘ hmn :=
  rfl

theorem comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) : (hnp.comp hmn : α → γ) x = hnp (hmn x) :=
  rfl

omit rγ

@[simp]
theorem comp_id (f : α →+* β) : f.comp (id α) = f :=
  ext fun x => rfl

@[simp]
theorem id_comp (f : α →+* β) : (id β).comp f = f :=
  ext fun x => rfl

omit rβ

instance : Monoidₓ (α →+* α) where
  one := id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc := fun f g h => comp_assoc _ _ _

theorem one_def : (1 : α →+* α) = id α :=
  rfl

theorem mul_def (f g : α →+* α) : f * g = f.comp g :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : α →+* α) = _root_.id :=
  rfl

@[simp]
theorem coe_mul (f g : α →+* α) : ⇑(f * g) = f ∘ g :=
  rfl

include rβ rγ

theorem cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => RingHom.ext <| hf.forall.2 (ext_iff.1 h), fun h => h ▸ rfl⟩

theorem cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    RingHom.ext fun x =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    fun h => h ▸ rfl⟩

end RingHom

/-- Pullback `is_domain` instance along an injective function. -/
protected theorem Function.Injective.is_domain [Ringₓ α] [IsDomain α] [Ringₓ β] (f : β →+* α) (hf : Injective f) :
    IsDomain β :=
  { pullback_nonzero f f.map_zero f.map_one, hf.NoZeroDivisors f f.map_zero f.map_mul with }

namespace AddMonoidHom

variable [CommRingₓ α] [IsDomain α] [CommRingₓ β] (f : β →+ α)

/-- Make a ring homomorphism from an additive group homomorphism from a commutative ring to an
integral domain that commutes with self multiplication, assumes that two is nonzero and `1` is sent
to `1`. -/
def mkRingHomOfMulSelfOfTwoNeZero (h : ∀ x, f (x * x) = f x * f x) (h_two : (2 : α) ≠ 0) (h_one : f 1 = 1) : β →+* α :=
  { f with map_one' := h_one,
    map_mul' := fun x y => by
      have hxy := h (x + y)
      rw [mul_addₓ, add_mulₓ, add_mulₓ, f.map_add, f.map_add, f.map_add, f.map_add, h x, h y, add_mulₓ, mul_addₓ,
        mul_addₓ, ← sub_eq_zero, add_commₓ, ← sub_sub, ← sub_sub, ← sub_sub, mul_comm y x, mul_comm (f y) (f x)] at hxy
      simp only [← add_assocₓ, ← add_sub_assoc, ← add_sub_cancel'_right] at hxy
      rw [sub_sub, ← two_mul, ← add_sub_assoc, ← two_mul, ← mul_sub, mul_eq_zero, sub_eq_zero, or_iff_not_imp_left] at
        hxy
      exact hxy h_two }

@[simp]
theorem coe_fn_mk_ring_hom_of_mul_self_of_two_ne_zero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β → α) = f :=
  rfl

@[simp]
theorem coe_add_monoid_hom_mk_ring_hom_of_mul_self_of_two_ne_zero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β →+ α) = f := by
  ext
  rfl

end AddMonoidHom

