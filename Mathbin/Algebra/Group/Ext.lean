/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov
-/
import Mathbin.Algebra.Hom.Group

/-!
# Extensionality lemmas for monoid and group structures

In this file we prove extensionality lemmas for `monoid` and higher algebraic structures with one
binary operation. Extensionality lemmas for structures that are lower in the hierarchy can be found
in `algebra.group.defs`.

## Implementation details

To get equality of `npow` etc, we define a monoid homomorphism between two monoid structures on the
same type, then apply lemmas like `monoid_hom.map_div`, `monoid_hom.map_pow` etc.

## Tags
monoid, group, extensionality
-/


universe u

@[ext, to_additive]
theorem Monoidₓ.ext {M : Type u} ⦃m₁ m₂ : Monoidₓ M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ := by
  have h₁ : (@Monoidₓ.toMulOneClass _ m₁).one = (@Monoidₓ.toMulOneClass _ m₂).one :=
    congr_arg (@MulOneClassₓ.one M) (MulOneClassₓ.ext h_mul)
  set f : @MonoidHom M M (@Monoidₓ.toMulOneClass _ m₁) (@Monoidₓ.toMulOneClass _ m₂) :=
    { toFun := id, map_one' := h₁, map_mul' := fun x y => congr_fun (congr_fun h_mul x) y }
  have hpow : m₁.npow = m₂.npow := by
    ext n x
    exact @MonoidHom.map_pow M M m₁ m₂ f x n
  cases m₁
  cases m₂
  congr <;> assumption

@[to_additive]
theorem CommMonoidₓ.to_monoid_injective {M : Type u} : Function.Injective (@CommMonoidₓ.toMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h

@[ext, to_additive]
theorem CommMonoidₓ.ext {M : Type _} ⦃m₁ m₂ : CommMonoidₓ M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CommMonoidₓ.to_monoid_injective <| Monoidₓ.ext h_mul

@[to_additive]
theorem LeftCancelMonoid.to_monoid_injective {M : Type u} : Function.Injective (@LeftCancelMonoid.toMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h

@[ext, to_additive]
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  LeftCancelMonoid.to_monoid_injective <| Monoidₓ.ext h_mul

@[to_additive]
theorem RightCancelMonoid.to_monoid_injective {M : Type u} : Function.Injective (@RightCancelMonoid.toMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h

@[ext, to_additive]
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  RightCancelMonoid.to_monoid_injective <| Monoidₓ.ext h_mul

@[to_additive]
theorem CancelMonoid.to_left_cancel_monoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toLeftCancelMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h

@[ext, to_additive]
theorem CancelMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CancelMonoid.to_left_cancel_monoid_injective <| LeftCancelMonoid.ext h_mul

@[to_additive]
theorem CancelCommMonoid.to_comm_monoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h

@[ext, to_additive]
theorem CancelCommMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelCommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CancelCommMonoid.to_comm_monoid_injective <| CommMonoidₓ.ext h_mul

@[ext, to_additive]
theorem DivInvMonoidₓ.ext {M : Type _} ⦃m₁ m₂ : DivInvMonoidₓ M⦄ (h_mul : m₁.mul = m₂.mul) (h_inv : m₁.inv = m₂.inv) :
    m₁ = m₂ := by
  have h₁ : (@DivInvMonoidₓ.toMonoid _ m₁).one = (@DivInvMonoidₓ.toMonoid _ m₂).one :=
    congr_arg (@Monoidₓ.one M) (Monoidₓ.ext h_mul)
  set f :
    @MonoidHom M M
      (by
        let this := m₁ <;> infer_instance)
      (by
        let this := m₂ <;> infer_instance) :=
    { toFun := id, map_one' := h₁, map_mul' := fun x y => congr_fun (congr_fun h_mul x) y }
  have hpow : (@DivInvMonoidₓ.toMonoid _ m₁).npow = (@DivInvMonoidₓ.toMonoid _ m₂).npow :=
    congr_arg (@Monoidₓ.npow M) (Monoidₓ.ext h_mul)
  have hzpow : m₁.zpow = m₂.zpow := by
    ext m x
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have hdiv : m₁.div = m₂.div := by
    ext a b
    exact @map_div' M M _ m₁ m₂ _ f (congr_fun h_inv) a b
  cases m₁
  cases m₂
  congr
  exacts[h_mul, h₁, hpow, h_inv, hdiv, hzpow]

@[ext, to_additive]
theorem Groupₓ.ext {G : Type _} ⦃g₁ g₂ : Groupₓ G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ := by
  set f :=
    @MonoidHom.mk' G G
      (by
        let this := g₁ <;> infer_instance)
      g₂ id fun a b => congr_fun (congr_fun h_mul a) b
  exact
    Groupₓ.to_div_inv_monoid_injective
      (DivInvMonoidₓ.ext h_mul (funext <| @MonoidHom.map_inv G G g₁ (@Groupₓ.toDivisionMonoid _ g₂) f))

@[ext, to_additive]
theorem CommGroupₓ.ext {G : Type _} ⦃g₁ g₂ : CommGroupₓ G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  CommGroupₓ.to_group_injective <| Groupₓ.ext h_mul

