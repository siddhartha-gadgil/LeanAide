/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathbin.Tactic.PiInstances
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Hom.Ring

/-!
# Pi instances for ring

This file defines instances for ring, semiring and related structures on Pi Types
-/


namespace Pi

universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

instance distrib [∀ i, Distribₓ <| f i] : Distribₓ (∀ i : I, f i) := by
  refine_struct { add := (· + ·), mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalNonAssocSemiring [∀ i, NonUnitalNonAssocSemiringₓ <| f i] :
    NonUnitalNonAssocSemiringₓ (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), add := (· + ·), mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalSemiring [∀ i, NonUnitalSemiringₓ <| f i] : NonUnitalSemiringₓ (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), add := (· + ·), mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonAssocSemiring [∀ i, NonAssocSemiringₓ <| f i] : NonAssocSemiringₓ (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), one := 1, add := (· + ·), mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance semiring [∀ i, Semiringₓ <| f i] : Semiringₓ (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), one := 1, add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul,
        npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalCommSemiring [∀ i, NonUnitalCommSemiring <| f i] : NonUnitalCommSemiring (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance commSemiring [∀ i, CommSemiringₓ <| f i] : CommSemiringₓ (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), one := 1, add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul,
        npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalNonAssocRing [∀ i, NonUnitalNonAssocRing <| f i] : NonUnitalNonAssocRing (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), add := (· + ·), mul := (· * ·), neg := Neg.neg, nsmul := AddMonoidₓ.nsmul,
        zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalRing [∀ i, NonUnitalRing <| f i] : NonUnitalRing (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), add := (· + ·), mul := (· * ·), neg := Neg.neg, nsmul := AddMonoidₓ.nsmul,
        zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonAssocRing [∀ i, NonAssocRing <| f i] : NonAssocRing (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), add := (· + ·), mul := (· * ·), neg := Neg.neg, nsmul := AddMonoidₓ.nsmul,
        zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance ring [∀ i, Ringₓ <| f i] : Ringₓ (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), one := 1, add := (· + ·), mul := (· * ·), neg := Neg.neg, nsmul := AddMonoidₓ.nsmul,
        zsmul := SubNegMonoidₓ.zsmul, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalCommRing [∀ i, NonUnitalCommRing <| f i] : NonUnitalCommRing (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), add := (· + ·), mul := (· * ·), neg := Neg.neg, nsmul := AddMonoidₓ.nsmul,
        zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance commRing [∀ i, CommRingₓ <| f i] : CommRingₓ (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), one := 1, add := (· + ·), mul := (· * ·), neg := Neg.neg, nsmul := AddMonoidₓ.nsmul,
        zsmul := SubNegMonoidₓ.zsmul, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

/-- A family of non-unital ring homomorphisms `f a : γ →ₙ+* β a` defines a non-unital ring
homomorphism `pi.non_unital_ring_hom f : γ →+* Π a, β a` given by
`pi.non_unital_ring_hom f x b = f b x`. -/
@[simps]
protected def nonUnitalRingHom {γ : Type w} [∀ i, NonUnitalNonAssocSemiringₓ (f i)] [NonUnitalNonAssocSemiringₓ γ]
    (g : ∀ i, γ →ₙ+* f i) : γ →ₙ+* ∀ i, f i where
  toFun := fun x b => g b x
  map_add' := fun x y => funext fun z => map_add (g z) x y
  map_mul' := fun x y => funext fun z => map_mul (g z) x y
  map_zero' := funext fun z => map_zero (g z)

theorem non_unital_ring_hom_injective {γ : Type w} [Nonempty I] [∀ i, NonUnitalNonAssocSemiringₓ (f i)]
    [NonUnitalNonAssocSemiringₓ γ] (g : ∀ i, γ →ₙ+* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (Pi.nonUnitalRingHom g) := fun x y h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((Function.funext_iffₓ.mp h : _) i)

/-- A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`pi.ring_hom f : γ →+* Π a, β a` given by `pi.ring_hom f x b = f b x`. -/
@[simps]
protected def ringHom {γ : Type w} [∀ i, NonAssocSemiringₓ (f i)] [NonAssocSemiringₓ γ] (g : ∀ i, γ →+* f i) :
    γ →+* ∀ i, f i where
  toFun := fun x b => g b x
  map_add' := fun x y => funext fun z => (g z).map_add x y
  map_mul' := fun x y => funext fun z => (g z).map_mul x y
  map_one' := funext fun z => (g z).map_one
  map_zero' := funext fun z => (g z).map_zero

theorem ring_hom_injective {γ : Type w} [Nonempty I] [∀ i, NonAssocSemiringₓ (f i)] [NonAssocSemiringₓ γ]
    (g : ∀ i, γ →+* f i) (hg : ∀ i, Function.Injective (g i)) : Function.Injective (Pi.ringHom g) := fun x y h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((Function.funext_iffₓ.mp h : _) i)

end Pi

section NonUnitalRingHom

universe u v

variable {I : Type u}

/-- Evaluation of functions into an indexed collection of non-unital rings at a point is a
non-unital ring homomorphism. This is `function.eval` as a `non_unital_ring_hom`. -/
@[simps]
def Pi.evalNonUnitalRingHom (f : I → Type v) [∀ i, NonUnitalNonAssocSemiringₓ (f i)] (i : I) : (∀ i, f i) →ₙ+* f i :=
  { Pi.evalMulHom f i, Pi.evalAddMonoidHom f i with }

/-- `function.const` as a `non_unital_ring_hom`. -/
@[simps]
def Pi.constNonUnitalRingHom (α β : Type _) [NonUnitalNonAssocSemiringₓ β] : β →ₙ+* α → β :=
  { Pi.nonUnitalRingHom fun _ => NonUnitalRingHom.id β with toFun := Function.const _ }

/-- Non-unital ring homomorphism between the function spaces `I → α` and `I → β`, induced by a
non-unital ring homomorphism `f` between `α` and `β`. -/
@[simps]
protected def NonUnitalRingHom.compLeft {α β : Type _} [NonUnitalNonAssocSemiringₓ α] [NonUnitalNonAssocSemiringₓ β]
    (f : α →ₙ+* β) (I : Type _) : (I → α) →ₙ+* I → β :=
  { f.toMulHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

end NonUnitalRingHom

section RingHom

universe u v

variable {I : Type u}

/-- Evaluation of functions into an indexed collection of rings at a point is a ring
homomorphism. This is `function.eval` as a `ring_hom`. -/
@[simps]
def Pi.evalRingHom (f : I → Type v) [∀ i, NonAssocSemiringₓ (f i)] (i : I) : (∀ i, f i) →+* f i :=
  { Pi.evalMonoidHom f i, Pi.evalAddMonoidHom f i with }

/-- `function.const` as a `ring_hom`. -/
@[simps]
def Pi.constRingHom (α β : Type _) [NonAssocSemiringₓ β] : β →+* α → β :=
  { Pi.ringHom fun _ => RingHom.id β with toFun := Function.const _ }

/-- Ring homomorphism between the function spaces `I → α` and `I → β`, induced by a ring
homomorphism `f` between `α` and `β`. -/
@[simps]
protected def RingHom.compLeft {α β : Type _} [NonAssocSemiringₓ α] [NonAssocSemiringₓ β] (f : α →+* β) (I : Type _) :
    (I → α) →+* I → β :=
  { f.toMonoidHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

end RingHom

