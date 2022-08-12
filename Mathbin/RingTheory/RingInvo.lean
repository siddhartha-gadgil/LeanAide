/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau
-/
import Mathbin.Algebra.Ring.Equiv
import Mathbin.Algebra.Ring.Opposite

/-!
# Ring involutions

This file defines a ring involution as a structure extending `R ≃+* Rᵐᵒᵖ`,
with the additional fact `f.involution : (f (f x).unop).unop = x`.

## Notations

We provide a coercion to a function `R → Rᵐᵒᵖ`.

## References

* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring involution
-/


variable (R : Type _)

/-- A ring involution -/
structure RingInvo [Semiringₓ R] extends R ≃+* Rᵐᵒᵖ where
  involution' : ∀ x, (to_fun (to_fun x).unop).unop = x

namespace RingInvo

variable {R} [Semiringₓ R]

/-- Construct a ring involution from a ring homomorphism. -/
def mk' (f : R →+* Rᵐᵒᵖ) (involution : ∀ r, (f (f r).unop).unop = r) : RingInvo R :=
  { f with invFun := fun r => (f r.unop).unop, left_inv := fun r => involution r,
    right_inv := fun r => MulOpposite.unop_injective <| involution _, involution' := involution }

instance : CoeFun (RingInvo R) fun _ => R → Rᵐᵒᵖ :=
  ⟨fun f => f.toRingEquiv.toFun⟩

@[simp]
theorem to_fun_eq_coe (f : RingInvo R) : f.toFun = f :=
  rfl

@[simp]
theorem involution (f : RingInvo R) (x : R) : (f (f x).unop).unop = x :=
  f.involution' x

instance hasCoeToRingEquiv : Coe (RingInvo R) (R ≃+* Rᵐᵒᵖ) :=
  ⟨RingInvo.toRingEquiv⟩

@[norm_cast]
theorem coe_ring_equiv (f : RingInvo R) (a : R) : (f : R ≃+* Rᵐᵒᵖ) a = f a :=
  rfl

@[simp]
theorem map_eq_zero_iff (f : RingInvo R) {x : R} : f x = 0 ↔ x = 0 :=
  f.toRingEquiv.map_eq_zero_iff

end RingInvo

open RingInvo

section CommRingₓ

variable [CommRingₓ R]

/-- The identity function of a `comm_ring` is a ring involution. -/
protected def RingInvo.id : RingInvo R :=
  { RingEquiv.toOpposite R with involution' := fun r => rfl }

instance : Inhabited (RingInvo R) :=
  ⟨RingInvo.id _⟩

end CommRingₓ

