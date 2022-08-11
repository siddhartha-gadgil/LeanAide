/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathbin.Algebra.Hom.Aut
import Mathbin.Algebra.Ring.Equiv

/-!
# Ring automorphisms

This file defines the automorphism group structure on `ring_aut R := ring_equiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, but not with
`category_theory.comp`.

This file is kept separate from `data/equiv/ring` so that `group_theory.perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

ring_aut
-/


/-- The group of ring automorphisms. -/
@[reducible]
def RingAut (R : Type _) [Mul R] [Add R] :=
  RingEquiv R R

namespace RingAut

variable (R : Type _) [Mul R] [Add R]

/-- The group operation on automorphisms of a ring is defined by
`λ g h, ring_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance : Groupₓ (RingAut R) := by
  refine_struct
      { mul := fun g h => RingEquiv.trans h g, one := RingEquiv.refl R, inv := RingEquiv.symm, div := _,
        npow := @npowRec _ ⟨RingEquiv.refl R⟩ ⟨fun g h => RingEquiv.trans h g⟩,
        zpow := @zpowRec _ ⟨RingEquiv.refl R⟩ ⟨fun g h => RingEquiv.trans h g⟩ ⟨RingEquiv.symm⟩ } <;>
    intros <;>
      ext <;>
        try
            rfl <;>
          apply Equivₓ.left_inv

instance : Inhabited (RingAut R) :=
  ⟨1⟩

/-- Monoid homomorphism from ring automorphisms to additive automorphisms. -/
def toAddAut : RingAut R →* AddAut R := by
  refine_struct { toFun := RingEquiv.toAddEquiv } <;> intros <;> rfl

/-- Monoid homomorphism from ring automorphisms to multiplicative automorphisms. -/
def toMulAut : RingAut R →* MulAut R := by
  refine_struct { toFun := RingEquiv.toMulEquiv } <;> intros <;> rfl

/-- Monoid homomorphism from ring automorphisms to permutations. -/
def toPerm : RingAut R →* Equivₓ.Perm R := by
  refine_struct { toFun := RingEquiv.toEquiv } <;> intros <;> rfl

end RingAut

