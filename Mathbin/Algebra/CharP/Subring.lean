/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.RingTheory.Subring.Basic

/-!
# Characteristic of subrings
-/


universe u v

namespace CharP

instance subsemiring (R : Type u) [Semiringₓ R] (p : ℕ) [CharP R p] (S : Subsemiring R) : CharP S p :=
  ⟨fun x =>
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h =>
          Subtype.eq <|
            show S.Subtype x = 0 by
              rw [map_nat_cast, h],
          fun h =>
          map_nat_cast S.Subtype x ▸ by
            rw [h, RingHom.map_zero]⟩⟩

instance subring (R : Type u) [Ringₓ R] (p : ℕ) [CharP R p] (S : Subring R) : CharP S p :=
  ⟨fun x =>
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h =>
          Subtype.eq <|
            show S.Subtype x = 0 by
              rw [map_nat_cast, h],
          fun h =>
          map_nat_cast S.Subtype x ▸ by
            rw [h, RingHom.map_zero]⟩⟩

instance subring' (R : Type u) [CommRingₓ R] (p : ℕ) [CharP R p] (S : Subring R) : CharP S p :=
  CharP.subring R p S

end CharP

