/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.Algebra.CharP.Basic

/-!
# Matrices in prime characteristic
-/


open Matrix

variable {n : Type _} [Fintype n] {R : Type _} [Ringₓ R]

instance Matrix.char_p [DecidableEq n] [Nonempty n] (p : ℕ) [CharP R p] : CharP (Matrix n n R) p :=
  ⟨by
    intro k
    rw [← CharP.cast_eq_zero_iff R p k, ← Nat.cast_zeroₓ, ← map_nat_cast <| scalar n]
    convert scalar_inj
    · simp
      
    · assumption
      ⟩

