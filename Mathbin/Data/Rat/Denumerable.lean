/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Denumerability of ℚ

This file proves that ℚ is infinite, denumerable, and deduces that it has cardinality `omega`.
-/


namespace Rat

open Denumerable

instance : Infinite ℚ :=
  Infinite.of_injective (coe : ℕ → ℚ) Nat.cast_injective

private def denumerable_aux : ℚ ≃ { x : ℤ × ℕ // 0 < x.2 ∧ x.1.natAbs.Coprime x.2 } where
  toFun := fun x => ⟨⟨x.1, x.2⟩, x.3, x.4⟩
  invFun := fun x => ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _, _⟩ => rfl

/-- **Denumerability of the Rational Numbers** -/
instance : Denumerable ℚ := by
  let T := { x : ℤ × ℕ // 0 < x.2 ∧ x.1.natAbs.Coprime x.2 }
  let this : Infinite T := Infinite.of_injective _ denumerable_aux.injective
  let this : Encodable T := Subtype.encodable
  let this : Denumerable T := of_encodable_of_infinite T
  exact Denumerable.ofEquiv T denumerable_aux

end Rat

open Cardinal

theorem Cardinal.mk_rat : # ℚ = ℵ₀ := by
  simp

