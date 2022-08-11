/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.Data.Complex.Basic
import Mathbin.Data.Real.Cardinality

/-!
# The cardinality of the complex numbers

This file shows that the complex numbers have cardinality continuum, i.e. `#ℂ = 𝔠`.
-/


open Cardinal Set

open Cardinal

/-- The cardinality of the complex numbers, as a type. -/
@[simp]
theorem mk_complex : # ℂ = 𝔠 := by
  rw [mk_congr Complex.equivRealProd, mk_prod, lift_id, mk_real, continuum_mul_self]

/-- The cardinality of the complex numbers, as a set. -/
@[simp]
theorem mk_univ_complex : # (Set.Univ : Set ℂ) = 𝔠 := by
  rw [mk_univ, mk_complex]

/-- The complex numbers are not countable. -/
theorem not_countable_complex : ¬(Set.Univ : Set ℂ).Countable := by
  rw [← mk_set_le_aleph_0, not_leₓ, mk_univ_complex]
  apply cantor

