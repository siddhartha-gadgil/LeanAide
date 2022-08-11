/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathbin.RepresentationTheory.FdRep
import Mathbin.LinearAlgebra.Trace
import Mathbin.RepresentationTheory.Basic
import Mathbin.RepresentationTheory.Invariants

/-!
# Characters of representations

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

# TODO
* Once we have the monoidal closed structure on `fdRep k G` and a better API for the rigid
structure, `char_dual` and `char_lin_hom` should probably be stated in terms of `Vᘁ` and `ihom V W`.
-/


noncomputable section

universe u

open LinearMap CategoryTheory.MonoidalCategory Representation FiniteDimensional

open BigOperators

variable {k G : Type u} [Field k]

namespace FdRep

section Monoidₓ

variable [Monoidₓ G]

/-- The character of a representation `V : fdRep k G` is the function associating to `g : G` the
trace of the linear map `V.ρ g`.-/
def character (V : FdRep k G) (g : G) :=
  LinearMap.trace k V (V.ρ g)

theorem char_mul_comm (V : FdRep k G) (g : G) (h : G) : V.character (h * g) = V.character (g * h) := by
  simp only [← trace_mul_comm, ← character, ← map_mul]

@[simp]
theorem char_one (V : FdRep k G) : V.character 1 = FiniteDimensional.finrank k V := by
  simp only [← character, ← map_one, ← trace_one]

/-- The character is multiplicative under the tensor product. -/
@[simp]
theorem char_tensor (V W : FdRep k G) : (V ⊗ W).character = V.character * W.character := by
  ext g
  convert trace_tensor_product' (V.ρ g) (W.ρ g)

/-- The character of isomorphic representations is the same. -/
theorem char_iso {V W : FdRep k G} (i : V ≅ W) : V.character = W.character := by
  ext g
  simp only [← character, ← FdRep.Iso.conj_ρ i]
  exact (trace_conj' (V.ρ g) _).symm

end Monoidₓ

section Groupₓ

variable [Groupₓ G]

/-- The character of a representation is constant on conjugacy classes. -/
@[simp]
theorem char_conj (V : FdRep k G) (g : G) (h : G) : V.character (h * g * h⁻¹) = V.character g := by
  rw [char_mul_comm, inv_mul_cancel_leftₓ]

@[simp]
theorem char_dual (V : FdRep k G) (g : G) : (of (dual V.ρ)).character g = V.character g⁻¹ :=
  trace_transpose' (V.ρ g⁻¹)

@[simp]
theorem char_lin_hom (V W : FdRep k G) (g : G) : (of (linHom V.ρ W.ρ)).character g = V.character g⁻¹ * W.character g :=
  by
  rw [← char_iso (dual_tensor_iso_lin_hom _ _), char_tensor, Pi.mul_apply, char_dual]
  rfl

variable [Fintype G] [Invertible (Fintype.card G : k)]

theorem average_char_eq_finrank_invariants (V : FdRep k G) :
    (⅟ (Fintype.card G : k) • ∑ g : G, V.character g) = finrank k (invariants V.ρ) := by
  rw [← (is_proj_average_map V.ρ).trace]
  simp [← character, ← GroupAlgebra.average, ← _root_.map_sum]

end Groupₓ

end FdRep

