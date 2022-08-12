/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.Algebra.Subalgebra.Basic

/-!
# Star subalgebras

A *-subalgebra is a subalgebra of a *-algebra which is closed under *.

The centralizer of a *-closed set is a *-subalgebra.
-/


universe u v

/-- A *-subalgebra is a subalgebra of a *-algebra which is closed under *. -/
structure StarSubalgebra (R : Type u) (A : Type v) [CommSemiringₓ R] [StarRing R] [Semiringₓ A] [StarRing A]
  [Algebra R A] [StarModule R A] extends Subalgebra R A : Type v where
  star_mem' {a} : a ∈ carrier → star a ∈ carrier

namespace StarSubalgebra

/-- Forgetting that a *-subalgebra is closed under *.
-/
add_decl_doc StarSubalgebra.toSubalgebra

variable (R : Type u) (A : Type v) [CommSemiringₓ R] [StarRing R] [Semiringₓ A] [StarRing A] [Algebra R A]
  [StarModule R A]

instance : SetLike (StarSubalgebra R A) A :=
  ⟨StarSubalgebra.Carrier, fun p q h => by
    cases p <;> cases q <;> congr⟩

instance : HasTop (StarSubalgebra R A) :=
  ⟨{ (⊤ : Subalgebra R A) with
      star_mem' := by
        tidy }⟩

instance : Inhabited (StarSubalgebra R A) :=
  ⟨⊤⟩

section Centralizer

variable {A}

/-- The centralizer, or commutant, of a *-closed set as star subalgebra. -/
def centralizer (s : Set A) (w : ∀ a : A, a ∈ s → star a ∈ s) : StarSubalgebra R A :=
  { Subalgebra.centralizer R s with
    star_mem' := fun x xm y hy => by
      simpa using congr_arg star (xm _ (w _ hy)).symm }

@[simp]
theorem coe_centralizer (s : Set A) (w : ∀ a : A, a ∈ s → star a ∈ s) : (centralizer R s w : Set A) = s.Centralizer :=
  rfl

theorem mem_centralizer_iff {s : Set A} {w} {z : A} : z ∈ centralizer R s w ↔ ∀, ∀ g ∈ s, ∀, g * z = z * g :=
  Iff.rfl

theorem centralizer_le (s t : Set A) (ws : ∀ a : A, a ∈ s → star a ∈ s) (wt : ∀ a : A, a ∈ t → star a ∈ t) (h : s ⊆ t) :
    centralizer R t wt ≤ centralizer R s ws :=
  Set.centralizer_subset h

end Centralizer

end StarSubalgebra

