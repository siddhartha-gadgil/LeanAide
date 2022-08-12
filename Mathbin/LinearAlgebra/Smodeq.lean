/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Data.Polynomial.Eval
import Mathbin.RingTheory.Ideal.Quotient

/-!
# modular equivalence for submodule
-/


open Submodule

open Polynomial

variable {R : Type _} [Ringₓ R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M] (U U₁ U₂ : Submodule R M)

variable {x x₁ x₂ y y₁ y₂ z z₁ z₂ : M}

variable {N : Type _} [AddCommGroupₓ N] [Module R N] (V V₁ V₂ : Submodule R N)

/-- A predicate saying two elements of a module are equivalent modulo a submodule. -/
def Smodeq (x y : M) : Prop :=
  (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y

-- mathport name: «expr ≡ [SMOD ]»
notation:50 x " ≡ " y " [SMOD " N "]" => Smodeq N x y

variable {U U₁ U₂}

protected theorem Smodeq.def : x ≡ y [SMOD U] ↔ (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y :=
  Iff.rfl

namespace Smodeq

theorem sub_mem : x ≡ y [SMOD U] ↔ x - y ∈ U := by
  rw [Smodeq.def, Submodule.Quotient.eq]

@[simp]
theorem top : x ≡ y [SMOD (⊤ : Submodule R M)] :=
  (Submodule.Quotient.eq ⊤).2 mem_top

@[simp]
theorem bot : x ≡ y [SMOD (⊥ : Submodule R M)] ↔ x = y := by
  rw [Smodeq.def, Submodule.Quotient.eq, mem_bot, sub_eq_zero]

@[mono]
theorem mono (HU : U₁ ≤ U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD U₂] :=
  (Submodule.Quotient.eq U₂).2 <| HU <| (Submodule.Quotient.eq U₁).1 hxy

@[refl]
theorem refl : x ≡ x [SMOD U] :=
  Eq.refl _

@[symm]
theorem symm (hxy : x ≡ y [SMOD U]) : y ≡ x [SMOD U] :=
  hxy.symm

@[trans]
theorem trans (hxy : x ≡ y [SMOD U]) (hyz : y ≡ z [SMOD U]) : x ≡ z [SMOD U] :=
  hxy.trans hyz

theorem add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ + x₂ ≡ y₁ + y₂ [SMOD U] := by
  rw [Smodeq.def] at hxy₁ hxy₂⊢
  simp_rw [quotient.mk_add, hxy₁, hxy₂]

theorem smul (hxy : x ≡ y [SMOD U]) (c : R) : c • x ≡ c • y [SMOD U] := by
  rw [Smodeq.def] at hxy⊢
  simp_rw [quotient.mk_smul, hxy]

theorem zero : x ≡ 0 [SMOD U] ↔ x ∈ U := by
  rw [Smodeq.def, Submodule.Quotient.eq, sub_zero]

theorem map (hxy : x ≡ y [SMOD U]) (f : M →ₗ[R] N) : f x ≡ f y [SMOD U.map f] :=
  (Submodule.Quotient.eq _).2 <| f.map_sub x y ▸ mem_map_of_mem <| (Submodule.Quotient.eq _).1 hxy

theorem comap {f : M →ₗ[R] N} (hxy : f x ≡ f y [SMOD V]) : x ≡ y [SMOD V.comap f] :=
  (Submodule.Quotient.eq _).2 <| show f (x - y) ∈ V from (f.map_sub x y).symm ▸ (Submodule.Quotient.eq _).1 hxy

theorem eval {R : Type _} [CommRingₓ R] {I : Ideal R} {x y : R} (h : x ≡ y [SMOD I]) (f : R[X]) :
    f.eval x ≡ f.eval y [SMOD I] := by
  rw [Smodeq.def] at h⊢
  show Ideal.Quotient.mk I (f.eval x) = Ideal.Quotient.mk I (f.eval y)
  change Ideal.Quotient.mk I x = Ideal.Quotient.mk I y at h
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply, h]

end Smodeq

