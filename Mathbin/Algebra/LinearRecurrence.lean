/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Data.Polynomial.Eval
import Mathbin.LinearAlgebra.Dimension

/-!
# Linear recurrence

Informally, a "linear recurrence" is an assertion of the form
`∀ n : ℕ, u (n + d) = a 0 * u n + a 1 * u (n+1) + ... + a (d-1) * u (n+d-1)`,
where `u` is a sequence, `d` is the *order* of the recurrence and the `a i`
are its *coefficients*.

In this file, we define the structure `linear_recurrence` so that
`linear_recurrence.mk d a` represents the above relation, and we call
a sequence `u` which verifies it a *solution* of the linear recurrence.

We prove a few basic lemmas about this concept, such as :

* the space of solutions is a submodule of `(ℕ → α)` (i.e a vector space if `α`
  is a field)
* the function that maps a solution `u` to its first `d` terms builds a `linear_equiv`
  between the solution space and `fin d → α`, aka `α ^ d`. As a consequence, two
  solutions are equal if and only if their first `d` terms are equals.
* a geometric sequence `q ^ n` is solution iff `q` is a root of a particular polynomial,
  which we call the *characteristic polynomial* of the recurrence

Of course, although we can inductively generate solutions (cf `mk_sol`), the
interesting part would be to determinate closed-forms for the solutions.
This is currently *not implemented*, as we are waiting for definition and
properties of eigenvalues and eigenvectors.

-/


noncomputable section

open Finset

open BigOperators Polynomial

/-- A "linear recurrence relation" over a commutative semiring is given by its
  order `n` and `n` coefficients. -/
structure LinearRecurrence (α : Type _) [CommSemiringₓ α] where
  order : ℕ
  coeffs : Finₓ order → α

instance (α : Type _) [CommSemiringₓ α] : Inhabited (LinearRecurrence α) :=
  ⟨⟨0, default⟩⟩

namespace LinearRecurrence

section CommSemiringₓ

variable {α : Type _} [CommSemiringₓ α] (E : LinearRecurrence α)

/-- We say that a sequence `u` is solution of `linear_recurrence order coeffs` when we have
  `u (n + order) = ∑ i : fin order, coeffs i * u (n + i)` for any `n`. -/
def IsSolution (u : ℕ → α) :=
  ∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i)

/-- A solution of a `linear_recurrence` which satisfies certain initial conditions.
  We will prove this is the only such solution. -/
def mkSol (init : Finₓ E.order → α) : ℕ → α
  | n =>
    if h : n < E.order then init ⟨n, h⟩
    else
      ∑ k : Finₓ E.order,
        have : n - E.order + k < n := by
          rw [add_commₓ, ← add_tsub_assoc_of_le (not_lt.mp h), tsub_lt_iff_left]
          · exact add_lt_add_right k.is_lt n
            
          · convert add_le_add (zero_le (k : ℕ)) (not_lt.mp h)
            simp only [← zero_addₓ]
            
        E.coeffs k * mk_sol (n - E.order + k)

/-- `E.mk_sol` indeed gives solutions to `E`. -/
theorem is_sol_mk_sol (init : Finₓ E.order → α) : E.IsSolution (E.mkSol init) := fun n => by
  rw [mk_sol] <;> simp

/-- `E.mk_sol init`'s first `E.order` terms are `init`. -/
theorem mk_sol_eq_init (init : Finₓ E.order → α) : ∀ n : Finₓ E.order, E.mkSol init n = init n := fun n => by
  rw [mk_sol]
  simp only [← n.is_lt, ← dif_pos, ← Finₓ.mk_coe, ← Finₓ.eta]

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `∀ n, u n = E.mk_sol init n`. -/
theorem eq_mk_of_is_sol_of_eq_init {u : ℕ → α} {init : Finₓ E.order → α} (h : E.IsSolution u)
    (heq : ∀ n : Finₓ E.order, u n = init n) : ∀ n, u n = E.mkSol init n
  | n =>
    if h' : n < E.order then by
      rw [mk_sol] <;> simp only [← h', ← dif_pos] <;> exact_mod_cast HEq ⟨n, h'⟩
    else by
      rw [mk_sol, ← tsub_add_cancel_of_le (le_of_not_ltₓ h'), h (n - E.order)]
      simp [← h']
      congr with k
      exact by
        have wf : n - E.order + k < n := by
          rw [add_commₓ, ← add_tsub_assoc_of_le (not_lt.mp h'), tsub_lt_iff_left]
          · exact add_lt_add_right k.is_lt n
            
          · convert add_le_add (zero_le (k : ℕ)) (not_lt.mp h')
            simp only [← zero_addₓ]
            
        rw [eq_mk_of_is_sol_of_eq_init]

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `u = E.mk_sol init`. This proves that `E.mk_sol init` is the only solution
  of `E` whose first `E.order` values are given by `init`. -/
theorem eq_mk_of_is_sol_of_eq_init' {u : ℕ → α} {init : Finₓ E.order → α} (h : E.IsSolution u)
    (heq : ∀ n : Finₓ E.order, u n = init n) : u = E.mkSol init :=
  funext (E.eq_mk_of_is_sol_of_eq_init h HEq)

/-- The space of solutions of `E`, as a `submodule` over `α` of the module `ℕ → α`. -/
def solSpace : Submodule α (ℕ → α) where
  Carrier := { u | E.IsSolution u }
  zero_mem' := fun n => by
    simp
  add_mem' := fun u v hu hv n => by
    simp [← mul_addₓ, ← sum_add_distrib, ← hu n, ← hv n]
  smul_mem' := fun a u hu n => by
    simp [← hu n, ← mul_sum] <;> congr <;> ext <;> ac_rfl

/-- Defining property of the solution space : `u` is a solution
  iff it belongs to the solution space. -/
theorem is_sol_iff_mem_sol_space (u : ℕ → α) : E.IsSolution u ↔ u ∈ E.solSpace :=
  Iff.rfl

/-- The function that maps a solution `u` of `E` to its first
  `E.order` terms as a `linear_equiv`. -/
def toInit : E.solSpace ≃ₗ[α] Finₓ E.order → α where
  toFun := fun u x => (u : ℕ → α) x
  map_add' := fun u v => by
    ext
    simp
  map_smul' := fun a u => by
    ext
    simp
  invFun := fun u => ⟨E.mkSol u, E.is_sol_mk_sol u⟩
  left_inv := fun u => by
    ext n <;> symm <;> apply E.eq_mk_of_is_sol_of_eq_init u.2 <;> intro k <;> rfl
  right_inv := fun u => Function.funext_iffₓ.mpr fun n => E.mk_sol_eq_init u n

/-- Two solutions are equal iff they are equal on `range E.order`. -/
theorem sol_eq_of_eq_init (u v : ℕ → α) (hu : E.IsSolution u) (hv : E.IsSolution v) :
    u = v ↔ Set.EqOn u v ↑(range E.order) := by
  refine' Iff.intro (fun h x hx => h ▸ rfl) _
  intro h
  set u' : ↥E.sol_space := ⟨u, hu⟩
  set v' : ↥E.sol_space := ⟨v, hv⟩
  change u'.val = v'.val
  suffices h' : u' = v'
  exact h' ▸ rfl
  rw [← E.to_init.to_equiv.apply_eq_iff_eq, LinearEquiv.coe_to_equiv]
  ext x
  exact_mod_cast h (mem_range.mpr x.2)

/-! `E.tuple_succ` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
  where `n := E.order`. This operation is quite useful for determining closed-form
  solutions of `E`. -/


/-- `E.tuple_succ` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
  where `n := E.order`. -/
def tupleSucc : (Finₓ E.order → α) →ₗ[α] Finₓ E.order → α where
  toFun := fun X i => if h : (i : ℕ) + 1 < E.order then X ⟨i + 1, h⟩ else ∑ i, E.coeffs i * X i
  map_add' := fun x y => by
    ext i
    split_ifs <;> simp [← h, ← mul_addₓ, ← sum_add_distrib]
  map_smul' := fun x y => by
    ext i
    split_ifs <;> simp [← h, ← mul_sum]
    exact
      sum_congr rfl fun x _ => by
        ac_rfl

end CommSemiringₓ

section Field

variable {α : Type _} [Field α] (E : LinearRecurrence α)

/-- The dimension of `E.sol_space` is `E.order`. -/
theorem sol_space_dim : Module.rank α E.solSpace = E.order :=
  @dim_fin_fun α _ E.order ▸ E.toInit.dim_eq

end Field

section CommRingₓ

variable {α : Type _} [CommRingₓ α] (E : LinearRecurrence α)

/-- The characteristic polynomial of `E` is
`X ^ E.order - ∑ i : fin E.order, (E.coeffs i) * X ^ i`. -/
def charPoly : α[X] :=
  Polynomial.monomial E.order 1 - ∑ i : Finₓ E.order, Polynomial.monomial i (E.coeffs i)

/-- The geometric sequence `q^n` is a solution of `E` iff
  `q` is a root of `E`'s characteristic polynomial. -/
theorem geom_sol_iff_root_char_poly (q : α) : (E.IsSolution fun n => q ^ n) ↔ E.charPoly.IsRoot q := by
  rw [char_poly, Polynomial.IsRoot.def, Polynomial.eval]
  simp only [← Polynomial.eval₂_finset_sum, ← one_mulₓ, ← RingHom.id_apply, ← Polynomial.eval₂_monomial, ←
    Polynomial.eval₂_sub]
  constructor
  · intro h
    simpa [← sub_eq_zero] using h 0
    
  · intro h n
    simp only [← pow_addₓ, ← sub_eq_zero.mp h, ← mul_sum]
    exact
      sum_congr rfl fun _ _ => by
        ring
    

end CommRingₓ

end LinearRecurrence

