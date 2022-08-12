/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Data.List.Nodup

/-!
# Finite products of types

This file defines the product of types over a list. For `l : list ι` and `α : ι → Type*` we define
`list.tprod α l = l.foldr (λ i β, α i × β) punit`.
This type should not be used if `Π i, α i` or `Π i ∈ l, α i` can be used instead
(in the last expression, we could also replace the list `l` by a set or a finset).
This type is used as an intermediary between binary products and finitary products.
The application of this type is finitary product measures, but it could be used in any
construction/theorem that is easier to define/prove on binary products than on finitary products.

* Once we have the construction on binary products (like binary product measures in
  `measure_theory.prod`), we can easily define a finitary version on the type `tprod l α`
  by iterating. Properties can also be easily extended from the binary case to the finitary case
  by iterating.
* Then we can use the equivalence `list.tprod.pi_equiv_tprod` below (or enhanced versions of it,
  like a `measurable_equiv` for product measures) to get the construction on `Π i : ι, α i`, at
  least when assuming `[fintype ι] [encodable ι]` (using `encodable.sorted_univ`).
  Using `local attribute [instance] fintype.to_encodable` we can get rid of the argument
  `[encodable ι]`.

## Main definitions

* We have the equivalence `tprod.pi_equiv_tprod : (Π i, α i) ≃ tprod α l`
  if `l` contains every element of `ι` exactly once.
* The product of sets is `set.tprod : (Π i, set (α i)) → set (tprod α l)`.
-/


open List Function

variable {ι : Type _} {α : ι → Type _} {i j : ι} {l : List ι} {f : ∀ i, α i}

namespace List

variable (α)

/-- The product of a family of types over a list. -/
def Tprod (l : List ι) : Type _ :=
  l.foldr (fun i β => α i × β) PUnit

variable {α}

namespace Tprod

open List

/-- Turning a function `f : Π i, α i` into an element of the iterated product `tprod α l`. -/
protected def mkₓ : ∀ (l : List ι) (f : ∀ i, α i), Tprod α l
  | [] => fun f => PUnit.unit
  | i :: is => fun f => (f i, mk is f)

instance [∀ i, Inhabited (α i)] : Inhabited (Tprod α l) :=
  ⟨Tprod.mkₓ l default⟩

@[simp]
theorem fst_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (Tprod.mkₓ (i :: l) f).1 = f i :=
  rfl

@[simp]
theorem snd_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (Tprod.mkₓ (i :: l) f).2 = Tprod.mkₓ l f :=
  rfl

variable [DecidableEq ι]

/-- Given an element of the iterated product `l.prod α`, take a projection into direction `i`.
  If `i` appears multiple times in `l`, this chooses the first component in direction `i`. -/
protected def elimₓ : ∀ {l : List ι} (v : Tprod α l) {i : ι} (hi : i ∈ l), α i
  | i :: is, v, j, hj =>
    if hji : j = i then by
      subst hji
      exact v.1
    else elim v.2 (hj.resolve_left hji)

@[simp]
theorem elim_self (v : Tprod α (i :: l)) : v.elim (l.mem_cons_self i) = v.1 := by
  simp [← tprod.elim]

@[simp]
theorem elim_of_ne (hj : j ∈ i :: l) (hji : j ≠ i) (v : Tprod α (i :: l)) :
    v.elim hj = Tprod.elimₓ v.2 (hj.resolve_left hji) := by
  simp [← tprod.elim, ← hji]

@[simp]
theorem elim_of_mem (hl : (i :: l).Nodup) (hj : j ∈ l) (v : Tprod α (i :: l)) :
    v.elim (mem_cons_of_memₓ _ hj) = Tprod.elimₓ v.2 hj := by
  apply elim_of_ne
  rintro rfl
  exact hl.not_mem hj

theorem elim_mk : ∀ (l : List ι) (f : ∀ i, α i) {i : ι} (hi : i ∈ l), (Tprod.mkₓ l f).elim hi = f i
  | i :: is, f, j, hj => by
    by_cases' hji : j = i
    · subst hji
      simp
      
    · rw [elim_of_ne _ hji, snd_mk, elim_mk]
      

@[ext]
theorem ext : ∀ {l : List ι} (hl : l.Nodup) {v w : Tprod α l} (hvw : ∀ (i) (hi : i ∈ l), v.elim hi = w.elim hi), v = w
  | [], hl, v, w, hvw => PUnit.extₓ
  | i :: is, hl, v, w, hvw => by
    ext
    rw [← elim_self v, hvw, elim_self]
    refine' ext (nodup_cons.mp hl).2 fun j hj => _
    rw [← elim_of_mem hl, hvw, elim_of_mem hl]

/-- A version of `tprod.elim` when `l` contains all elements. In this case we get a function into
  `Π i, α i`. -/
@[simp]
protected def elim' (h : ∀ i, i ∈ l) (v : Tprod α l) (i : ι) : α i :=
  v.elim (h i)

theorem mk_elim (hnd : l.Nodup) (h : ∀ i, i ∈ l) (v : Tprod α l) : Tprod.mkₓ l (v.elim' h) = v :=
  Tprod.ext hnd fun i hi => by
    simp [← elim_mk]

/-- Pi-types are equivalent to iterated products. -/
def piEquivTprod (hnd : l.Nodup) (h : ∀ i, i ∈ l) : (∀ i, α i) ≃ Tprod α l :=
  ⟨Tprod.mkₓ l, Tprod.elim' h, fun f => funext fun i => elim_mk l f (h i), mk_elim hnd h⟩

end Tprod

end List

namespace Set

open List

/-- A product of sets in `tprod α l`. -/
@[simp]
protected def Tprodₓ : ∀ (l : List ι) (t : ∀ i, Set (α i)), Set (Tprod α l)
  | [], t => Univ
  | i :: is, t => t i ×ˢ tprod is t

theorem mk_preimage_tprod : ∀ (l : List ι) (t : ∀ i, Set (α i)), Tprod.mkₓ l ⁻¹' Set.Tprodₓ l t = { i | i ∈ l }.pi t
  | [], t => by
    simp [← Set.Tprodₓ]
  | i :: l, t => by
    ext f
    have : f ∈ tprod.mk l ⁻¹' Set.Tprodₓ l t ↔ f ∈ { x | x ∈ l }.pi t := by
      rw [mk_preimage_tprod l t]
    change tprod.mk l f ∈ Set.Tprodₓ l t ↔ ∀ i : ι, i ∈ l → f i ∈ t i at this
    -- `simp [set.tprod, tprod.mk, this]` can close this goal but is slow.
    rw [Set.Tprodₓ, tprod.mk, mem_preimage, mem_pi, prod_mk_mem_set_prod_eq]
    simp_rw [mem_set_of_eq, mem_cons_iff]
    rw [forall_eq_or_imp, And.congr_right_iff]
    exact fun _ => this

theorem elim_preimage_pi [DecidableEq ι] {l : List ι} (hnd : l.Nodup) (h : ∀ i, i ∈ l) (t : ∀ i, Set (α i)) :
    Tprod.elim' h ⁻¹' Pi Univ t = Set.Tprodₓ l t := by
  have : { i | i ∈ l } = univ := by
    ext i
    simp [← h]
  rw [← this, ← mk_preimage_tprod, preimage_preimage]
  convert preimage_id
  simp [← tprod.mk_elim hnd h, ← id_def]

end Set

