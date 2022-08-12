/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet
-/
import Mathbin.Order.Ideal

/-!
# Order filters

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections
require more structure, such as a bottom element, a top element, or
a join-semilattice structure.

- `order.pfilter P`: The type of nonempty, downward directed, upward closed
               subsets of `P`. This is dual to `order.ideal`, so it
               simply wraps `order.ideal Pᵒᵈ`.
- `order.is_pfilter P`: a predicate for when a `set P` is a filter.


Note the relation between `order/filter` and `order/pfilter`: for any
type `α`, `filter α` represents the same mathematical object as
`pfilter (set α)`.

## References

- <https://en.wikipedia.org/wiki/Filter_(mathematics)>

## Tags

pfilter, filter, ideal, dual

-/


namespace Order

variable {P : Type _}

/-- A filter on a preorder `P` is a subset of `P` that is
  - nonempty
  - downward directed
  - upward closed. -/
structure Pfilter (P) [Preorderₓ P] where
  dual : Ideal Pᵒᵈ

/-- A predicate for when a subset of `P` is a filter. -/
def IsPfilter [Preorderₓ P] (F : Set P) : Prop :=
  @IsIdeal Pᵒᵈ _ F

theorem IsPfilter.of_def [Preorderₓ P] {F : Set P} (nonempty : F.Nonempty) (directed : DirectedOn (· ≥ ·) F)
    (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) : IsPfilter F :=
  ⟨fun _ _ _ _ => mem_of_le ‹_› ‹_›, Nonempty, Directed⟩

/-- Create an element of type `order.pfilter` from a set satisfying the predicate
`order.is_pfilter`. -/
def IsPfilter.toPfilter [Preorderₓ P] {F : Set P} (h : IsPfilter F) : Pfilter P :=
  ⟨h.toIdeal⟩

namespace Pfilter

section Preorderₓ

variable [Preorderₓ P] {x y : P} (F s t : Pfilter P)

instance [Inhabited P] : Inhabited (Pfilter P) :=
  ⟨⟨default⟩⟩

/-- A filter on `P` is a subset of `P`. -/
instance : Coe (Pfilter P) (Set P) :=
  ⟨fun F => F.dual.Carrier⟩

/-- For the notation `x ∈ F`. -/
instance : HasMem P (Pfilter P) :=
  ⟨fun x F => x ∈ (F : Set P)⟩

@[simp]
theorem mem_coe : x ∈ (F : Set P) ↔ x ∈ F :=
  iff_of_eq rfl

theorem is_pfilter : IsPfilter (F : Set P) :=
  F.dual.IsIdeal

theorem nonempty : (F : Set P).Nonempty :=
  F.dual.Nonempty

theorem directed : DirectedOn (· ≥ ·) (F : Set P) :=
  F.dual.Directed

theorem mem_of_le {F : Pfilter P} : x ≤ y → x ∈ F → y ∈ F := fun h => F.dual.lower h

/-- Two filters are equal when their underlying sets are equal. -/
@[ext]
theorem ext (h : (s : Set P) = t) : s = t := by
  cases s
  cases t
  exact congr_arg _ (ideal.ext h)

/-- The partial ordering by subset inclusion, inherited from `set P`. -/
instance : PartialOrderₓ (Pfilter P) :=
  PartialOrderₓ.lift coe ext

@[trans]
theorem mem_of_mem_of_le {F G : Pfilter P} : x ∈ F → F ≤ G → x ∈ G :=
  ideal.mem_of_mem_of_le

/-- The smallest filter containing a given element. -/
def principal (p : P) : Pfilter P :=
  ⟨Ideal.principal p⟩

@[simp]
theorem mem_def (x : P) (I : Ideal Pᵒᵈ) : x ∈ (⟨I⟩ : Pfilter P) ↔ OrderDual.toDual x ∈ I :=
  Iff.rfl

@[simp]
theorem principal_le_iff {F : Pfilter P} : principal x ≤ F ↔ x ∈ F :=
  ideal.principal_le_iff

@[simp]
theorem mem_principal : x ∈ principal y ↔ y ≤ x :=
  ideal.mem_principal

-- defeq abuse
theorem antitone_principal : Antitone (principal : P → Pfilter P) := by
  delta' Antitone <;> simp

theorem principal_le_principal_iff {p q : P} : principal q ≤ principal p ↔ p ≤ q := by
  simp

end Preorderₓ

section OrderTop

variable [Preorderₓ P] [OrderTop P] {F : Pfilter P}

/-- A specific witness of `pfilter.nonempty` when `P` has a top element. -/
@[simp]
theorem top_mem : ⊤ ∈ F :=
  Ideal.bot_mem _

/-- There is a bottom filter when `P` has a top element. -/
instance : OrderBot (Pfilter P) where
  bot := ⟨⊥⟩
  bot_le := fun F => (bot_le : ⊥ ≤ F.dual)

end OrderTop

/-- There is a top filter when `P` has a bottom element. -/
instance {P} [Preorderₓ P] [OrderBot P] : OrderTop (Pfilter P) where
  top := ⟨⊤⟩
  le_top := fun F => (le_top : F.dual ≤ ⊤)

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {F : Pfilter P}

/-- A specific witness of `pfilter.directed` when `P` has meets. -/
theorem inf_mem (hx : x ∈ F) (hy : y ∈ F) : x⊓y ∈ F :=
  Ideal.sup_mem hx hy

@[simp]
theorem inf_mem_iff : x⊓y ∈ F ↔ x ∈ F ∧ y ∈ F :=
  ideal.sup_mem_iff

end SemilatticeInf

section CompleteSemilatticeInf

variable [CompleteSemilatticeInf P] {F : Pfilter P}

theorem Inf_gc :
    GaloisConnection (fun x => OrderDual.toDual (principal x)) fun F => inf (OrderDual.ofDual F : Pfilter P) :=
  fun x F => by
  simp
  rfl

/-- If a poset `P` admits arbitrary `Inf`s, then `principal` and `Inf` form a Galois coinsertion. -/
def infGi :
    GaloisCoinsertion (fun x => OrderDual.toDual (principal x)) fun F => inf (OrderDual.ofDual F : Pfilter P) where
  choice := fun F _ => inf (id F : Pfilter P)
  gc := Inf_gc
  u_l_le := fun s => Inf_le <| mem_principal.2 <| le_reflₓ s
  choice_eq := fun _ _ => rfl

end CompleteSemilatticeInf

end Pfilter

end Order

