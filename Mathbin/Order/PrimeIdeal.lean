/-
Copyright (c) 2021 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar
-/
import Mathbin.Order.Ideal
import Mathbin.Order.Pfilter

/-!
# Prime ideals

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more
structure, such as a bottom element, a top element, or a join-semilattice structure.

- `order.ideal.prime_pair`: A pair of an `ideal` and a `pfilter` which form a partition of `P`.
  This is useful as giving the data of a prime ideal is the same as giving the data of a prime
  filter.
- `order.ideal.is_prime`: a predicate for prime ideals. Dual to the notion of a prime filter.
- `order.pfilter.is_prime`: a predicate for prime filters. Dual to the notion of a prime ideal.

## References

- <https://en.wikipedia.org/wiki/Ideal_(order_theory)>

## Tags

ideal, prime

-/


open Order.Pfilter

namespace Order

variable {P : Type _}

namespace Ideal

/-- A pair of an `ideal` and a `pfilter` which form a partition of `P`.
-/
@[nolint has_inhabited_instance]
structure PrimePair (P : Type _) [Preorderₓ P] where
  i : Ideal P
  f : Pfilter P
  is_compl_I_F : IsCompl (I : Set P) F

namespace PrimePair

variable [Preorderₓ P] (IF : PrimePair P)

theorem compl_I_eq_F : (IF.i : Set P)ᶜ = IF.f :=
  IF.is_compl_I_F.compl_eq

theorem compl_F_eq_I : (IF.f : Set P)ᶜ = IF.i :=
  IF.is_compl_I_F.eq_compl.symm

theorem I_is_proper : IsProper IF.i := by
  cases IF.F.nonempty
  apply is_proper_of_not_mem (_ : w ∉ IF.I)
  rwa [← IF.compl_I_eq_F] at h

theorem disjoint : Disjoint (IF.i : Set P) IF.f :=
  IF.is_compl_I_F.Disjoint

theorem I_union_F : (IF.i : Set P) ∪ IF.f = Set.Univ :=
  IF.is_compl_I_F.sup_eq_top

theorem F_union_I : (IF.f : Set P) ∪ IF.i = Set.Univ :=
  IF.is_compl_I_F.symm.sup_eq_top

end PrimePair

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mk_iff]
class IsPrime [Preorderₓ P] (I : Ideal P) extends IsProper I : Prop where
  compl_filter : IsPfilter ((I : Set P)ᶜ)

section Preorderₓ

variable [Preorderₓ P]

/-- Create an element of type `order.ideal.prime_pair` from an ideal satisfying the predicate
`order.ideal.is_prime`. -/
def IsPrime.toPrimePair {I : Ideal P} (h : IsPrime I) : PrimePair P :=
  { i, f := h.compl_filter.toPfilter, is_compl_I_F := is_compl_compl }

theorem PrimePair.I_is_prime (IF : PrimePair P) : IsPrime IF.i :=
  { IF.I_is_proper with
    compl_filter := by
      rw [IF.compl_I_eq_F]
      exact IF.F.is_pfilter }

end Preorderₓ

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {I : Ideal P}

theorem IsPrime.mem_or_mem (hI : IsPrime I) {x y : P} : x⊓y ∈ I → x ∈ I ∨ y ∈ I := by
  contrapose!
  let F := hI.compl_filter.to_pfilter
  show x ∈ F ∧ y ∈ F → x⊓y ∈ F
  exact fun h => inf_mem h.1 h.2

theorem IsPrime.of_mem_or_mem [IsProper I] (hI : ∀ {x y : P}, x⊓y ∈ I → x ∈ I ∨ y ∈ I) : IsPrime I := by
  rw [is_prime_iff]
  use ‹_›
  apply is_pfilter.of_def
  · exact Set.nonempty_compl.2 (I.is_proper_iff.1 ‹_›)
    
  · intro x _ y _
    refine' ⟨x⊓y, _, inf_le_left, inf_le_right⟩
    have := mt hI
    tauto!
    
  · exact @mem_compl_of_ge _ _ _
    

theorem is_prime_iff_mem_or_mem [IsProper I] : IsPrime I ↔ ∀ {x y : P}, x⊓y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨IsPrime.mem_or_mem, IsPrime.of_mem_or_mem⟩

end SemilatticeInf

section DistribLattice

variable [DistribLattice P] {I : Ideal P}

instance (priority := 100) IsMaximal.is_prime [IsMaximal I] : IsPrime I := by
  rw [is_prime_iff_mem_or_mem]
  intro x y
  contrapose!
  rintro ⟨hx, hynI⟩ hxy
  apply hynI
  let J := I⊔principal x
  have hJuniv : (J : Set P) = Set.Univ := is_maximal.maximal_proper (lt_sup_principal_of_not_mem ‹_›)
  have hyJ : y ∈ ↑J := set.eq_univ_iff_forall.mp hJuniv y
  rw [coe_sup_eq] at hyJ
  rcases hyJ with ⟨a, ha, b, hb, hy⟩
  rw [hy]
  refine' sup_mem ha (I.lower (le_inf hb _) hxy)
  rw [hy]
  exact le_sup_right

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra P] {x : P} {I : Ideal P}

theorem IsPrime.mem_or_compl_mem (hI : IsPrime I) : x ∈ I ∨ xᶜ ∈ I := by
  apply hI.mem_or_mem
  rw [inf_compl_eq_bot]
  exact I.bot_mem

theorem IsPrime.mem_compl_of_not_mem (hI : IsPrime I) (hxnI : x ∉ I) : xᶜ ∈ I :=
  hI.mem_or_compl_mem.resolve_left hxnI

theorem is_prime_of_mem_or_compl_mem [IsProper I] (h : ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I) : IsPrime I := by
  simp only [← is_prime_iff_mem_or_mem, ← or_iff_not_imp_left]
  intro x y hxy hxI
  have hxcI : xᶜ ∈ I := h.resolve_left hxI
  have ass : x⊓y⊔y⊓xᶜ ∈ I := sup_mem hxy (I.lower inf_le_right hxcI)
  rwa [inf_comm, sup_inf_inf_compl] at ass

theorem is_prime_iff_mem_or_compl_mem [IsProper I] : IsPrime I ↔ ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I :=
  ⟨fun h _ => h.mem_or_compl_mem, is_prime_of_mem_or_compl_mem⟩

instance (priority := 100) IsPrime.is_maximal [IsPrime I] : IsMaximal I := by
  simp only [← is_maximal_iff, ← Set.eq_univ_iff_forall, ← is_prime.to_is_proper, ← true_andₓ]
  intro J hIJ x
  rcases Set.exists_of_ssubset hIJ with ⟨y, hyJ, hyI⟩
  suffices ass : x⊓y⊔x⊓yᶜ ∈ J
  · rwa [sup_inf_inf_compl] at ass
    
  exact sup_mem (J.lower inf_le_right hyJ) (hIJ.le <| I.lower inf_le_right <| is_prime.mem_compl_of_not_mem ‹_› hyI)

end BooleanAlgebra

end Ideal

namespace Pfilter

variable [Preorderₓ P]

/-- A filter `F` is prime if its complement is an ideal.
-/
@[mk_iff]
class IsPrime (F : Pfilter P) : Prop where
  compl_ideal : IsIdeal ((F : Set P)ᶜ)

/-- Create an element of type `order.ideal.prime_pair` from a filter satisfying the predicate
`order.pfilter.is_prime`. -/
def IsPrime.toPrimePair {F : Pfilter P} (h : IsPrime F) : Ideal.PrimePair P :=
  { i := h.compl_ideal.toIdeal, f, is_compl_I_F := is_compl_compl.symm }

theorem _root_.order.ideal.prime_pair.F_is_prime (IF : Ideal.PrimePair P) : IsPrime IF.f :=
  { compl_ideal := by
      rw [IF.compl_F_eq_I]
      exact IF.I.is_ideal }

end Pfilter

end Order

