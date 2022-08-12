/-
Copyright (c) 2022 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import Mathbin.GroupTheory.OrderOfElement
import Mathbin.Data.Finset.NoncommProd
import Mathbin.Data.Fintype.Card

/-!
# Canonical homomorphism from a finite family of monoids

This file defines the construction of the canonical homomorphism from a family of monoids.

Given a family of morphisms `ϕ i : N i →* M` for each `i : ι` where elements in the
images of different morphisms commute, we obtain a canonical morphism
`monoid_hom.noncomm_pi_coprod : (Π i, N i) →* M` that coincides with `ϕ`

## Main definitions

* `monoid_hom.noncomm_pi_coprod : (Π i, N i) →* M` is the main homomorphism
* `subgroup.noncomm_pi_coprod : (Π i, H i) →* G` is the specialization to `H i : subgroup G`
   and the subgroup embedding.

## Main theorems

* `monoid_hom.noncomm_pi_coprod` coincides with `ϕ i` when restricted to `N i`
* `monoid_hom.noncomm_pi_coprod_mrange`: The range of `monoid_hom.noncomm_pi_coprod` is
  `⨆ (i : ι), (ϕ i).mrange`
* `monoid_hom.noncomm_pi_coprod_range`: The range of `monoid_hom.noncomm_pi_coprod` is
  `⨆ (i : ι), (ϕ i).range`
* `subgroup.noncomm_pi_coprod_range`: The range of `subgroup.noncomm_pi_coprod` is `⨆ (i : ι), H i`.
* `monoid_hom.injective_noncomm_pi_coprod_of_independent`: in the case of groups, `pi_hom.hom` is
   injective if the `ϕ` are injective and the ranges of the `ϕ` are independent.
* `monoid_hom.independent_range_of_coprime_order`: If the `N i` have coprime orders, then the ranges
   of the `ϕ` are independent.
* `subgroup.independent_of_coprime_order`: If commuting normal subgroups `H i` have coprime orders,
   they are independent.

-/


open BigOperators

section FamilyOfMonoids

variable {M : Type _} [Monoidₓ M]

-- We have a family of monoids
-- The fintype assumption is not always used, but declared here, to keep things in order
variable {ι : Type _} [hdec : DecidableEq ι] [Fintype ι]

variable {N : ι → Type _} [∀ i, Monoidₓ (N i)]

-- And morphisms ϕ into G
variable (ϕ : ∀ i : ι, N i →* M)

-- We assume that the elements of different morphism commute
variable (hcomm : ∀ i j : ι, i ≠ j → ∀ (x : N i) (y : N j), Commute (ϕ i x) (ϕ j y))

include hcomm

-- We use `f` and `g` to denote elements of `Π (i : ι), N i`
variable (f g : ∀ i : ι, N i)

namespace MonoidHom

/-- The canonical homomorphism from a family of monoids. -/
@[to_additive
      "The canonical homomorphism from a family of additive monoids.\n\nSee also `linear_map.lsum` for a linear version without the commutativity assumption."]
def noncommPiCoprod : (∀ i : ι, N i) →* M where
  toFun := fun f =>
    (Finset.univ.noncommProd fun i => ϕ i (f i)) <| by
      rintro i - j -
      by_cases' h : i = j
      · subst h
        
      · exact hcomm _ _ h _ _
        
  map_one' := by
    apply (Finset.noncomm_prod_eq_pow_card _ _ _ _ _).trans (one_pow _)
    simp
  map_mul' := fun f g => by
    classical
    convert @Finset.noncomm_prod_mul_distrib _ _ _ _ (fun i => ϕ i (f i)) (fun i => ϕ i (g i)) _ _ _
    · ext i
      exact map_mul (ϕ i) (f i) (g i)
      
    · rintro i - j - h
      exact hcomm _ _ h _ _
      

variable {hcomm}

include hdec

@[simp, to_additive]
theorem noncomm_pi_coprod_mul_single (i : ι) (y : N i) : noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y := by
  change finset.univ.noncomm_prod (fun j => ϕ j (Pi.mulSingle i y j)) _ = ϕ i y
  simp (config := { singlePass := true })only [Finset.insert_erase (Finset.mem_univ i)]
  rw [Finset.noncomm_prod_insert_of_not_mem _ _ _ _ (Finset.not_mem_erase i _)]
  rw [Pi.mul_single_eq_same]
  rw [Finset.noncomm_prod_eq_pow_card]
  · rw [one_pow]
    exact mul_oneₓ _
    
  · intro j hj
    simp only [← Finset.mem_erase] at hj
    simp [← hj]
    

omit hcomm

/-- The universal property of `noncomm_pi_coprod` -/
@[to_additive "The universal property of `noncomm_pi_coprod`"]
def noncommPiCoprodEquiv :
    { ϕ : ∀ i, N i →* M // Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y) } ≃ ((∀ i, N i) →* M) where
  toFun := fun ϕ => noncommPiCoprod ϕ.1 ϕ.2
  invFun := fun f =>
    ⟨fun i => f.comp (MonoidHom.single N i), fun i j hij x y => Commute.map (Pi.mul_single_commute i j hij x y) f⟩
  left_inv := fun ϕ => by
    ext
    simp
  right_inv := fun f =>
    pi_ext fun i x => by
      simp

omit hdec

include hcomm

@[to_additive]
theorem noncomm_pi_coprod_mrange : (noncommPiCoprod ϕ hcomm).mrange = ⨆ i : ι, (ϕ i).mrange := by
  classical
  apply le_antisymmₓ
  · rintro x ⟨f, rfl⟩
    refine' Submonoid.noncomm_prod_mem _ _ _ _ _
    intro i hi
    apply Submonoid.mem_Sup_of_mem
    · use i
      
    simp
    
  · refine' supr_le _
    rintro i x ⟨y, rfl⟩
    refine' ⟨Pi.mulSingle i y, noncomm_pi_coprod_mul_single _ _ _⟩
    

end MonoidHom

end FamilyOfMonoids

section FamilyOfGroups

variable {G : Type _} [Groupₓ G]

variable {ι : Type _} [hdec : DecidableEq ι] [hfin : Fintype ι]

variable {H : ι → Type _} [∀ i, Groupₓ (H i)]

variable (ϕ : ∀ i : ι, H i →* G)

variable {hcomm : ∀ i j : ι, i ≠ j → ∀ (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)}

include hcomm

-- We use `f` and `g` to denote elements of `Π (i : ι), H i`
variable (f g : ∀ i : ι, H i)

include hfin

namespace MonoidHom

-- The subgroup version of `noncomm_pi_coprod_mrange`
@[to_additive]
theorem noncomm_pi_coprod_range : (noncommPiCoprod ϕ hcomm).range = ⨆ i : ι, (ϕ i).range := by
  classical
  apply le_antisymmₓ
  · rintro x ⟨f, rfl⟩
    refine' Subgroup.noncomm_prod_mem _ _ _
    intro i hi
    apply Subgroup.mem_Sup_of_mem
    · use i
      
    simp
    
  · refine' supr_le _
    rintro i x ⟨y, rfl⟩
    refine' ⟨Pi.mulSingle i y, noncomm_pi_coprod_mul_single _ _ _⟩
    

@[to_additive]
theorem injective_noncomm_pi_coprod_of_independent (hind : CompleteLattice.Independent fun i => (ϕ i).range)
    (hinj : ∀ i, Function.Injective (ϕ i)) : Function.Injective (noncommPiCoprod ϕ hcomm) := by
  classical
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro f heq1
  change finset.univ.noncomm_prod (fun i => ϕ i (f i)) _ = 1 at heq1
  change f = 1
  have : ∀ i, i ∈ Finset.univ → ϕ i (f i) = 1 :=
    Subgroup.eq_one_of_noncomm_prod_eq_one_of_independent _ _ _ _ hind
      (by
        simp )
      heq1
  ext i
  apply hinj
  simp [← this i (Finset.mem_univ i)]

variable (hcomm)

@[to_additive]
theorem independent_range_of_coprime_order [∀ i, Fintype (H i)]
    (hcoprime : ∀ i j, i ≠ j → Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j))) :
    CompleteLattice.Independent fun i => (ϕ i).range := by
  classical
  rintro i f ⟨hxi, hxp⟩
  dsimp'  at hxi hxp
  rw [supr_subtype', ← noncomm_pi_coprod_range] at hxp
  rotate_left
  · intro _ _ hj
    apply hcomm
    exact hj ∘ Subtype.ext
    
  cases' hxp with g hgf
  cases' hxi with g' hg'f
  have hxi : orderOf f ∣ Fintype.card (H i) := by
    rw [← hg'f]
    exact (order_of_map_dvd _ _).trans order_of_dvd_card_univ
  have hxp : orderOf f ∣ ∏ j : { j // j ≠ i }, Fintype.card (H j) := by
    rw [← hgf, ← Fintype.card_pi]
    exact (order_of_map_dvd _ _).trans order_of_dvd_card_univ
  change f = 1
  rw [← pow_oneₓ f, ← order_of_dvd_iff_pow_eq_one]
  convert ← Nat.dvd_gcdₓ hxp hxi
  rw [← Nat.coprime_iff_gcd_eq_oneₓ]
  apply Nat.coprime_prod_left
  intro j _
  apply hcoprime
  exact j.2

end MonoidHom

end FamilyOfGroups

namespace Subgroup

-- We have an family of subgroups
variable {G : Type _} [Groupₓ G]

variable {ι : Type _} [hdec : DecidableEq ι] [hfin : Fintype ι] {H : ι → Subgroup G}

-- Elements of `Π (i : ι), H i` are called `f` and `g` here
variable (f g : ∀ i : ι, H i)

section CommutingSubgroups

-- We assume that the elements of different subgroups commute
variable (hcomm : ∀ i j : ι, i ≠ j → ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)

include hcomm

@[to_additive]
theorem commute_subtype_of_commute (i j : ι) (hne : i ≠ j) :
    ∀ (x : H i) (y : H j), Commute ((H i).Subtype x) ((H j).Subtype y) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  exact hcomm i j hne x y hx hy

include hfin

/-- The canonical homomorphism from a family of subgroups where elements from different subgroups
commute -/
@[to_additive
      "The canonical homomorphism from a family of additive subgroups where elements from\ndifferent subgroups commute"]
def noncommPiCoprod : (∀ i : ι, H i) →* G :=
  MonoidHom.noncommPiCoprod (fun i => (H i).Subtype) (commute_subtype_of_commute hcomm)

variable {hcomm}

include hdec

@[simp, to_additive]
theorem noncomm_pi_coprod_mul_single (i : ι) (y : H i) : noncommPiCoprod hcomm (Pi.mulSingle i y) = y := by
  apply MonoidHom.noncomm_pi_coprod_mul_single

omit hdec

@[to_additive]
theorem noncomm_pi_coprod_range : (noncommPiCoprod hcomm).range = ⨆ i : ι, H i := by
  simp [← noncomm_pi_coprod, ← MonoidHom.noncomm_pi_coprod_range]

@[to_additive]
theorem injective_noncomm_pi_coprod_of_independent (hind : CompleteLattice.Independent H) :
    Function.Injective (noncommPiCoprod hcomm) := by
  apply MonoidHom.injective_noncomm_pi_coprod_of_independent
  · simpa using hind
    
  · intro i
    exact Subtype.coe_injective
    

variable (hcomm)

@[to_additive]
theorem independent_of_coprime_order [∀ i, Fintype (H i)]
    (hcoprime : ∀ i j, i ≠ j → Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j))) : CompleteLattice.Independent H :=
  by
  simpa using
    MonoidHom.independent_range_of_coprime_order (fun i => (H i).Subtype) (commute_subtype_of_commute hcomm) hcoprime

end CommutingSubgroups

end Subgroup

