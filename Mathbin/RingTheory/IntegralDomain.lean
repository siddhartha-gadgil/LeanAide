/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Polynomial.RingDivision
import Mathbin.GroupTheory.SpecificGroups.Cyclic
import Mathbin.Algebra.GeomSum

/-!
# Integral domains

Assorted theorems about integral domains.

## Main theorems

* `is_cyclic_of_subgroup_is_domain`: A finite subgroup of the units of an integral domain is cyclic.
* `fintype.field_of_domain`: A finite integral domain is a field.

## TODO

Prove Wedderburn's little theorem, which shows that all finite division rings are actually fields.

## Tags

integral domain, finite integral domain, finite field
-/


section

open Finset Polynomial Function

open BigOperators Nat

section CancelMonoidWithZero

-- There doesn't seem to be a better home for these right now
variable {M : Type _} [CancelMonoidWithZero M] [Fintype M]

theorem mul_right_bijective_of_fintype₀ {a : M} (ha : a ≠ 0) : Bijective fun b => a * b :=
  Fintype.injective_iff_bijective.1 <| mul_right_injective₀ ha

theorem mul_left_bijective_of_fintype₀ {a : M} (ha : a ≠ 0) : Bijective fun b => b * a :=
  Fintype.injective_iff_bijective.1 <| mul_left_injective₀ ha

/-- Every finite nontrivial cancel_monoid_with_zero is a group_with_zero. -/
def Fintype.groupWithZeroOfCancel (M : Type _) [CancelMonoidWithZero M] [DecidableEq M] [Fintype M] [Nontrivial M] :
    GroupWithZeroₓ M :=
  { ‹Nontrivial M›, ‹CancelMonoidWithZero M› with
    inv := fun a => if h : a = 0 then 0 else Fintype.bijInv (mul_right_bijective_of_fintype₀ h) 1,
    mul_inv_cancel := fun a ha => by
      simp [← Inv.inv, ← dif_neg ha]
      exact Fintype.right_inverse_bij_inv _ _,
    inv_zero := by
      simp [← Inv.inv, ← dif_pos rfl] }

end CancelMonoidWithZero

variable {R : Type _} {G : Type _}

section Ringₓ

variable [Ringₓ R] [IsDomain R] [Fintype R]

/-- Every finite domain is a division ring.

TODO: Prove Wedderburn's little theorem,
which shows a finite domain is in fact commutative, hence a field. -/
def Fintype.divisionRingOfIsDomain (R : Type _) [Ringₓ R] [IsDomain R] [DecidableEq R] [Fintype R] : DivisionRing R :=
  { show GroupWithZeroₓ R from Fintype.groupWithZeroOfCancel R, ‹Ringₓ R› with }

/-- Every finite commutative domain is a field.

TODO: Prove Wedderburn's little theorem, which shows a finite domain is automatically commutative,
dropping one assumption from this theorem. -/
def Fintype.fieldOfDomain (R) [CommRingₓ R] [IsDomain R] [DecidableEq R] [Fintype R] : Field R :=
  { Fintype.groupWithZeroOfCancel R, ‹CommRingₓ R› with }

theorem Fintype.is_field_of_domain (R) [CommRingₓ R] [IsDomain R] [Fintype R] : IsField R :=
  @Field.to_is_field R <| @Fintype.fieldOfDomain R _ _ (Classical.decEq R) _

end Ringₓ

variable [CommRingₓ R] [IsDomain R] [Groupₓ G] [Fintype G]

theorem card_nth_roots_subgroup_units (f : G →* R) (hf : Injective f) {n : ℕ} (hn : 0 < n) (g₀ : G) :
    ({ g ∈ univ | g ^ n = g₀ } : Finset G).card ≤ (nthRoots n (f g₀)).card := by
  have : DecidableEq R := Classical.decEq _
  refine' le_transₓ _ (nth_roots n (f g₀)).to_finset_card_le
  apply card_le_card_of_inj_on f
  · intro g hg
    rw [sep_def, mem_filter] at hg
    rw [Multiset.mem_to_finset, mem_nth_roots hn, ← f.map_pow, hg.2]
    
  · intros
    apply hf
    assumption
    

/-- A finite subgroup of the unit group of an integral domain is cyclic. -/
theorem is_cyclic_of_subgroup_is_domain (f : G →* R) (hf : Injective f) : IsCyclic G := by
  classical
  apply is_cyclic_of_card_pow_eq_one_le
  intro n hn
  convert le_transₓ (card_nth_roots_subgroup_units f hf hn 1) (card_nth_roots n (f 1))

/-- The unit group of a finite integral domain is cyclic.

To support `ℤˣ` and other infinite monoids with finite groups of units, this requires only
`fintype Rˣ` rather than deducing it from `fintype R`. -/
instance [Fintype Rˣ] : IsCyclic Rˣ :=
  is_cyclic_of_subgroup_is_domain (Units.coeHom R) <| Units.ext

section

variable (S : Subgroup Rˣ) [Fintype S]

/-- A finite subgroup of the units of an integral domain is cyclic. -/
instance subgroup_units_cyclic : IsCyclic S := by
  refine' is_cyclic_of_subgroup_is_domain ⟨(coe : S → R), _, _⟩ (units.ext.comp Subtype.val_injective)
  · simp
    
  · intros
    simp
    

end

theorem card_fiber_eq_of_mem_range {H : Type _} [Groupₓ H] [DecidableEq H] (f : G →* H) {x y : H} (hx : x ∈ Set.Range f)
    (hy : y ∈ Set.Range f) : (univ.filter fun g => f g = x).card = (univ.filter fun g => f g = y).card := by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  refine' card_congr (fun g _ => g * x⁻¹ * y) _ _ fun g hg => ⟨g * y⁻¹ * x, _⟩
  · simp (config := { contextual := true })only [← mem_filter, ← one_mulₓ, ← MonoidHom.map_mul, ← mem_univ, ←
      mul_right_invₓ, ← eq_self_iff_true, ← MonoidHom.map_mul_inv, ← and_selfₓ, ← forall_true_iff]
    
  · simp only [← mul_left_injₓ, ← imp_self, ← forall_2_true_iff]
    
  · simp only [← true_andₓ, ← mem_filter, ← mem_univ] at hg
    simp only [← hg, ← mem_filter, ← one_mulₓ, ← MonoidHom.map_mul, ← mem_univ, ← mul_right_invₓ, ← eq_self_iff_true, ←
      exists_prop_of_true, ← MonoidHom.map_mul_inv, ← and_selfₓ, ← mul_inv_cancel_rightₓ, ← inv_mul_cancel_right]
    

/-- In an integral domain, a sum indexed by a nontrivial homomorphism from a finite group is zero.
-/
theorem sum_hom_units_eq_zero (f : G →* R) (hf : f ≠ 1) : (∑ g : G, f g) = 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : MonoidHom.range f.to_hom_units, ∀ y : MonoidHom.range f.to_hom_units, y ∈ Submonoid.powers x
  exact IsCyclic.exists_monoid_generator
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hf
    ext g
    rw [MonoidHom.one_apply]
    cases' hx ⟨f.to_hom_units g, g, rfl⟩ with n hn
    rwa [Subtype.ext_iff, Units.ext_iff, Subtype.coe_mk, MonoidHom.coe_to_hom_units, one_pow, eq_comm] at hn
  replace hx1 : (x : R) - 1 ≠ 0
  exact fun h => hx1 (Subtype.eq (Units.ext (sub_eq_zero.1 h)))
  let c := (univ.filter fun g => f.to_hom_units g = 1).card
  calc (∑ g : G, f g) = ∑ g : G, f.to_hom_units g :=
      rfl _ = ∑ u : Rˣ in univ.image f.to_hom_units, (univ.filter fun g => f.to_hom_units g = u).card • u :=
      sum_comp (coe : Rˣ → R) f.to_hom_units _ = ∑ u : Rˣ in univ.image f.to_hom_units, c • u :=
      sum_congr rfl fun u hu => congr_arg2ₓ _ _ rfl-- remaining goal 1, proven below
        _ =
        ∑ b : MonoidHom.range f.to_hom_units, c • ↑b :=
      Finset.sum_subtype _
        (by
          simp )
        _ _ = c • ∑ b : MonoidHom.range f.to_hom_units, (b : R) :=
      smul_sum.symm _ = c • 0 :=
      congr_arg2ₓ _ rfl _-- remaining goal 2, proven below
        _ =
        0 :=
      smul_zero _
  · -- remaining goal 1
    show (univ.filter fun g : G => f.to_hom_units g = u).card = c
    apply card_fiber_eq_of_mem_range f.to_hom_units
    · simpa only [← mem_image, ← mem_univ, ← exists_prop_of_true, ← Set.mem_range] using hu
      
    · exact ⟨1, f.to_hom_units.map_one⟩
      
    
  -- remaining goal 2
  show (∑ b : MonoidHom.range f.to_hom_units, (b : R)) = 0
  calc (∑ b : MonoidHom.range f.to_hom_units, (b : R)) = ∑ n in range (orderOf x), x ^ n :=
      Eq.symm <|
        sum_bij (fun n _ => x ^ n)
          (by
            simp only [← mem_univ, ← forall_true_iff])
          (by
            simp only [← implies_true_iff, ← eq_self_iff_true, ← Subgroup.coe_pow, ← Units.coe_pow, ← coe_coe])
          (fun m n hm hn =>
            pow_injective_of_lt_order_of _
              (by
                simpa only [← mem_range] using hm)
              (by
                simpa only [← mem_range] using hn))
          fun b hb =>
          let ⟨n, hn⟩ := hx b
          ⟨n % orderOf x, mem_range.2 (Nat.mod_ltₓ _ (order_of_pos _)), by
            rw [← pow_eq_mod_order_of, hn]⟩_ = 0 :=
      _
  rw [← mul_left_inj' hx1, zero_mul, geom_sum_mul, coe_coe]
  norm_cast
  simp [← pow_order_of_eq_one]

/-- In an integral domain, a sum indexed by a homomorphism from a finite group is zero,
unless the homomorphism is trivial, in which case the sum is equal to the cardinality of the group.
-/
theorem sum_hom_units (f : G →* R) [Decidable (f = 1)] : (∑ g : G, f g) = if f = 1 then Fintype.card G else 0 := by
  split_ifs with h h
  · simp [← h, ← card_univ]
    
  · exact sum_hom_units_eq_zero f h
    

end

