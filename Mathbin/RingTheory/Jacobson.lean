/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathbin.RingTheory.Localization.Away
import Mathbin.RingTheory.Ideal.Over
import Mathbin.RingTheory.JacobsonIdeal

/-!
# Jacobson Rings
The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its Jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its Jacobson radical
Any ring satisfying any of these equivalent conditions is said to be Jacobson.
Some particular examples of Jacobson rings are also proven.
`is_jacobson_quotient` says that the quotient of a Jacobson ring is Jacobson.
`is_jacobson_localization` says the localization of a Jacobson ring to a single element is Jacobson.
`is_jacobson_polynomial_iff_is_jacobson` says polynomials over a Jacobson ring form a Jacobson ring.
## Main definitions
Let `R` be a commutative ring. Jacobson Rings are defined using the first of the above conditions
* `is_jacobson R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.radical = I` implies `I.jacobson = I`.

## Main statements
* `is_jacobson_iff_prime_eq` is the equivalence between conditions 1 and 3 above.
* `is_jacobson_iff_Inf_maximal` is the equivalence between conditions 1 and 2 above.
* `is_jacobson_of_surjective` says that if `R` is a Jacobson ring and `f : R →+* S` is surjective,
  then `S` is also a Jacobson ring
* `is_jacobson_mv_polynomial` says that multi-variate polynomials over a Jacobson ring are Jacobson.
## Tags
Jacobson, Jacobson Ring
-/


namespace Ideal

open Polynomial

open Polynomial

section IsJacobson

variable {R S : Type _} [CommRingₓ R] [CommRingₓ S] {I : Ideal R}

/-- A ring is a Jacobson ring if for every radical ideal `I`,
 the Jacobson radical of `I` is equal to `I`.
 See `is_jacobson_iff_prime_eq` and `is_jacobson_iff_Inf_maximal` for equivalent definitions. -/
class IsJacobson (R : Type _) [CommRingₓ R] : Prop where
  out' : ∀ I : Ideal R, I.radical = I → I.jacobson = I

theorem is_jacobson_iff {R} [CommRingₓ R] : IsJacobson R ↔ ∀ I : Ideal R, I.radical = I → I.jacobson = I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem IsJacobson.out {R} [CommRingₓ R] : IsJacobson R → ∀ {I : Ideal R}, I.radical = I → I.jacobson = I :=
  is_jacobson_iff.1

/-- A ring is a Jacobson ring if and only if for all prime ideals `P`,
 the Jacobson radical of `P` is equal to `P`. -/
theorem is_jacobson_iff_prime_eq : IsJacobson R ↔ ∀ P : Ideal R, IsPrime P → P.jacobson = P := by
  refine' is_jacobson_iff.trans ⟨fun h I hI => h I (is_prime.radical hI), _⟩
  refine' fun h I hI => le_antisymmₓ (fun x hx => _) fun x hx => mem_Inf.mpr fun _ hJ => hJ.left hx
  rw [← hI, radical_eq_Inf I, mem_Inf]
  intro P hP
  rw [Set.mem_set_of_eq] at hP
  erw [mem_Inf] at hx
  erw [← h P hP.right, mem_Inf]
  exact fun J hJ => hx ⟨le_transₓ hP.left hJ.left, hJ.right⟩

/-- A ring `R` is Jacobson if and only if for every prime ideal `I`,
 `I` can be written as the infimum of some collection of maximal ideals.
 Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs cleaner. -/
theorem is_jacobson_iff_Inf_maximal :
    IsJacobson R ↔ ∀ {I : Ideal R}, I.IsPrime → ∃ M : Set (Ideal R), (∀, ∀ J ∈ M, ∀, IsMaximal J ∨ J = ⊤) ∧ I = inf M :=
  ⟨fun H I h => eq_jacobson_iff_Inf_maximal.1 (H.out (IsPrime.radical h)), fun H =>
    is_jacobson_iff_prime_eq.2 fun P hP => eq_jacobson_iff_Inf_maximal.2 (H hP)⟩

theorem is_jacobson_iff_Inf_maximal' :
    IsJacobson R ↔
      ∀ {I : Ideal R}, I.IsPrime → ∃ M : Set (Ideal R), (∀, ∀ J ∈ M, ∀ (K : Ideal R), J < K → K = ⊤) ∧ I = inf M :=
  ⟨fun H I h => eq_jacobson_iff_Inf_maximal'.1 (H.out (IsPrime.radical h)), fun H =>
    is_jacobson_iff_prime_eq.2 fun P hP => eq_jacobson_iff_Inf_maximal'.2 (H hP)⟩

theorem radical_eq_jacobson [H : IsJacobson R] (I : Ideal R) : I.radical = I.jacobson :=
  le_antisymmₓ (le_Inf fun J ⟨hJ, hJ_max⟩ => (IsPrime.radical_le_iff hJ_max.IsPrime).mpr hJ)
    (H.out (radical_idem I) ▸ jacobson_mono le_radical)

/-- Fields have only two ideals, and the condition holds for both of them.  -/
instance (priority := 100) is_jacobson_field {K : Type _} [Field K] : IsJacobson K :=
  ⟨fun I hI =>
    Or.rec_on (eq_bot_or_top I)
      (fun h => le_antisymmₓ (Inf_le ⟨le_of_eqₓ rfl, Eq.symm h ▸ bot_is_maximal⟩) (Eq.symm h ▸ bot_le)) fun h => by
      rw [h, jacobson_eq_top_iff]⟩

theorem is_jacobson_of_surjective [H : IsJacobson R] : (∃ f : R →+* S, Function.Surjective f) → IsJacobson S := by
  rintro ⟨f, hf⟩
  rw [is_jacobson_iff_Inf_maximal]
  intro p hp
  use map f '' { J : Ideal R | comap f p ≤ J ∧ J.IsMaximal }
  use fun j ⟨J, hJ, hmap⟩ => hmap ▸ Or.symm (map_eq_top_or_is_maximal_of_surjective f hf hJ.right)
  have : p = map f (comap f p).jacobson :=
    (is_jacobson.out' (comap f p)
          (by
            rw [← comap_radical, is_prime.radical hp])).symm ▸
      (map_comap_of_surjective f hf p).symm
  exact Eq.trans this (map_Inf hf fun J ⟨hJ, _⟩ => le_transₓ (Ideal.ker_le_comap f) hJ)

instance (priority := 100) is_jacobson_quotient [IsJacobson R] : IsJacobson (R ⧸ I) :=
  is_jacobson_of_surjective
    ⟨Quotient.mk I, by
      rintro ⟨x⟩ <;> use x <;> rfl⟩

theorem is_jacobson_iso (e : R ≃+* S) : IsJacobson R ↔ IsJacobson S :=
  ⟨fun h => @is_jacobson_of_surjective _ _ _ _ h ⟨(e : R →+* S), e.Surjective⟩, fun h =>
    @is_jacobson_of_surjective _ _ _ _ h ⟨(e.symm : S →+* R), e.symm.Surjective⟩⟩

theorem is_jacobson_of_is_integral [Algebra R S] (hRS : Algebra.IsIntegral R S) (hR : IsJacobson R) : IsJacobson S := by
  rw [is_jacobson_iff_prime_eq]
  intro P hP
  by_cases' hP_top : comap (algebraMap R S) P = ⊤
  · simp [← comap_eq_top_iff.1 hP_top]
    
  · have : Nontrivial (R ⧸ comap (algebraMap R S) P) := quotient.nontrivial hP_top
    rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    refine' eq_bot_of_comap_eq_bot (is_integral_quotient_of_is_integral hRS) _
    rw [eq_bot_iff, ←
      jacobson_eq_iff_jacobson_quotient_eq_bot.1
        ((is_jacobson_iff_prime_eq.1 hR) (comap (algebraMap R S) P) (comap_is_prime _ _)),
      comap_jacobson]
    refine' Inf_le_Inf fun J hJ => _
    simp only [← true_andₓ, ← Set.mem_image, ← bot_le, ← Set.mem_set_of_eq]
    have : J.is_maximal := by
      simpa using hJ
    exact
      exists_ideal_over_maximal_of_is_integral (is_integral_quotient_of_is_integral hRS) J
        (comap_bot_le_of_injective _ algebra_map_quotient_injective)
    

theorem is_jacobson_of_is_integral' (f : R →+* S) (hf : f.IsIntegral) (hR : IsJacobson R) : IsJacobson S :=
  @is_jacobson_of_is_integral _ _ _ _ f.toAlgebra hf hR

end IsJacobson

section Localization

open IsLocalization Submonoid

variable {R S : Type _} [CommRingₓ R] [CommRingₓ S] {I : Ideal R}

variable (y : R) [Algebra R S] [IsLocalization.Away y S]

theorem disjoint_powers_iff_not_mem (hI : I.radical = I) : Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ I.1 := by
  refine' ⟨fun h => Set.disjoint_left.1 h (mem_powers _), fun h => disjoint_iff.mpr (eq_bot_iff.mpr _)⟩
  rintro x ⟨⟨n, rfl⟩, hx'⟩
  rw [← hI] at hx'
  exact absurd (hI ▸ mem_radical_of_pow_mem hx' : y ∈ I.carrier) h

variable (S)

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its comap.
See `le_rel_iso_of_maximal` for the more general relation isomorphism -/
theorem is_maximal_iff_is_maximal_disjoint [H : IsJacobson R] (J : Ideal S) :
    J.IsMaximal ↔ (comap (algebraMap R S) J).IsMaximal ∧ y ∉ Ideal.comap (algebraMap R S) J := by
  constructor
  · refine' fun h =>
      ⟨_, fun hy => h.ne_top (Ideal.eq_top_of_is_unit_mem _ hy (map_units _ ⟨y, Submonoid.mem_powers _⟩))⟩
    have hJ : J.is_prime := is_maximal.is_prime h
    rw [is_prime_iff_is_prime_disjoint (Submonoid.powers y)] at hJ
    have : y ∉ (comap (algebraMap R S) J).1 := Set.disjoint_left.1 hJ.right (Submonoid.mem_powers _)
    erw [← H.out (is_prime.radical hJ.left), mem_Inf] at this
    push_neg  at this
    rcases this with ⟨I, hI, hI'⟩
    convert hI.right
    by_cases' hJ : J = map (algebraMap R S) I
    · rw [hJ, comap_map_of_is_prime_disjoint (powers y) S I (is_maximal.is_prime hI.right)]
      rwa [disjoint_powers_iff_not_mem y (is_maximal.is_prime hI.right).radical]
      
    · have hI_p : (map (algebraMap R S) I).IsPrime := by
        refine' is_prime_of_is_prime_disjoint (powers y) _ I hI.right.is_prime _
        rwa [disjoint_powers_iff_not_mem y (is_maximal.is_prime hI.right).radical]
      have : J ≤ map (algebraMap R S) I := map_comap (Submonoid.powers y) S J ▸ map_mono hI.left
      exact absurd (h.1.2 _ (lt_of_le_of_neₓ this hJ)) hI_p.1
      
    
  · refine' fun h => ⟨⟨fun hJ => h.1.ne_top (eq_top_iff.2 _), fun I hI => _⟩⟩
    · rwa [eq_top_iff, ← (IsLocalization.orderEmbedding (powers y) S).le_iff_le] at hJ
      
    · have := congr_arg (map (algebraMap R S)) (h.1.1.2 _ ⟨comap_mono (le_of_ltₓ hI), _⟩)
      rwa [map_comap (powers y) S I, map_top] at this
      refine' fun hI' => hI.right _
      rw [← map_comap (powers y) S I, ← map_comap (powers y) S J]
      exact map_mono hI'
      
    

variable {S}

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its map.
See `le_rel_iso_of_maximal` for the more general statement, and the reverse of this implication -/
theorem is_maximal_of_is_maximal_disjoint [IsJacobson R] (I : Ideal R) (hI : I.IsMaximal) (hy : y ∉ I) :
    (map (algebraMap R S) I).IsMaximal := by
  rw [is_maximal_iff_is_maximal_disjoint S y,
    comap_map_of_is_prime_disjoint (powers y) S I (is_maximal.is_prime hI)
      ((disjoint_powers_iff_not_mem y (is_maximal.is_prime hI).radical).2 hy)]
  exact ⟨hI, hy⟩

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y` -/
def orderIsoOfMaximal [IsJacobson R] : { p : Ideal S // p.IsMaximal } ≃o { p : Ideal R // p.IsMaximal ∧ y ∉ p } where
  toFun := fun p => ⟨Ideal.comap (algebraMap R S) p.1, (is_maximal_iff_is_maximal_disjoint S y p.1).1 p.2⟩
  invFun := fun p => ⟨Ideal.map (algebraMap R S) p.1, is_maximal_of_is_maximal_disjoint y p.1 p.2.1 p.2.2⟩
  left_inv := fun J => Subtype.eq (map_comap (powers y) S J)
  right_inv := fun I =>
    Subtype.eq
      (comap_map_of_is_prime_disjoint _ _ I.1 (IsMaximal.is_prime I.2.1)
        ((disjoint_powers_iff_not_mem y I.2.1.IsPrime.radical).2 I.2.2))
  map_rel_iff' := fun I I' =>
    ⟨fun h => show I.val ≤ I'.val from map_comap (powers y) S I.val ▸ map_comap (powers y) S I'.val ▸ Ideal.map_mono h,
      fun h x hx => h hx⟩

include y

/-- If `S` is the localization of the Jacobson ring `R` at the submonoid generated by `y : R`, then
`S` is Jacobson. -/
theorem is_jacobson_localization [H : IsJacobson R] : IsJacobson S := by
  rw [is_jacobson_iff_prime_eq]
  refine' fun P' hP' => le_antisymmₓ _ le_jacobson
  obtain ⟨hP', hPM⟩ := (IsLocalization.is_prime_iff_is_prime_disjoint (powers y) S P').mp hP'
  have hP := H.out (is_prime.radical hP')
  refine'
    (le_of_eqₓ (IsLocalization.map_comap (powers y) S P'.jacobson).symm).trans
      ((map_mono _).trans (le_of_eqₓ (IsLocalization.map_comap (powers y) S P')))
  have : Inf { I : Ideal R | comap (algebraMap R S) P' ≤ I ∧ I.IsMaximal ∧ y ∉ I } ≤ comap (algebraMap R S) P' := by
    intro x hx
    have hxy : x * y ∈ (comap (algebraMap R S) P').jacobson := by
      rw [Ideal.jacobson, mem_Inf]
      intro J hJ
      by_cases' y ∈ J
      · exact J.mul_mem_left x h
        
      · exact J.mul_mem_right y ((mem_Inf.1 hx) ⟨hJ.left, ⟨hJ.right, h⟩⟩)
        
    rw [hP] at hxy
    cases' hP'.mem_or_mem hxy with hxy hxy
    · exact hxy
      
    · exact (hPM ⟨Submonoid.mem_powers _, hxy⟩).elim
      
  refine' le_transₓ _ this
  rw [Ideal.jacobson, comap_Inf', Inf_eq_infi]
  refine' infi_le_infi_of_subset fun I hI => ⟨map (algebraMap R S) I, ⟨_, _⟩⟩
  · exact
      ⟨le_transₓ (le_of_eqₓ (IsLocalization.map_comap (powers y) S P').symm) (map_mono hI.1),
        is_maximal_of_is_maximal_disjoint y _ hI.2.1 hI.2.2⟩
    
  · exact
      IsLocalization.comap_map_of_is_prime_disjoint _ S I (is_maximal.is_prime hI.2.1)
        ((disjoint_powers_iff_not_mem y hI.2.1.IsPrime.radical).2 hI.2.2)
    

end Localization

namespace Polynomial

open Polynomial

section CommRingₓ

variable {R S : Type _} [CommRingₓ R] [CommRingₓ S] [IsDomain S]

variable {Rₘ Sₘ : Type _} [CommRingₓ Rₘ] [CommRingₓ Sₘ]

/-- If `I` is a prime ideal of `polynomial R` and `pX ∈ I` is a non-constant polynomial,
  then the map `R →+* R[x]/I` descends to an integral map when localizing at `pX.leading_coeff`.
  In particular `X` is integral because it satisfies `pX`, and constants are trivially integral,
  so integrality of the entire extension follows by closure under addition and multiplication. -/
theorem is_integral_is_localization_polynomial_quotient (P : Ideal R[X]) (pX : R[X]) (hpX : pX ∈ P)
    [Algebra (R ⧸ P.comap (c : R →+* _)) Rₘ]
    [IsLocalization.Away (pX.map (Quotient.mk (P.comap (c : R →+* R[X])))).leadingCoeff Rₘ] [Algebra (R[X] ⧸ P) Sₘ]
    [IsLocalization
        ((Submonoid.powers (pX.map (Quotient.mk (P.comap (c : R →+* R[X])))).leadingCoeff).map
          (quotientMap P c le_rfl) :
          Submonoid (R[X] ⧸ P))
        Sₘ] :
    (IsLocalization.map Sₘ (quotientMap P c le_rfl)
        (Submonoid.powers (pX.map (Quotient.mk (P.comap (c : R →+* R[X])))).leadingCoeff).le_comap_map :
        Rₘ →+* _).IsIntegral :=
  by
  let P' : Ideal R := P.comap C
  let M : Submonoid (R ⧸ P') := Submonoid.powers (pX.map (Quotientₓ.mk (P.comap (C : R →+* R[X])))).leadingCoeff
  let M' : Submonoid (R[X] ⧸ P) :=
    (Submonoid.powers (pX.map (Quotientₓ.mk (P.comap (C : R →+* R[X])))).leadingCoeff).map (quotient_map P C le_rfl)
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotient_map P C le_rfl
  let φ' : Rₘ →+* Sₘ := IsLocalization.map Sₘ φ M.le_comap_map
  have hφ' : φ.comp (Quotientₓ.mk P') = (Quotientₓ.mk P).comp C := rfl
  intro p
  obtain ⟨⟨p', ⟨q, hq⟩⟩, hp⟩ := IsLocalization.surj M' p
  suffices φ'.is_integral_elem (algebraMap _ _ p') by
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨q'', hq''⟩ := is_unit_iff_exists_inv'.1 (IsLocalization.map_units Rₘ (⟨q', hq'⟩ : M))
    refine' φ'.is_integral_of_is_integral_mul_unit p (algebraMap _ _ (φ q')) q'' _ (hp.symm ▸ this)
    convert trans (trans (φ'.map_mul _ _).symm (congr_arg φ' hq'')) φ'.map_one using 2
    rw [← φ'.comp_apply, IsLocalization.map_comp, RingHom.comp_apply, Subtype.coe_mk]
  refine' is_integral_of_mem_closure'' ((algebraMap _ Sₘ).comp (Quotientₓ.mk P) '' insert X { p | p.degree ≤ 0 }) _ _ _
  · rintro x ⟨p, hp, rfl⟩
    refine' hp.rec_on (fun hy => _) fun hy => _
    · refine'
        hy.symm ▸
          φ.is_integral_elem_localization_at_leading_coeff ((Quotientₓ.mk P) X) (pX.map (Quotientₓ.mk P')) _ M
            ⟨1, pow_oneₓ _⟩
      rwa [eval₂_map, hφ', ← hom_eval₂, quotient.eq_zero_iff_mem, eval₂_C_X]
      
    · rw [Set.mem_set_of_eq, degree_le_zero_iff] at hy
      refine' hy.symm ▸ ⟨X - C (algebraMap _ _ ((Quotientₓ.mk P') (p.coeff 0))), monic_X_sub_C _, _⟩
      simp only [← eval₂_sub, ← eval₂_C, ← eval₂_X]
      rw [sub_eq_zero, ← φ'.comp_apply, IsLocalization.map_comp]
      rfl
      
    
  · obtain ⟨p, rfl⟩ := quotient.mk_surjective p'
    refine'
      Polynomial.induction_on p (fun r => Subring.subset_closure <| Set.mem_image_of_mem _ (Or.inr degree_C_le))
        (fun _ _ h1 h2 => _) fun n _ hr => _
    · convert Subring.add_mem _ h1 h2
      rw [RingHom.map_add, RingHom.map_add]
      
    · rw [pow_succₓ X n, mul_comm X, ← mul_assoc, RingHom.map_mul, RingHom.map_mul]
      exact Subring.mul_mem _ hr (Subring.subset_closure (Set.mem_image_of_mem _ (Or.inl rfl)))
      
    

/-- If `f : R → S` descends to an integral map in the localization at `x`,
  and `R` is a Jacobson ring, then the intersection of all maximal ideals in `S` is trivial -/
theorem jacobson_bot_of_integral_localization {R : Type _} [CommRingₓ R] [IsDomain R] [IsJacobson R] (Rₘ Sₘ : Type _)
    [CommRingₓ Rₘ] [CommRingₓ Sₘ] (φ : R →+* S) (hφ : Function.Injective φ) (x : R) (hx : x ≠ 0) [Algebra R Rₘ]
    [IsLocalization.Away x Rₘ] [Algebra S Sₘ] [IsLocalization ((Submonoid.powers x).map φ : Submonoid S) Sₘ]
    (hφ' : RingHom.IsIntegral (IsLocalization.map Sₘ φ (Submonoid.powers x).le_comap_map : Rₘ →+* Sₘ)) :
    (⊥ : Ideal S).jacobson = (⊥ : Ideal S) := by
  have hM : ((Submonoid.powers x).map φ : Submonoid S) ≤ nonZeroDivisors S :=
    map_le_non_zero_divisors_of_injective φ hφ (powers_le_non_zero_divisors_of_no_zero_divisors hx)
  let this : IsDomain Sₘ := IsLocalization.is_domain_of_le_non_zero_divisors _ hM
  let φ' : Rₘ →+* Sₘ := IsLocalization.map _ φ (Submonoid.powers x).le_comap_map
  suffices ∀ I : Ideal Sₘ, I.IsMaximal → (I.comap (algebraMap S Sₘ)).IsMaximal by
    have hϕ' : comap (algebraMap S Sₘ) (⊥ : Ideal Sₘ) = (⊥ : Ideal S) := by
      rw [← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
      exact IsLocalization.injective Sₘ hM
    have hSₘ : is_jacobson Sₘ := is_jacobson_of_is_integral' φ' hφ' (is_jacobson_localization x)
    refine' eq_bot_iff.mpr (le_transₓ _ (le_of_eqₓ hϕ'))
    rw [← hSₘ.out radical_bot_of_is_domain, comap_jacobson]
    exact
      Inf_le_Inf fun j hj =>
        ⟨bot_le,
          let ⟨J, hJ⟩ := hj
          hJ.2 ▸ this J hJ.1.2⟩
  intro I hI
  -- Remainder of the proof is pulling and pushing ideals around the square and the quotient square
  have : (I.comap (algebraMap S Sₘ)).IsPrime := comap_is_prime _ I
  have : (I.comap φ').IsPrime := comap_is_prime φ' I
  have : (⊥ : Ideal (S ⧸ I.comap (algebraMap S Sₘ))).IsPrime := bot_prime
  have hcomm : φ'.comp (algebraMap R Rₘ) = (algebraMap S Sₘ).comp φ := IsLocalization.map_comp _
  let f := quotient_map (I.comap (algebraMap S Sₘ)) φ le_rfl
  let g := quotient_map I (algebraMap S Sₘ) le_rfl
  have :=
    is_maximal_comap_of_is_integral_of_is_maximal' φ' hφ' I
      (by
        convert hI <;> cases _inst_4 <;> rfl)
  have := ((is_maximal_iff_is_maximal_disjoint Rₘ x _).1 this).left
  have : ((I.comap (algebraMap S Sₘ)).comap φ).IsMaximal := by
    rwa [comap_comap, hcomm, ← comap_comap] at this
  rw [← bot_quotient_is_maximal_iff] at this⊢
  refine'
    is_maximal_of_is_integral_of_is_maximal_comap' f _ ⊥
      ((eq_bot_iff.2 (comap_bot_le_of_injective f quotient_map_injective)).symm ▸ this)
  exact
    f.is_integral_tower_bot_of_is_integral g quotient_map_injective
      ((comp_quotient_map_eq_of_comp_eq hcomm I).symm ▸
        RingHom.is_integral_trans _ _
          (RingHom.is_integral_of_surjective _
            (IsLocalization.surjective_quotient_map_of_maximal_of_localization (Submonoid.powers x) Rₘ
              (by
                rwa [comap_comap, hcomm, ← bot_quotient_is_maximal_iff])))
          (RingHom.is_integral_quotient_of_is_integral _ hφ'))

/-- Used to bootstrap the proof of `is_jacobson_polynomial_iff_is_jacobson`.
  That theorem is more general and should be used instead of this one. -/
private theorem is_jacobson_polynomial_of_domain (R : Type _) [CommRingₓ R] [IsDomain R] [hR : IsJacobson R]
    (P : Ideal R[X]) [IsPrime P] (hP : ∀ x : R, c x ∈ P → x = 0) : P.jacobson = P := by
  by_cases' Pb : P = ⊥
  · exact Pb.symm ▸ jacobson_bot_polynomial_of_jacobson_bot (hR.out radical_bot_of_is_domain)
    
  · rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    have : (P.comap (C : R →+* R[X])).IsPrime := comap_is_prime C P
    obtain ⟨p, pP, p0⟩ := exists_nonzero_mem_of_ne_bot Pb hP
    let x := (Polynomial.map (Quotientₓ.mk (comap (C : R →+* _) P)) p).leadingCoeff
    have hx : x ≠ 0 := by
      rwa [Ne.def, leading_coeff_eq_zero]
    refine'
      jacobson_bot_of_integral_localization (Localization.Away x)
        (Localization ((Submonoid.powers x).map (P.quotient_map C le_rfl) : Submonoid (R[X] ⧸ P)))
        (quotient_map P C le_rfl) quotient_map_injective x hx _
    -- `convert` is noticeably faster than `exact` here:
    convert is_integral_is_localization_polynomial_quotient P p pP
    

theorem is_jacobson_polynomial_of_is_jacobson (hR : IsJacobson R) : IsJacobson R[X] := by
  refine' is_jacobson_iff_prime_eq.mpr fun I => _
  intro hI
  let R' : Subring (R[X] ⧸ I) := ((Quotientₓ.mk I).comp C).range
  let i : R →+* R' := ((Quotientₓ.mk I).comp C).range_restrict
  have hi : Function.Surjective (i : R → R') := ((Quotientₓ.mk I).comp C).range_restrict_surjective
  have hi' : (Polynomial.mapRingHom i : R[X] →+* R'[X]).ker ≤ I := by
    refine' fun f hf => polynomial_mem_ideal_of_coeff_mem_ideal I f fun n => _
    replace hf := congr_arg (fun g : Polynomial ((Quotientₓ.mk I).comp C).range => g.Coeff n) hf
    change (Polynomial.map ((Quotientₓ.mk I).comp C).range_restrict f).Coeff n = 0 at hf
    rw [coeff_map, Subtype.ext_iff] at hf
    rwa [mem_comap, ← quotient.eq_zero_iff_mem, ← RingHom.comp_apply]
  have := map_is_prime_of_surjective (show Function.Surjective (map_ring_hom i) from map_surjective i hi) hi'
  suffices (I.map (Polynomial.mapRingHom i)).jacobson = I.map (Polynomial.mapRingHom i) by
    replace this := congr_arg (comap (Polynomial.mapRingHom i)) this
    rw [← map_jacobson_of_surjective _ hi', comap_map_of_surjective _ _, comap_map_of_surjective _ _] at this
    refine'
      le_antisymmₓ (le_transₓ (le_sup_of_le_left le_rfl) (le_transₓ (le_of_eqₓ this) (sup_le le_rfl hi'))) le_jacobson
    all_goals
      exact Polynomial.map_surjective i hi
  exact
    @is_jacobson_polynomial_of_domain R' _ _ (is_jacobson_of_surjective ⟨i, hi⟩) (map (map_ring_hom i) I) _
      (eq_zero_of_polynomial_mem_map_range I)

theorem is_jacobson_polynomial_iff_is_jacobson : IsJacobson R[X] ↔ IsJacobson R := by
  refine' ⟨_, is_jacobson_polynomial_of_is_jacobson⟩
  intro H
  exact
    is_jacobson_of_surjective
      ⟨eval₂_ring_hom (RingHom.id _) 1, fun x =>
        ⟨C x, by
          simp only [← coe_eval₂_ring_hom, ← RingHom.id_apply, ← eval₂_C]⟩⟩

instance [IsJacobson R] : IsJacobson R[X] :=
  is_jacobson_polynomial_iff_is_jacobson.mpr ‹IsJacobson R›

end CommRingₓ

section

variable {R : Type _} [CommRingₓ R] [IsJacobson R]

variable (P : Ideal R[X]) [hP : P.IsMaximal]

include P hP

theorem is_maximal_comap_C_of_is_maximal [Nontrivial R] (hP' : ∀ x : R, c x ∈ P → x = 0) :
    IsMaximal (comap (c : R →+* R[X]) P : Ideal R) := by
  have hp'_prime : (P.comap (C : R →+* R[X]) : Ideal R).IsPrime := comap_is_prime C P
  obtain ⟨m, hm⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_of_maximal P polynomial_not_is_field)
  have : (m : R[X]) ≠ 0
  rwa [Ne.def, Submodule.coe_eq_zero]
  let φ : R ⧸ P.comap (C : R →+* R[X]) →+* R[X] ⧸ P := quotient_map P (C : R →+* R[X]) le_rfl
  let M : Submonoid (R ⧸ P.comap C) :=
    Submonoid.powers ((m : R[X]).map (Quotientₓ.mk (P.comap (C : R →+* R[X]) : Ideal R))).leadingCoeff
  rw [← bot_quotient_is_maximal_iff]
  have hp0 : ((m : R[X]).map (Quotientₓ.mk (P.comap (C : R →+* R[X]) : Ideal R))).leadingCoeff ≠ 0 := fun hp0' =>
    this <|
      map_injective (Quotientₓ.mk (P.comap (C : R →+* R[X]) : Ideal R))
        ((injective_iff_map_eq_zero (Quotientₓ.mk (P.comap (C : R →+* R[X]) : Ideal R))).2 fun x hx => by
          rwa [quotient.eq_zero_iff_mem,
            (by
              rwa [eq_bot_iff] : (P.comap C : Ideal R) = ⊥)] at
            hx)
        (by
          simpa only [← leading_coeff_eq_zero, ← Polynomial.map_zero] using hp0')
  have hM : (0 : R ⧸ P.comap C) ∉ M := fun ⟨n, hn⟩ => hp0 (pow_eq_zero hn)
  suffices (⊥ : Ideal (Localization M)).IsMaximal by
    rw [← IsLocalization.comap_map_of_is_prime_disjoint M (Localization M) ⊥ bot_prime fun x hx => hM (hx.2 ▸ hx.1)]
    refine'
      ((is_maximal_iff_is_maximal_disjoint (Localization M) _ _).mp
          (by
            rwa [map_bot])).1
    swap
    exact Localization.is_localization
  let M' : Submonoid (R[X] ⧸ P) := M.map φ
  have hM' : (0 : R[X] ⧸ P) ∉ M' := fun ⟨z, hz⟩ => hM (quotient_map_injective (trans hz.2 φ.map_zero.symm) ▸ hz.1)
  have : IsDomain (Localization M') :=
    IsLocalization.is_domain_localization (le_non_zero_divisors_of_no_zero_divisors hM')
  suffices (⊥ : Ideal (Localization M')).IsMaximal by
    rw
      [le_antisymmₓ bot_le
        (comap_bot_le_of_injective _
          (IsLocalization.map_injective_of_injective M (Localization M) (Localization M') quotient_map_injective))]
    refine' is_maximal_comap_of_is_integral_of_is_maximal' _ _ ⊥ this
    apply is_integral_is_localization_polynomial_quotient P _ (Submodule.coe_mem m)
  rw [(map_bot.symm : (⊥ : Ideal (Localization M')) = map (algebraMap (R[X] ⧸ P) (Localization M')) ⊥)]
  let bot_maximal := (bot_quotient_is_maximal_iff _).mpr hP
  refine' map.is_maximal (algebraMap _ _) (IsField.localization_map_bijective hM' _) bot_maximal
  rwa [← quotient.maximal_ideal_iff_is_field_quotient, ← bot_quotient_is_maximal_iff]

/-- Used to bootstrap the more general `quotient_mk_comp_C_is_integral_of_jacobson` -/
private theorem quotient_mk_comp_C_is_integral_of_jacobson' [Nontrivial R] (hR : IsJacobson R)
    (hP' : ∀ x : R, c x ∈ P → x = 0) : ((Quotient.mk P).comp c : R →+* R[X] ⧸ P).IsIntegral := by
  refine' (is_integral_quotient_map_iff _).mp _
  let P' : Ideal R := P.comap C
  obtain ⟨pX, hpX, hp0⟩ :=
    exists_nonzero_mem_of_ne_bot (ne_of_ltₓ (bot_lt_of_maximal P polynomial_not_is_field)).symm hP'
  let M : Submonoid (R ⧸ P') := Submonoid.powers (pX.map (Quotientₓ.mk P')).leadingCoeff
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotient_map P C le_rfl
  have hp'_prime : P'.is_prime := comap_is_prime C P
  have hM : (0 : R ⧸ P') ∉ M := fun ⟨n, hn⟩ => hp0 <| leading_coeff_eq_zero.mp (pow_eq_zero hn)
  let M' : Submonoid (R[X] ⧸ P) := M.map (quotient_map P C le_rfl)
  refine' (quotient_map P C le_rfl).is_integral_tower_bot_of_is_integral (algebraMap _ (Localization M')) _ _
  · refine'
      IsLocalization.injective (Localization M')
        (show M' ≤ _ from le_non_zero_divisors_of_no_zero_divisors fun hM' => hM _)
    exact
      let ⟨z, zM, z0⟩ := hM'
      quotient_map_injective (trans z0 φ.map_zero.symm) ▸ zM
    
  · rw [← IsLocalization.map_comp M.le_comap_map]
    refine'
      RingHom.is_integral_trans (algebraMap (R ⧸ P') (Localization M))
        (IsLocalization.map (Localization M') _ M.le_comap_map) _ _
    · exact
        (algebraMap (R ⧸ P') (Localization M)).is_integral_of_surjective
          (IsField.localization_map_bijective hM
              ((quotient.maximal_ideal_iff_is_field_quotient _).mp (is_maximal_comap_C_of_is_maximal P hP'))).2
      
    · -- `convert` here is faster than `exact`, and this proof is near the time limit.
      convert is_integral_is_localization_polynomial_quotient P pX hpX
      
    

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
/-- If `R` is a Jacobson ring, and `P` is a maximal ideal of `polynomial R`,
  then `R → R[X]/P` is an integral map. -/
theorem quotient_mk_comp_C_is_integral_of_jacobson : ((Quotient.mk P).comp c : R →+* R[X] ⧸ P).IsIntegral := by
  let P' : Ideal R := P.comap C
  have : P'.is_prime := comap_is_prime C P
  let f : R[X] →+* Polynomial (R ⧸ P') := Polynomial.mapRingHom (Quotientₓ.mk P')
  have hf : Function.Surjective f := map_surjective (Quotientₓ.mk P') quotient.mk_surjective
  have hPJ : P = (P.map f).comap f := by
    rw [comap_map_of_surjective _ hf]
    refine' le_antisymmₓ (le_sup_of_le_left le_rfl) (sup_le le_rfl _)
    refine' fun p hp => polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => quotient.eq_zero_iff_mem.mp _
    simpa only [← coeff_map, ← coe_map_ring_hom] using (polynomial.ext_iff.mp hp) n
  refine' RingHom.is_integral_tower_bot_of_is_integral _ _ (injective_quotient_le_comap_map P) _
  rw [← quotient_mk_maps_eq]
  refine' RingHom.is_integral_trans _ _ ((Quotientₓ.mk P').is_integral_of_surjective quotient.mk_surjective) _
  apply quotient_mk_comp_C_is_integral_of_jacobson' _ _ fun x hx => _
  any_goals {
  }
  · exact
      Or.rec_on (map_eq_top_or_is_maximal_of_surjective f hf hP)
        (fun h => absurd (trans (h ▸ hPJ : P = comap f ⊤) comap_top : P = ⊤) hP.ne_top) id
    
  · infer_instance
    
  · obtain ⟨z, rfl⟩ := quotient.mk_surjective x
    rwa [quotient.eq_zero_iff_mem, mem_comap, hPJ, mem_comap, coe_map_ring_hom, map_C]
    

theorem is_maximal_comap_C_of_is_jacobson : (P.comap (c : R →+* R[X])).IsMaximal := by
  rw [← @mk_ker _ _ P, RingHom.ker_eq_comap_bot, comap_comap]
  exact
    is_maximal_comap_of_is_integral_of_is_maximal' _ (quotient_mk_comp_C_is_integral_of_jacobson P) ⊥
      ((bot_quotient_is_maximal_iff _).mpr hP)

omit P hP

theorem comp_C_integral_of_surjective_of_jacobson {S : Type _} [Field S] (f : R[X] →+* S) (hf : Function.Surjective f) :
    (f.comp c).IsIntegral := by
  have : f.ker.IsMaximal := RingHom.ker_is_maximal_of_surjective f hf
  let g : R[X] ⧸ f.ker →+* S := Ideal.Quotient.lift f.ker f fun _ h => h
  have hfg : g.comp (Quotientₓ.mk f.ker) = f := ring_hom_ext' rfl rfl
  rw [← hfg, RingHom.comp_assoc]
  refine'
    RingHom.is_integral_trans _ g (quotient_mk_comp_C_is_integral_of_jacobson f.ker) (g.is_integral_of_surjective _)
  --(quotient.lift_surjective f.ker f _ hf)),
  rw [← hfg] at hf
  exact Function.Surjective.of_comp hf

end

end Polynomial

open MvPolynomial RingHom

namespace MvPolynomial

theorem is_jacobson_mv_polynomial_fin {R : Type _} [CommRingₓ R] [H : IsJacobson R] :
    ∀ n : ℕ, IsJacobson (MvPolynomial (Finₓ n) R)
  | 0 =>
    (is_jacobson_iso ((renameEquiv R (Equivₓ.equivPempty (Finₓ 0))).toRingEquiv.trans (isEmptyRingEquiv R Pempty))).mpr
      H
  | n + 1 =>
    (is_jacobson_iso (finSuccEquiv R n).toRingEquiv).2
      (Polynomial.is_jacobson_polynomial_iff_is_jacobson.2 (is_jacobson_mv_polynomial_fin n))

/-- General form of the nullstellensatz for Jacobson rings, since in a Jacobson ring we have
  `Inf {P maximal | P ≥ I} = Inf {P prime | P ≥ I} = I.radical`. Fields are always Jacobson,
  and in that special case this is (most of) the classical Nullstellensatz,
  since `I(V(I))` is the intersection of maximal ideals containing `I`, which is then `I.radical` -/
instance {R : Type _} [CommRingₓ R] {ι : Type _} [Fintype ι] [IsJacobson R] : IsJacobson (MvPolynomial ι R) := by
  have := Classical.decEq ι
  let e := Fintype.equivFin ι
  rw [is_jacobson_iso (rename_equiv R e).toRingEquiv]
  exact is_jacobson_mv_polynomial_fin _

variable {n : ℕ}

theorem quotient_mk_comp_C_is_integral_of_jacobson {R : Type _} [CommRingₓ R] [IsJacobson R]
    (P : Ideal (MvPolynomial (Finₓ n) R)) [P.IsMaximal] :
    ((Quotient.mk P).comp MvPolynomial.c : R →+* MvPolynomial _ R ⧸ P).IsIntegral := by
  induction' n with n IH
  · refine' RingHom.is_integral_of_surjective _ (Function.Surjective.comp quotient.mk_surjective _)
    exact C_surjective (Finₓ 0)
    
  · rw [← fin_succ_equiv_comp_C_eq_C, ← RingHom.comp_assoc, ← RingHom.comp_assoc, ← quotient_map_comp_mk le_rfl,
      RingHom.comp_assoc Polynomial.c, ← quotient_map_comp_mk le_rfl, RingHom.comp_assoc, RingHom.comp_assoc, ←
      quotient_map_comp_mk le_rfl, ← RingHom.comp_assoc (Quotientₓ.mk _)]
    refine' RingHom.is_integral_trans _ _ _ _
    · refine' RingHom.is_integral_trans _ _ (is_integral_of_surjective _ quotient.mk_surjective) _
      refine' RingHom.is_integral_trans _ _ _ _
      · apply (is_integral_quotient_map_iff _).mpr (IH _)
        apply polynomial.is_maximal_comap_C_of_is_jacobson _
        · exact mv_polynomial.is_jacobson_mv_polynomial_fin n
          
        · apply comap_is_maximal_of_surjective
          exact (finSuccEquiv R n).symm.Surjective
          
        
      · refine' (is_integral_quotient_map_iff _).mpr _
        rw [← quotient_map_comp_mk le_rfl]
        refine' RingHom.is_integral_trans _ _ _ ((is_integral_quotient_map_iff _).mpr _)
        · exact RingHom.is_integral_of_surjective _ quotient.mk_surjective
          
        · apply polynomial.quotient_mk_comp_C_is_integral_of_jacobson _
          · exact mv_polynomial.is_jacobson_mv_polynomial_fin n
            
          · exact comap_is_maximal_of_surjective _ (finSuccEquiv R n).symm.Surjective
            
          
        
      
    · refine' (is_integral_quotient_map_iff _).mpr _
      refine' RingHom.is_integral_trans _ _ _ (is_integral_of_surjective _ quotient.mk_surjective)
      exact RingHom.is_integral_of_surjective _ (finSuccEquiv R n).symm.Surjective
      
    

theorem comp_C_integral_of_surjective_of_jacobson {R : Type _} [CommRingₓ R] [IsJacobson R] {σ : Type _} [Fintype σ]
    {S : Type _} [Field S] (f : MvPolynomial σ R →+* S) (hf : Function.Surjective f) : (f.comp c).IsIntegral := by
  have e := (Fintype.equivFin σ).symm
  let f' : MvPolynomial (Finₓ _) R →+* S := f.comp (rename_equiv R e).toRingEquiv.toRingHom
  have hf' : Function.Surjective f' := Function.Surjective.comp hf (rename_equiv R e).Surjective
  have : (f'.comp C).IsIntegral := by
    have : f'.ker.IsMaximal := ker_is_maximal_of_surjective f' hf'
    let g : MvPolynomial _ R ⧸ f'.ker →+* S := Ideal.Quotient.lift f'.ker f' fun _ h => h
    have hfg : g.comp (Quotientₓ.mk f'.ker) = f' := ring_hom_ext (fun r => rfl) fun i => rfl
    rw [← hfg, RingHom.comp_assoc]
    refine'
      RingHom.is_integral_trans _ g (quotient_mk_comp_C_is_integral_of_jacobson f'.ker) (g.is_integral_of_surjective _)
    rw [← hfg] at hf'
    exact Function.Surjective.of_comp hf'
  rw [RingHom.comp_assoc] at this
  convert this
  refine' RingHom.ext fun x => _
  exact ((rename_equiv R e).commutes' x).symm

end MvPolynomial

end Ideal

