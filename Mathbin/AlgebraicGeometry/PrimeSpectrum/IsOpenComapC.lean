/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathbin.RingTheory.Polynomial.Basic

/-!
The morphism `Spec R[x] --> Spec R` induced by the natural inclusion `R --> R[x]` is an open map.

The main result is the first part of the statement of Lemma 00FB in the Stacks Project.

https://stacks.math.columbia.edu/tag/00FB
-/


open Ideal Polynomial PrimeSpectrum Set

open Polynomial

namespace AlgebraicGeometry

namespace Polynomial

variable {R : Type _} [CommRingₓ R] {f : R[X]}

/-- Given a polynomial `f ∈ R[x]`, `image_of_Df` is the subset of `Spec R` where at least one
of the coefficients of `f` does not vanish.  Lemma `image_of_Df_eq_comap_C_compl_zero_locus`
proves that `image_of_Df` is the image of `(zero_locus {f})ᶜ` under the morphism
`comap C : Spec R[x] → Spec R`. -/
def ImageOfDf (f) : Set (PrimeSpectrum R) :=
  { p : PrimeSpectrum R | ∃ i : ℕ, coeff f i ∉ p.asIdeal }

theorem is_open_image_of_Df : IsOpen (ImageOfDf f) := by
  rw [image_of_Df, set_of_exists fun i (x : PrimeSpectrum R) => coeff f i ∉ x.val]
  exact is_open_Union fun i => is_open_basic_open

/-- If a point of `Spec R[x]` is not contained in the vanishing set of `f`, then its image in
`Spec R` is contained in the open set where at least one of the coefficients of `f` is non-zero.
This lemma is a reformulation of `exists_coeff_not_mem_C_inverse`. -/
theorem comap_C_mem_image_of_Df {I : PrimeSpectrum R[X]} (H : I ∈ (ZeroLocus {f} : Set (PrimeSpectrum R[X]))ᶜ) :
    PrimeSpectrum.comap (Polynomial.c : R →+* R[X]) I ∈ ImageOfDf f :=
  exists_coeff_not_mem_C_inverse (mem_compl_zero_locus_iff_not_mem.mp H)

/-- The open set `image_of_Df f` coincides with the image of `basic_open f` under the
morphism `C⁺ : Spec R[x] → Spec R`. -/
theorem image_of_Df_eq_comap_C_compl_zero_locus :
    ImageOfDf f = PrimeSpectrum.comap (c : R →+* R[X]) '' ZeroLocus {f}ᶜ := by
  refine' ext fun x => ⟨fun hx => ⟨⟨map C x.val, is_prime_map_C_of_is_prime x.property⟩, ⟨_, _⟩⟩, _⟩
  · rw [mem_compl_eq, mem_zero_locus, singleton_subset_iff]
    cases' hx with i hi
    exact fun a => hi (mem_map_C_iff.mp a i)
    
  · refine' Subtype.ext (ext fun x => ⟨fun h => _, fun h => subset_span (mem_image_of_mem C.1 h)⟩)
    rw [← @coeff_C_zero R x _]
    exact mem_map_C_iff.mp h 0
    
  · rintro ⟨xli, complement, rfl⟩
    exact comap_C_mem_image_of_Df complement
    

/-- The morphism `C⁺ : Spec R[x] → Spec R` is open.
Stacks Project "Lemma 00FB", first part.

https://stacks.math.columbia.edu/tag/00FB
-/
theorem is_open_map_comap_C : IsOpenMap (PrimeSpectrum.comap (c : R →+* R[X])) := by
  rintro U ⟨s, z⟩
  rw [← compl_compl U, ← z, ← Union_of_singleton_coe s, zero_locus_Union, compl_Inter, image_Union]
  simp_rw [← image_of_Df_eq_comap_C_compl_zero_locus]
  exact is_open_Union fun f => is_open_image_of_Df

end Polynomial

end AlgebraicGeometry

