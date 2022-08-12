/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz, Johan Commelin
-/
import Mathbin.Algebra.Homology.Additive
import Mathbin.AlgebraicTopology.MooreComplex
import Mathbin.Algebra.BigOperators.Fin

/-!

# The alternating face map complex of a simplicial object in a preadditive category

We construct the alternating face map complex, as a
functor `alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ`
for any preadditive category `C`. For any simplicial object `X` in `C`,
this is the homological complex `... → X_2 → X_1 → X_0`
where the differentials are alternating sums of faces.

We also construct the natural transformation
`inclusion_of_Moore_complex : normalized_Moore_complex A ⟶ alternating_face_map_complex A`
when `A` is an abelian category.

## References
* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex

-/


open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

open CategoryTheory.Preadditive CategoryTheory.Category

open Opposite

open BigOperators

open Simplicial

noncomputable section

namespace AlgebraicTopology

namespace AlternatingFaceMapComplex

/-!
## Construction of the alternating face map complex
-/


variable {C : Type _} [Category C] [Preadditive C]

variable (X : SimplicialObject C)

variable (Y : SimplicialObject C)

/-- The differential on the alternating face map complex is the alternate
sum of the face maps -/
@[simp]
def objD (n : ℕ) : X _[n + 1] ⟶ X _[n] :=
  ∑ i : Finₓ (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i

/-- ## The chain complex relation `d ≫ d`
-/
theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 := by
  -- we start by expanding d ≫ d as a double sum
  dsimp'
  rw [comp_sum]
  let d_l := fun j : Finₓ (n + 3) => (-1 : ℤ) ^ (j : ℕ) • X.δ j
  let d_r := fun i : Finₓ (n + 2) => (-1 : ℤ) ^ (i : ℕ) • X.δ i
  rw
    [show (fun i => (∑ j : Finₓ (n + 3), d_l j) ≫ d_r i) = fun i => ∑ j : Finₓ (n + 3), d_l j ≫ d_r i by
      ext i
      rw [sum_comp]]
  rw [← Finset.sum_product']
  -- then, we decompose the index set P into a subet S and its complement Sᶜ
  let P := Finₓ (n + 2) × Finₓ (n + 3)
  let S := finset.univ.filter fun ij : P => (ij.2 : ℕ) ≤ (ij.1 : ℕ)
  let term := fun ij : P => d_l ij.2 ≫ d_r ij.1
  erw
    [show (∑ ij : P, term ij) = (∑ ij in S, term ij) + ∑ ij in Sᶜ, term ij by
      rw [Finset.sum_add_sum_compl]]
  rw [← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  /- we are reduced to showing that two sums are equal, and this is obtained
    by constructing a bijection φ : S -> Sᶜ, which maps (i,j) to (j,i+1),
    and by comparing the terms -/
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Finₓ.castLt ij.2 (lt_of_le_of_ltₓ (finset.mem_filter.mp hij).right (Finₓ.is_lt ij.1)), ij.1.succ)
  apply Finset.sum_bij φ
  · -- φ(S) is contained in Sᶜ
    intro ij hij
    simp only [← Finset.mem_univ, ← Finset.compl_filter, ← Finset.mem_filter, ← true_andₓ, ← Finₓ.coe_succ, ←
      Finₓ.coe_cast_lt] at hij⊢
    linarith
    
  · -- identification of corresponding terms in both sums
    rintro ⟨i, j⟩ hij
    simp only [← term, ← d_l, ← d_r, ← φ, ← comp_zsmul, ← zsmul_comp, neg_smul, mul_smul, ← pow_addₓ, ← neg_mul, ←
      mul_oneₓ, ← Finₓ.coe_cast_lt, ← Finₓ.coe_succ, ← pow_oneₓ, ← mul_neg, ← neg_negₓ]
    let jj : Finₓ (n + 2) := (φ (i, j) hij).1
    have ineq : jj ≤ i := by
      rw [← Finₓ.coe_fin_le]
      simpa using hij
    rw [CategoryTheory.SimplicialObject.δ_comp_δ X ineq, Finₓ.cast_succ_cast_lt, mul_comm]
    
  · -- φ : S → Sᶜ is injective
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij hij' h
    rw [Prod.mk.inj_iff]
    refine'
      ⟨by
        simpa using congr_arg Prod.snd h, _⟩
    have h1 := congr_arg Finₓ.castSucc (congr_arg Prod.fst h)
    simpa [← Finₓ.cast_succ_cast_lt] using h1
    
  · -- φ : S → Sᶜ is surjective
    rintro ⟨i', j'⟩ hij'
    simp only [← true_andₓ, ← Finset.mem_univ, ← Finset.compl_filter, ← not_leₓ, ← Finset.mem_filter] at hij'
    refine' ⟨(j'.pred _, Finₓ.castSucc i'), _, _⟩
    · intro H
      simpa only [← H, ← Nat.not_lt_zeroₓ, ← Finₓ.coe_zero] using hij'
      
    · simpa only [← true_andₓ, ← Finset.mem_univ, ← Finₓ.coe_cast_succ, ← Finₓ.coe_pred, ← Finset.mem_filter] using
        Nat.le_pred_of_ltₓ hij'
      
    · simp only [← Prod.mk.inj_iff, ← Finₓ.succ_pred, ← Finₓ.cast_lt_cast_succ]
      constructor <;> rfl
      
    

/-!
## Construction of the alternating face map complex functor
-/


/-- The alternating face map complex, on objects -/
def obj : ChainComplex C ℕ :=
  ChainComplex.of (fun n => X _[n]) (objD X) (d_squared X)

variable {X} {Y}

/-- The alternating face map complex, on morphisms -/
@[simp]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => f.app (op [n])) fun n => by
    dsimp'
    rw [comp_sum, sum_comp]
    apply Finset.sum_congr rfl fun x h => _
    rw [comp_zsmul, zsmul_comp]
    apply congr_arg
    erw [f.naturality]
    rfl

end AlternatingFaceMapComplex

variable (C : Type _) [Category C] [Preadditive C]

/-- The alternating face map complex, as a functor -/
@[simps]
def alternatingFaceMapComplex : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj := AlternatingFaceMapComplex.obj
  map := fun X Y f => AlternatingFaceMapComplex.map f

variable {C}

theorem map_alternating_face_map_complex {D : Type _} [Category D] [Preadditive D] (F : C ⥤ D) [F.Additive] :
    alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex _ =
      (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D :=
  by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    ext n
    simp only [← functor.comp_map, ← alternating_face_map_complex.map, ← alternating_face_map_complex_map, ←
      functor.map_homological_complex_map_f, ← ChainComplex.of_hom_f, ← simplicial_object.whiskering_obj_map_app, ←
      HomologicalComplex.comp_f, ← HomologicalComplex.eq_to_hom_f, ← eq_to_hom_refl, ← comp_id, ← id_comp]
    
  · intro X
    erw [ChainComplex.map_chain_complex_of]
    congr
    ext n
    simp only [← alternating_face_map_complex.obj_d, ← functor.map_sum]
    congr
    ext
    apply functor.map_zsmul
    

/-!
## Construction of the natural inclusion of the normalized Moore complex
-/


variable {A : Type _} [Category A] [Abelian A]

/-- The inclusion map of the Moore complex in the alternating face map complex -/
def inclusionOfMooreComplexMap (X : SimplicialObject A) :
    (normalizedMooreComplex A).obj X ⟶ (alternatingFaceMapComplex A).obj X :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => (NormalizedMooreComplex.objX X n).arrow) fun n => by
    /- we have to show the compatibility of the differentials on the alternating
             face map complex with those defined on the normalized Moore complex:
             we first get rid of the terms of the alternating sum that are obviously
             zero on the normalized_Moore_complex -/
    simp only [← alternating_face_map_complex.obj_d]
    rw [comp_sum]
    let t := fun j : Finₓ (n + 2) => (normalized_Moore_complex.obj_X X (n + 1)).arrow ≫ ((-1 : ℤ) ^ (j : ℕ) • X.δ j)
    have def_t :
      ∀ j : Finₓ (n + 2), t j = (normalized_Moore_complex.obj_X X (n + 1)).arrow ≫ ((-1 : ℤ) ^ (j : ℕ) • X.δ j) := by
      intro j
      rfl
    rw [Finₓ.sum_univ_succ t]
    have null : ∀ j : Finₓ (n + 1), t j.succ = 0 := by
      intro j
      rw [def_t, comp_zsmul, ← zsmul_zero ((-1 : ℤ) ^ (j.succ : ℕ))]
      apply congr_arg
      rw [normalized_Moore_complex.obj_X]
      rw [←
        factor_thru_arrow _ _
          (finset_inf_arrow_factors Finset.univ _ j
            (by
              simp only [← Finset.mem_univ]))]
      slice_lhs 2 3 => rw [kernel_subobject_arrow_comp (X.δ j.succ)]
      simp only [← comp_zero]
    rw [Fintype.sum_eq_zero _ null]
    simp only [← add_zeroₓ]
    -- finally, we study the remaining term which is induced by X.δ 0
    let eq := def_t 0
    rw
      [show (-1 : ℤ) ^ ((0 : Finₓ (n + 2)) : ℕ) = 1 by
        ring] at
      eq
    rw [one_smul] at eq
    rw [Eq]
    cases n <;> dsimp' <;> simp

@[simp]
theorem inclusion_of_Moore_complex_map_f (X : SimplicialObject A) (n : ℕ) :
    (inclusionOfMooreComplexMap X).f n = (NormalizedMooreComplex.objX X n).arrow :=
  ChainComplex.of_hom_f _ _ _ _ _ _ _ _ n

variable (A)

/-- The inclusion map of the Moore complex in the alternating face map complex,
as a natural transformation -/
@[simps]
def inclusionOfMooreComplex :
    normalizedMooreComplex A ⟶ alternatingFaceMapComplex A where app := inclusionOfMooreComplexMap

end AlgebraicTopology

