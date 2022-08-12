/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.Algebra.Homology.Homotopy
import Mathbin.AlgebraicTopology.DoldKan.Notations

/-!

# Construction of homotopies for the Dold-Kan correspondence

TODO (@joelriou) continue adding the various files references below

(The general strategy of proof of the Dold-Kan correspondence is explained
in `equivalence.lean`.)

The purpose of the files `homotopies.lean`, `faces.lean`, `projections.lean`
and `p_infty.lean` is to construct an idempotent endomorphism
`P_infty : K[X] ⟶ K[X]` of the alternating face map complex
for each `X : simplicial_object C` when `C` is a preadditive category.
In the case `C` is abelian, this `P_infty` shall be the projection on the
normalized Moore subcomplex of `K[X]` associated to the decomposition of the
complex `K[X]` as a direct sum of this normalized subcomplex and of the
degenerate subcomplex.

In `p_infty.lean`, this endomorphism `P_infty` shall be obtained by
passing to the limit idempotent endomorphisms `P q` for all `(q : ℕ)`.
These endomorphisms `P q` are defined by induction. The idea is to
start from the identity endomorphism `P 0` of `K[X]` and to ensure by
induction that the `q` higher face maps (except $d_0$) vanish on the
image of `P q`. Then, in a certain degree `n`, the image of `P q` for
a big enough `q` will be contained in the normalized subcomplex. This
construction is done in `projections.lean`.

It would be easy to define the `P q` degreewise (similarly as it is done
in *Simplicial Homotopy Theory* by Goerrs-Jardine p. 149), but then we would
have to prove that they are compatible with the differential (i.e. they
are chain complex maps), and also that they are homotopic to the identity.
These two verifications are quite technical. In order to reduce the number
of such technical lemmas, the strategy that is followed here is to define
a series of null homotopic maps `Hσ q` (attached to families of maps `hσ`)
and use these in order to construct `P q` : the endomorphisms `P q`
shall basically be obtained by altering the identity endomorphism by adding
null homotopic maps, so that we get for free that they are morphisms
of chain complexes and that they are homotopic to the identity. The most
technical verifications that are needed about the null homotopic maps `Hσ`
are obtained in `faces.lean`.

In this file `homotopies.lean`, we define the null homotopic maps
`Hσ q : K[X] ⟶ K[X]`, show that they are natural (see `nat_trans_Hσ`) and
compatible the application of additive functors (see `map_Hσ`).

## References
* [Albrecht Dold, *Homology of Symmetric Products and Other Functors of Complexes*][dold1958]
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Preadditive

open CategoryTheory.SimplicialObject

open Homotopy

open Opposite

open Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C]

variable {X : SimplicialObject C}

/-- As we are using chain complexes indexed by `ℕ`, we shall need the relation
`c` such `c m n` if and only if `n+1=m`. -/
abbrev c :=
  ComplexShape.down ℕ

/-- Helper when we need some `c.rel i j` (i.e. `complex_shape.down ℕ`),
e.g. `c_mk n (n+1) rfl` -/
theorem c_mk (i j : ℕ) (h : j + 1 = i) : c.Rel i j :=
  ComplexShape.down_mk i j h

/-- This lemma is meant to be used with `null_homotopic_map'_f_of_not_rel_left` -/
theorem cs_down_0_not_rel_left (j : ℕ) : ¬c.Rel 0 j := by
  intro hj
  dsimp'  at hj
  apply Nat.not_succ_le_zeroₓ j
  rw [Nat.succ_eq_add_one, hj]

/-- The sequence of maps which gives the null homotopic maps `Hσ` that shall be in
the inductive construction of the projections `P q : K[X] ⟶ K[X]` -/
def hσ (q : ℕ) (n : ℕ) : X _[n] ⟶ X _[n + 1] :=
  if n < q then 0 else (-1 : ℤ) ^ (n - q) • X.σ ⟨n - q, Nat.sub_lt_succₓ n q⟩

/-- We can turn `hσ` into a datum that can be passed to `null_homotopic_map'`. -/
def hσ' (q : ℕ) : ∀ n m, c.Rel m n → (K[X].x n ⟶ K[X].x m) := fun n m hnm =>
  hσ q n ≫
    eqToHom
      (by
        congr)

theorem hσ'_eq_zero {q n m : ℕ} (hnq : n < q) (hnm : c.Rel m n) : (hσ' q n m hnm : X _[n] ⟶ X _[m]) = 0 := by
  simp only [← hσ', ← hσ]
  split_ifs
  exact zero_comp

theorem hσ'_eq {q n a m : ℕ} (ha : n = a + q) (hnm : c.Rel m n) :
    (hσ' q n m hnm : X _[n] ⟶ X _[m]) =
      ((-1 : ℤ) ^ a • X.σ ⟨a, Nat.lt_succ_iffₓ.mpr (Nat.Le.intro (Eq.symm ha))⟩) ≫
        eqToHom
          (by
            congr) :=
  by
  simp only [← hσ', ← hσ]
  split_ifs
  · exfalso
    linarith
    
  · have h' := tsub_eq_of_eq_add ha
    congr
    

/-- The null homotopic map $(hσ q) ∘ d + d ∘ (hσ q)$ -/
def hσₓ (q : ℕ) : K[X] ⟶ K[X] :=
  nullHomotopicMap' (hσ' q)

/-- `Hσ` is null homotopic -/
def homotopyHσToZero (q : ℕ) : Homotopy (hσₓ q : K[X] ⟶ K[X]) 0 :=
  nullHomotopy' (hσ' q)

/-- In degree `0`, the null homotopic map `Hσ` is zero. -/
theorem Hσ_eq_zero (q : ℕ) : (hσₓ q : K[X] ⟶ K[X]).f 0 = 0 := by
  unfold Hσ
  rw [null_homotopic_map'_f_of_not_rel_left (c_mk 1 0 rfl) cs_down_0_not_rel_left]
  cases q
  · rw
      [hσ'_eq
        (show 0 = 0 + 0 by
          rfl)
        (c_mk 1 0 rfl)]
    simp only [← pow_zeroₓ, ← Finₓ.mk_zero, ← one_zsmul, ← eq_to_hom_refl, ← category.comp_id]
    erw [ChainComplex.of_d]
    simp only [← alternating_face_map_complex.obj_d, ← Finₓ.sum_univ_two, ← Finₓ.coe_zero, ← pow_zeroₓ, ← one_zsmul, ←
      Finₓ.coe_one, ← pow_oneₓ, ← comp_add, ← neg_smul, ← one_zsmul, ← comp_neg, ← add_neg_eq_zero]
    erw [δ_comp_σ_self, δ_comp_σ_succ]
    
  · rw [hσ'_eq_zero (Nat.succ_posₓ q) (c_mk 1 0 rfl), zero_comp]
    

/-- The maps `hσ' q n m hnm` are natural on the simplicial object -/
theorem hσ'_naturality (q : ℕ) (n m : ℕ) (hnm : c.Rel m n) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op [n]) ≫ hσ' q n m hnm = hσ' q n m hnm ≫ f.app (op [m]) := by
  have h : n + 1 = m := hnm
  subst h
  simp only [← hσ', ← eq_to_hom_refl, ← comp_id]
  unfold hσ
  split_ifs
  · rw [zero_comp, comp_zero]
    
  · simp only [← zsmul_comp, ← comp_zsmul]
    erw [f.naturality]
    rfl
    

/-- For each q, `Hσ q` is a natural transformation. -/
def natTransHσ (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app := fun X => hσₓ q
  naturality' := fun X Y f => by
    unfold Hσ
    rw [null_homotopic_map'_comp, comp_null_homotopic_map']
    congr
    ext n m hnm
    simp only [← alternating_face_map_complex_map, ← alternating_face_map_complex.map, ← ChainComplex.of_hom_f, ←
      hσ'_naturality]

/-- The maps `hσ' q n m hnm` are compatible with the application of additive functors. -/
theorem map_hσ' {D : Type _} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive] (X : SimplicialObject C) (q n m : ℕ)
    (hnm : c.Rel m n) :
    (hσ' q n m hnm : K[((whiskering _ _).obj G).obj X].x n ⟶ _) = G.map (hσ' q n m hnm : K[X].x n ⟶ _) := by
  unfold hσ' hσ
  split_ifs
  · simp only [← functor.map_zero, ← zero_comp]
    
  · simpa only [← eq_to_hom_map, ← functor.map_comp, ← functor.map_zsmul]
    

/-- The null homotopic maps `Hσ` are compatible with the application of additive functors. -/
theorem map_Hσ {D : Type _} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive] (X : SimplicialObject C) (q n : ℕ) :
    (hσₓ q : K[((whiskering C D).obj G).obj X] ⟶ _).f n = G.map ((hσₓ q : K[X] ⟶ _).f n) := by
  unfold Hσ
  have eq := HomologicalComplex.congr_hom (map_null_homotopic_map' G (hσ' q)) n
  simp only [← functor.map_homological_complex_map_f, map_hσ'] at eq
  rw [Eq]
  let h := (functor.congr_obj (map_alternating_face_map_complex G) X).symm
  congr

end DoldKan

end AlgebraicTopology

