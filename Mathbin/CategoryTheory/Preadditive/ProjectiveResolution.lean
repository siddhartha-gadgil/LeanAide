/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Preadditive.Projective
import Mathbin.Algebra.Homology.Single
import Mathbin.Algebra.Homology.HomotopyCategory

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
a `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a chain map `P.π` from `C` to the chain complex consisting just of `Z` in degree zero,
so that the augmented chain complex is exact.

When `C` is abelian, this exactness condition is equivalent to `π` being a quasi-isomorphism.
It turns out that this formulation allows us to set up the basic theory of derived functors
without even assuming `C` is abelian.

(Typically, however, to show `has_projective_resolutions C`
one will assume `enough_projectives C` and `abelian C`.
This construction appears in `category_theory.abelian.projectives`.)

We show that given `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y`,
any morphism `X ⟶ Y` admits a lift to a chain map `P.complex ⟶ Q.complex`.
(It is a lift in the sense that
the projection maps `P.π` and `Q.π` intertwine the lift and the original morphism.)

Moreover, we show that any two such lifts are homotopic.

As a consequence, if every object admits a projective resolution,
we can construct a functor `projective_resolutions C : C ⥤ homotopy_category C`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Projective

section

variable [HasZeroObject C] [HasZeroMorphisms C] [HasEqualizers C] [HasImages C]

/-- A `ProjectiveResolution Z` consists of a bundled `ℕ`-indexed chain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.

(We don't actually ask here that the chain map is a quasi-iso, just exactness everywhere:
that `π` is a quasi-iso is a lemma when the category is abelian.
Should we just ask for it here?)

Except in situations where you want to provide a particular projective resolution
(for example to compute a derived functor),
you will not typically need to use this bundled object, and will instead use
* `projective_resolution Z`: the `ℕ`-indexed chain complex
  (equipped with `projective` and `exact` instances)
* `projective_resolution.π Z`: the chain map from `projective_resolution Z` to
  `(single C _ 0).obj Z` (all the components are equipped with `epi` instances,
  and when the category is `abelian` we will show `π` is a quasi-iso).
-/
@[nolint has_inhabited_instance]
structure ProjectiveResolution (Z : C) where
  complex : ChainComplex C ℕ
  π : HomologicalComplex.Hom complex ((ChainComplex.single₀ C).obj Z)
  Projective : ∀ n, Projective (complex.x n) := by
    run_tac
      tactic.apply_instance
  exact₀ : Exact (complex.d 1 0) (π.f 0)
  exact : ∀ n, Exact (complex.d (n + 2) (n + 1)) (complex.d (n + 1) n)
  Epi : Epi (π.f 0) := by
    run_tac
      tactic.apply_instance

attribute [instance] ProjectiveResolution.projective ProjectiveResolution.epi

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`out] []
/-- An object admits a projective resolution.
-/
class HasProjectiveResolution (Z : C) : Prop where
  out : Nonempty (ProjectiveResolution Z)

section

variable (C)

/-- You will rarely use this typeclass directly: it is implied by the combination
`[enough_projectives C]` and `[abelian C]`.
By itself it's enough to set up the basic theory of derived functors.
-/
class HasProjectiveResolutions : Prop where
  out : ∀ Z : C, HasProjectiveResolution Z

attribute [instance] has_projective_resolutions.out

end

namespace ProjectiveResolution

@[simp]
theorem π_f_succ {Z : C} (P : ProjectiveResolution Z) (n : ℕ) : P.π.f (n + 1) = 0 := by
  apply zero_of_target_iso_zero
  dsimp'
  rfl

@[simp]
theorem complex_d_comp_π_f_zero {Z : C} (P : ProjectiveResolution Z) : P.complex.d 1 0 ≫ P.π.f 0 = 0 :=
  P.exact₀.w

@[simp]
theorem complex_d_succ_comp {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
    P.complex.d (n + 2) (n + 1) ≫ P.complex.d (n + 1) n = 0 :=
  (P.exact _).w

instance {Z : C} (P : ProjectiveResolution Z) (n : ℕ) : CategoryTheory.Epi (P.π.f n) := by
  cases n <;> infer_instance

/-- A projective object admits a trivial projective resolution: itself in degree 0. -/
def self (Z : C) [CategoryTheory.Projective Z] : ProjectiveResolution Z where
  complex := (ChainComplex.single₀ C).obj Z
  π := 𝟙 ((ChainComplex.single₀ C).obj Z)
  Projective := fun n => by
    cases n
    · dsimp'
      infer_instance
      
    · dsimp'
      infer_instance
      
  exact₀ := by
    dsimp'
    exact exact_zero_mono _
  exact := fun n => by
    dsimp'
    exact exact_of_zero _ _
  Epi := by
    dsimp'
    infer_instance

/-- Auxiliary construction for `lift`. -/
def liftFZero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.x 0 ⟶ Q.complex.x 0 :=
  factorThru (P.π.f 0 ≫ f) (Q.π.f 0)

/-- Auxiliary construction for `lift`. -/
def liftFOne {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.x 1 ⟶ Q.complex.x 1 :=
  Exact.lift (P.complex.d 1 0 ≫ liftFZero f P Q) (Q.complex.d 1 0) (Q.π.f 0) Q.exact₀
    (by
      simp [← lift_f_zero, ← P.exact₀.w_assoc])

/-- Auxiliary lemma for `lift`. -/
@[simp]
theorem lift_f_one_zero_comm {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    liftFOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ liftFZero f P Q := by
  dsimp' [← lift_f_zero, ← lift_f_one]
  simp

/-- Auxiliary construction for `lift`. -/
def liftFSucc {Y Z : C} (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) (n : ℕ)
    (g : P.complex.x n ⟶ Q.complex.x n) (g' : P.complex.x (n + 1) ⟶ Q.complex.x (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ'g'' : P.complex.x (n + 2) ⟶ Q.complex.x (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨Exact.lift (P.complex.d (n + 2) (n + 1) ≫ g') (Q.complex.d (n + 2) (n + 1)) (Q.complex.d (n + 1) n) (Q.exact _)
      (by
        simp [← w]),
    by
    simp ⟩

/-- A morphism in `C` lifts to a chain map between projective resolutions. -/
def lift {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) : P.complex ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (liftFZero f _ _) (liftFOne f _ _) (lift_f_one_zero_comm f _ _) fun n ⟨g, g', w⟩ =>
    liftFSucc P Q n g g' w

/-- The resolution maps intertwine the lift of a morphism and that morphism. -/
@[simp, reassoc]
theorem lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
  ext n
  rcases n with (_ | _ | n) <;>
    · dsimp' [← lift, ← lift_f_zero, ← lift_f_one]
      simp
      

-- Now that we've checked this property of the lift,
-- we can seal away the actual definition.
end ProjectiveResolution

end

namespace ProjectiveResolution

variable [HasZeroObject C] [Preadditive C] [HasEqualizers C] [HasImages C]

/-- An auxiliary definition for `lift_homotopy_zero`. -/
def liftHomotopyZeroZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z} (f : P.complex ⟶ Q.complex)
    (comm : f ≫ Q.π = 0) : P.complex.x 0 ⟶ Q.complex.x 1 :=
  Exact.lift (f.f 0) (Q.complex.d 1 0) (Q.π.f 0) Q.exact₀ (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

/-- An auxiliary definition for `lift_homotopy_zero`. -/
def liftHomotopyZeroOne {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z} (f : P.complex ⟶ Q.complex)
    (comm : f ≫ Q.π = 0) : P.complex.x 1 ⟶ Q.complex.x 2 :=
  Exact.lift (f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm) (Q.complex.d 2 1) (Q.complex.d 1 0) (Q.exact _)
    (by
      simp [← lift_homotopy_zero_zero])

/-- An auxiliary definition for `lift_homotopy_zero`. -/
def liftHomotopyZeroSucc {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z} (f : P.complex ⟶ Q.complex)
    (n : ℕ) (g : P.complex.x n ⟶ Q.complex.x (n + 1)) (g' : P.complex.x (n + 1) ⟶ Q.complex.x (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    P.complex.x (n + 2) ⟶ Q.complex.x (n + 3) :=
  Exact.lift (f.f (n + 2) - P.complex.d (n + 2) (n + 1) ≫ g') (Q.complex.d (n + 3) (n + 2))
    (Q.complex.d (n + 2) (n + 1)) (Q.exact _)
    (by
      simp [← w])

/-- Any lift of the zero morphism is homotopic to zero. -/
def liftHomotopyZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z} (f : P.complex ⟶ Q.complex)
    (comm : f ≫ Q.π = 0) : Homotopy f 0 :=
  Homotopy.mkInductive _ (liftHomotopyZeroZero f comm)
    (by
      simp [← lift_homotopy_zero_zero])
    (liftHomotopyZeroOne f comm)
    (by
      simp [← lift_homotopy_zero_one])
    fun n ⟨g, g', w⟩ =>
    ⟨liftHomotopyZeroSucc f n g g' w, by
      simp [← lift_homotopy_zero_succ, ← w]⟩

/-- Two lifts of the same morphism are homotopic. -/
def liftHomotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (g h : P.complex ⟶ Q.complex) (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) : Homotopy g h :=
  Homotopy.equivSubZero.invFun
    (liftHomotopyZero _
      (by
        simp [← g_comm, ← h_comm]))

/-- The lift of the identity morphism is homotopic to the identity chain map. -/
def liftIdHomotopy (X : C) (P : ProjectiveResolution X) : Homotopy (lift (𝟙 X) P P) (𝟙 P.complex) := by
  apply lift_homotopy (𝟙 X) <;> simp

/-- The lift of a composition is homotopic to the composition of the lifts. -/
def liftCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (R : ProjectiveResolution Z) : Homotopy (lift (f ≫ g) P R) (lift f P Q ≫ lift g Q R) := by
  apply lift_homotopy (f ≫ g) <;> simp

/-- Any two projective resolutions are homotopy equivalent. -/
-- We don't care about the actual definitions of these homotopies.
def homotopyEquiv {X : C} (P Q : ProjectiveResolution X) : HomotopyEquiv P.complex Q.complex where
  Hom := lift (𝟙 X) P Q
  inv := lift (𝟙 X) Q P
  homotopyHomInvId := by
    refine' (lift_comp_homotopy (𝟙 X) (𝟙 X) P Q P).symm.trans _
    simp [← category.id_comp]
    apply lift_id_homotopy
  homotopyInvHomId := by
    refine' (lift_comp_homotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans _
    simp [← category.id_comp]
    apply lift_id_homotopy

@[simp, reassoc]
theorem homotopy_equiv_hom_π {X : C} (P Q : ProjectiveResolution X) : (homotopyEquiv P Q).Hom ≫ Q.π = P.π := by
  simp [← HomotopyEquiv]

@[simp, reassoc]
theorem homotopy_equiv_inv_π {X : C} (P Q : ProjectiveResolution X) : (homotopyEquiv P Q).inv ≫ P.π = Q.π := by
  simp [← HomotopyEquiv]

end ProjectiveResolution

section

variable [HasZeroMorphisms C] [HasZeroObject C] [HasEqualizers C] [HasImages C]

/-- An arbitrarily chosen projective resolution of an object. -/
abbrev projectiveResolution (Z : C) [HasProjectiveResolution Z] : ChainComplex C ℕ :=
  (HasProjectiveResolution.out Z).some.complex

/-- The chain map from the arbitrarily chosen projective resolution `projective_resolution Z`
back to the chain complex consisting of `Z` supported in degree `0`. -/
abbrev projectiveResolution.π (Z : C) [HasProjectiveResolution Z] :
    projectiveResolution Z ⟶ (ChainComplex.single₀ C).obj Z :=
  (HasProjectiveResolution.out Z).some.π

/-- The lift of a morphism to a chain map between the arbitrarily chosen projective resolutions. -/
abbrev projectiveResolution.lift {X Y : C} (f : X ⟶ Y) [HasProjectiveResolution X] [HasProjectiveResolution Y] :
    projectiveResolution X ⟶ projectiveResolution Y :=
  ProjectiveResolution.lift f _ _

end

variable (C) [Preadditive C] [HasZeroObject C] [HasEqualizers C] [HasImages C] [HasProjectiveResolutions C]

/-- Taking projective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed chain complexes and chain maps up to homotopy).
-/
def projectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.down ℕ) where
  obj := fun X => (HomotopyCategory.quotient _ _).obj (projectiveResolution X)
  map := fun X Y f => (HomotopyCategory.quotient _ _).map (projectiveResolution.lift f)
  map_id' := fun X => by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.lift_id_homotopy
  map_comp' := fun X Y Z f g => by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.lift_comp_homotopy

end CategoryTheory

