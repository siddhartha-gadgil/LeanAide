import Mathlib
import LeanAide.TheoremElab
import LeanAide.SimpleFrontend
import LeanAide.TranslateM
import LeanAide.TheoremElabCheck


open Lean Meta Elab Term
namespace LeanAide
open Translate

open Lean.Parser.Category
elab "#elab_thm4" s:str : command =>
  Command.liftTermElabM do
  let s := s.getString
  let res ←  elabThm4Aux s |>.run' {}
  match res with
  | Except.ok e =>
      logInfo m!"Obtained type: {e}"
  | Except.error err =>
      logInfo m!"Elaboration error: {err}"

elab "#elab_thm4_compare" s:str "equals" t:term : command =>
  Command.liftTermElabM do
  let s := s.getString
  let res ←  elabThm4Aux s |>.run' {}
  match res with
  | Except.ok e =>
      let tExpr ← elabType t
      logInfo m!"Obtained type: {e}; matches target: {← isDefEq e tExpr}"
  | Except.error err =>
      logInfo m!"Elaboration error: {err}"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 " /-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by sorry"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 " /-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by sorry"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 " /-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by sorry"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 " /-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
(R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by sorry"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 "theorem uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by sorry"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 "uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by sorry"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 "theorem (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by sorry"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 "(R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1:= by sorry"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 " /-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 " /-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 " /-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 " /-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
(R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 "theorem uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 "uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 "theorem (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 "(R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1"

/--
info: Obtained type: {R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)
-/
#guard_msgs in
#elab_thm4 "/-- The map from `Matrix n n R` to bilinear forms on `n → R`.
This is an auxiliary definition for the equivalence `Matrix.toBilin'`. -/

def Matrix.toBilin'Aux {R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁)"

/--
info: Obtained type: {R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)
-/
#guard_msgs in
#elab_thm4 "/-- The map from `Matrix n n R` to bilinear forms on `n → R`.
This is an auxiliary definition for the equivalence `Matrix.toBilin'`. -/

Matrix.toBilin'Aux {R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁)"

/--
info: Obtained type: {R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)
-/
#guard_msgs in
#elab_thm4 "/-- The map from `Matrix n n R` to bilinear forms on `n → R`.
This is an auxiliary definition for the equivalence `Matrix.toBilin'`. -/

def {R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁)"

/--
info: Obtained type: {R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)
-/
#guard_msgs in
#elab_thm4 "/-- The map from `Matrix n n R` to bilinear forms on `n → R`.
This is an auxiliary definition for the equivalence `Matrix.toBilin'`. -/
{R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁)"

/--
info: Obtained type: {R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)
-/
#guard_msgs in
#elab_thm4 " def Matrix.toBilin'Aux {R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁)"

/--
info: Obtained type: {R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)
-/
#guard_msgs in
#elab_thm4 "Matrix.toBilin'Aux {R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁)"

/--
info: Obtained type: {R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)
-/
#guard_msgs in
#elab_thm4 "def {R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁)"

/--
info: Obtained type: {R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)
-/
#guard_msgs in
#elab_thm4 "{R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁)"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)
-/
#guard_msgs in
#elab_thm4 "/-- If `X` is totally disconnected,
its singular chain complex is given by `R[X] ←0- R[X] ←𝟙- R[X] ←0- R[X] ⋯`,
where `R[X]` is the coproduct of copies of `R` indexed by elements of `X`. -/

noncomputable def AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace(C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] (R : C) (X : TopCat) [TotallyDisconnectedSpace ↑X] :
((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅ ChainComplex.alternatingConst.obj (∐ fun (x : ↑X) => R)"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)
-/
#guard_msgs in
#elab_thm4 "/-- If `X` is totally disconnected,
its singular chain complex is given by `R[X] ←0- R[X] ←𝟙- R[X] ←0- R[X] ⋯`,
where `R[X]` is the coproduct of copies of `R` indexed by elements of `X`. -/

AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace(C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] (R : C) (X : TopCat) [TotallyDisconnectedSpace ↑X] :
((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅ ChainComplex.alternatingConst.obj (∐ fun (x : ↑X) => R)"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)
-/
#guard_msgs in
#elab_thm4 "/-- If `X` is totally disconnected,
its singular chain complex is given by `R[X] ←0- R[X] ←𝟙- R[X] ←0- R[X] ⋯`,
where `R[X]` is the coproduct of copies of `R` indexed by elements of `X`. -/

noncomputable def (C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] (R : C) (X : TopCat) [TotallyDisconnectedSpace ↑X] :
((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅ ChainComplex.alternatingConst.obj (∐ fun (x : ↑X) => R)"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)
-/
#guard_msgs in
#elab_thm4 "/-- If `X` is totally disconnected,
its singular chain complex is given by `R[X] ←0- R[X] ←𝟙- R[X] ←0- R[X] ⋯`,
where `R[X]` is the coproduct of copies of `R` indexed by elements of `X`. -/

(C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] (R : C) (X : TopCat) [TotallyDisconnectedSpace ↑X] :
((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅ ChainComplex.alternatingConst.obj (∐ fun (x : ↑X) => R)"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)
-/
#guard_msgs in
#elab_thm4 "noncomputable def AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace(C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] (R : C) (X : TopCat) [TotallyDisconnectedSpace ↑X] :
((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅ ChainComplex.alternatingConst.obj (∐ fun (x : ↑X) => R)"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)
-/
#guard_msgs in
#elab_thm4 "AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace(C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] (R : C) (X : TopCat) [TotallyDisconnectedSpace ↑X] :
((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅ ChainComplex.alternatingConst.obj (∐ fun (x : ↑X) => R)"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)
-/
#guard_msgs in
#elab_thm4 "noncomputable def (C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] (R : C) (X : TopCat) [TotallyDisconnectedSpace ↑X] :
((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅ ChainComplex.alternatingConst.obj (∐ fun (x : ↑X) => R)"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)
-/
#guard_msgs in
#elab_thm4 " (C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] (R : C) (X : TopCat) [TotallyDisconnectedSpace ↑X] :
((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅ ChainComplex.alternatingConst.obj (∐ fun (x : ↑X) => R)"

/--
info: Obtained type: ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H]
  {E : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4}
  [inst_4 : TopologicalSpace G] [inst_5 : ChartedSpace H G] [inst_6 : Group G] {a : WithTop ℕ∞} [LieGroup I ⊤ G]
  [h : ENat.LEInfty a], LieGroup I a G
-/
#guard_msgs in
#elab_thm4 "instance instLieGroupOfSomeENatTopOfLEInfty{𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {H : Type u_2} [TopologicalSpace H] {E : Type u_3} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4} [TopologicalSpace G] [ChartedSpace H G] [Group G] {a : WithTop ℕ∞} [LieGroup I (↑⊤) G] [h : ENat.LEInfty a] :
LieGroup I a G"

/--
info: Obtained type: ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H]
  {E : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4}
  [inst_4 : TopologicalSpace G] [inst_5 : ChartedSpace H G] [inst_6 : Group G] {a : WithTop ℕ∞} [LieGroup I ⊤ G]
  [h : ENat.LEInfty a], LieGroup I a G
-/
#guard_msgs in
#elab_thm4 "LieGroupOfSomeENatTopOfLEInfty{𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {H : Type u_2} [TopologicalSpace H] {E : Type u_3} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4} [TopologicalSpace G] [ChartedSpace H G] [Group G] {a : WithTop ℕ∞} [LieGroup I (↑⊤) G] [h : ENat.LEInfty a] :
LieGroup I a G"

/--
info: Obtained type: ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H]
  {E : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4}
  [inst_4 : TopologicalSpace G] [inst_5 : ChartedSpace H G] [inst_6 : Group G] {a : WithTop ℕ∞} [LieGroup I ⊤ G]
  [h : ENat.LEInfty a], LieGroup I a G
-/
#guard_msgs in
#elab_thm4 "instance {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {H : Type u_2} [TopologicalSpace H] {E : Type u_3} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4} [TopologicalSpace G] [ChartedSpace H G] [Group G] {a : WithTop ℕ∞} [LieGroup I (↑⊤) G] [h : ENat.LEInfty a] :
LieGroup I a G"

/--
info: Obtained type: ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H]
  {E : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4}
  [inst_4 : TopologicalSpace G] [inst_5 : ChartedSpace H G] [inst_6 : Group G] {a : WithTop ℕ∞} [LieGroup I ⊤ G]
  [h : ENat.LEInfty a], LieGroup I a G
-/
#guard_msgs in
#elab_thm4 "{𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {H : Type u_2} [TopologicalSpace H] {E : Type u_3} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4} [TopologicalSpace G] [ChartedSpace H G] [Group G] {a : WithTop ℕ∞} [LieGroup I (↑⊤) G] [h : ENat.LEInfty a] :
LieGroup I a G"


end LeanAide
