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

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 " /-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem (R : Type u) [Ring R] (hf : IsField R):
∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1"

/--
info: Obtained type: ∀ (R : Type u) [inst : Ring R], IsField R → ∀ (x : R), x ≠ 0 → ∃! y, x * y = 1
-/
#guard_msgs in
#elab_thm4 " /-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
(R : Type u) [Ring R] (hf : IsField R):
∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1"

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
#elab_thm4 "(R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by sorry"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        CategoryTheory.Functor C (CategoryTheory.Functor _root_.SSet (ChainComplex C ℕ))
-/
#guard_msgs in
#elab_thm4 "def AlgebraicTopology.SSet.singularChainComplexFunctor(C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] :
CategoryTheory.Functor C (CategoryTheory.Functor SSet (ChainComplex C ℕ))"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        CategoryTheory.Functor C (CategoryTheory.Functor _root_.SSet (ChainComplex C ℕ))
-/
#guard_msgs in
#elab_thm4 "def (C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] :
CategoryTheory.Functor C (CategoryTheory.Functor SSet (ChainComplex C ℕ))"

/--
info: Obtained type: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        [inst_3 : CategoryTheory.CategoryWithHomology C] →
          (R : C) →
            (X : TopCat) →
              [TotallyDisconnectedSpace ↑X] →
                ((AlgebraicTopology.singularHomologyFunctor C 0).obj R).obj X ≅ ∐ fun x => R
-/
#guard_msgs in
#elab_thm4 "noncomputable def AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace(C : Type u) [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] [CategoryTheory.CategoryWithHomology C] (R : C) (X : TopCat) [TotallyDisconnectedSpace ↑X] :
((AlgebraicTopology.singularHomologyFunctor C 0).obj R).obj X ≅ ∐ fun (x : ↑X) => R"
end LeanAide
