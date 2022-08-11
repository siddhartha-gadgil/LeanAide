/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Over
import Mathbin.CategoryTheory.Monad.Algebra
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Algebras for the coproduct monad

The functor `Y ↦ X ⨿ Y` forms a monad, whose category of monads is equivalent to the under category
of `X`. Similarly, `Y ↦ X ⨯ Y` forms a comonad, whose category of comonads is equivalent to the
over category of `X`.

## TODO

Show that `over.forget X : over X ⥤ C` is a comonadic left adjoint and `under.forget : under X ⥤ C`
is a monadic right adjoint.
-/


noncomputable section

universe v u

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] (X : C)

section

open Comonad

variable [HasBinaryProducts C]

/-- `X ⨯ -` has a comonad structure. This is sometimes called the writer comonad. -/
@[simps]
def prodComonad : Comonad C where
  toFunctor := prod.functor.obj X
  ε' := { app := fun Y => Limits.prod.snd }
  δ' := { app := fun Y => prod.lift Limits.prod.fst (𝟙 _) }

/-- The forward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
def coalgebraToOver : Coalgebra (prodComonad X) ⥤ Over X where
  obj := fun A => Over.mk (A.a ≫ limits.prod.fst)
  map := fun A₁ A₂ f =>
    Over.homMk f.f
      (by
        rw [over.mk_hom, ← f.h_assoc]
        dsimp'
        simp )

/-- The backward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
def overToCoalgebra : Over X ⥤ Coalgebra (prodComonad X) where
  obj := fun f => { a := f.left, a := prod.lift f.Hom (𝟙 _) }
  map := fun f₁ f₂ g => { f := g.left }

/-- The equivalence from coalgebras for the product comonad to the over category. -/
@[simps]
def coalgebraEquivOver : Coalgebra (prodComonad X) ≌ Over X where
  Functor := coalgebraToOver X
  inverse := overToCoalgebra X
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        Coalgebra.isoMk (Iso.refl _)
          (prod.hom_ext
            (by
              dsimp'
              simp )
            (by
              dsimp'
              simpa using A.counit)))
      fun A₁ A₂ f => by
      ext
      simp
  counitIso :=
    NatIso.ofComponents (fun f => Over.isoMk (Iso.refl _)) fun f g k => by
      tidy

end

section

open _Root_.Monad

variable [HasBinaryCoproducts C]

/-- `X ⨿ -` has a monad structure. This is sometimes called the either monad. -/
@[simps]
def coprodMonad : Monad C where
  toFunctor := coprod.functor.obj X
  η' := { app := fun Y => coprod.inr }
  μ' := { app := fun Y => coprod.desc coprod.inl (𝟙 _) }

/-- The forward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
def algebraToUnder : Monad.Algebra (coprodMonad X) ⥤ Under X where
  obj := fun A => Under.mk (coprod.inl ≫ A.a)
  map := fun A₁ A₂ f =>
    Under.homMk f.f
      (by
        rw [under.mk_hom, assoc, ← f.h]
        dsimp'
        simp )

/-- The backward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
def underToAlgebra : Under X ⥤ Monad.Algebra (coprodMonad X) where
  obj := fun f => { a := f.right, a := coprod.desc f.Hom (𝟙 _) }
  map := fun f₁ f₂ g => { f := g.right }

/-- The equivalence from algebras for the coproduct monad to the under category.
-/
@[simps]
def algebraEquivUnder : Monad.Algebra (coprodMonad X) ≌ Under X where
  Functor := algebraToUnder X
  inverse := underToAlgebra X
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        Monad.Algebra.isoMk (Iso.refl _)
          (coprod.hom_ext
            (by
              tidy)
            (by
              dsimp'
              simpa using A.unit.symm)))
      fun A₁ A₂ f => by
      ext
      simp
  counitIso :=
    NatIso.ofComponents
      (fun f =>
        Under.isoMk (Iso.refl _)
          (by
            tidy))
      fun f g k => by
      tidy

end

end CategoryTheory

