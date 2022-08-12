/-
Copyright (c) 2020 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Functor.Multivariate
import Mathbin.Data.Qpf.Multivariate.Basic

/-!
Projection functors are QPFs. The `n`-ary projection functors on `i` is an `n`-ary
functor `F` such that `F (α₀..αᵢ₋₁, αᵢ, αᵢ₊₁..αₙ₋₁) = αᵢ`
-/


universe u v

namespace Mvqpf

open Mvfunctor

variable {n : ℕ} (i : Fin2 n)

/-- The projection `i` functor -/
def Prj (v : Typevec.{u} n) : Type u :=
  v i

instance Prj.inhabited {v : Typevec.{u} n} [Inhabited (v i)] : Inhabited (Prj i v) :=
  ⟨(default : v i)⟩

/-- `map` on functor `prj i` -/
def Prj.map ⦃α β : Typevec n⦄ (f : α ⟹ β) : Prj i α → Prj i β :=
  f _

instance Prj.mvfunctor : Mvfunctor (Prj i) where map := Prj.map i

/-- Polynomial representation of the projection functor -/
def Prj.p : Mvpfunctor.{u} n where
  A := PUnit
  B := fun _ j => ULift <| Plift <| i = j

/-- Abstraction function of the `qpf` instance -/
def Prj.abs ⦃α : Typevec n⦄ : (Prj.p i).Obj α → Prj i α
  | ⟨x, f⟩ => f _ ⟨⟨rfl⟩⟩

/-- Representation function of the `qpf` instance -/
def Prj.repr ⦃α : Typevec n⦄ : Prj i α → (Prj.p i).Obj α := fun x : α i => ⟨⟨⟩, fun j ⟨⟨h⟩⟩ => (h.rec x : α j)⟩

instance Prj.mvqpf : Mvqpf (Prj i) where
  p := Prj.p i
  abs := Prj.abs i
  repr := Prj.repr i
  abs_repr := by
    intros <;> rfl
  abs_map := by
    intros <;> cases p <;> rfl

end Mvqpf

