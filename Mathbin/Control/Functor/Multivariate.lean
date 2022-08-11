/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import Mathbin.Data.Fin.Fin2
import Mathbin.Data.Typevec
import Mathbin.Logic.Function.Basic
import Mathbin.Tactic.Basic

/-!

Functors between the category of tuples of types, and the category Type

Features:

`mvfunctor n` : the type class of multivariate functors
`f <$$> x`    : notation for map

-/


universe u v w

open Mvfunctor

/-- multivariate functors, i.e. functor between the category of type vectors
and the category of Type -/
class Mvfunctor {n : ℕ} (F : Typevec n → Type _) where
  map : ∀ {α β : Typevec n}, α ⟹ β → F α → F β

-- mathport name: «expr <$$> »
localized [Mvfunctor] infixr:100 " <$$> " => Mvfunctor.map

variable {n : ℕ}

namespace Mvfunctor

variable {α β γ : Typevec.{u} n} {F : Typevec.{u} n → Type v} [Mvfunctor F]

/-- predicate lifting over multivariate functors -/
def Liftp {α : Typevec n} (p : ∀ i, α i → Prop) (x : F α) : Prop :=
  ∃ u : F fun i => Subtype (p i), (fun i => @Subtype.val _ (p i)) <$$> u = x

/-- relational lifting over multivariate functors -/
def Liftr {α : Typevec n} (r : ∀ {i}, α i → α i → Prop) (x y : F α) : Prop :=
  ∃ u : F fun i => { p : α i × α i // r p.fst p.snd },
    (fun i (t : { p : α i × α i // r p.fst p.snd }) => t.val.fst) <$$> u = x ∧
      (fun i (t : { p : α i × α i // r p.fst p.snd }) => t.val.snd) <$$> u = y

/-- given `x : F α` and a projection `i` of type vector `α`, `supp x i` is the set
of `α.i` contained in `x` -/
def Supp {α : Typevec n} (x : F α) (i : Fin2 n) : Set (α i) :=
  { y : α i | ∀ ⦃p⦄, Liftp p x → p i y }

theorem of_mem_supp {α : Typevec n} {x : F α} {p : ∀ ⦃i⦄, α i → Prop} (h : Liftp p x) (i : Fin2 n) :
    ∀, ∀ y ∈ Supp x i, ∀, p y := fun y hy => hy h

end Mvfunctor

/-- laws for `mvfunctor` -/
class IsLawfulMvfunctor {n : ℕ} (F : Typevec n → Type _) [Mvfunctor F] : Prop where
  id_map : ∀ {α : Typevec n} (x : F α), Typevec.id <$$> x = x
  comp_map : ∀ {α β γ : Typevec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α), (h ⊚ g) <$$> x = h <$$> g <$$> x

open Nat Typevec

namespace Mvfunctor

export IsLawfulMvfunctor (comp_map)

open IsLawfulMvfunctor

variable {α β γ : Typevec.{u} n}

variable {F : Typevec.{u} n → Type v} [Mvfunctor F]

variable (p : α ⟹ Repeat n Prop) (r : α ⊗ α ⟹ Repeat n Prop)

/-- adapt `mvfunctor.liftp` to accept predicates as arrows -/
def Liftp' : F α → Prop :=
  Mvfunctor.Liftp fun i x => of_repeat <| p i x

/-- adapt `mvfunctor.liftp` to accept relations as arrows -/
def Liftr' : F α → F α → Prop :=
  Mvfunctor.Liftr fun i x y => of_repeat <| r i <| Typevec.Prod.mk _ x y

variable [IsLawfulMvfunctor F]

@[simp]
theorem id_map (x : F α) : Typevec.id <$$> x = x :=
  id_map x

@[simp]
theorem id_map' (x : F α) : (fun i a => a) <$$> x = x :=
  id_map x

theorem map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h <$$> g <$$> x = (h ⊚ g) <$$> x :=
  Eq.symm <| comp_map _ _ _

section Liftp'

variable (F)

theorem exists_iff_exists_of_mono {p : F α → Prop} {q : F β → Prop} (f : α ⟹ β) (g : β ⟹ α) (h₀ : f ⊚ g = id)
    (h₁ : ∀ u : F α, p u ↔ q (f <$$> u)) : (∃ u : F α, p u) ↔ ∃ u : F β, q u := by
  constructor <;> rintro ⟨u, h₂⟩ <;> [use f <$$> u, use g <$$> u]
  · apply (h₁ u).mp h₂
    
  · apply (h₁ _).mpr _
    simp only [← Mvfunctor.map_map, ← h₀, ← IsLawfulMvfunctor.id_map, ← h₂]
    

variable {F}

theorem liftp_def (x : F α) : Liftp' p x ↔ ∃ u : F (Subtype_ p), subtypeVal p <$$> u = x :=
  exists_iff_exists_of_mono F _ _ (to_subtype_of_subtype p)
    (by
      simp [← Mvfunctor.map_map])

theorem liftr_def (x y : F α) :
    Liftr' r x y ↔
      ∃ u : F (Subtype_ r),
        (Typevec.Prod.fst ⊚ subtypeVal r) <$$> u = x ∧ (Typevec.Prod.snd ⊚ subtypeVal r) <$$> u = y :=
  exists_iff_exists_of_mono _ _ _ (to_subtype'_of_subtype' r)
    (by
      simp only [← map_map, ← comp_assoc, ← subtype_val_to_subtype'] <;> simp [← comp])

end Liftp'

end Mvfunctor

open Nat

namespace Mvfunctor

open Typevec

section LiftpLastPredIff

variable {F : Typevec.{u} (n + 1) → Type _} [Mvfunctor F] [IsLawfulMvfunctor F] {α : Typevec.{u} n}

variable (p : α ⟹ Repeat n Prop) (r : α ⊗ α ⟹ Repeat n Prop)

open Mvfunctor

variable {β : Type u}

variable (pp : β → Prop)

private def f :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 // ofRepeat (predLast' α pp i p_1) }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 : (α ::: β) i // PredLast α pp p_1 }
  | _, α, Fin2.fs i, x =>
    ⟨x.val,
      cast
        (by
          simp only [← pred_last] <;> erw [const_iff_true])
        x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

private def g :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i // PredLast α pp p_1 }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 // ofRepeat (predLast' α pp i p_1) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val,
      cast
        (by
          simp only [← pred_last] <;> erw [const_iff_true])
        x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

theorem liftp_last_pred_iff {β} (p : β → Prop) (x : F (α ::: β)) : Liftp' (predLast' _ p) x ↔ Liftp (PredLast _ p) x :=
  by
  dsimp' only [← liftp, ← liftp']
  apply exists_iff_exists_of_mono F (f _ n α) (g _ n α)
  · clear x _inst_2 _inst_1 F
    ext i ⟨x, _⟩
    cases i <;> rfl
    
  · intros
    rw [Mvfunctor.map_map, (· ⊚ ·)]
    congr <;> ext i ⟨x, _⟩ <;> cases i <;> rfl
    

open Function

variable (rr : β → β → Prop)

private def f :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : _ × _ // ofRepeat (relLast' α rr i (Typevec.Prod.mk _ p_1.fst p_1.snd)) }) ⟹
        fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // RelLast α rr p_1.fst p_1.snd }
  | _, α, Fin2.fs i, x =>
    ⟨x.val,
      cast
        (by
          simp only [← rel_last] <;> erw [repeat_eq_iff_eq])
        x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

private def g :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // RelLast α rr p_1.fst p_1.snd }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 : _ × _ // ofRepeat (relLast' α rr i (Typevec.Prod.mk _ p_1.1 p_1.2)) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val,
      cast
        (by
          simp only [← rel_last] <;> erw [repeat_eq_iff_eq])
        x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

theorem liftr_last_rel_iff (x y : F (α ::: β)) : Liftr' (relLast' _ rr) x y ↔ Liftr (RelLast _ rr) x y := by
  dsimp' only [← liftr, ← liftr']
  apply exists_iff_exists_of_mono F (f rr _ _) (g rr _ _)
  · clear x y _inst_2 _inst_1 F
    ext i ⟨x, _⟩ : 2
    cases i <;> rfl
    
  · intros
    rw [Mvfunctor.map_map, Mvfunctor.map_map, (· ⊚ ·), (· ⊚ ·)]
    congr <;> ext i ⟨x, _⟩ <;> cases i <;> rfl
    

end LiftpLastPredIff

end Mvfunctor

