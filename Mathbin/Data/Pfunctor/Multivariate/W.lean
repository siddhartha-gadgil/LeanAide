/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import Mathbin.Data.Pfunctor.Multivariate.Basic

/-!
# The W construction as a multivariate polynomial functor.

W types are well-founded tree-like structures. They are defined
as the least fixpoint of a polynomial functor.

## Main definitions

 * `W_mk`     - constructor
 * `W_dest    - destructor
 * `W_rec`    - recursor: basis for defining functions by structural recursion on `P.W α`
 * `W_rec_eq` - defining equation for `W_rec`
 * `W_ind`    - induction principle for `P.W α`

## Implementation notes

Three views of M-types:

 * `Wp`: polynomial functor
 * `W`: data type inductively defined by a triple:
     shape of the root, data in the root and children of the root
 * `W`: least fixed point of a polynomial functor

Specifically, we define the polynomial functor `Wp` as:

 * A := a tree-like structure without information in the nodes
 * B := given the tree-like structure `t`, `B t` is a valid path
   (specified inductively by `W_path`) from the root of `t` to any given node.

As a result `Wp.obj α` is made of a dataless tree and a function from
its valid paths to values of `α`

## Reference

 * Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
   [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u v

namespace Mvpfunctor

open Typevec

open Mvfunctor

variable {n : ℕ} (P : Mvpfunctor.{u} (n + 1))

/-- A path from the root of a tree to one of its node -/
inductive WPath : P.last.W → Fin2 n → Type u
  | root (a : P.A) (f : P.last.B a → P.last.W) (i : Fin2 n) (c : P.drop.B a i) : W_path ⟨a, f⟩ i
  | child (a : P.A) (f : P.last.B a → P.last.W) (i : Fin2 n) (j : P.last.B a) (c : W_path (f j) i) : W_path ⟨a, f⟩ i

instance WPath.inhabited (x : P.last.W) {i} [I : Inhabited (P.drop.B x.head i)] : Inhabited (WPath P x i) :=
  ⟨match x, I with
    | ⟨a, f⟩, I => WPath.root a f i (@default _ I)⟩

/-- Specialized destructor on `W_path` -/
def wPathCasesOn {α : Typevec n} {a : P.A} {f : P.last.B a → P.last.W} (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) : P.WPath ⟨a, f⟩ ⟹ α := by
  intro i x
  cases x
  case W_path.root _ _ i c =>
    exact g' i c
  case W_path.child _ _ i j c =>
    exact g j i c

/-- Specialized destructor on `W_path` -/
def wPathDestLeft {α : Typevec n} {a : P.A} {f : P.last.B a → P.last.W} (h : P.WPath ⟨a, f⟩ ⟹ α) : P.drop.B a ⟹ α :=
  fun i c => h i (WPath.root a f i c)

/-- Specialized destructor on `W_path` -/
def wPathDestRight {α : Typevec n} {a : P.A} {f : P.last.B a → P.last.W} (h : P.WPath ⟨a, f⟩ ⟹ α) :
    ∀ j : P.last.B a, P.WPath (f j) ⟹ α := fun j i c => h i (WPath.child a f i j c)

theorem W_path_dest_left_W_path_cases_on {α : Typevec n} {a : P.A} {f : P.last.B a → P.last.W} (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) : P.wPathDestLeft (P.wPathCasesOn g' g) = g' :=
  rfl

theorem W_path_dest_right_W_path_cases_on {α : Typevec n} {a : P.A} {f : P.last.B a → P.last.W} (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) : P.wPathDestRight (P.wPathCasesOn g' g) = g :=
  rfl

theorem W_path_cases_on_eta {α : Typevec n} {a : P.A} {f : P.last.B a → P.last.W} (h : P.WPath ⟨a, f⟩ ⟹ α) :
    P.wPathCasesOn (P.wPathDestLeft h) (P.wPathDestRight h) = h := by
  ext i x <;> cases x <;> rfl

theorem comp_W_path_cases_on {α β : Typevec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a → P.last.W} (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) : h ⊚ P.wPathCasesOn g' g = P.wPathCasesOn (h ⊚ g') fun i => h ⊚ g i := by
  ext i x <;> cases x <;> rfl

/-- Polynomial functor for the W-type of `P`. `A` is a data-less well-founded
tree whereas, for a given `a : A`, `B a` is a valid path in tree `a` so
that `Wp.obj α` is made of a tree and a function from its valid paths to
the values it contains  -/
def wp : Mvpfunctor n where
  A := P.last.W
  B := P.WPath

/-- W-type of `P` -/
@[nolint has_inhabited_instance]
def W (α : Typevec n) : Type _ :=
  P.wp.Obj α

instance mvfunctorW : Mvfunctor P.W := by
  delta' Mvpfunctor.W <;> infer_instance

/-!
First, describe operations on `W` as a polynomial functor.
-/


/-- Constructor for `Wp` -/
def wpMk {α : Typevec n} (a : P.A) (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) : P.W α :=
  ⟨⟨a, f⟩, f'⟩

/-- Recursor for `Wp` -/
def wpRecₓ {α : Typevec n} {C : Type _}
    (g : ∀ (a : P.A) (f : P.last.B a → P.last.W), P.WPath ⟨a, f⟩ ⟹ α → (P.last.B a → C) → C) :
    ∀ (x : P.last.W) (f' : P.WPath x ⟹ α), C
  | ⟨a, f⟩, f' => g a f f' fun i => Wp_rec (f i) (P.wPathDestRight f' i)

theorem Wp_rec_eq {α : Typevec n} {C : Type _}
    (g : ∀ (a : P.A) (f : P.last.B a → P.last.W), P.WPath ⟨a, f⟩ ⟹ α → (P.last.B a → C) → C) (a : P.A)
    (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) :
    P.wpRec g ⟨a, f⟩ f' = g a f f' fun i => P.wpRec g (f i) (P.wPathDestRight f' i) :=
  rfl

-- Note: we could replace Prop by Type* and obtain a dependent recursor
theorem Wp_ind {α : Typevec n} {C : ∀ x : P.last.W, P.WPath x ⟹ α → Prop}
    (ih :
      ∀ (a : P.A) (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α),
        (∀ i : P.last.B a, C (f i) (P.wPathDestRight f' i)) → C ⟨a, f⟩ f') :
    ∀ (x : P.last.W) (f' : P.WPath x ⟹ α), C x f'
  | ⟨a, f⟩, f' => ih a f f' fun i => Wp_ind _ _

/-!
Now think of W as defined inductively by the data ⟨a, f', f⟩ where
- `a  : P.A` is the shape of the top node
- `f' : P.drop.B a ⟹ α` is the contents of the top node
- `f  : P.last.B a → P.last.W` are the subtrees
 -/


/-- Constructor for `W` -/
def wMk {α : Typevec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) : P.W α :=
  let g : P.last.B a → P.last.W := fun i => (f i).fst
  let g' : P.WPath ⟨a, g⟩ ⟹ α := P.wPathCasesOn f' fun i => (f i).snd
  ⟨⟨a, g⟩, g'⟩

/-- Recursor for `W` -/
def wRecₓ {α : Typevec n} {C : Type _} (g : ∀ a : P.A, P.drop.B a ⟹ α → (P.last.B a → P.W α) → (P.last.B a → C) → C) :
    P.W α → C
  | ⟨a, f'⟩ =>
    let g' (a : P.A) (f : P.last.B a → P.last.W) (h : P.WPath ⟨a, f⟩ ⟹ α) (h' : P.last.B a → C) : C :=
      g a (P.wPathDestLeft h) (fun i => ⟨f i, P.wPathDestRight h i⟩) h'
    P.wpRec g' a f'

/-- Defining equation for the recursor of `W` -/
theorem W_rec_eq {α : Typevec n} {C : Type _}
    (g : ∀ a : P.A, P.drop.B a ⟹ α → (P.last.B a → P.W α) → (P.last.B a → C) → C) (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.last.B a → P.W α) : P.wRec g (P.wMk a f' f) = g a f' f fun i => P.wRec g (f i) := by
  rw [W_mk, W_rec]
  dsimp'
  rw [Wp_rec_eq]
  dsimp' only [← W_path_dest_left_W_path_cases_on, ← W_path_dest_right_W_path_cases_on]
  congr <;> ext1 i <;> cases f i <;> rfl

/-- Induction principle for `W` -/
theorem W_ind {α : Typevec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α), (∀ i, C (f i)) → C (P.wMk a f' f)) : ∀ x, C x :=
  by
  intro x
  cases' x with a f
  apply @Wp_ind n P α fun a f => C ⟨a, f⟩
  dsimp'
  intro a f f' ih'
  dsimp' [← W_mk]  at ih
  let ih'' := ih a (P.W_path_dest_left f') fun i => ⟨f i, P.W_path_dest_right f' i⟩
  dsimp'  at ih''
  rw [W_path_cases_on_eta] at ih''
  apply ih''
  apply ih'

theorem W_cases {α : Typevec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α), C (P.wMk a f' f)) : ∀ x, C x :=
  P.W_ind fun a f' f ih' => ih a f' f

/-- W-types are functorial -/
def wMap {α β : Typevec n} (g : α ⟹ β) : P.W α → P.W β := fun x => g <$$> x

theorem W_mk_eq {α : Typevec n} (a : P.A) (f : P.last.B a → P.last.W) (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) : (P.wMk a g' fun i => ⟨f i, g i⟩) = ⟨⟨a, f⟩, P.wPathCasesOn g' g⟩ :=
  rfl

theorem W_map_W_mk {α β : Typevec n} (g : α ⟹ β) (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
    g <$$> P.wMk a f' f = P.wMk a (g ⊚ f') fun i => g <$$> f i := by
  show _ = P.W_mk a (g ⊚ f') (Mvfunctor.map g ∘ f)
  have : Mvfunctor.map g ∘ f = fun i => ⟨(f i).fst, g ⊚ (f i).snd⟩ := by
    ext i : 1
    dsimp' [← Function.comp]
    cases f i
    rfl
  rw [this]
  have : f = fun i => ⟨(f i).fst, (f i).snd⟩ := by
    ext1
    cases f x
    rfl
  rw [this]
  dsimp'
  rw [W_mk_eq, W_mk_eq]
  have h := Mvpfunctor.map_eq P.Wp g
  rw [h, comp_W_path_cases_on]

/-- Constructor of a value of `P.obj (α ::: β)` from components.
Useful to avoid complicated type annotation -/
-- TODO: this technical theorem is used in one place in constructing the initial algebra.
-- Can it be avoided?
@[reducible]
def objAppend1 {α : Typevec n} {β : Type _} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) : P.Obj (α ::: β) :=
  ⟨a, splitFun f' f⟩

theorem map_obj_append1 {α γ : Typevec n} (g : α ⟹ γ) (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
    appendFun g (P.wMap g) <$$> P.objAppend1 a f' f = P.objAppend1 a (g ⊚ f') fun x => P.wMap g (f x) := by
  rw [obj_append1, obj_append1, map_eq, append_fun, ← split_fun_comp] <;> rfl

/-!
Yet another view of the W type: as a fixed point for a multivariate polynomial functor.
These are needed to use the W-construction to construct a fixed point of a qpf, since
the qpf axioms are expressed in terms of `map` on `P`.
-/


/-- Constructor for the W-type of `P` -/
def wMk' {α : Typevec n} : P.Obj (α ::: P.W α) → P.W α
  | ⟨a, f⟩ => P.wMk a (dropFun f) (lastFun f)

/-- Destructor for the W-type of `P` -/
def wDest' {α : Typevec.{u} n} : P.W α → P.Obj (α.Append1 (P.W α)) :=
  P.wRec fun a f' f _ => ⟨a, splitFun f' f⟩

theorem W_dest'_W_mk {α : Typevec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
    P.wDest' (P.wMk a f' f) = ⟨a, splitFun f' f⟩ := by
  rw [W_dest', W_rec_eq]

theorem W_dest'_W_mk' {α : Typevec n} (x : P.Obj (α.Append1 (P.W α))) : P.wDest' (P.wMk' x) = x := by
  cases' x with a f <;> rw [W_mk', W_dest'_W_mk, split_drop_fun_last_fun]

end Mvpfunctor

