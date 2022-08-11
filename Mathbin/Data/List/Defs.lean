/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathbin.Data.Option.Defs
import Mathbin.Logic.Basic
import Mathbin.Tactic.Cache
import Mathbin.Data.Rbmap.Basic
import Mathbin.Data.Rbtree.DefaultLt

/-!
## Definitions on lists

This file contains various definitions on lists. It does not contain
proofs about these definitions, those are contained in other files in `data/list`
-/


namespace List

open Function Nat

universe u v w x

variable {α β γ δ ε ζ : Type _}

instance [DecidableEq α] : HasSdiff (List α) :=
  ⟨List.diffₓ⟩

/-- Split a list at an index.

     split_at 2 [a, b, c] = ([a, b], [c]) -/
def splitAtₓ : ℕ → List α → List α × List α
  | 0, a => ([], a)
  | succ n, [] => ([], [])
  | succ n, x :: xs =>
    let (l, r) := split_at n xs
    (x :: l, r)

/-- An auxiliary function for `split_on_p`. -/
def splitOnPAux {α : Type u} (P : α → Prop) [DecidablePred P] : List α → (List α → List α) → List (List α)
  | [], f => [f []]
  | h :: t, f => if P h then f [] :: split_on_p_aux t id else split_on_p_aux t fun l => f (h :: l)

/-- Split a list at every element satisfying a predicate. -/
def splitOnP {α : Type u} (P : α → Prop) [DecidablePred P] (l : List α) : List (List α) :=
  splitOnPAux P l id

/-- Split a list at every occurrence of an element.

    [1,1,2,3,2,4,4].split_on 2 = [[1,1],[3],[4,4]] -/
def splitOn {α : Type u} [DecidableEq α] (a : α) (as : List α) : List (List α) :=
  as.splitOnP (· = a)

/-- Concatenate an element at the end of a list.

     concat [a, b] c = [a, b, c] -/
@[simp]
def concat : List α → α → List α
  | [], a => [a]
  | b :: l, a => b :: concat l a

/-- `head' xs` returns the first element of `xs` if `xs` is non-empty;
it returns `none` otherwise -/
@[simp]
def head' : List α → Option α
  | [] => none
  | a :: l => some a

/-- Convert a list into an array (whose length is the length of `l`). -/
def toArrayₓ (l : List α) : Arrayₓ l.length α where data := fun v => l.nthLe v.1 v.2

/-- "inhabited" `nth` function: returns `default` instead of `none` in the case
  that the index is out of bounds. -/
@[simp]
def inth [h : Inhabited α] (l : List α) (n : Nat) : α :=
  (nth l n).iget

/-- Apply a function to the nth tail of `l`. Returns the input without
  using `f` if the index is larger than the length of the list.

     modify_nth_tail f 2 [a, b, c] = [a, b] ++ f [c] -/
@[simp]
def modifyNthTailₓ (f : List α → List α) : ℕ → List α → List α
  | 0, l => f l
  | n + 1, [] => []
  | n + 1, a :: l => a :: modify_nth_tail n l

/-- Apply `f` to the head of the list, if it exists. -/
@[simp]
def modifyHead (f : α → α) : List α → List α
  | [] => []
  | a :: l => f a :: l

/-- Apply `f` to the nth element of the list, if it exists. -/
def modifyNthₓ (f : α → α) : ℕ → List α → List α :=
  modifyNthTailₓ (modifyHead f)

/-- Apply `f` to the last element of `l`, if it exists. -/
@[simp]
def modifyLast (f : α → α) : List α → List α
  | [] => []
  | [x] => [f x]
  | x :: xs => x :: modify_last xs

/-- `insert_nth n a l` inserts `a` into the list `l` after the first `n` elements of `l`
 `insert_nth 2 1 [1, 2, 3, 4] = [1, 2, 1, 3, 4]`-/
def insertNthₓ (n : ℕ) (a : α) : List α → List α :=
  modifyNthTailₓ (List.cons a) n

section Take'

variable [Inhabited α]

/-- Take `n` elements from a list `l`. If `l` has less than `n` elements, append `n - length l`
elements `default`. -/
def take' : ∀ n, List α → List α
  | 0, l => []
  | n + 1, l => l.head :: take' n l.tail

end Take'

/-- Get the longest initial segment of the list whose members all satisfy `p`.

     take_while (λ x, x < 3) [0, 2, 5, 1] = [0, 2] -/
def takeWhileₓ (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | a :: l => if p a then a :: take_while l else []

/-- Fold a function `f` over the list from the left, returning the list
  of partial results.

     scanl (+) 0 [1, 2, 3] = [0, 1, 3, 6] -/
def scanl (f : α → β → α) : α → List β → List α
  | a, [] => [a]
  | a, b :: l => a :: scanl (f a b) l

/-- Auxiliary definition used to define `scanr`. If `scanr_aux f b l = (b', l')`
then `scanr f b l = b' :: l'` -/
def scanrAux (f : α → β → β) (b : β) : List α → β × List β
  | [] => (b, [])
  | a :: l =>
    let (b', l') := scanr_aux l
    (f a b', b' :: l')

/-- Fold a function `f` over the list from the right, returning the list
  of partial results.

     scanr (+) 0 [1, 2, 3] = [6, 5, 3, 0] -/
def scanr (f : α → β → β) (b : β) (l : List α) : List β :=
  let (b', l') := scanrAux f b l
  b' :: l'

/-- Product of a list.

     prod [a, b, c] = ((1 * a) * b) * c -/
def prod [Mul α] [One α] : List α → α :=
  foldlₓ (· * ·) 1

/-- Sum of a list.

     sum [a, b, c] = ((0 + a) + b) + c -/
-- Later this will be tagged with `to_additive`, but this can't be done yet because of import
-- dependencies.
def sum [Add α] [Zero α] : List α → α :=
  foldlₓ (· + ·) 0

/-- The alternating sum of a list. -/
def alternatingSum {G : Type _} [Zero G] [Add G] [Neg G] : List G → G
  | [] => 0
  | g :: [] => g
  | g :: h :: t => g + -h + alternating_sum t

/-- The alternating product of a list. -/
def alternatingProd {G : Type _} [One G] [Mul G] [Inv G] : List G → G
  | [] => 1
  | g :: [] => g
  | g :: h :: t => g * h⁻¹ * alternating_prod t

/-- Given a function `f : α → β ⊕ γ`, `partition_map f l` maps the list by `f`
  whilst partitioning the result it into a pair of lists, `list β × list γ`,
  partitioning the `sum.inl _` into the left list, and the `sum.inr _` into the right list.
  `partition_map (id : ℕ ⊕ ℕ → ℕ ⊕ ℕ) [inl 0, inr 1, inl 2] = ([0,2], [1])`    -/
def partitionMap (f : α → Sum β γ) : List α → List β × List γ
  | [] => ([], [])
  | x :: xs =>
    match f x with
    | Sum.inr r => Prod.map id (cons r) <| partition_map xs
    | Sum.inl l => Prod.map (cons l) id <| partition_map xs

/-- `find p l` is the first element of `l` satisfying `p`, or `none` if no such
  element exists. -/
def find (p : α → Prop) [DecidablePred p] : List α → Option α
  | [] => none
  | a :: l => if p a then some a else find l

/-- `mfind tac l` returns the first element of `l` on which `tac` succeeds, and
fails otherwise. -/
def mfind {α} {m : Type u → Type v} [Monadₓ m] [Alternativeₓ m] (tac : α → m PUnit) : List α → m α :=
  List.mfirstₓ fun a => tac a $> a

/-- `mbfind' p l` returns the first element `a` of `l` for which `p a` returns
true. `mbfind'` short-circuits, so `p` is not necessarily run on every `a` in
`l`. This is a monadic version of `list.find`. -/
def mbfind' {m : Type u → Type v} [Monadₓ m] {α : Type u} (p : α → m (ULift Bool)) : List α → m (Option α)
  | [] => pure none
  | x :: xs => do
    let ⟨px⟩ ← p x
    if px then pure (some x) else mbfind' xs

section

variable {m : Type → Type v} [Monadₓ m]

/-- A variant of `mbfind'` with more restrictive universe levels. -/
def mbfind {α} (p : α → m Bool) (xs : List α) : m (Option α) :=
  xs.mbfind' (Functor.map ULift.up ∘ p)

/-- `many p as` returns true iff `p` returns true for any element of `l`.
`many` short-circuits, so if `p` returns true for any element of `l`, later
elements are not checked. This is a monadic version of `list.any`. -/
-- Implementing this via `mbfind` would give us less universe polymorphism.
def many {α : Type u} (p : α → m Bool) : List α → m Bool
  | [] => pure False
  | x :: xs => do
    let px ← p x
    if px then pure tt else many xs

/-- `mall p as` returns true iff `p` returns true for all elements of `l`.
`mall` short-circuits, so if `p` returns false for any element of `l`, later
elements are not checked. This is a monadic version of `list.all`. -/
def mall {α : Type u} (p : α → m Bool) (as : List α) : m Bool :=
  bnot <$> many (fun a => bnot <$> p a) as

/-- `mbor xs` runs the actions in `xs`, returning true if any of them returns
true. `mbor` short-circuits, so if an action returns true, later actions are
not run. This is a monadic version of `list.bor`. -/
def mbor : List (m Bool) → m Bool :=
  many id

/-- `mband xs` runs the actions in `xs`, returning true if all of them return
true. `mband` short-circuits, so if an action returns false, later actions are
not run. This is a monadic version of `list.band`. -/
def mband : List (m Bool) → m Bool :=
  mall id

end

/-- Auxiliary definition for `foldl_with_index`. -/
def foldlWithIndexAux (f : ℕ → α → β → α) : ℕ → α → List β → α
  | _, a, [] => a
  | i, a, b :: l => foldl_with_index_aux (i + 1) (f i a b) l

/-- Fold a list from left to right as with `foldl`, but the combining function
also receives each element's index. -/
def foldlWithIndex (f : ℕ → α → β → α) (a : α) (l : List β) : α :=
  foldlWithIndexAux f 0 a l

/-- Auxiliary definition for `foldr_with_index`. -/
def foldrWithIndexAux (f : ℕ → α → β → β) : ℕ → β → List α → β
  | _, b, [] => b
  | i, b, a :: l => f i a (foldr_with_index_aux (i + 1) b l)

/-- Fold a list from right to left as with `foldr`, but the combining function
also receives each element's index. -/
def foldrWithIndex (f : ℕ → α → β → β) (b : β) (l : List α) : β :=
  foldrWithIndexAux f 0 b l

/-- `find_indexes p l` is the list of indexes of elements of `l` that satisfy `p`. -/
def findIndexes (p : α → Prop) [DecidablePred p] (l : List α) : List Nat :=
  foldrWithIndex (fun i a is => if p a then i :: is else is) [] l

/-- Returns the elements of `l` that satisfy `p` together with their indexes in
`l`. The returned list is ordered by index. -/
def indexesValues (p : α → Prop) [DecidablePred p] (l : List α) : List (ℕ × α) :=
  foldrWithIndex (fun i a l => if p a then (i, a) :: l else l) [] l

/-- `indexes_of a l` is the list of all indexes of `a` in `l`. For example:
```
indexes_of a [a, b, a, a] = [0, 2, 3]
```
-/
def indexesOf [DecidableEq α] (a : α) : List α → List Nat :=
  findIndexes (Eq a)

section MfoldWithIndex

variable {m : Type v → Type w} [Monadₓ m]

/-- Monadic variant of `foldl_with_index`. -/
def mfoldlWithIndex {α β} (f : ℕ → β → α → m β) (b : β) (as : List α) : m β :=
  as.foldlWithIndex
    (fun i ma b => do
      let a ← ma
      f i a b)
    (pure b)

/-- Monadic variant of `foldr_with_index`. -/
def mfoldrWithIndex {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) : m β :=
  as.foldrWithIndex
    (fun i a mb => do
      let b ← mb
      f i a b)
    (pure b)

end MfoldWithIndex

section MmapWithIndex

variable {m : Type v → Type w} [Applicativeₓ m]

/-- Auxiliary definition for `mmap_with_index`. -/
def mmapWithIndexAuxₓ {α β} (f : ℕ → α → m β) : ℕ → List α → m (List β)
  | _, [] => pure []
  | i, a :: as => List.cons <$> f i a <*> mmap_with_index_aux (i + 1) as

/-- Applicative variant of `map_with_index`. -/
def mmapWithIndex {α β} (f : ℕ → α → m β) (as : List α) : m (List β) :=
  mmapWithIndexAuxₓ f 0 as

/-- Auxiliary definition for `mmap_with_index'`. -/
def mmapWithIndex'Auxₓ {α} (f : ℕ → α → m PUnit) : ℕ → List α → m PUnit
  | _, [] => pure ⟨⟩
  | i, a :: as => f i a *> mmap_with_index'_aux (i + 1) as

/-- A variant of `mmap_with_index` specialised to applicative actions which
return `unit`. -/
def mmapWithIndex' {α} (f : ℕ → α → m PUnit) (as : List α) : m PUnit :=
  mmapWithIndex'Auxₓ f 0 as

end MmapWithIndex

/-- `lookmap` is a combination of `lookup` and `filter_map`.
  `lookmap f l` will apply `f : α → option α` to each element of the list,
  replacing `a → b` at the first value `a` in the list such that `f a = some b`. -/
def lookmap (f : α → Option α) : List α → List α
  | [] => []
  | a :: l =>
    match f a with
    | some b => b :: l
    | none => a :: lookmap l

/-- `countp p l` is the number of elements of `l` that satisfy `p`. -/
def countp (p : α → Prop) [DecidablePred p] : List α → Nat
  | [] => 0
  | x :: xs => if p x then succ (countp xs) else countp xs

/-- `count a l` is the number of occurrences of `a` in `l`. -/
def count [DecidableEq α] (a : α) : List α → Nat :=
  countp (Eq a)

/-- `is_prefix l₁ l₂`, or `l₁ <+: l₂`, means that `l₁` is a prefix of `l₂`,
  that is, `l₂` has the form `l₁ ++ t` for some `t`. -/
def IsPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

/-- `is_suffix l₁ l₂`, or `l₁ <:+ l₂`, means that `l₁` is a suffix of `l₂`,
  that is, `l₂` has the form `t ++ l₁` for some `t`. -/
def IsSuffix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, t ++ l₁ = l₂

/-- `is_infix l₁ l₂`, or `l₁ <:+: l₂`, means that `l₁` is a contiguous
  substring of `l₂`, that is, `l₂` has the form `s ++ l₁ ++ t` for some `s, t`. -/
def IsInfix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ s t, s ++ l₁ ++ t = l₂

-- mathport name: «expr <+: »
infixl:50 " <+: " => IsPrefix

-- mathport name: «expr <:+ »
infixl:50 " <:+ " => IsSuffix

-- mathport name: «expr <:+: »
infixl:50 " <:+: " => IsInfix

/-- `inits l` is the list of initial segments of `l`.

     inits [1, 2, 3] = [[], [1], [1, 2], [1, 2, 3]] -/
@[simp]
def inits : List α → List (List α)
  | [] => [[]]
  | a :: l => [] :: map (fun t => a :: t) (inits l)

/-- `tails l` is the list of terminal segments of `l`.

     tails [1, 2, 3] = [[1, 2, 3], [2, 3], [3], []] -/
@[simp]
def tails : List α → List (List α)
  | [] => [[]]
  | a :: l => (a :: l) :: tails l

def sublists'Aux : List α → (List α → List β) → List (List β) → List (List β)
  | [], f, r => f [] :: r
  | a :: l, f, r => sublists'_aux l f (sublists'_aux l (f ∘ cons a) r)

/-- `sublists' l` is the list of all (non-contiguous) sublists of `l`.
  It differs from `sublists` only in the order of appearance of the sublists;
  `sublists'` uses the first element of the list as the MSB,
  `sublists` uses the first element of the list as the LSB.

     sublists' [1, 2, 3] = [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]] -/
def sublists' (l : List α) : List (List α) :=
  sublists'Aux l id []

def sublistsAux : List α → (List α → List β → List β) → List β
  | [], f => []
  | a :: l, f => f [a] (sublists_aux l fun ys r => f ys (f (a :: ys) r))

/-- `sublists l` is the list of all (non-contiguous) sublists of `l`; cf. `sublists'`
  for a different ordering.

     sublists [1, 2, 3] = [[], [1], [2], [1, 2], [3], [1, 3], [2, 3], [1, 2, 3]] -/
def sublists (l : List α) : List (List α) :=
  [] :: sublistsAux l cons

def sublistsAux₁ : List α → (List α → List β) → List β
  | [], f => []
  | a :: l, f => f [a] ++ sublists_aux₁ l fun ys => f ys ++ f (a :: ys)

section Forall₂

variable {r : α → β → Prop} {p : γ → δ → Prop}

/-- `forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length,
  and whenever `a` is the nth element of `l₁`, and `b` is the nth element of `l₂`,
  then `R a b` is satisfied. -/
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil : forall₂ [] []
  | cons {a b l₁ l₂} : R a b → forall₂ l₁ l₂ → forall₂ (a :: l₁) (b :: l₂)

attribute [simp] forall₂.nil

end Forall₂

/-- `l.all₂ p` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunction, i.e.
`list.all₂ p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
@[simp]
def All₂ (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ all₂ l

/-- Auxiliary definition used to define `transpose`.
  `transpose_aux l L` takes each element of `l` and appends it to the start of
  each element of `L`.

  `transpose_aux [a, b, c] [l₁, l₂, l₃] = [a::l₁, b::l₂, c::l₃]` -/
def transposeAuxₓ : List α → List (List α) → List (List α)
  | [], ls => ls
  | a :: i, [] => [a] :: transpose_aux i []
  | a :: i, l :: ls => (a :: l) :: transpose_aux i ls

/-- transpose of a list of lists, treated as a matrix.

     transpose [[1, 2], [3, 4], [5, 6]] = [[1, 3, 5], [2, 4, 6]] -/
def transposeₓ : List (List α) → List (List α)
  | [] => []
  | l :: ls => transposeAuxₓ l (transpose ls)

/-- List of all sections through a list of lists. A section
  of `[L₁, L₂, ..., Lₙ]` is a list whose first element comes from
  `L₁`, whose second element comes from `L₂`, and so on. -/
def sections : List (List α) → List (List α)
  | [] => [[]]
  | l :: L => (bind (sections L)) fun s => map (fun a => a :: s) l

section Permutations

/-- An auxiliary function for defining `permutations`. `permutations_aux2 t ts r ys f` is equal to
`(ys ++ ts, (insert_left ys t ts).map f ++ r)`, where `insert_left ys t ts` (not explicitly
defined) is the list of lists of the form `insert_nth n t (ys ++ ts)` for `0 ≤ n < length ys`.

    permutations_aux2 10 [4, 5, 6] [] [1, 2, 3] id =
      ([1, 2, 3, 4, 5, 6],
       [[10, 1, 2, 3, 4, 5, 6],
        [1, 10, 2, 3, 4, 5, 6],
        [1, 2, 10, 3, 4, 5, 6]]) -/
def permutationsAux2 (t : α) (ts : List α) (r : List β) : List α → (List α → β) → List α × List β
  | [], f => (ts, r)
  | y :: ys, f =>
    let (us, zs) := permutations_aux2 ys fun x : List α => f (y :: x)
    (y :: us, f (t :: y :: us) :: zs)

private def meas : (Σ'_ : List α, List α) → ℕ × ℕ
  | ⟨l, i⟩ => (length l + length i, length l)

-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => InvImage (Prod.Lex (· < ·) (· < ·)) meas

/-- A recursor for pairs of lists. To have `C l₁ l₂` for all `l₁`, `l₂`, it suffices to have it for
`l₂ = []` and to be able to pour the elements of `l₁` into `l₂`. -/
@[elab_as_eliminator]
def PermutationsAux.recₓ {C : List α → List α → Sort v} (H0 : ∀ is, C [] is)
    (H1 : ∀ t ts is, C ts (t :: is) → C is [] → C (t :: ts) is) : ∀ l₁ l₂, C l₁ l₂
  | [], is => H0 is
  | t :: ts, is =>
    have h1 : ⟨ts, t :: is⟩ ≺ ⟨t :: ts, is⟩ :=
      show Prod.Lex _ _ (succ (length ts + length is), length ts) (succ (length ts) + length is, length (t :: ts)) by
        rw [Nat.succ_add] <;> exact Prod.Lex.right _ (lt_succ_self _)
    have h2 : ⟨is, []⟩ ≺ ⟨t :: ts, is⟩ := Prod.Lex.left _ _ (Nat.lt_add_of_pos_leftₓ (succ_posₓ _))
    H1 t ts is (permutations_aux.rec ts (t :: is)) (permutations_aux.rec is [])

/-- An auxiliary function for defining `permutations`. `permutations_aux ts is` is the set of all
permutations of `is ++ ts` that do not fix `ts`. -/
def permutationsAux : List α → List α → List (List α) :=
  @PermutationsAux.recₓ (fun _ _ => List (List α)) (fun is => []) fun t ts is IH1 IH2 =>
    foldr (fun y r => (permutationsAux2 t ts r y id).2) IH1 (is :: IH2)

/-- List of all permutations of `l`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [3, 2, 1],
        [2, 3, 1], [3, 1, 2], [1, 3, 2]] -/
def permutations (l : List α) : List (List α) :=
  l :: permutationsAux l []

/-- `permutations'_aux t ts` inserts `t` into every position in `ts`, including the last.
This function is intended for use in specifications, so it is simpler than `permutations_aux2`,
which plays roughly the same role in `permutations`.

Note that `(permutations_aux2 t [] [] ts id).2` is similar to this function, but skips the last
position:

    permutations'_aux 10 [1, 2, 3] =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3], [1, 2, 3, 10]]
    (permutations_aux2 10 [] [] [1, 2, 3] id).2 =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3]] -/
@[simp]
def permutations'Aux (t : α) : List α → List (List α)
  | [] => [[t]]
  | y :: ys => (t :: y :: ys) :: (permutations'_aux ys).map (cons y)

/-- List of all permutations of `l`. This version of `permutations` is less efficient but has
simpler definitional equations. The permutations are in a different order,
but are equal up to permutation, as shown by `list.permutations_perm_permutations'`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 3, 2], [3, 1, 2], [3, 2, 1]] -/
@[simp]
def permutations' : List α → List (List α)
  | [] => [[]]
  | t :: ts => (permutations' ts).bind <| permutations'Aux t

end Permutations

/-- `erasep p l` removes the first element of `l` satisfying the predicate `p`. -/
def erasep (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | a :: l => if p a then l else a :: erasep l

/-- `extractp p l` returns a pair of an element `a` of `l` satisfying the predicate
  `p`, and `l`, with `a` removed. If there is no such element `a` it returns `(none, l)`. -/
def extractp (p : α → Prop) [DecidablePred p] : List α → Option α × List α
  | [] => (none, [])
  | a :: l =>
    if p a then (some a, l)
    else
      let (a', l') := extractp l
      (a', a :: l')

/-- `revzip l` returns a list of pairs of the elements of `l` paired
  with the elements of `l` in reverse order.

`revzip [1,2,3,4,5] = [(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)]`
 -/
def revzipₓ (l : List α) : List (α × α) :=
  zipₓ l l.reverse

/-- `product l₁ l₂` is the list of pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂`.

     product [1, 2] [5, 6] = [(1, 5), (1, 6), (2, 5), (2, 6)] -/
def product (l₁ : List α) (l₂ : List β) : List (α × β) :=
  l₁.bind fun a => l₂.map <| Prod.mk a

/-- `sigma l₁ l₂` is the list of dependent pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂ a`.

     sigma [1, 2] (λ_, [(5 : ℕ), 6]) = [(1, 5), (1, 6), (2, 5), (2, 6)] -/
protected def sigma {σ : α → Type _} (l₁ : List α) (l₂ : ∀ a, List (σ a)) : List (Σa, σ a) :=
  l₁.bind fun a => (l₂ a).map <| Sigma.mk a

/-- Auxliary definition used to define `of_fn`.

  `of_fn_aux f m h l` returns the first `m` elements of `of_fn f`
  appended to `l` -/
def ofFnAuxₓ {n} (f : Finₓ n → α) : ∀ m, m ≤ n → List α → List α
  | 0, h, l => l
  | succ m, h, l => of_fn_aux m (le_of_ltₓ h) (f ⟨m, h⟩ :: l)

/-- `of_fn f` with `f : fin n → α` returns the list whose ith element is `f i`
  `of_fun f = [f 0, f 1, ... , f(n - 1)]` -/
def ofFnₓ {n} (f : Finₓ n → α) : List α :=
  ofFnAuxₓ f n (le_reflₓ _) []

/-- `of_fn_nth_val f i` returns `some (f i)` if `i < n` and `none` otherwise. -/
def ofFnNthValₓ {n} (f : Finₓ n → α) (i : ℕ) : Option α :=
  if h : i < n then some (f ⟨i, h⟩) else none

/-- `disjoint l₁ l₂` means that `l₁` and `l₂` have no elements in common. -/
def Disjoint (l₁ l₂ : List α) : Prop :=
  ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False

section Pairwise

variable (R : α → α → Prop)

/-- `pairwise R l` means that all the elements with earlier indexes are
  `R`-related to all the elements with later indexes.

     pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3

  For example if `R = (≠)` then it asserts `l` has no duplicates,
  and if `R = (<)` then it asserts that `l` is (strictly) sorted. -/
inductive Pairwiseₓ : List α → Prop
  | nil : pairwise []
  | cons : ∀ {a : α} {l : List α}, (∀, ∀ a' ∈ l, ∀, R a a') → pairwise l → pairwise (a :: l)

variable {R}

@[simp]
theorem pairwise_cons {a : α} {l : List α} : Pairwiseₓ R (a :: l) ↔ (∀, ∀ a' ∈ l, ∀, R a a') ∧ Pairwiseₓ R l :=
  ⟨fun p => by
    cases' p with a l n p <;> exact ⟨n, p⟩, fun ⟨n, p⟩ => p.cons n⟩

attribute [simp] pairwise.nil

instance decidablePairwiseₓ [DecidableRel R] (l : List α) : Decidable (Pairwiseₓ R l) := by
  induction' l with hd tl ih <;> [exact is_true pairwise.nil, exact decidableOfIff' _ pairwise_cons]

end Pairwise

/-- `pw_filter R l` is a maximal sublist of `l` which is `pairwise R`.
  `pw_filter (≠)` is the erase duplicates function (cf. `dedup`), and `pw_filter (<)` finds
  a maximal increasing subsequence in `l`. For example,

     pw_filter (<) [0, 1, 5, 2, 6, 3, 4] = [0, 1, 2, 3, 4] -/
def pwFilterₓ (R : α → α → Prop) [DecidableRel R] : List α → List α
  | [] => []
  | x :: xs =>
    let IH := pw_filter xs
    if ∀, ∀ y ∈ IH, ∀, R x y then x :: IH else IH

section Chain

variable (R : α → α → Prop)

/-- `chain R a l` means that `R` holds between adjacent elements of `a::l`.

     chain R a [b, c, d] ↔ R a b ∧ R b c ∧ R c d -/
inductive Chain : α → List α → Prop
  | nil {a : α} : chain a []
  | cons : ∀ {a b : α} {l : List α}, R a b → chain b l → chain a (b :: l)

/-- `chain' R l` means that `R` holds between adjacent elements of `l`.

     chain' R [a, b, c, d] ↔ R a b ∧ R b c ∧ R c d -/
def Chain' : List α → Prop
  | [] => True
  | a :: l => Chain R a l

variable {R}

@[simp]
theorem chain_cons {a b : α} {l : List α} : Chain R a (b :: l) ↔ R a b ∧ Chain R b l :=
  ⟨fun p => by
    cases' p with _ a b l n p <;> exact ⟨n, p⟩, fun ⟨n, p⟩ => p.cons n⟩

attribute [simp] chain.nil

instance decidableChain [DecidableRel R] (a : α) (l : List α) : Decidable (Chain R a l) := by
  induction l generalizing a <;> simp only [← chain.nil, ← chain_cons] <;> skip <;> infer_instance

instance decidableChain' [DecidableRel R] (l : List α) : Decidable (Chain' R l) := by
  cases l <;> dunfold chain' <;> infer_instance

end Chain

/-- `nodup l` means that `l` has no duplicates, that is, any element appears at most
  once in the list. It is defined as `pairwise (≠)`. -/
def Nodupₓ : List α → Prop :=
  Pairwiseₓ (· ≠ ·)

instance nodupDecidableₓ [DecidableEq α] : ∀ l : List α, Decidable (Nodupₓ l) :=
  List.decidablePairwiseₓ

/-- `dedup l` removes duplicates from `l` (taking only the first occurrence).
  Defined as `pw_filter (≠)`.

     dedup [1, 0, 2, 2, 1] = [0, 2, 1] -/
def dedup [DecidableEq α] : List α → List α :=
  pwFilterₓ (· ≠ ·)

/-- Greedily create a sublist of `a :: l` such that, for every two adjacent elements `a, b`,
`R a b` holds. Mostly used with ≠; for example, `destutter' (≠) 1 [2, 2, 1, 1] = [1, 2, 1]`,
`destutter' (≠) 1, [2, 3, 3] = [1, 2, 3]`, `destutter' (<) 1 [2, 5, 2, 3, 4, 9] = [1, 2, 5, 9]`. -/
def destutter' (R : α → α → Prop) [DecidableRel R] : α → List α → List α
  | a, [] => [a]
  | a, h :: l => if R a h then a :: destutter' h l else destutter' a l

/-- Greedily create a sublist of `l` such that, for every two adjacent elements `a, b ∈ l`,
`R a b` holds. Mostly used with ≠; for example, `destutter (≠) [1, 2, 2, 1, 1] = [1, 2, 1]`,
`destutter (≠) [1, 2, 3, 3] = [1, 2, 3]`, `destutter (<) [1, 2, 5, 2, 3, 4, 9] = [1, 2, 5, 9]`. -/
def destutter (R : α → α → Prop) [DecidableRel R] : List α → List α
  | h :: l => destutter' R h l
  | [] => []

/-- `range' s n` is the list of numbers `[s, s+1, ..., s+n-1]`.
  It is intended mainly for proving properties of `range` and `iota`. -/
@[simp]
def range' : ℕ → ℕ → List ℕ
  | s, 0 => []
  | s, n + 1 => s :: range' (s + 1) n

/-- Drop `none`s from a list, and replace each remaining `some a` with `a`. -/
def reduceOption {α} : List (Option α) → List α :=
  List.filterMap id

/-- `ilast' x xs` returns the last element of `xs` if `xs` is non-empty;
it returns `x` otherwise -/
@[simp]
def ilast' {α} : α → List α → α
  | a, [] => a
  | a, b :: l => ilast' b l

/-- `last' xs` returns the last element of `xs` if `xs` is non-empty;
it returns `none` otherwise -/
@[simp]
def last' {α} : List α → Option α
  | [] => none
  | [a] => some a
  | b :: l => last' l

/-- `rotate l n` rotates the elements of `l` to the left by `n`

     rotate [0, 1, 2, 3, 4, 5] 2 = [2, 3, 4, 5, 0, 1] -/
def rotateₓ (l : List α) (n : ℕ) : List α :=
  let (l₁, l₂) := List.splitAtₓ (n % l.length) l
  l₂ ++ l₁

/-- rotate' is the same as `rotate`, but slower. Used for proofs about `rotate`-/
def rotate'ₓ : List α → ℕ → List α
  | [], n => []
  | l, 0 => l
  | a :: l, n + 1 => rotate' (l ++ [a]) n

section Choose

variable (p : α → Prop) [DecidablePred p] (l : List α)

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns both `a` and proofs
of `a ∈ l` and `p a`. -/
def chooseX : ∀ l : List α, ∀ hp : ∃ a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a }
  | [], hp => False.elim (Exists.elim hp fun a h => not_mem_nilₓ a h.left)
  | l :: ls, hp =>
    if pl : p l then ⟨l, ⟨Or.inl rfl, pl⟩⟩
    else
      let ⟨a, ⟨a_mem_ls, pa⟩⟩ := choose_x ls (hp.imp fun b ⟨o, h₂⟩ => ⟨o.resolve_left fun e => pl <| e ▸ h₂, h₂⟩)
      ⟨a, ⟨Or.inr a_mem_ls, pa⟩⟩

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns `a : α`, and properties
are given by `choose_mem` and `choose_property`. -/
def choose (hp : ∃ a, a ∈ l ∧ p a) : α :=
  chooseX p l hp

end Choose

/-- Filters and maps elements of a list -/
def mmapFilterₓₓ {m : Type → Type v} [Monadₓ m] {α β} (f : α → m (Option β)) : List α → m (List β)
  | [] => return []
  | h :: t => do
    let b ← f h
    let t' ← t.mmapFilter
    return <|
        match b with
        | none => t'
        | some x => x :: t'

/-- `mmap_upper_triangle f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mmap_upper_triangle f l` will produce the list
`[f 1 1, f 1 2, f 1 3, f 2 2, f 2 3, f 3 3]`.
-/
def mmapUpperTriangleₓₓ {m} [Monadₓ m] {α β : Type u} (f : α → α → m β) : List α → m (List β)
  | [] => return []
  | h :: t => do
    let v ← f h h
    let l ← t.mmap (f h)
    let t ← t.mmapUpperTriangle
    return <| v :: l ++ t

/-- `mmap'_diag f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mmap'_diag f l` will evaluate, in this order,
`f 1 1`, `f 1 2`, `f 1 3`, `f 2 2`, `f 2 3`, `f 3 3`.
-/
def mmap'Diagₓₓ {m} [Monadₓ m] {α} (f : α → α → m Unit) : List α → m Unit
  | [] => return ()
  | h :: t => (f h h >> t.mmap' (f h)) >> t.mmap'Diag

protected def traverseₓₓ {F : Type u → Type v} [Applicativeₓ F] {α β : Type _} (f : α → F β) : List α → F (List β)
  | [] => pure []
  | x :: xs => List.cons <$> f x <*> traverse xs

/-- `get_rest l l₁` returns `some l₂` if `l = l₁ ++ l₂`.
  If `l₁` is not a prefix of `l`, returns `none` -/
def getRestₓ [DecidableEq α] : List α → List α → Option (List α)
  | l, [] => some l
  | [], _ => none
  | x :: l, y :: l₁ => if x = y then get_rest l l₁ else none

/-- `list.slice n m xs` removes a slice of length `m` at index `n` in list `xs`.
-/
def sliceₓ {α} : ℕ → ℕ → List α → List α
  | 0, n, xs => xs.drop n
  | succ n, m, [] => []
  | succ n, m, x :: xs => x :: slice n m xs

/-- Left-biased version of `list.map₂`. `map₂_left' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is
applied to `none` for the remaining `aᵢ`. Returns the results of the `f`
applications and the remaining `bs`.

```
map₂_left' prod.mk [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])

map₂_left' prod.mk [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
```
-/
@[simp]
def map₂Left'ₓ (f : α → Option β → γ) : List α → List β → List γ × List β
  | [], bs => ([], bs)
  | a :: as, [] => ((a :: as).map fun a => f a none, [])
  | a :: as, b :: bs =>
    let rec := map₂_left' as bs
    (f a (some b) :: rec.fst, rec.snd)

/-- Right-biased version of `list.map₂`. `map₂_right' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is
applied to `none` for the remaining `bᵢ`. Returns the results of the `f`
applications and the remaining `as`.

```
map₂_right' prod.mk [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])

map₂_right' prod.mk [1, 2] ['a'] = ([(some 1, 'a')], [2])
```
-/
def map₂Right'ₓ (f : Option α → β → γ) (as : List α) (bs : List β) : List γ × List α :=
  map₂Left'ₓ (flip f) bs as

/-- Left-biased version of `list.zip`. `zip_left' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`. Also returns the remaining `bs`.

```
zip_left' [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])

zip_left' [1] ['a', 'b'] = ([(1, some 'a')], ['b'])

zip_left' = map₂_left' prod.mk

```
-/
def zipLeft'ₓ : List α → List β → List (α × Option β) × List β :=
  map₂Left'ₓ Prod.mk

/-- Right-biased version of `list.zip`. `zip_right' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`. Also returns the remaining `as`.

```
zip_right' [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])

zip_right' [1, 2] ['a'] = ([(some 1, 'a')], [2])

zip_right' = map₂_right' prod.mk
```
-/
def zipRight'ₓ : List α → List β → List (Option α × β) × List α :=
  map₂Right'ₓ Prod.mk

/-- Left-biased version of `list.map₂`. `map₂_left f as bs` applies `f` to each pair
`aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `bs` is shorter than `as`, `f` is applied to `none`
for the remaining `aᵢ`.

```
map₂_left prod.mk [1, 2] ['a'] = [(1, some 'a'), (2, none)]

map₂_left prod.mk [1] ['a', 'b'] = [(1, some 'a')]

map₂_left f as bs = (map₂_left' f as bs).fst
```
-/
@[simp]
def map₂Leftₓ (f : α → Option β → γ) : List α → List β → List γ
  | [], _ => []
  | a :: as, [] => (a :: as).map fun a => f a none
  | a :: as, b :: bs => f a (some b) :: map₂_left as bs

/-- Right-biased version of `list.map₂`. `map₂_right f as bs` applies `f` to each
pair `aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `as` is shorter than `bs`, `f` is applied to
`none` for the remaining `bᵢ`.

```
map₂_right prod.mk [1, 2] ['a'] = [(some 1, 'a')]

map₂_right prod.mk [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

map₂_right f as bs = (map₂_right' f as bs).fst
```
-/
def map₂Rightₓ (f : Option α → β → γ) (as : List α) (bs : List β) : List γ :=
  map₂Leftₓ (flip f) bs as

/-- Left-biased version of `list.zip`. `zip_left as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`.

```
zip_left [1, 2] ['a'] = [(1, some 'a'), (2, none)]

zip_left [1] ['a', 'b'] = [(1, some 'a')]

zip_left = map₂_left prod.mk
```
-/
def zipLeftₓ : List α → List β → List (α × Option β) :=
  map₂Leftₓ Prod.mk

/-- Right-biased version of `list.zip`. `zip_right as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`.

```
zip_right [1, 2] ['a'] = [(some 1, 'a')]

zip_right [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

zip_right = map₂_right prod.mk
```
-/
def zipRightₓ : List α → List β → List (Option α × β) :=
  map₂Rightₓ Prod.mk

/-- If all elements of `xs` are `some xᵢ`, `all_some xs` returns the `xᵢ`. Otherwise
it returns `none`.

```
all_some [some 1, some 2] = some [1, 2]
all_some [some 1, none  ] = none
```
-/
def allSome : List (Option α) → Option (List α)
  | [] => some []
  | some a :: as => cons a <$> all_some as
  | none :: as => none

/-- `fill_nones xs ys` replaces the `none`s in `xs` with elements of `ys`. If there
are not enough `ys` to replace all the `none`s, the remaining `none`s are
dropped from `xs`.

```
fill_nones [none, some 1, none, none] [2, 3] = [2, 1, 3]
```
-/
def fillNonesₓ {α} : List (Option α) → List α → List α
  | [], _ => []
  | some a :: as, as' => a :: fill_nones as as'
  | none :: as, [] => as.reduceOption
  | none :: as, a :: as' => a :: fill_nones as as'

/-- `take_list as ns` extracts successive sublists from `as`. For `ns = n₁ ... nₘ`,
it first takes the `n₁` initial elements from `as`, then the next `n₂` ones,
etc. It returns the sublists of `as` -- one for each `nᵢ` -- and the remaining
elements of `as`. If `as` does not have at least as many elements as the sum of
the `nᵢ`, the corresponding sublists will have less than `nᵢ` elements.

```
take_list ['a', 'b', 'c', 'd', 'e'] [2, 1, 1] = ([['a', 'b'], ['c'], ['d']], ['e'])
take_list ['a', 'b'] [3, 1] = ([['a', 'b'], []], [])
```
-/
def takeListₓ {α} : List α → List ℕ → List (List α) × List α
  | xs, [] => ([], xs)
  | xs, n :: ns =>
    let ⟨xs₁, xs₂⟩ := xs.splitAt n
    let ⟨xss, rest⟩ := take_list xs₂ ns
    (xs₁ :: xss, rest)

/-- `to_rbmap as` is the map that associates each index `i` of `as` with the
corresponding element of `as`.

```
to_rbmap ['a', 'b', 'c'] = rbmap_of [(0, 'a'), (1, 'b'), (2, 'c')]
```
-/
def toRbmap {α : Type _} : List α → Rbmap ℕ α :=
  foldlWithIndex (fun i mapp a => mapp.insert i a) (mkRbmap ℕ α)

/-- Auxliary definition used to define `to_chunks`.

  `to_chunks_aux n xs i` returns `(xs.take i, (xs.drop i).to_chunks (n+1))`,
  that is, the first `i` elements of `xs`, and the remaining elements chunked into
  sublists of length `n+1`. -/
def toChunksAuxₓ {α} (n : ℕ) : List α → ℕ → List α × List (List α)
  | [], i => ([], [])
  | x :: xs, 0 =>
    let (l, L) := to_chunks_aux xs n
    ([], (x :: l) :: L)
  | x :: xs, i + 1 =>
    let (l, L) := to_chunks_aux xs i
    (x :: l, L)

/-- `xs.to_chunks n` splits the list into sublists of size at most `n`,
such that `(xs.to_chunks n).join = xs`.

```
[1, 2, 3, 4, 5, 6, 7, 8].to_chunks 10 = [[1, 2, 3, 4, 5, 6, 7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].to_chunks 3 = [[1, 2, 3], [4, 5, 6], [7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].to_chunks 2 = [[1, 2], [3, 4], [5, 6], [7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].to_chunks 0 = [[1, 2, 3, 4, 5, 6, 7, 8]]
```
-/
def toChunksₓ {α} : ℕ → List α → List (List α)
  | _, [] => []
  | 0, xs => [xs]
  | n + 1, x :: xs =>
    let (l, L) := toChunksAuxₓ n xs n
    (x :: l) :: L

/-- Asynchronous version of `list.map`.
-/
unsafe def map_async_chunked {α β} (f : α → β) (xs : List α) (chunk_size := 1024) : List β :=
  ((xs.toChunks chunk_size).map fun xs => task.delay fun _ => List.map f xs).bind task.get

/-!
We add some n-ary versions of `list.zip_with` for functions with more than two arguments.
These can also be written in terms of `list.zip` or `list.zip_with`.
For example, `zip_with3 f xs ys zs` could also be written as
`zip_with id (zip_with f xs ys) zs`
or as
`(zip xs $ zip ys zs).map $ λ ⟨x, y, z⟩, f x y z`.
-/


/-- Ternary version of `list.zip_with`. -/
def zipWith3 (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | x :: xs, y :: ys, z :: zs => f x y z :: zip_with3 xs ys zs
  | _, _, _ => []

/-- Quaternary version of `list.zip_with`. -/
def zipWith4 (f : α → β → γ → δ → ε) : List α → List β → List γ → List δ → List ε
  | x :: xs, y :: ys, z :: zs, u :: us => f x y z u :: zip_with4 xs ys zs us
  | _, _, _, _ => []

/-- Quinary version of `list.zip_with`. -/
def zipWith5 (f : α → β → γ → δ → ε → ζ) : List α → List β → List γ → List δ → List ε → List ζ
  | x :: xs, y :: ys, z :: zs, u :: us, v :: vs => f x y z u v :: zip_with5 xs ys zs us vs
  | _, _, _, _, _ => []

/-- An auxiliary function for `list.map_with_prefix_suffix`. -/
def mapWithPrefixSuffixAux {α β} (f : List α → α → List α → β) : List α → List α → List β
  | prev, [] => []
  | prev, h :: t => f prev h t :: map_with_prefix_suffix_aux (prev.concat h) t

/-- `list.map_with_prefix_suffix f l` maps `f` across a list `l`.
For each `a ∈ l` with `l = pref ++ [a] ++ suff`, `a` is mapped to `f pref a suff`.

Example: if `f : list ℕ → ℕ → list ℕ → β`,
`list.map_with_prefix_suffix f [1, 2, 3]` will produce the list
`[f [] 1 [2, 3], f [1] 2 [3], f [1, 2] 3 []]`.
-/
def mapWithPrefixSuffix {α β} (f : List α → α → List α → β) (l : List α) : List β :=
  mapWithPrefixSuffixAux f [] l

/-- `list.map_with_complement f l` is a variant of `list.map_with_prefix_suffix`
that maps `f` across a list `l`.
For each `a ∈ l` with `l = pref ++ [a] ++ suff`, `a` is mapped to `f a (pref ++ suff)`,
i.e., the list input to `f` is `l` with `a` removed.

Example: if `f : ℕ → list ℕ → β`, `list.map_with_complement f [1, 2, 3]` will produce the list
`[f 1 [2, 3], f 2 [1, 3], f 3 [1, 2]]`.
-/
def mapWithComplement {α β} (f : α → List α → β) : List α → List β :=
  map_with_prefix_suffix fun pref a suff => f a (pref ++ suff)

end List

