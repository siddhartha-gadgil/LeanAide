/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Random
import Mathbin.Control.Uliftable

/-!
# `gen` Monad

This monad is used to formulate randomized computations with a parameter
to specify the desired size of the result.

This is a port of the Haskell QuickCheck library.

## Main definitions
  * `gen` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/


universe u v

namespace SlimCheck

/-- Monad to generate random examples to test properties with.
It has a `nat` parameter so that the caller can decide on the
size of the examples. -/
@[reducible]
def Genₓ (α : Type u) :=
  ReaderTₓ (ULift ℕ) Randₓ α deriving Monadₓ, IsLawfulMonad

variable (α : Type u)

-- mathport name: «expr .. »
local infixl:41 " .. " => Set.Icc

/-- Execute a `gen` inside the `io` monad using `i` as the example
size and with a fresh random number generator. -/
def Io.runGen {α} (x : Genₓ α) (i : ℕ) : Io α :=
  Io.runRand (x.run ⟨i⟩)

namespace Gen

section Randₓ

/-- Lift `random.random` to the `gen` monad. -/
def chooseAny [Randomₓ α] : Genₓ α :=
  ⟨fun _ => Randₓ.random α⟩

variable {α} [Preorderₓ α]

/-- Lift `random.random_r` to the `gen` monad. -/
def choose [BoundedRandomₓ α] (x y : α) (p : x ≤ y) : Genₓ (x .. y) :=
  ⟨fun _ => Randₓ.randomR x y p⟩

end Randₓ

open Nat hiding choose

/-- Generate a `nat` example between `x` and `y`. -/
def chooseNat (x y : ℕ) (p : x ≤ y) : Genₓ (x .. y) :=
  choose x y p

/-- Generate a `nat` example between `x` and `y`. -/
def chooseNat' (x y : ℕ) (p : x < y) : Genₓ (Set.Ico x y) :=
  have : ∀ i, x < i → i ≤ y → i.pred < y := fun i h₀ h₁ =>
    show i.pred.succ ≤ y by
      rwa [succ_pred_eq_of_pos] <;> apply lt_of_le_of_ltₓ (Nat.zero_leₓ _) h₀
  (Subtype.map pred fun i (h : x + 1 ≤ i ∧ i ≤ y) => ⟨le_pred_of_ltₓ h.1, this _ h.1 h.2⟩) <$> choose (x + 1) y p

open Nat

instance : Uliftable Genₓ.{u} Genₓ.{v} :=
  ReaderTₓ.uliftable' (Equivₓ.ulift.trans Equivₓ.ulift.symm)

instance : HasOrelse Genₓ.{u} :=
  ⟨fun α x y => do
    let b ← Uliftable.up <| chooseAny Bool
    if b then x else y⟩

variable {α}

/-- Get access to the size parameter of the `gen` monad. For
reasons of universe polymorphism, it is specified in
continuation passing style. -/
def sized (cmd : ℕ → Genₓ α) : Genₓ α :=
  ⟨fun ⟨sz⟩ => ReaderTₓ.run (cmd sz) ⟨sz⟩⟩

/-- Apply a function to the size parameter. -/
def resize (f : ℕ → ℕ) (cmd : Genₓ α) : Genₓ α :=
  ⟨fun ⟨sz⟩ => ReaderTₓ.run cmd ⟨f sz⟩⟩

/-- Create `n` examples using `cmd`. -/
def vectorOf : ∀ (n : ℕ) (cmd : Genₓ α), Genₓ (Vector α n)
  | 0, _ => return Vector.nil
  | succ n, cmd => Vector.cons <$> cmd <*> vector_of n cmd

/-- Create a list of examples using `cmd`. The size is controlled
by the size parameter of `gen`. -/
def listOf (cmd : Genₓ α) : Genₓ (List α) :=
  sized fun sz => do
    do
      let ⟨n⟩ ←
        Uliftable.up <|
            choose_nat 0 (sz + 1)
              (by
                decide)
      let v ← vector_of n cmd
      return v

open ULift

/-- Given a list of example generators, choose one to create an example. -/
def oneOf (xs : List (Genₓ α)) (pos : 0 < xs.length) : Genₓ α := do
  let ⟨⟨n, h, h'⟩⟩ ← Uliftable.up <| chooseNat' 0 xs.length Pos
  List.nthLe xs n h'

/-- Given a list of example generators, choose one to create an example. -/
def elements (xs : List α) (pos : 0 < xs.length) : Genₓ α := do
  let ⟨⟨n, h₀, h₁⟩⟩ ← Uliftable.up <| chooseNat' 0 xs.length Pos
  pure <| List.nthLe xs n h₁

/-- `freq_aux xs i _` takes a weighted list of generator and a number meant to select one of the
generators.

If we consider `freq_aux [(1, gena), (3, genb), (5, genc)] 4 _`, we choose a generator by splitting
the interval 1-9 into 1-1, 2-4, 5-9 so that the width of each interval corresponds to one of the
number in the list of generators. Then, we check which interval 4 falls into: it selects `genb`.
-/
def freqAux : ∀ (xs : List (ℕ+ × Genₓ α)) (i), i < (xs.map (Subtype.val ∘ Prod.fst)).Sum → Genₓ α
  | [], i, h => False.elim (Nat.not_lt_zeroₓ _ h)
  | (i, x) :: xs, j, h =>
    if h' : j < i then x
    else
      freq_aux xs (j - i)
        (by
          rw [tsub_lt_iff_right (le_of_not_gtₓ h')]
          simpa [← List.sum_cons, ← add_commₓ] using h)

/-- `freq [(1, gena), (3, genb), (5, genc)] _` will choose one of `gena`, `genb`, `genc` with
probabilities proportional to the number accompanying them. In this example, the sum of
those numbers is 9, `gena` will be chosen with probability ~1/9, `genb` with ~3/9 (i.e. 1/3)
and `genc` with probability 5/9.
-/
def freq (xs : List (ℕ+ × Genₓ α)) (pos : 0 < xs.length) : Genₓ α :=
  let s := (xs.map (Subtype.val ∘ Prod.fst)).Sum
  have ha : 1 ≤ s :=
    le_transₓ Pos <|
      List.length_mapₓ (Subtype.val ∘ Prod.fst) xs ▸
        List.length_le_sum_of_one_le _ fun i => by
          simp
          intros
          assumption
  have : 0 ≤ s - 1 := le_tsub_of_add_le_right ha
  (Uliftable.adaptUp Genₓ.{0} Genₓ.{u} (chooseNat 0 (s - 1) this)) fun i =>
    freqAux xs i.1
      (by
        rcases i with ⟨i, h₀, h₁⟩ <;> rwa [le_tsub_iff_right] at h₁ <;> exact ha)

/-- Generate a random permutation of a given list. -/
def permutationOf {α : Type u} : ∀ xs : List α, Genₓ (Subtype <| List.Perm xs)
  | [] => pure ⟨[], List.Perm.nil⟩
  | x :: xs => do
    let ⟨xs', h⟩ ← permutation_of xs
    let ⟨⟨n, _, h'⟩⟩ ←
      Uliftable.up <|
          chooseNat 0 xs'.length
            (by
              decide)
    pure ⟨List.insertNthₓ n x xs', List.Perm.trans (List.Perm.cons _ h) (List.perm_insert_nth _ _ h').symm⟩

end Gen

end SlimCheck

