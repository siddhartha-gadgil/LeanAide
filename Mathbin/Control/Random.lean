/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Monad.Basic
import Mathbin.Data.Int.Basic
import Mathbin.Data.Stream.Defs
import Mathbin.Control.Uliftable
import Mathbin.Tactic.NormNum
import Mathbin.Data.Bitvec.Basic

/-!
# Rand Monad and Random Class

This module provides tools for formulating computations guided by randomness and for
defining objects that can be created randomly.

## Main definitions
  * `rand` monad for computations guided by randomness;
  * `random` class for objects that can be generated randomly;
    * `random` to generate one object;
    * `random_r` to generate one object inside a range;
    * `random_series` to generate an infinite series of objects;
    * `random_series_r` to generate an infinite series of objects inside a range;
  * `io.mk_generator` to create a new random number generator;
  * `io.run_rand` to run a randomized computation inside the `io` monad;
  * `tactic.run_rand` to run a randomized computation inside the `tactic` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random monad io

## References

  * Similar library in Haskell: https://hackage.haskell.org/package/MonadRandom

-/


open List Io Applicativeₓ

universe u v w

/-- A monad to generate random objects using the generator type `g` -/
@[reducible]
def RandGₓ (g : Type) (α : Type u) : Type u :=
  State (ULift.{u} g) α

/-- A monad to generate random objects using the generator type `std_gen` -/
@[reducible]
def Randₓ :=
  RandGₓ StdGen

instance (g : Type) : Uliftable (RandGₓ.{u} g) (RandGₓ.{v} g) :=
  @StateTₓ.uliftable' _ _ _ _ _ (Equivₓ.ulift.trans Equivₓ.ulift.symm)

open ULift hiding Inhabited

/-- Generate one more `ℕ` -/
def RandGₓ.next {g : Type} [RandomGen g] : RandGₓ g ℕ :=
  ⟨Prod.map id up ∘ RandomGen.next ∘ down⟩

-- mathport name: «expr .. »
local infixl:41 " .. " => Set.Icc

open Streamₓ

/-- `bounded_random α` gives us machinery to generate values of type `α` between certain bounds -/
class BoundedRandomₓ (α : Type u) [Preorderₓ α] where
  randomR : ∀ (g) [RandomGen g] (x y : α), x ≤ y → RandGₓ g (x .. y)

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`Random] []
/-- `random α` gives us machinery to generate values of type `α` -/
class Randomₓ (α : Type u) where
  Random : ∀ (g : Type) [RandomGen g], RandGₓ g α

/-- shift_31_left = 2^31; multiplying by it shifts the binary
representation of a number left by 31 bits, dividing by it shifts it
right by 31 bits -/
def shift31Left : ℕ := by
  apply_normed 2 ^ 31

namespace Randₓ

open Streamₓ

variable (α : Type u)

variable (g : Type) [RandomGen g]

/-- create a new random number generator distinct from the one stored in the state -/
def split : RandGₓ g g :=
  ⟨Prod.map id up ∘ RandomGen.split ∘ down⟩

variable {g}

section Randomₓ

variable [Randomₓ α]

export Randomₓ (Random)

/-- Generate a random value of type `α`. -/
def random : RandGₓ g α :=
  Randomₓ.random α g

/-- generate an infinite series of random values of type `α` -/
def randomSeries : RandGₓ g (Streamₓ α) := do
  let gen ← Uliftable.up (split g)
  pure <| Streamₓ.corecState (Randomₓ.random α g) gen

end Randomₓ

variable {α}

/-- Generate a random value between `x` and `y` inclusive. -/
def randomR [Preorderₓ α] [BoundedRandomₓ α] (x y : α) (h : x ≤ y) : RandGₓ g (x .. y) :=
  BoundedRandomₓ.randomR g x y h

/-- generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
def randomSeriesR [Preorderₓ α] [BoundedRandomₓ α] (x y : α) (h : x ≤ y) : RandGₓ g (Streamₓ (x .. y)) := do
  let gen ← Uliftable.up (split g)
  pure <| corec_state (BoundedRandomₓ.randomR g x y h) gen

end Randₓ

namespace Io

private def accum_char (w : ℕ) (c : Charₓ) : ℕ :=
  c.toNat + 256 * w

/-- create and a seed a random number generator -/
def mkGenerator : Io StdGen := do
  let seed ← Io.rand 0 shift31Left
  return <| mkStdGenₓ seed

variable {α : Type}

/-- Run `cmd` using a randomly seeded random number generator -/
def runRand (cmd : Randₓ α) : Io α := do
  let g ← Io.mkGenerator
  return <| (cmd ⟨g⟩).1

/-- Run `cmd` using the provided seed. -/
def runRandWith (seed : ℕ) (cmd : Randₓ α) : Io α :=
  return <| (cmd.run ⟨mkStdGenₓ seed⟩).1

section Randomₓ

variable [Randomₓ α]

/-- randomly generate a value of type α -/
def random : Io α :=
  Io.runRand (Randₓ.random α)

/-- randomly generate an infinite series of value of type α -/
def randomSeries : Io (Streamₓ α) :=
  Io.runRand (Randₓ.randomSeries α)

end Randomₓ

section BoundedRandomₓ

variable [Preorderₓ α] [BoundedRandomₓ α]

/-- randomly generate a value of type α between `x` and `y` -/
def randomR (x y : α) (p : x ≤ y) : Io (x .. y) :=
  Io.runRand (BoundedRandomₓ.randomR _ x y p)

/-- randomly generate an infinite series of value of type α between `x` and `y` -/
def randomSeriesR (x y : α) (h : x ≤ y) : Io (Streamₓ <| x .. y) :=
  Io.runRand (Randₓ.randomSeriesR x y h)

end BoundedRandomₓ

end Io

namespace Tactic

/-- create a seeded random number generator in the `tactic` monad -/
unsafe def mk_generator : tactic StdGen := do
  tactic.unsafe_run_io @Io.mkGenerator

/-- run `cmd` using the a randomly seeded random number generator
in the tactic monad -/
unsafe def run_rand {α : Type u} (cmd : Randₓ α) : tactic α := do
  let ⟨g⟩ ← tactic.up mk_generator
  return (cmd ⟨g⟩).1

variable {α : Type u}

section BoundedRandomₓ

variable [Preorderₓ α] [BoundedRandomₓ α]

/-- Generate a random value between `x` and `y` inclusive. -/
unsafe def random_r (x y : α) (h : x ≤ y) : tactic (x .. y) :=
  run_rand (Randₓ.randomR x y h)

/-- Generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
unsafe def random_series_r (x y : α) (h : x ≤ y) : tactic (Streamₓ <| x .. y) :=
  run_rand (Randₓ.randomSeriesR x y h)

end BoundedRandomₓ

section Randomₓ

variable [Randomₓ α]

/-- randomly generate a value of type α -/
unsafe def random : tactic α :=
  run_rand (Randₓ.random α)

/-- randomly generate an infinite series of value of type α -/
unsafe def random_series : tactic (Streamₓ α) :=
  run_rand (Randₓ.randomSeries α)

end Randomₓ

end Tactic

open Nat (succ one_add mod_eq_of_lt zero_lt_succ add_one succ_le_succ)

variable {g : Type} [RandomGen g]

open Nat

namespace Finₓ

variable {n : ℕ} [Fact (0 < n)]

/-- generate a `fin` randomly -/
protected def random : RandGₓ g (Finₓ n) :=
  ⟨fun ⟨g⟩ => Prod.map ofNat' up <| randNatₓ g 0 n⟩

end Finₓ

open Nat

instance natBoundedRandom :
    BoundedRandomₓ ℕ where randomR := fun g inst x y hxy => do
    let z ← @Finₓ.random g inst (succ <| y - x) _
    pure
        ⟨z + x, Nat.le_add_leftₓ _ _, by
          rw [← le_tsub_iff_right hxy] <;> apply le_of_succ_le_succ z.is_lt⟩

/-- This `bounded_random` interval generates integers between `x` and
`y` by first generating a natural number between `0` and `y - x` and
shifting the result appropriately. -/
instance intBoundedRandom :
    BoundedRandomₓ ℤ where randomR := fun g inst x y hxy => do
    let ⟨z, h₀, h₁⟩ ←
      @BoundedRandomₓ.randomR ℕ _ _ g inst 0 (Int.natAbs <| y - x)
          (by
            decide)
    pure
        ⟨z + x, Int.le_add_of_nonneg_leftₓ (Int.coe_nat_nonneg _),
          Int.add_le_of_le_sub_rightₓ <|
            le_transₓ (Int.coe_nat_le_coe_nat_of_le h₁)
              (le_of_eqₓ <| Int.of_nat_nat_abs_eq_of_nonneg (Int.sub_nonneg_of_leₓ hxy))⟩

instance finRandom (n : ℕ) [Fact (0 < n)] : Randomₓ (Finₓ n) where Random := fun g inst => @Finₓ.random g inst _ _

instance finBoundedRandom (n : ℕ) :
    BoundedRandomₓ (Finₓ n) where randomR := fun g inst (x y : Finₓ n) p => do
    let ⟨r, h, h'⟩ ← @Randₓ.randomR ℕ g inst _ _ x.val y.val p
    pure ⟨⟨r, lt_of_le_of_ltₓ h' y⟩, h, h'⟩

/-- A shortcut for creating a `random (fin n)` instance from
a proof that `0 < n` rather than on matching on `fin (succ n)`  -/
def randomFinOfPos : ∀ {n : ℕ} (h : 0 < n), Randomₓ (Finₓ n)
  | succ n, _ => finRandom _
  | 0, h => False.elim (Nat.not_lt_zeroₓ _ h)

theorem bool_of_nat_mem_Icc_of_mem_Icc_to_nat (x y : Bool) (n : ℕ) :
    n ∈ (x.toNat .. y.toNat) → Bool.ofNat n ∈ (x .. y) := by
  simp only [← and_imp, ← Set.mem_Icc]
  intro h₀ h₁
  constructor <;> [have h₂ := Bool.of_nat_le_of_nat h₀, have h₂ := Bool.of_nat_le_of_nat h₁] <;>
    rw [Bool.of_nat_to_nat] at h₂ <;> exact h₂

instance :
    Randomₓ
      Bool where Random := fun g inst =>
    (Bool.ofNat ∘ Subtype.val) <$> @BoundedRandomₓ.randomR ℕ _ _ g inst 0 1 (Nat.zero_leₓ _)

instance :
    BoundedRandomₓ
      Bool where randomR := fun g _inst x y p =>
    Subtype.map Bool.ofNat (bool_of_nat_mem_Icc_of_mem_Icc_to_nat x y) <$>
      @BoundedRandomₓ.randomR ℕ _ _ g _inst x.toNat y.toNat (Bool.to_nat_le_to_nat p)

open FinFact

/-- generate a random bit vector of length `n` -/
def Bitvec.random (n : ℕ) : RandGₓ g (Bitvec n) :=
  Bitvec.ofFin <$> Randₓ.random (Finₓ <| 2 ^ n)

/-- generate a random bit vector of length `n` -/
def Bitvec.randomR {n : ℕ} (x y : Bitvec n) (h : x ≤ y) : RandGₓ g (x .. y) :=
  have h' : ∀ a : Finₓ (2 ^ n), a ∈ (x.toFin .. y.toFin) → Bitvec.ofFin a ∈ (x .. y) := by
    simp only [← and_imp, ← Set.mem_Icc]
    intro z h₀ h₁
    replace h₀ := Bitvec.of_fin_le_of_fin_of_le h₀
    replace h₁ := Bitvec.of_fin_le_of_fin_of_le h₁
    rw [Bitvec.of_fin_to_fin] at h₀ h₁
    constructor <;> assumption
  Subtype.map Bitvec.ofFin h' <$> Randₓ.randomR x.toFin y.toFin (Bitvec.to_fin_le_to_fin_of_le h)

open Nat

instance randomBitvec (n : ℕ) : Randomₓ (Bitvec n) where Random := fun _ inst => @Bitvec.random _ inst n

instance boundedRandomBitvec (n : ℕ) :
    BoundedRandomₓ (Bitvec n) where randomR := fun _ inst x y p => @Bitvec.randomR _ inst _ _ _ p

