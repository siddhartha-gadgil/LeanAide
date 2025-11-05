import Mathlib
import LeanAide
import Std.Internal.Async.Process
open Nat LeanAide Std.Internal.IO Process Async System
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


abbrev hard.prop : Prop := False


def deferred.hard [inst_hard: Fact hard.prop] : hard.prop := inst_hard.elim

section
open deferred (hard)
variable [Fact hard.prop]

theorem hard_copy : hard.prop := hard

end


/-- info: hard_copy [Fact hard.prop] : hard.prop -/
#guard_msgs in
#check hard_copy -- hard_copy [inst_hard : Fact hard.prop] : hard.prop

example : 1 ≤ 2 := by first | (simp? ; done) | hammer


universe u

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : ∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m : ℕ, n = m * orderOf a := by sorry

example : ∀ {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module ℝ V] [Module ℝ W] (T : V →ₗ[ℝ] W),
  ((LinearMap.ker T) : Submodule ℝ V) := by sorry

#check Submodule -- Submodule.{u, v} (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v

/--
error: Function expected at
  Submodule ℝ V
but this term has type
  Type

Note: Expected a function because this term is being applied to the argument
  (LinearMap.ker T)
-/
#guard_msgs in
example : ∀ {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℝ V] [Module ℝ W] (T : V →ₗ[ℝ] W), Submodule ℝ V (LinearMap.ker T) := by sorry

-- Gemini output:
example {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℝ V] [Module ℝ W] (T : V →ₗ[ℝ] W) : Submodule ℝ V :=
  LinearMap.ker T

theorem kernel_is_a_submodule {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module ℝ V] [Module ℝ W] (T : V →ₗ[ℝ] W) :
  ∃ (S : Submodule ℝ V), ∀ (x : V), x ∈ S ↔ T x = 0 := by
  -- We prove this by providing the kernel itself as the submodule.
  use LinearMap.ker T
  -- The condition then becomes the definition of the kernel, which is true by reflexivity.
  intro x
  exact LinearMap.mem_ker -- T (corrected)

example : ∀ n : ℕ, (fun x => 1 + x)^[n] 0 = n  := by
  intro n
  induction n with
  | zero => aesop
  | succ n ih => aesop

example : ∀ f: ℕ → ℕ, f 0 = 0 → (∀ n: ℕ, f (n + 1) = f n + 1) → ∀ n: ℕ, f n = n := by
  intro f h₁ h₂ n
  induction n with
  | zero => aesop
  | succ n ih =>
    aesop

open IO FS

def logHandleTest : IO Handle :=
  Handle.mk "log.txt" Mode.append

def setErr : IO Unit := do
  discard <| IO.setStderr <| Stream.ofHandle (← logHandleTest)

def writeToErr (s : String) : IO Unit := do
  setErr
  IO.eprintln s
  IO.sleep 5000
  IO.eprintln <| s ++ " again"

-- #eval writeToErr "hello"

-- #eval setErr

-- #eval writeToErr "hello"

#eval getId

#eval getCwd

#eval getTmpDir

#eval getHomeDir

#eval getEnv "OPENAI_API_KEY"

#check φ

#check Lake.Toml.ppInlineTable

#print Lean.Json

#check Lake.Toml.DecodeM

#check Lean.fromJson?

#print Lake.Toml.Value /-
Lake.Toml.Value.string : Lean.Syntax → String → Lake.Toml.Value
Lake.Toml.Value.integer : Lean.Syntax → ℤ → Lake.Toml.Value
Lake.Toml.Value.float : Lean.Syntax → Float → Lake.Toml.Value
Lake.Toml.Value.boolean : Lean.Syntax → Bool → Lake.Toml.Value
Lake.Toml.Value.dateTime : Lean.Syntax → Lake.Toml.DateTime → Lake.Toml.Value
Lake.Toml.Value.array : Lean.Syntax → Array Lake.Toml.Value → Lake.Toml.Value
-/

open Lean
structure S where
  a : Nat
  b : String
deriving ToJson, FromJson, Repr

#eval toJson ({ a := 10, b := "hello" } : S)

#eval fromJson? (α := S) <| (toJson ({ a := 10, b := "hello" } : S)).mergeObj (Json.mkObj [("a", Json.num 20), ("d", Json.str "extra")])
