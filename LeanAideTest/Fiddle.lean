import Mathlib
import LeanAide
open Nat LeanAide
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
error: function expected at
  Submodule ℝ V
term has type
  Type
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
