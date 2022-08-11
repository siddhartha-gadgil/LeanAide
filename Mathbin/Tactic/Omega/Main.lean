/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.Int.Main
import Mathbin.Tactic.Omega.Nat.Main

/-
A tactic for discharging linear integer & natural
number arithmetic goals using the Omega test.
-/
namespace Omega

open Tactic

unsafe def select_domain (t s : tactic (Option Bool)) : tactic (Option Bool) := do
  let a ← t
  let b ← s
  match a, b with
    | a, none => return a
    | none, b => return b
    | some tt, some tt => return (some tt)
    | some ff, some ff => return (some ff)
    | _, _ => failed

unsafe def type_domain (x : expr) : tactic (Option Bool) :=
  if x = quote.1 Int then return (some true) else if x = quote.1 Nat then return (some false) else failed

/-- Detects domain of a formula from its expr.
* Returns none, if domain can be either ℤ or ℕ
* Returns some tt, if domain is exclusively ℤ
* Returns some ff, if domain is exclusively ℕ
* Fails, if domain is neither ℤ nor ℕ -/
unsafe def form_domain : expr → tactic (Option Bool)
  | quote.1 ¬%%ₓpx => form_domain px
  | quote.1 ((%%ₓpx) ∨ %%ₓqx) => select_domain (form_domain px) (form_domain qx)
  | quote.1 ((%%ₓpx) ∧ %%ₓqx) => select_domain (form_domain px) (form_domain qx)
  | quote.1 ((%%ₓpx) ↔ %%ₓqx) => select_domain (form_domain px) (form_domain qx)
  | quote.1 (%%ₓexpr.pi _ _ px qx) =>
    Monadₓ.cond (if expr.has_var px then return true else is_prop px) (select_domain (form_domain px) (form_domain qx))
      (select_domain (type_domain px) (form_domain qx))
  | quote.1 (@LT.lt (%%ₓdx) (%%ₓh) _ _) => type_domain dx
  | quote.1 (@LE.le (%%ₓdx) (%%ₓh) _ _) => type_domain dx
  | quote.1 (@Eq (%%ₓdx) _ _) => type_domain dx
  | quote.1 (@Ge (%%ₓdx) (%%ₓh) _ _) => type_domain dx
  | quote.1 (@Gt (%%ₓdx) (%%ₓh) _ _) => type_domain dx
  | quote.1 (@Ne (%%ₓdx) _ _) => type_domain dx
  | quote.1 True => return none
  | quote.1 False => return none
  | x => failed

unsafe def goal_domain_aux (x : expr) : tactic Bool :=
  omega.int.wff x >> return true <|> omega.nat.wff x >> return false

/-- Use the current goal to determine.
    Return tt if the domain is ℤ, and return ff if it is ℕ -/
unsafe def goal_domain : tactic Bool := do
  let gx ← target
  let hxs ← local_context >>= Monadₓ.mapm infer_type
  app_first goal_domain_aux (gx :: hxs)

/-- Return tt if the domain is ℤ, and return ff if it is ℕ -/
unsafe def determine_domain (opt : List Name) : tactic Bool :=
  if `int ∈ opt then return true else if `nat ∈ opt then return false else goal_domain

end Omega

open Lean.Parser Interactive Omega

/-- Attempts to discharge goals in the quantifier-free fragment of
linear integer and natural number arithmetic using the Omega test.
Guesses the correct domain by looking at the goal and hypotheses,
and then reverts all relevant hypotheses and variables.
Use `omega manual` to disable automatic reverts, and `omega int` or
`omega nat` to specify the domain.
-/
unsafe def tactic.interactive.omega (opt : parse (many ident)) : tactic Unit := do
  let is_int ← determine_domain opt
  let is_manual : Bool := if `manual ∈ opt then true else false
  if is_int then omega_int is_manual else omega_nat is_manual

add_hint_tactic omega

initialize
  registerTraceClass.1 `omega

/-- `omega` attempts to discharge goals in the quantifier-free fragment of linear integer and natural
number arithmetic using the Omega test. In other words, the core procedure of `omega` works with
goals of the form
```lean
∀ x₁, ... ∀ xₖ, P
```
where `x₁, ... xₖ` are integer (resp. natural number) variables, and `P` is a quantifier-free
formula of linear integer (resp. natural number) arithmetic. For instance:
```lean
example : ∀ (x y : int), (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by omega
```
By default, `omega` tries to guess the correct domain by looking at the goal and hypotheses, and
then reverts all relevant hypotheses and variables (e.g., all variables of type `nat` and `Prop`s
in linear natural number arithmetic, if the domain was determined to be `nat`) to universally close
the goal before calling the main procedure. Therefore, `omega` will often work even if the goal
is not in the above form:
```lean
example (x y : nat) (h : 2 * x + 1 = 2 * y) : false := by omega
```
But this behaviour is not always optimal, since it may revert irrelevant hypotheses or incorrectly
guess the domain. Use `omega manual` to disable automatic reverts, and `omega int` or `omega nat`
to specify the domain.
```lean
example (x y z w : int) (h1 : 3 * y ≥ x) (h2 : z > 19 * w) : 3 * x ≤ 9 * y :=
by {revert h1 x y, omega manual}

example (i : int) (n : nat) (h1 : i = 0) (h2 : n < n) : false := by omega nat

example (n : nat) (h1 : n < 34) (i : int) (h2 : i * 9 = -72) : i = -8 :=
by {revert h2 i, omega manual int}
```
`omega` handles `nat` subtraction by repeatedly rewriting goals of the form `P[t-s]` into
`P[x] ∧ (t = s + x ∨ (t ≤ s ∧ x = 0))`, where `x` is fresh. This means that each (distinct)
occurrence of subtraction will cause the goal size to double during DNF transformation.

`omega` implements the real shadow step of the Omega test, but not the dark and gray shadows.
Therefore, it should (in principle) succeed whenever the negation of the goal has no real solution,
but it may fail if a real solution exists, even if there is no integer/natural number solution.

You can enable `set_option trace.omega true` to see how `omega` interprets your goal.
-/
add_tactic_doc
  { Name := "omega", category := DocCategory.tactic, declNames := [`tactic.interactive.omega],
    tags := ["finishing", "arithmetic", "decision procedure"] }

