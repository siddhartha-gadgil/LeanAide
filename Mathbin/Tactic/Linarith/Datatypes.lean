/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathbin.Tactic.Linarith.Lemmas
import Mathbin.Tactic.Ring

/-!
# Datatypes for `linarith`

Some of the data structures here are used in multiple parts of the tactic.
We split them into their own file.

This file also contains a few convenient auxiliary functions.
-/


initialize
  registerTraceClass.1 `linarith

open Native

namespace Linarith

/-- A shorthand for tracing when the `trace.linarith` option is set to true. -/
unsafe def linarith_trace {α} [has_to_tactic_format α] (s : α) : tactic Unit :=
  tactic.when_tracing `linarith (tactic.trace s)

/-- A shorthand for tracing the types of a list of proof terms
when the `trace.linarith` option is set to true.
-/
unsafe def linarith_trace_proofs (s : Stringₓ := "") (l : List expr) : tactic Unit :=
  tactic.when_tracing `linarith <| do
    tactic.trace s
    l tactic.infer_type >>= tactic.trace

/-! ### Linear expressions -/


/-- A linear expression is a list of pairs of variable indices and coefficients,
representing the sum of the products of each coefficient with its corresponding variable.

Some functions on `linexp` assume that `n : ℕ` occurs at most once as the first element of a pair,
and that the list is sorted in decreasing order of the first argument.
This is not enforced by the type but the operations here preserve it.
-/
@[reducible]
def Linexp : Type :=
  List (ℕ × ℤ)

namespace Linexp

/-- Add two `linexp`s together componentwise.
Preserves sorting and uniqueness of the first argument.
-/
unsafe def add : Linexp → Linexp → Linexp
  | [], a => a
  | a, [] => a
  | a@(n1, z1) :: t1, b@(n2, z2) :: t2 =>
    if n1 < n2 then b :: add (a :: t1) t2
    else
      if n2 < n1 then a :: add t1 (b :: t2)
      else
        let sum := z1 + z2
        if Sum = 0 then add t1 t2 else (n1, Sum) :: add t1 t2

/-- `l.scale c` scales the values in `l` by `c` without modifying the order or keys. -/
def scale (c : ℤ) (l : Linexp) : Linexp :=
  if c = 0 then [] else if c = 1 then l else l.map fun ⟨n, z⟩ => (n, z * c)

/-- `l.get n` returns the value in `l` associated with key `n`, if it exists, and `none` otherwise.
This function assumes that `l` is sorted in decreasing order of the first argument,
that is, it will return `none` as soon as it finds a key smaller than `n`.
-/
def get (n : ℕ) : Linexp → Option ℤ
  | [] => none
  | (a, b) :: t => if a < n then none else if a = n then some b else get t

/-- `l.contains n` is true iff `n` is the first element of a pair in `l`.
-/
def contains (n : ℕ) : Linexp → Bool :=
  Option.isSome ∘ get n

/-- `l.zfind n` returns the value associated with key `n` if there is one, and 0 otherwise.
-/
def zfind (n : ℕ) (l : Linexp) : ℤ :=
  match l.get n with
  | none => 0
  | some v => v

/-- `l.vars` returns the list of variables that occur in `l`. -/
def vars (l : Linexp) : List ℕ :=
  l.map Prod.fst

/-- Defines a lex ordering on `linexp`. This function is performance critical.
-/
def cmp : Linexp → Linexp → Ordering
  | [], [] => Ordering.eq
  | [], _ => Ordering.lt
  | _, [] => Ordering.gt
  | (n1, z1) :: t1, (n2, z2) :: t2 =>
    if n1 < n2 then Ordering.lt
    else if n2 < n1 then Ordering.gt else if z1 < z2 then Ordering.lt else if z2 < z1 then Ordering.gt else cmp t1 t2

end Linexp

/-! ### Inequalities -/


/-- The three-element type `ineq` is used to represent the strength of a comparison between
terms. -/
inductive Ineq : Type
  | Eq
  | le
  | lt
  deriving DecidableEq, Inhabited

namespace Ineq

/-- `max R1 R2` computes the strength of the sum of two inequalities. If `t1 R1 0` and `t2 R2 0`,
then `t1 + t2 (max R1 R2) 0`.
-/
def max : Ineq → Ineq → Ineq
  | lt, a => lt
  | a, lt => lt
  | le, a => le
  | a, le => le
  | Eq, Eq => eq

/-- `ineq` is ordered `eq < le < lt`. -/
def cmp : Ineq → Ineq → Ordering
  | Eq, Eq => Ordering.eq
  | Eq, _ => Ordering.lt
  | le, le => Ordering.eq
  | le, lt => Ordering.lt
  | lt, lt => Ordering.eq
  | _, _ => Ordering.gt

/-- Prints an `ineq` as the corresponding infix symbol. -/
def toString : Ineq → Stringₓ
  | Eq => "="
  | le => "≤"
  | lt => "<"

/-- Finds the name of a multiplicative lemma corresponding to an inequality strength. -/
unsafe def to_const_mul_nm : Ineq → Name
  | lt => `` mul_neg
  | le => `` mul_nonpos
  | Eq => `` mul_eq

instance : HasToString Ineq :=
  ⟨Ineq.toString⟩

unsafe instance : has_to_format Ineq :=
  ⟨fun i => Ineq.toString i⟩

end Ineq

/-! ### Comparisons with 0 -/


/-- The main datatype for FM elimination.
Variables are represented by natural numbers, each of which has an integer coefficient.
Index 0 is reserved for constants, i.e. `coeffs.find 0` is the coefficient of 1.
The represented term is `coeffs.sum (λ ⟨k, v⟩, v * Var[k])`.
str determines the strength of the comparison -- is it < 0, ≤ 0, or = 0?
-/
structure Comp : Type where
  str : Ineq
  coeffs : Linexp
  deriving Inhabited

/-- `c.vars` returns the list of variables that appear in the linear expression contained in `c`. -/
def Comp.vars : Comp → List ℕ :=
  linexp.vars ∘ comp.coeffs

/-- `comp.coeff_of c a` projects the coefficient of variable `a` out of `c`. -/
def Comp.coeffOf (c : Comp) (a : ℕ) : ℤ :=
  c.coeffs.zfind a

/-- `comp.scale c n` scales the coefficients of `c` by `n`. -/
def Comp.scale (c : Comp) (n : ℕ) : Comp :=
  { c with coeffs := c.coeffs.scale n }

/-- `comp.add c1 c2` adds the expressions represented by `c1` and `c2`.
The coefficient of variable `a` in `c1.add c2`
is the sum of the coefficients of `a` in `c1` and `c2`.
 -/
unsafe def comp.add (c1 c2 : Comp) : Comp :=
  ⟨c1.str.max c2.str, c1.coeffs.add c2.coeffs⟩

/-- `comp` has a lex order. First the `ineq`s are compared, then the `coeff`s. -/
unsafe def comp.cmp : Comp → Comp → Ordering
  | ⟨str1, coeffs1⟩, ⟨str2, coeffs2⟩ =>
    match str1.cmp str2 with
    | Ordering.lt => Ordering.lt
    | Ordering.gt => Ordering.gt
    | Ordering.eq => coeffs1.cmp coeffs2

/-- A `comp` represents a contradiction if its expression has no coefficients and its strength is <,
that is, it represents the fact `0 < 0`.
 -/
unsafe def comp.is_contr (c : Comp) : Bool :=
  c.coeffs.Empty ∧ c.str = ineq.lt

unsafe instance comp.to_format : has_to_format Comp :=
  ⟨fun p => to_fmt p.coeffs ++ toString p.str ++ "0"⟩

/-! ### Parsing into linear form -/


/-! ### Control -/


/-- A preprocessor transforms a proof of a proposition into a proof of a different propositon.
The return type is `list expr`, since some preprocessing steps may create multiple new hypotheses,
and some may remove a hypothesis from the list.
A "no-op" preprocessor should return its input as a singleton list.
-/
unsafe structure preprocessor : Type where
  Name : Stringₓ
  transform : expr → tactic (List expr)

/-- Some preprocessors need to examine the full list of hypotheses instead of working item by item.
As with `preprocessor`, the input to a `global_preprocessor` is replaced by, not added to, its
output.
-/
unsafe structure global_preprocessor : Type where
  Name : Stringₓ
  transform : List expr → tactic (List expr)

/-- Some preprocessors perform branching case splits. A `branch` is used to track one of these case
splits. The first component, an `expr`, is the goal corresponding to this branch of the split,
given as a metavariable. The `list expr` component is the list of hypotheses for `linarith`
in this branch. Every `expr` in this list should be type correct in the context of the associated
goal.
-/
unsafe def branch : Type :=
  expr × List expr

/-- Some preprocessors perform branching case splits.
A `global_branching_preprocessor` produces a list of branches to run.
Each branch is independent, so hypotheses that appear in multiple branches should be duplicated.
The preprocessor is responsible for making sure that each branch contains the correct goal
metavariable.
-/
unsafe structure global_branching_preprocessor : Type where
  Name : Stringₓ
  transform : List expr → tactic (List branch)

/-- A `preprocessor` lifts to a `global_preprocessor` by folding it over the input list.
-/
unsafe def preprocessor.globalize (pp : preprocessor) : global_preprocessor where
  Name := pp.Name
  transform :=
    List.mfoldl
      (fun ret e => do
        let l' ← pp.transform e
        return (l' ++ ret))
      []

/-- A `global_preprocessor` lifts to a `global_branching_preprocessor` by producing only one branch.
-/
unsafe def global_preprocessor.branching (pp : global_preprocessor) : global_branching_preprocessor where
  Name := pp.Name
  transform := fun l => do
    let g ← tactic.get_goal
    singleton <$> Prod.mk g <$> pp l

/-- `process pp l` runs `pp.transform` on `l` and returns the result,
tracing the result if `trace.linarith` is on.
-/
unsafe def global_branching_preprocessor.process (pp : global_branching_preprocessor) (l : List expr) :
    tactic (List branch) := do
  let l ← pp.transform l
  when (l > 1) <| linarith_trace f! "Preprocessing: {pp} has branched, with branches:"
  l fun l => tactic.set_goals [l.1] >> linarith_trace_proofs (toString f! "Preprocessing: {pp}") l.2
  return l

unsafe instance preprocessor_to_gb_preprocessor : Coe preprocessor global_branching_preprocessor :=
  ⟨global_preprocessor.branching ∘ preprocessor.globalize⟩

unsafe instance global_preprocessor_to_gb_preprocessor : Coe global_preprocessor global_branching_preprocessor :=
  ⟨global_preprocessor.branching⟩

/-- A `certificate_oracle` is a function `produce_certificate : list comp → ℕ → tactic (rb_map ℕ ℕ)`.
`produce_certificate hyps max_var` tries to derive a contradiction from the comparisons in `hyps`
by eliminating all variables ≤ `max_var`.
If successful, it returns a map `coeff : ℕ → ℕ` as a certificate.
This map represents that we can find a contradiction by taking the sum  `∑ (coeff i) * hyps[i]`.

The default `certificate_oracle` used by `linarith` is
`linarith.fourier_motzkin.produce_certificate`.
-/
unsafe def certificate_oracle : Type :=
  List Comp → ℕ → tactic (rb_map ℕ ℕ)

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- A configuration object for `linarith`. -/
unsafe structure linarith_config : Type where
  discharger : tactic Unit := sorry
  restrict_type : Option Type := none
  restrict_type_reflect : reflected _ restrict_type := by
    run_tac
      tactic.apply_instance
  exfalso : Bool := true
  Transparency : Tactic.Transparency := reducible
  split_hypotheses : Bool := true
  split_ne : Bool := false
  preprocessors : Option (List global_branching_preprocessor) := none
  oracle : Option certificate_oracle := none

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- `cfg.update_reducibility reduce_semi` will change the transparency setting of `cfg` to
`semireducible` if `reduce_semi` is true. In this case, it also sets the discharger to `ring!`,
since this is typically needed when using stronger unification.
-/
unsafe def linarith_config.update_reducibility (cfg : linarith_config) (reduce_semi : Bool) : linarith_config :=
  if reduce_semi then { cfg with Transparency := semireducible, discharger := sorry } else cfg

/-!
### Auxiliary functions

These functions are used by multiple modules, so we put them here for accessibility.
-/


open Tactic

/-- `get_rel_sides e` returns the left and right hand sides of `e` if `e` is a comparison,
and fails otherwise.
This function is more naturally in the `option` monad, but it is convenient to put in `tactic`
for compositionality.
 -/
unsafe def get_rel_sides : expr → tactic (expr × expr)
  | quote.1 ((%%ₓa) < %%ₓb) => return (a, b)
  | quote.1 ((%%ₓa) ≤ %%ₓb) => return (a, b)
  | quote.1 ((%%ₓa) = %%ₓb) => return (a, b)
  | quote.1 ((%%ₓa) ≥ %%ₓb) => return (a, b)
  | quote.1 ((%%ₓa) > %%ₓb) => return (a, b)
  | _ => tactic.failed

/-- `parse_into_comp_and_expr e` checks if `e` is of the form `t < 0`, `t ≤ 0`, or `t = 0`.
If it is, it returns the comparison along with `t`.
 -/
unsafe def parse_into_comp_and_expr : expr → Option (ineq × expr)
  | quote.1 ((%%ₓe) < 0) => (Ineq.lt, e)
  | quote.1 ((%%ₓe) ≤ 0) => (Ineq.le, e)
  | quote.1 ((%%ₓe) = 0) => (Ineq.eq, e)
  | _ => none

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- `mk_single_comp_zero_pf c h` assumes that `h` is a proof of `t R 0`.
It produces a pair `(R', h')`, where `h'` is a proof of `c*t R' 0`.
Typically `R` and `R'` will be the same, except when `c = 0`, in which case `R'` is `=`.
If `c = 1`, `h'` is the same as `h` -- specifically, it does *not* change the type to `1*t R 0`.
-/
unsafe def mk_single_comp_zero_pf (c : ℕ) (h : expr) : tactic (ineq × expr) := do
  let tp ← infer_type h
  let some (iq, e) ← return <| parse_into_comp_and_expr tp
  if c = 0 then do
      let e' ← mk_app `` zero_mul [e]
      return (ineq.eq, e')
    else
      if c = 1 then return (iq, h)
      else do
        let tp ← Prod.snd <$> (infer_type h >>= get_rel_sides) >>= infer_type
        let c ← tp c
        let cpos ← to_expr (pquote.1 ((%%ₓc) > 0))
        let (_, ex) ← solve_aux cpos sorry
        let e' ← mk_app iq [h, ex]
        return (iq, e')

end Linarith

