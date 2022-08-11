/-
Copyright (c) 2019 Lucas Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen, Scott Morrison
-/
import Mathbin.Data.Bool.Basic
import Mathbin.Data.Mllist
import Mathbin.Tactic.SolveByElim

/-!
# `suggest` and `library_search`

`suggest` and `library_search` are a pair of tactics for applying lemmas from the library to the
current goal.

* `suggest` prints a list of `exact ...` or `refine ...` statements, which may produce new goals
* `library_search` prints a single `exact ...` which closes the goal, or fails
-/


namespace Tactic

open Native

namespace Suggest

open SolveByElim

/-- Map a name (typically a head symbol) to a "canonical" definitional synonym.
Given a name `n`, we want a name `n'` such that a sufficiently applied
expression with head symbol `n` is always definitionally equal to an expression
with head symbol `n'`.
Thus, we can search through all lemmas with a result type of `n'`
to solve a goal with head symbol `n`.

For example, `>` is mapped to `<` because `a > b` is definitionally equal to `b < a`,
and `not` is mapped to `false` because `¬ a` is definitionally equal to `p → false`
The default is that the original argument is returned, so `<` is just mapped to `<`.

`normalize_synonym` is called for every lemma in the library, so it needs to be fast.
-/
-- TODO this is a hack; if you suspect more cases here would help, please report them
unsafe def normalize_synonym : Name → Name
  | `gt => `has_lt.lt
  | `ge => `has_le.le
  | `monotone => `has_le.le
  | `not => `false
  | n => n

/-- Compute the head symbol of an expression, then normalise synonyms.

This is only used when analysing the goal, so it is okay to do more expensive analysis here.
-/
-- We may want to tweak this further?
unsafe def allowed_head_symbols : expr → List Name
  |-- We first have a various "customisations":
      --   Because in `ℕ` `a.succ ≤ b` is definitionally `a < b`,
      --   we add some special cases to allow looking for `<` lemmas even when the goal has a `≤`.
      --   Note we only do this in the `ℕ` case, for performance.
      quote.1
      (@LE.le ℕ _ (Nat.succ _) _) =>
    [`has_le.le, `has_lt.lt]
  | quote.1 (@Ge ℕ _ _ (Nat.succ _)) => [`has_le.le, `has_lt.lt]
  | quote.1 (@LE.le ℕ _ 1 _) => [`has_le.le, `has_lt.lt]
  | quote.1 (@Ge ℕ _ _ 1) => [`has_le.le, `has_lt.lt]
  |-- These allow `library_search` to search for lemmas of type `¬ a = b` when proving `a ≠ b`
      --   and vice-versa.
      quote.1
      (_ ≠ _) =>
    [`false, `ne]
  | quote.1 ¬_ = _ => [`ne, `false]
  |-- And then the generic cases:
      expr.pi
      _ _ _ t =>
    allowed_head_symbols t
  | expr.app f _ => allowed_head_symbols f
  | expr.const n _ => [normalize_synonym n]
  | _ => [`_]

/-- A declaration can match the head symbol of the current goal in four possible ways:
* `ex`  : an exact match
* `mp`  : the declaration returns an `iff`, and the right hand side matches the goal
* `mpr` : the declaration returns an `iff`, and the left hand side matches the goal
* `both`: the declaration returns an `iff`, and the both sides match the goal
-/
inductive HeadSymbolMatch
  | ex
  | mp
  | mpr
  | both
  deriving DecidableEq, Inhabited

open HeadSymbolMatch

/-- a textual representation of a `head_symbol_match`, for trace debugging. -/
def HeadSymbolMatch.toString : HeadSymbolMatch → Stringₓ
  | ex => "exact"
  | mp => "iff.mp"
  | mpr => "iff.mpr"
  | both => "iff.mp and iff.mpr"

/-- Determine if, and in which way, a given expression matches the specified head symbol. -/
unsafe def match_head_symbol (hs : name_set) : expr → Option HeadSymbolMatch
  | expr.pi _ _ _ t => match_head_symbol t
  | quote.1 ((%%ₓa) ↔ %%ₓb) =>
    if hs.contains `iff then some ex
    else
      match (match_head_symbol a, match_head_symbol b) with
      | (some ex, some ex) => some both
      | (some ex, _) => some mpr
      | (_, some ex) => some mp
      | _ => none
  | expr.app f _ => match_head_symbol f
  | expr.const n _ => if hs.contains (normalize_synonym n) then some ex else none
  | _ => if hs.contains `_ then some ex else none

/-- A package of `declaration` metadata, including the way in which its type matches the head symbol
which we are searching for. -/
unsafe structure decl_data where
  d : declaration
  n : Name
  m : HeadSymbolMatch
  l : ℕ

/-- Generate a `decl_data` from the given declaration if
it matches the head symbol `hs` for the current goal.
-/
-- cached length of name
-- We used to check here for private declarations, or declarations with certain suffixes.
-- It turns out `apply` is so fast, it's better to just try them all.
unsafe def process_declaration (hs : name_set) (d : declaration) : Option decl_data :=
  let n := d.to_name
  if !d.is_trusted || n.is_internal then none else (fun m => ⟨d, n, m, n.length⟩) <$> match_head_symbol hs d.type

/-- Retrieve all library definitions with a given head symbol. -/
unsafe def library_defs (hs : name_set) : tactic (List decl_data) := do
  trace_if_enabled `suggest f! "Looking for lemmas with head symbols {hs}."
  let env ← get_env
  let defs := env.decl_filter_map (process_declaration hs)
  let-- Sort by length; people like short proofs
  defs := defs.qsort fun d₁ d₂ => d₁.l ≤ d₂.l
  trace_if_enabled `suggest f! "Found {defs} relevant lemmas:"
  trace_if_enabled `suggest <| defs fun ⟨d, n, m, l⟩ => (n, m)
  return defs

/-- We unpack any element of a list of `decl_data` corresponding to an `↔` statement that could apply
in both directions into two separate elements.

This ensures that both directions can be independently returned by `suggest`,
and avoids a problem where the application of one direction prevents
the application of the other direction. (See `exp_le_exp` in the tests.)
-/
unsafe def unpack_iff_both : List decl_data → List decl_data
  | [] => []
  | ⟨d, n, both, l⟩ :: L => ⟨d, n, mp, l⟩ :: ⟨d, n, mpr, l⟩ :: unpack_iff_both L
  | ⟨d, n, m, l⟩ :: L => ⟨d, n, m, l⟩ :: unpack_iff_both L

/-- An extension to the option structure for `solve_by_elim`.
* `compulsory_hyps` specifies a list of local hypotheses which must appear in any solution.
  These are useful for constraining the results from `library_search` and `suggest`.
* `try_this` is a flag (default: `tt`) that controls whether a "Try this:"-line should be traced.
-/
unsafe structure suggest_opt extends opt where
  compulsory_hyps : List expr := []
  try_this : Bool := true

/-- Convert a `suggest_opt` structure to a `opt` structure suitable for `solve_by_elim`,
by setting the `accept` parameter to require that all complete solutions
use everything in `compulsory_hyps`.
-/
unsafe def suggest_opt.mk_accept (o : suggest_opt) : opt :=
  { o with
    accept := fun gs =>
      o.accept gs >> (guardₓ <| o.compulsory_hyps.all fun h => gs.any fun g => g.contains_expr_or_mvar h) }

/-- Apply the lemma `e`, then attempt to close all goals using
`solve_by_elim opt`, failing if `close_goals = tt`
and there are any goals remaining.

Returns the number of subgoals which were closed using `solve_by_elim`.
-/
-- Implementation note: as this is used by both `library_search` and `suggest`,
-- we first run `solve_by_elim` separately on the independent goals,
-- whether or not `close_goals` is set,
-- and then run `solve_by_elim { all_goals := tt }`,
-- requiring that it succeeds if `close_goals = tt`.
unsafe def apply_and_solve (close_goals : Bool) (opt : suggest_opt := {  }) (e : expr) : tactic ℕ := do
  trace_if_enabled `suggest f! "Trying to apply lemma: {e}"
  apply e opt
  trace_if_enabled `suggest f! "Applied lemma: {e}"
  let ng ← num_goals
  -- Phase 1
      -- Run `solve_by_elim` on each "safe" goal separately, not worrying about failures.
      -- (We only attempt the "safe" goals in this way in Phase 1.
      -- In Phase 2 we will do backtracking search across all goals,
      -- allowing us to guess solutions that involve data or unify metavariables,
      -- but only as long as we can finish all goals.)
      -- If `compulsory_hyps` is non-empty, we skip this phase and defer to phase 2.
      try
      (guardₓ (opt = []) >> any_goals (independent_goal >> solve_by_elim opt))
  -- Phase 2
        done >>
        return ng <|>
      do
      (-- If there were any goals that we did not attempt solving in the first phase
                -- (because they weren't propositional, or contained a metavariable)
                -- as a second phase we attempt to solve all remaining goals at once
                -- (with backtracking across goals).
                guardₓ
                (opt ≠ []) <|>
              any_goals (success_if_fail independent_goal) >> skip) >>
            solve_by_elim { opt with backtrack_all_goals := tt } <|>-- and fail unless `close_goals = ff`
            guardₓ
            ¬close_goals
      let ng' ← num_goals
      return (ng - ng')

/-- Apply the declaration `d` (or the forward and backward implications separately, if it is an `iff`),
and then attempt to solve the subgoal using `apply_and_solve`.

Returns the number of subgoals successfully closed.
-/
unsafe def apply_declaration (close_goals : Bool) (opt : suggest_opt := {  }) (d : decl_data) : tactic ℕ :=
  let tac := apply_and_solve close_goals opt
  do
  let (e, t) ← decl_mk_const d.d
  match d with
    | ex => tac e
    | mp => do
      let l ← iff_mp_core e t
      tac l
    | mpr => do
      let l ← iff_mpr_core e t
      tac l
    | both => undefined

/-- An `application` records the result of a successful application of a library lemma. -/
-- we use `unpack_iff_both` to ensure this isn't reachable
unsafe structure application where
  State : tactic_state
  script : Stringₓ
  decl : Option declaration
  num_goals : ℕ
  hyps_used : List expr

end Suggest

open SolveByElim

open Suggest

initialize
  registerTraceClass.1 `suggest

-- Trace a list of all relevant lemmas
-- Call `apply_declaration`, then prepare the tactic script and
-- count the number of local hypotheses used.
private unsafe def apply_declaration_script (g : expr) (hyps : List expr) (opt : suggest_opt := {  }) (d : decl_data) :
    tactic application :=
  -- (This tactic block is only executed when we evaluate the mllist,
    -- so we need to do the `focus1` here.)
    retrieve <|
    focus1 <| do
      apply_declaration ff opt d
      let g
        ←-- This `instantiate_mvars` is necessary so that we count used hypotheses correctly.
            instantiate_mvars
            g
      guardₓ <| opt fun h => h g
      let ng ← num_goals
      let s ← read
      let m ← tactic_statement g
      return { State := s, decl := d, script := m, num_goals := ng, hyps_used := hyps fun h => h g }

-- implementation note: we produce a `tactic (mllist tactic application)` first,
-- because it's easier to work in the tactic monad, but in a moment we squash this
-- down to an `mllist tactic application`.
private unsafe def suggest_core' (opt : suggest_opt := {  }) : tactic (mllist tactic application) := do
  let g :: _ ← get_goals
  let hyps ← local_context
  (-- Check if `solve_by_elim` can solve the goal immediately:
        -- This `instantiate_mvars` is necessary so that we count used hypotheses correctly.
        retrieve
        do
        focus1 <| solve_by_elim opt
        let s ← read
        let m ← tactic_statement g
        let g ← instantiate_mvars g
        guardₓ (opt fun h => h g)
        return <|
            mllist.of_list
              [⟨s, m, none, 0, hyps fun h => h g⟩]) <|>-- Otherwise, let's actually try applying library lemmas.
    do
      let t
        ←-- Collect all definitions with the correct head symbol
            infer_type
            g
      let defs ← unpack_iff_both <$> library_defs (name_set.of_list <| allowed_head_symbols t)
      let defs : mllist tactic _ := mllist.of_list defs
      let-- Try applying each lemma against the goal,
      -- recording the tactic script as a string,
      -- the number of remaining goals,
      -- and number of local hypotheses used.
      results := defs (apply_declaration_script g hyps opt)
      let symm_state
        ←-- Now call `symmetry` and try again.
            -- (Because we are using `mllist`, this is essentially free if we've already found a lemma.)
            retrieve <|
            try_core <| symmetry >> read
      let results_symm :=
        match symm_state with
        | some s => defs fun d => retrieve <| set_state s >> apply_declaration_script g hyps opt d
        | none => mllist.nil
      return (results results_symm)

/-- The core `suggest` tactic.
It attempts to apply a declaration from the library,
then solve new goals using `solve_by_elim`.

It returns a list of `application`s consisting of fields:
* `state`, a tactic state resulting from the successful application of a declaration from
  the library,
* `script`, a string of the form `Try this: refine ...` or `Try this: exact ...` which will
  reproduce that tactic state,
* `decl`, an `option declaration` indicating the declaration that was applied
  (or none, if `solve_by_elim` succeeded),
* `num_goals`, the number of remaining goals, and
* `hyps_used`, the number of local hypotheses used in the solution.
-/
unsafe def suggest_core (opt : suggest_opt := {  }) : mllist tactic application :=
  (mllist.monad_lift (suggest_core' opt)).join

/-- See `suggest_core`.

Returns a list of at most `limit` `application`s,
sorted by number of goals, and then (reverse) number of hypotheses used.
-/
unsafe def suggest (limit : Option ℕ := none) (opt : suggest_opt := {  }) : tactic (List application) := do
  let results := suggest_core opt
  let L
    ←-- Get the first n elements of the successful lemmas
        if h : limit.isSome then results.take (Option.getₓ h)
      else results.force
  -- Sort by number of remaining goals, then by number of hypotheses used.
      return <|
      L fun d₁ d₂ => d₁ < d₂ ∨ d₁ = d₂ ∧ d₁ ≥ d₂

/-- Returns a list of at most `limit` strings, of the form `Try this: exact ...` or
`Try this: refine ...`, which make progress on the current goal using a declaration
from the library.
-/
unsafe def suggest_scripts (limit : Option ℕ := none) (opt : suggest_opt := {  }) : tactic (List Stringₓ) := do
  let L ← suggest limit opt
  return <| L application.script

/-- Returns a string of the form `Try this: exact ...`, which closes the current goal.
-/
unsafe def library_search (opt : suggest_opt := {  }) : tactic Stringₓ :=
  (suggest_core opt).mfirst fun a => do
    guardₓ (a = 0)
    write a
    return a

namespace Interactive

setup_tactic_parser

open SolveByElim

initialize
  registerTraceClass.1 `silence_suggest

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `suggest` tries to apply suitable theorems/defs from the library, and generates
a list of `exact ...` or `refine ...` scripts that could be used at this step.
It leaves the tactic state unchanged. It is intended as a complement of the search
function in your editor, the `#find` tactic, and `library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num`
(or less, if all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.
For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that
`suggest` might miss some results if `num` is not large enough. However, because
`suggest` uses monadic lazy lists, smaller values of `num` run faster than larger values.

You can add additional lemmas to be used along with local hypotheses
after the application of a library lemma,
using the same syntax as for `solve_by_elim`, e.g.
```
example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  suggest [add_lt_add], -- Says: `Try this: exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
end
```
You can also use `suggest with attr` to include all lemmas with the attribute `attr`.
-/
-- Turn off `Try this: exact/refine ...` trace messages for `suggest`
unsafe def suggest (n : parse («expr ?» (with_desc "n" small_nat))) (hs : parse simp_arg_list)
    (attr_names : parse with_ident_list) (use : parse <| tk "using" *> many ident_ <|> return [])
    (opt : suggest_opt := {  }) : tactic Unit := do
  let (lemma_thunks, ctx_thunk) ← mk_assumption_set false hs attr_names
  let use ← use.mmap get_local
  let L ←
    tactic.suggest_scripts (n.getOrElse 50)
        { opt with compulsory_hyps := use, lemma_thunks := some lemma_thunks, ctx_thunk }
  if !opt || is_trace_enabled_for `silence_suggest then skip
    else if L = 0 then fail "There are no applicable declarations" else L trace >> skip

/-- `suggest` lists possible usages of the `refine` tactic and leaves the tactic state unchanged.
It is intended as a complement of the search function in your editor, the `#find` tactic, and
`library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num` (or less, if
all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.

`suggest using h₁ h₂` will only show solutions that make use of the local hypotheses `h₁` and `h₂`.

For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that `suggest`
might miss some results if `num` is not large enough. However, because `suggest` uses monadic
lazy lists, smaller values of `num` run faster than larger values.

An example of `suggest` in action,

```lean
example (n : nat) : n < n + 1 :=
begin suggest, sorry end
```

prints the list,

```lean
Try this: exact nat.lt.base n
Try this: exact nat.lt_succ_self n
Try this: refine not_le.mp _
Try this: refine gt_iff_lt.mp _
Try this: refine nat.lt.step _
Try this: refine lt_of_not_ge _
...
```
-/
add_tactic_doc
  { Name := "suggest", category := DocCategory.tactic, declNames := [`tactic.interactive.suggest],
    tags := ["search", "Try this"] }

-- Turn off `Try this: exact ...` trace message for `library_search`
initialize
  registerTraceClass.1 `silence_library_search

/-- `library_search` is a tactic to identify existing lemmas in the library. It tries to close the
current goal by applying a lemma from the library, then discharging any new goals using
`solve_by_elim`.

If it succeeds, it prints a trace message `exact ...` which can replace the invocation
of `library_search`.

Typical usage is:
```lean
example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by library_search -- Try this: exact mul_tsub n m k
```

`library_search using h₁ h₂` will only show solutions
that make use of the local hypotheses `h₁` and `h₂`.

By default `library_search` only unfolds `reducible` definitions
when attempting to match lemmas against the goal.
Previously, it would unfold most definitions, sometimes giving surprising answers, or slow answers.
The old behaviour is still available via `library_search!`.

You can add additional lemmas to be used along with local hypotheses
after the application of a library lemma,
using the same syntax as for `solve_by_elim`, e.g.
```
example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  library_search [add_lt_add], -- Says: `Try this: exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
end
```
You can also use `library_search with attr` to include all lemmas with the attribute `attr`.
-/
unsafe def library_search (semireducible : parse <| optionalₓ (tk "!")) (hs : parse simp_arg_list)
    (attr_names : parse with_ident_list) (use : parse <| tk "using" *> many ident_ <|> return [])
    (opt : suggest_opt := {  }) : tactic Unit := do
  let (lemma_thunks, ctx_thunk) ← mk_assumption_set false hs attr_names
  let use ← use.mmap get_local
  (tactic.library_search
          { opt with compulsory_hyps := use, backtrack_all_goals := tt, lemma_thunks := some lemma_thunks, ctx_thunk,
            md := if semireducible then Tactic.Transparency.semireducible else Tactic.Transparency.reducible } >>=
        if !opt || is_trace_enabled_for `silence_library_search then fun _ => skip else trace) <|>
      fail
        "`library_search` failed.\nIf you aren't sure what to do next, you can also\ntry `library_search!`, `suggest`, or `hint`.\n\nPossible reasons why `library_search` failed:\n* `library_search` will only apply a single lemma from the library,\n  and then try to fill in its hypotheses from local hypotheses.\n* If you haven't already, try stating the theorem you want in its own lemma.\n* Sometimes the library has one version of a lemma\n  but not a very similar version obtained by permuting arguments.\n  Try replacing `a + b` with `b + a`, or `a - b < c` with `a < b + c`,\n  to see if maybe the lemma exists but isn't stated quite the way you would like.\n* Make sure that you have all the side conditions for your theorem to be true.\n  For example you won't find `a - b + b = a` for natural numbers in the library because it's false!\n  Search for `b ≤ a → a - b + b = a` instead.\n* If a definition you made is in the goal,\n  you won't find any theorems about it in the library.\n  Try unfolding the definition using `unfold my_definition`.\n* If all else fails, ask on https://leanprover.zulipchat.com/,\n  and maybe we can improve the library and/or `library_search` for next time."

add_tactic_doc
  { Name := "library_search", category := DocCategory.tactic, declNames := [`tactic.interactive.library_search],
    tags := ["search", "Try this"] }

end Interactive

/-- Invoking the hole command `library_search` ("Use `library_search` to complete the goal") calls
the tactic `library_search` to produce a proof term with the type of the hole.

Running it on

```lean
example : 0 < 1 :=
{!!}
```

produces

```lean
example : 0 < 1 :=
nat.one_pos
```
-/
@[hole_command]
unsafe def library_search_hole_cmd : hole_command where
  Name := "library_search"
  descr := "Use `library_search` to complete the goal."
  action := fun _ => do
    let script ← library_search
    -- Is there a better API for dropping the 'Try this: exact ' prefix on this string?
        return
        [((script "Try this: exact ").getOrElse script, "by library_search")]

add_tactic_doc
  { Name := "library_search", category := DocCategory.hole_cmd, declNames := [`tactic.library_search_hole_cmd],
    tags := ["search", "Try this"] }

end Tactic

