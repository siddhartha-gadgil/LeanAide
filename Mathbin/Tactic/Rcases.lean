/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Leanbin.Data.Dlist
import Mathbin.Tactic.Core
import Mathbin.Tactic.Clear

/-!

# Recursive cases (`rcases`) tactic and related tactics

`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* An alteration pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

The patterns are fairly liberal about the exact shape of the constructors, and will insert
additional alternation branches and tuple arguments if there are not enough arguments provided, and
reuse the tail for further matches if there are too many arguments provided to alternation and
tuple patterns.

This file also contains the `obtain` and `rintro` tactics, which use the same syntax of `rcases`
patterns but with a slightly different use case:

* `rintro` (or `rintros`) is used like `rintro x ⟨y, z⟩` and is the same as `intros` followed by
  `rcases` on the newly introduced arguments.
* `obtain` is the same as `rcases` but with a syntax styled after `have` rather than `cases`.
  `obtain ⟨hx, hy⟩ | hz := foo` is equivalent to `rcases foo with ⟨hx, hy⟩ | hz`. Unlike `rcases`,
  `obtain` also allows one to omit `:= foo`, although a type must be provided in this case,
  as in `obtain ⟨hx, hy⟩ | hz : a ∧ b ∨ c`, in which case it produces a subgoal for proving
  `a ∧ b ∨ c` in addition to the subgoals `hx : a, hy : b |- goal` and `hz : c |- goal`.

## Tags

rcases, rintro, obtain, destructuring, cases, pattern matching, match
-/


open Lean Lean.Parser

namespace Tactic

/-!
These synonyms for `list` are used to clarify the meanings of the many
usages of lists in this module.

- `listΣ` is used where a list represents a disjunction, such as the
  list of possible constructors of an inductive type.

- `listΠ` is used where a list represents a conjunction, such as the
  list of arguments of an individual constructor.

These are merely type synonyms, and so are not checked for consistency
by the compiler.

The `def`/`local notation` combination makes Lean retain these
annotations in reported types.
-/


/-- A list, with a disjunctive meaning (like a list of inductive constructors, or subgoals) -/
@[reducible]
def ListSigma :=
  List

/-- A list, with a conjunctive meaning (like a list of constructor arguments, or hypotheses) -/
@[reducible]
def ListPi :=
  List

-- mathport name: «exprlistΣ»
local notation "listΣ" => ListSigma

-- mathport name: «exprlistΠ»
local notation "listΠ" => ListPi

/-- A metavariable representing a subgoal, together with a list of local constants to clear. -/
@[reducible]
unsafe def uncleared_goal :=
  List expr × expr

/-- An `rcases` pattern can be one of the following, in a nested combination:

* A name like `foo`
* The special keyword `rfl` (for pattern matching on equality using `subst`)
* A hyphen `-`, which clears the active hypothesis and any dependents.
* A type ascription like `pat : ty` (parentheses are optional)
* A tuple constructor like `⟨p1, p2, p3⟩`
* An alternation / variant pattern `p1 | p2 | p3`

Parentheses can be used for grouping; alternation is higher precedence than type ascription, so
`p1 | p2 | p3 : ty` means `(p1 | p2 | p3) : ty`.

N-ary alternations are treated as a group, so `p1 | p2 | p3` is not the same as `p1 | (p2 | p3)`,
and similarly for tuples. However, note that an n-ary alternation or tuple can match an n-ary
conjunction or disjunction, because if the number of patterns exceeds the number of constructors in
the type being destructed, the extra patterns will match on the last element, meaning that
`p1 | p2 | p3` will act like `p1 | (p2 | p3)` when matching `a1 ∨ a2 ∨ a3`. If matching against a
type with 3 constructors,  `p1 | (p2 | p3)` will act like `p1 | (p2 | p3) | _` instead.
-/
unsafe inductive rcases_patt : Type
  | one : Name → rcases_patt
  | clear : rcases_patt
  | typed : rcases_patt → pexpr → rcases_patt
  | tuple : listΠ rcases_patt → rcases_patt
  | alts : listΣ rcases_patt → rcases_patt

namespace RcasesPatt

unsafe instance inhabited : Inhabited rcases_patt :=
  ⟨one `_⟩

/-- Get the name from a pattern, if provided -/
unsafe def name : rcases_patt → Option Name
  | one `_ => none
  | one `rfl => none
  | one n => some n
  | typed p _ => p.Name
  | alts [p] => p.Name
  | _ => none

/-- Interpret an rcases pattern as a tuple, where `p` becomes `⟨p⟩`
if `p` is not already a tuple. -/
unsafe def as_tuple : rcases_patt → listΠ rcases_patt
  | tuple ps => ps
  | p => [p]

/-- Interpret an rcases pattern as an alternation, where non-alternations are treated as one
alternative. -/
unsafe def as_alts : rcases_patt → listΣ rcases_patt
  | alts ps => ps
  | p => [p]

/-- Convert a list of patterns to a tuple pattern, but mapping `[p]` to `p` instead of `⟨p⟩`. -/
unsafe def tuple' : listΠ rcases_patt → rcases_patt
  | [p] => p
  | ps => tuple ps

/-- Convert a list of patterns to an alternation pattern, but mapping `[p]` to `p` instead of
a unary alternation `|p`. -/
unsafe def alts' : listΣ rcases_patt → rcases_patt
  | [p] => p
  | ps => alts ps

/-- This function is used for producing rcases patterns based on a case tree. Suppose that we have
a list of patterns `ps` that will match correctly against the branches of the case tree for one
constructor. This function will merge tuples at the end of the list, so that `[a, b, ⟨c, d⟩]`
becomes `⟨a, b, c, d⟩` instead of `⟨a, b, ⟨c, d⟩⟩`.

We must be careful to turn `[a, ⟨⟩]` into `⟨a, ⟨⟩⟩` instead of `⟨a⟩` (which will not perform the
nested match). -/
unsafe def tuple₁_core : listΠ rcases_patt → listΠ rcases_patt
  | [] => []
  | [tuple []] => [tuple []]
  | [tuple ps] => ps
  | p :: ps => p :: tuple₁_core ps

/-- This function is used for producing rcases patterns based on a case tree. This is like
`tuple₁_core` but it produces a pattern instead of a tuple pattern list, converting `[n]` to `n`
instead of `⟨n⟩` and `[]` to `_`, and otherwise just converting `[a, b, c]` to `⟨a, b, c⟩`. -/
unsafe def tuple₁ : listΠ rcases_patt → rcases_patt
  | [] => default
  | [one n] => one n
  | ps => tuple (tuple₁_core ps)

/-- This function is used for producing rcases patterns based on a case tree. Here we are given
the list of patterns to apply to each argument of each constructor after the main case, and must
produce a list of alternatives with the same effect. This function calls `tuple₁` to make the
individual alternatives, and handles merging `[a, b, c | d]` to `a | b | c | d` instead of
`a | b | (c | d)`. -/
unsafe def alts₁_core : listΣ (listΠ rcases_patt) → listΣ rcases_patt
  | [] => []
  | [[alts ps]] => ps
  | p :: ps => tuple₁ p :: alts₁_core ps

/-- This function is used for producing rcases patterns based on a case tree. This is like
`alts₁_core`, but it produces a cases pattern directly instead of a list of alternatives. We
specially translate the empty alternation to `⟨⟩`, and translate `|(a | b)` to `⟨a | b⟩` (because we
don't have any syntax for unary alternation). Otherwise we can use the regular merging of
alternations at the last argument so that `a | b | (c | d)` becomes `a | b | c | d`. -/
unsafe def alts₁ : listΣ (listΠ rcases_patt) → rcases_patt
  | [[]] => tuple []
  | [[alts ps]] => tuple [alts ps]
  | ps => alts' (alts₁_core ps)

unsafe instance has_reflect : has_reflect rcases_patt
  | one n => quote.1 _
  | clear => quote.1 _
  | typed l e => ((quote.1 typed).subst (has_reflect l)).subst (reflect e)
  | tuple l =>
    (quote.1 fun l => tuple l).subst <|
      have := has_reflect
      list.reflect l
  | alts l =>
    (quote.1 fun l => alts l).subst <|
      have := has_reflect
      list.reflect l

/-- Formats an `rcases` pattern. If the `bracket` argument is true, then it will be
printed at high precedence, i.e. it will have parentheses around it if it is not already a tuple
or atomic name. -/
protected unsafe def format : ∀ bracket : Bool, rcases_patt → tactic _root_.format
  | _, one n => pure <| to_fmt n
  | _, clear => pure "-"
  | _, tuple [] => pure "⟨⟩"
  | _, tuple ls => do
    let fs ← ls.mmap <| format false
    pure <|
        "⟨" ++
            _root_.format.group
              (_root_.format.nest 1 <| _root_.format.join <| List.intersperse ("," ++ _root_.format.line) fs) ++
          "⟩"
  | br, alts ls => do
    let fs ← ls.mmap <| format true
    let fmt := _root_.format.join <| List.intersperse (↑" |" ++ _root_.format.space) fs
    pure <| if br then _root_.format.bracket "(" ")" fmt else fmt
  | br, typed p e => do
    let fp ← format false p
    let fe ← pp e
    let fmt := fp ++ " : " ++ fe
    pure <| if br then _root_.format.bracket "(" ")" fmt else fmt

unsafe instance has_to_tactic_format : has_to_tactic_format rcases_patt :=
  ⟨rcases_patt.format false⟩

end RcasesPatt

/-- Takes the number of fields of a single constructor and patterns to match its fields against
(not necessarily the same number). The returned lists each contain one element per field of the
constructor. The `name` is the name which will be used in the top-level `cases` tactic, and the
`rcases_patt` is the pattern which the field will be matched against by subsequent `cases`
tactics. -/
unsafe def rcases.process_constructor : Nat → listΠ rcases_patt → listΠ Name × listΠ rcases_patt
  | 0, ps => ([], [])
  | 1, [] => ([`_], [default])
  | 1, [p] => ([p.Name.getOrElse `_], [p])
  |-- The interesting case: we matched the last field against multiple
    -- patterns, so split off the remaining patterns into a subsequent
    -- match. This handles matching `α × β × γ` against `⟨a, b, c⟩`.
    1,
    ps => ([`_], [rcases_patt.tuple ps])
  | n + 1, ps =>
    let hd := ps.head
    let (ns, tl) := rcases.process_constructor n ps.tail
    (hd.Name.getOrElse `_ :: ns, hd :: tl)

/-- Takes a list of constructor names, and an (alternation) list of patterns, and matches each
pattern against its constructor. It returns the list of names that will be passed to `cases`,
and the list of `(constructor name, patterns)` for each constructor, where `patterns` is the
(conjunctive) list of patterns to apply to each constructor argument. -/
unsafe def rcases.process_constructors (params : Nat) :
    listΣ Name → listΣ rcases_patt → tactic (Dlist Name × listΣ (Name × listΠ rcases_patt))
  | [], ps => pure (Dlist.empty, [])
  | c :: cs, ps => do
    let n ← mk_const c >>= get_arity
    let (h, t) :=
      (match cs, ps.tail with
      |-- We matched the last constructor against multiple patterns,
        -- so split off the remaining constructors. This handles matching
        -- `α ⊕ β ⊕ γ` against `a|b|c`.
        [],
        _ :: _ => ([rcases_patt.alts ps], [])
      | _, _ => (ps.head.as_tuple, ps.tail) :
        _)
    let (ns, ps) := rcases.process_constructor (n - params) h
    let (l, r) ← rcases.process_constructors cs t
    pure (Dlist.ofList ns ++ l, (c, ps) :: r)

/-- Like `zip`, but only elements satisfying a matching predicate `p` will go in the list,
and elements of the first list that fail to match the second list will be skipped. -/
private def align {α β} (p : α → β → Prop) [∀ a b, Decidable (p a b)] : List α → List β → List (α × β)
  | a :: as, b :: bs => if p a b then (a, b) :: align as bs else align as (b :: bs)
  | _, _ => []

/-- Given a local constant `e`, get its type. *But* if `e` does not exist, go find a hypothesis
with the same pretty name as `e` and get it instead. This is needed because we can sometimes lose
track of the unique names of hypotheses when they are revert/intro'd by `change` and `cases`. (A
better solution would be for these tactics to return a map of renamed hypotheses so that we don't
lose track of them.) -/
private unsafe def get_local_and_type (e : expr) : tactic (expr × expr) :=
  (do
      let t ← infer_type e
      pure (t, e)) <|>
    do
    let e ← get_local e.local_pp_name
    let t ← infer_type e
    pure (t, e)

mutual
  /-- * `rcases_core p e` will match a pattern `p` against a local hypothesis `e`.
    It returns the list of subgoals that were produced.
  * `rcases.continue pes` will match a (conjunctive) list of `(p, e)` pairs which refer to
    patterns and local hypotheses to match against, and applies all of them. Note that this can
    involve matching later arguments multiple times given earlier arguments, for example
    `⟨a | b, ⟨c, d⟩⟩` performs the `⟨c, d⟩` match twice, once on the `a` branch and once on `b`.
  -/
  unsafe def rcases_core : rcases_patt → expr → tactic (List uncleared_goal)
    | rcases_patt.one `rfl, e => do
      let (t, e) ← get_local_and_type e
      subst' e
      List.map (Prod.mk []) <$> get_goals
    |-- If the pattern is any other name, we already bound the name in the
        -- top-level `cases` tactic, so there is no more work to do for it.
        rcases_patt.one
        _,
      _ => List.map (Prod.mk []) <$> get_goals
    | rcases_patt.clear, e => do
      let m ← try_core (get_local_and_type e)
      List.map (Prod.mk <| m [] fun ⟨_, e⟩ => [e]) <$> get_goals
    | rcases_patt.typed p ty, e => do
      let (t, e) ← get_local_and_type e
      let ty ← i_to_expr_no_subgoals (pquote.1 (%%ₓty : Sort _))
      unify t ty
      let t ← instantiate_mvars t
      let ty ← instantiate_mvars ty
      let e ← if expr.alpha_eqv t ty then pure e else change_core ty (some e) >> get_local e.local_pp_name
      rcases_core p e
    | rcases_patt.alts [p], e => rcases_core p e
    | pat, e => do
      let (t, e) ← get_local_and_type e
      let t ← whnf t
      let env ← get_env
      let I := t.get_app_fn.const_name
      let pat := pat.as_alts
      let (ids, r, l) ←
        if I ≠ `quot then do
            when ¬env I <| fail f! "rcases tactic failed: {e } : {I} is not an inductive datatype"
            let params := env.inductive_num_params I
            let c := env.constructors_of I
            let (ids, r) ← rcases.process_constructors params c pat
            let l ← cases_core e ids.toList
            pure (ids, r, l)
          else do
            let (ids, r) ← rcases.process_constructors 2 [`quot.mk] pat
            let [(_, d)] ← induction e ids.toList `quot.induction_on |
              fail f! "quotient induction on {e} failed. Maybe goal is not in Prop?"
            -- the result from `induction` is missing the information that the original constructor was
                -- `quot.mk` so we fix this up:
                pure
                (ids, r, [(`quot.mk, d)])
      let gs ← get_goals
      let-- `cases_core` may not generate a new goal for every constructor,
      -- as some constructors may be impossible for type reasons. (See its
      -- documentation.) Match up the new goals with our remaining work
      -- by constructor name.
      ls := align (fun (a : Name × _) (b : _ × Name × _) => a.1 = b.2.1) r (gs.zip l)
      List.join <$> ls fun ⟨⟨_, ps⟩, g, _, hs, _⟩ => set_goals [g] >> rcases.continue (ps hs)
  /-- * `rcases_core p e` will match a pattern `p` against a local hypothesis `e`.
    It returns the list of subgoals that were produced.
  * `rcases.continue pes` will match a (conjunctive) list of `(p, e)` pairs which refer to
    patterns and local hypotheses to match against, and applies all of them. Note that this can
    involve matching later arguments multiple times given earlier arguments, for example
    `⟨a | b, ⟨c, d⟩⟩` performs the `⟨c, d⟩` match twice, once on the `a` branch and once on `b`.
  -/
  unsafe def rcases.continue : listΠ (rcases_patt × expr) → tactic (List uncleared_goal)
    | [] => List.map (Prod.mk []) <$> get_goals
    | (pat, e) :: pes => do
      let gs ← rcases_core pat e
      List.join <$>
          gs fun ⟨cs, g⟩ => do
            set_goals [g]
            let ugs ← rcases.continue pes
            pure <| ugs fun ⟨cs', gs⟩ => (cs ++ cs', gs)
end

/-- Given a list of `uncleared_goal`s, each of which is a goal metavariable and
a list of variables to clear, actually perform the clear and set the goals with the result. -/
unsafe def clear_goals (ugs : List uncleared_goal) : tactic Unit := do
  let gs ←
    ugs.mmap fun ⟨cs, g⟩ => do
        set_goals [g]
        let cs ←
          cs.mfoldr
              (fun c cs =>
                (do
                    let (_, c) ← get_local_and_type c
                    pure (c :: cs)) <|>
                  pure cs)
              []
        clear' tt cs
        let [g] ← get_goals
        pure g
  set_goals gs

/-- `rcases h e pat` performs case distinction on `e` using `pat` to
name the arising new variables and assumptions. If `h` is `some` name,
a new assumption `h : e = pat` will relate the expression `e` with the
current pattern. See the module comment for the syntax of `pat`. -/
unsafe def rcases (h : Option Name) (p : pexpr) (pat : rcases_patt) : tactic Unit := do
  let p :=
    match pat with
    | rcases_patt.typed _ ty => pquote.1 (%%ₓp : %%ₓty)
    | _ => p
  let e ←
    match h with
      | some h => do
        let x ← get_unused_name <| pat.Name.getOrElse `this
        interactive.generalize h () (p, x)
        get_local x
      | none => i_to_expr p
  if e then focus1 (rcases_core pat e >>= clear_goals)
    else do
      let x ← pat mk_fresh_name pure
      let n ← revert_kdependencies e semireducible
      tactic.generalize e x <|> do
          let t ← infer_type e
          tactic.assertv x t e
          get_local x >>= tactic.revert
          pure ()
      let h ← tactic.intro1
      focus1 (rcases_core pat h >>= clear_goals)

/-- `rcases_many es pats` performs case distinction on the `es` using `pat` to
name the arising new variables and assumptions.
See the module comment for the syntax of `pat`. -/
unsafe def rcases_many (ps : listΠ pexpr) (pat : rcases_patt) : tactic Unit := do
  let (_, pats) := rcases.process_constructor ps.length pat.as_tuple
  let pes ←
    (ps.zip pats).mmap fun ⟨p, pat⟩ => do
        let p :=
          match pat with
          | rcases_patt.typed _ ty => pquote.1 (%%ₓp : %%ₓty)
          | _ => p
        let e ← i_to_expr p
        if e then pure (pat, e)
          else do
            let x ← pat mk_fresh_name pure
            let n ← revert_kdependencies e semireducible
            tactic.generalize e x <|> do
                let t ← infer_type e
                tactic.assertv x t e
                get_local x >>= tactic.revert
                pure ()
            Prod.mk pat <$> tactic.intro1
  focus1 (rcases.continue pes >>= clear_goals)

/-- `rintro pat₁ pat₂ ... patₙ` introduces `n` arguments, then pattern matches on the `patᵢ` using
the same syntax as `rcases`. -/
unsafe def rintro (ids : listΠ rcases_patt) : tactic Unit := do
  let l ←
    ids.mmap fun id => do
        let e ← intro <| id.Name.getOrElse `_
        pure (id, e)
  focus1 (rcases.continue l >>= clear_goals)

/-- Like `zip_with`, but if the lists don't match in length, the excess elements will be put at the
end of the result. -/
def mergeList {α} (m : α → α → α) : List α → List α → List α
  | [], l₂ => l₂
  | l₁, [] => l₁
  | a :: l₁, b :: l₂ => m a b :: merge_list l₁ l₂

/-- Merge two `rcases` patterns. This is used to underapproximate a case tree by an `rcases`
pattern. The two patterns come from cases in two branches, that due to the syntax of `rcases`
patterns are forced to overlap. The rule here is that we take only the case splits that are in
common between both branches. For example if one branch does `⟨a, b⟩` and the other does `c`,
then we return `c` because we don't know that a case on `c` would be safe to do. -/
unsafe def rcases_patt.merge : rcases_patt → rcases_patt → rcases_patt
  | rcases_patt.alts p₁, p₂ => rcases_patt.alts (mergeList rcases_patt.merge p₁ p₂.as_alts)
  | p₁, rcases_patt.alts p₂ => rcases_patt.alts (mergeList rcases_patt.merge p₁.as_alts p₂)
  | rcases_patt.tuple p₁, p₂ => rcases_patt.tuple (mergeList rcases_patt.merge p₁ p₂.as_tuple)
  | p₁, rcases_patt.tuple p₂ => rcases_patt.tuple (mergeList rcases_patt.merge p₁.as_tuple p₂)
  | rcases_patt.typed p₁ e, p₂ => rcases_patt.typed (p₁.merge p₂) e
  | p₁, rcases_patt.typed p₂ e => rcases_patt.typed (p₁.merge p₂) e
  | rcases_patt.one `rfl, rcases_patt.one `rfl => rcases_patt.one `rfl
  | rcases_patt.one `_, p => p
  | p, rcases_patt.one `_ => p
  | rcases_patt.clear, p => p
  | p, rcases_patt.clear => p
  | rcases_patt.one n, _ => rcases_patt.one n

mutual
  /-- * `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output
    instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth
    `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform
    the same thing as the case tree we just constructed (or at least, the nearest expressible
    approximation to this.)
  * `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a
    matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for
    alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by
    `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`
    patterns describing the result, and the list of generated subgoals.
  * `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the
    patterns `ps` are an output instead of an input, created by matching on everything to depth
    `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.
  -/
  unsafe def rcases_hint_core : ℕ → expr → tactic (rcases_patt × List expr)
    | depth, e => do
      let (t, e) ← get_local_and_type e
      let t ← whnf t
      let env ← get_env
      let I := t.get_app_fn.const_name
      (do
            guardₓ (I = `` Eq)
            subst' e
            Prod.mk (rcases_patt.one `rfl) <$> get_goals) <|>
          do
          let c := env I
          let some l ← try_core (guardₓ (depth ≠ 0) >> cases_core e) |
            let n :=
                match e with
                | Name.anonymous => `_
                | n => n
              Prod.mk (rcases_patt.one n) <$> get_goals
          let gs ← get_goals
          if gs then pure (rcases_patt.tuple [], [])
            else do
              let (ps, gs') ← rcases_hint.process_constructors (depth - 1) c (gs l)
              pure (rcases_patt.alts₁ ps, gs')
  /-- * `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output
    instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth
    `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform
    the same thing as the case tree we just constructed (or at least, the nearest expressible
    approximation to this.)
  * `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a
    matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for
    alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by
    `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`
    patterns describing the result, and the list of generated subgoals.
  * `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the
    patterns `ps` are an output instead of an input, created by matching on everything to depth
    `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.
  -/
  unsafe def rcases_hint.process_constructors :
      ℕ →
        listΣ Name →
          List (expr × Name × listΠ expr × List (Name × expr)) → tactic (listΣ (listΠ rcases_patt) × List expr)
    | depth, [], _ => pure ([], [])
    | depth, cs, [] => pure (cs.map fun _ => [], [])
    | depth, c :: cs, ls@((g, c', hs, _) :: l) =>
      if c ≠ c' then do
        let (ps, gs) ← rcases_hint.process_constructors depth cs ls
        pure ([] :: ps, gs)
      else do
        let (p, gs) ← set_goals [g] >> rcases_hint.continue depth hs
        let (ps, gs') ← rcases_hint.process_constructors depth cs l
        pure (p :: ps, gs ++ gs')
  /-- * `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output
    instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth
    `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform
    the same thing as the case tree we just constructed (or at least, the nearest expressible
    approximation to this.)
  * `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a
    matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for
    alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by
    `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`
    patterns describing the result, and the list of generated subgoals.
  * `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the
    patterns `ps` are an output instead of an input, created by matching on everything to depth
    `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.
  -/
  unsafe def rcases_hint.continue : ℕ → listΠ expr → tactic (listΠ rcases_patt × List expr)
    | depth, [] => Prod.mk [] <$> get_goals
    | depth, e :: es => do
      let (p, gs) ← rcases_hint_core depth e
      let (ps, gs') ←
        gs.mfoldl
            (fun (r : listΠ rcases_patt × List expr) g => do
              let (ps, gs') ← set_goals [g] >> rcases_hint.continue depth es
              pure (merge_list rcases_patt.merge r.1 ps, r.2 ++ gs'))
            ([], [])
      pure (p :: ps, gs')
end

/-- * `rcases? e` is like `rcases e with ...`, except it generates `...` by matching on everything it
can, and it outputs an `rcases` invocation that should have the same effect.
* `rcases? e : n` can be used to control the depth of case splits (especially important for
recursive types like `nat`, which can be cased as many times as you like). -/
unsafe def rcases_hint (p : pexpr) (depth : Nat) : tactic rcases_patt := do
  let e ← i_to_expr p
  if e then
      focus1 <| do
        let (p, gs) ← rcases_hint_core depth e
        set_goals gs
        pure p
    else do
      let x ← mk_fresh_name
      let n ← revert_kdependencies e semireducible
      tactic.generalize e x <|> do
          let t ← infer_type e
          tactic.assertv x t e
          get_local x >>= tactic.revert
          pure ()
      let h ← tactic.intro1
      focus1 <| do
          let (p, gs) ← rcases_hint_core depth h
          set_goals gs
          pure p

/-- * `rcases? ⟨e1, e2, e3⟩` is like `rcases ⟨e1, e2, e3⟩ with ...`, except it
  generates `...` by matching on everything it can, and it outputs an `rcases`
  invocation that should have the same effect.
* `rcases? ⟨e1, e2, e3⟩ : n` can be used to control the depth of case splits
  (especially important for recursive types like `nat`, which can be cased as many
  times as you like). -/
unsafe def rcases_hint_many (ps : List pexpr) (depth : Nat) : tactic (listΠ rcases_patt) := do
  let es ←
    ps.mmap fun p => do
        let e ← i_to_expr p
        if e then pure e
          else do
            let x ← mk_fresh_name
            let n ← revert_kdependencies e semireducible
            tactic.generalize e x <|> do
                let t ← infer_type e
                tactic.assertv x t e
                get_local x >>= tactic.revert
                pure ()
            tactic.intro1
  focus1 <| do
      let (ps, gs) ← rcases_hint.continue depth es
      set_goals gs
      pure ps

/-- * `rintro?` is like `rintro ...`, except it generates `...` by introducing and matching on
everything it can, and it outputs an `rintro` invocation that should have the same effect.
* `rintro? : n` can be used to control the depth of case splits (especially important for
recursive types like `nat`, which can be cased as many times as you like). -/
unsafe def rintro_hint (depth : Nat) : tactic (listΠ rcases_patt) := do
  let l ← intros
  focus1 <| do
      let (p, gs) ← rcases_hint.continue depth l
      set_goals gs
      pure p

setup_tactic_parser

mutual
  /-- * `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.
    This means only tuples and identifiers are allowed; alternations and type ascriptions
    require `(...)` instead, which switches to `patt`.
  * `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a
    `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
    expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
    example in `rcases e with x : ty <|> skip`.
  * `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
    patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
    `(a | b) : ty` where `a | b` is the `patt_med` part.
  * `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.
  
  ```lean
  patt ::= patt_med (":" expr)?
  patt_med ::= (patt_hi "|")* patt_hi
  patt_hi ::= id | "rfl" | "_" | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
  ```
  -/
  unsafe def rcases_patt_parse_hi' : parser rcases_patt
    | x =>
      (brackets "(" ")" rcases_patt_parse' <|>
          rcases_patt.tuple <$> brackets "⟨" "⟩" (sep_by (tk ",") rcases_patt_parse') <|>
            tk "-" $> rcases_patt.clear <|> rcases_patt.one <$> ident_)
        x
  /-- * `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.
    This means only tuples and identifiers are allowed; alternations and type ascriptions
    require `(...)` instead, which switches to `patt`.
  * `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a
    `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
    expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
    example in `rcases e with x : ty <|> skip`.
  * `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
    patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
    `(a | b) : ty` where `a | b` is the `patt_med` part.
  * `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.
  
  ```lean
  patt ::= patt_med (":" expr)?
  patt_med ::= (patt_hi "|")* patt_hi
  patt_hi ::= id | "rfl" | "_" | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
  ```
  -/
  unsafe def rcases_patt_parse' : parser rcases_patt
    | x =>
      (do
          let pat ← rcases_patt.alts' <$> rcases_patt_parse_list'
          tk ":" *> pat <$> texpr <|> pure pat)
        x
  /-- * `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.
    This means only tuples and identifiers are allowed; alternations and type ascriptions
    require `(...)` instead, which switches to `patt`.
  * `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a
    `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
    expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
    example in `rcases e with x : ty <|> skip`.
  * `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
    patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
    `(a | b) : ty` where `a | b` is the `patt_med` part.
  * `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.
  
  ```lean
  patt ::= patt_med (":" expr)?
  patt_med ::= (patt_hi "|")* patt_hi
  patt_hi ::= id | "rfl" | "_" | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
  ```
  -/
  unsafe def rcases_patt_parse_list' : parser (listΣ rcases_patt)
    | x => (rcases_patt_parse_hi' >>= rcases_patt_parse_list_rest) x
  /-- * `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.
    This means only tuples and identifiers are allowed; alternations and type ascriptions
    require `(...)` instead, which switches to `patt`.
  * `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a
    `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
    expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
    example in `rcases e with x : ty <|> skip`.
  * `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
    patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
    `(a | b) : ty` where `a | b` is the `patt_med` part.
  * `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.
  
  ```lean
  patt ::= patt_med (":" expr)?
  patt_med ::= (patt_hi "|")* patt_hi
  patt_hi ::= id | "rfl" | "_" | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
  ```
  -/
  unsafe def rcases_patt_parse_list_rest : rcases_patt → parser (listΣ rcases_patt)
    | pat =>
      tk "|" *> List.cons pat <$> rcases_patt_parse_list' <|>-- hack to support `-|-` patterns, because `|-` is a token
              tk
              "|-" *>
            List.cons pat <$> rcases_patt_parse_list_rest rcases_patt.clear <|>
          pure [pat]
end

/-- `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.
This means only tuples and identifiers are allowed; alternations and type ascriptions
require `(...)` instead, which switches to `patt`.
```lean
patt_hi ::= id | "rfl" | "_" | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
```
-/
unsafe def rcases_patt_parse_hi :=
  with_desc "patt_hi" rcases_patt_parse_hi'

/-- `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a
`patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
example in `rcases e with x : ty <|> skip`.
```lean
patt ::= patt_med (":" expr)?
```
-/
unsafe def rcases_patt_parse :=
  with_desc "patt" rcases_patt_parse'

/-- `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
`(a | b) : ty` where `a | b` is the `patt_med` part.
```lean
patt_med ::= (patt_hi "|")* patt_hi
```
-/
unsafe def rcases_patt_parse_list :=
  with_desc "patt_med" rcases_patt_parse_list'

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- Parse the optional depth argument `(: n)?` of `rcases?` and `rintro?`, with default depth 5. -/
unsafe def rcases_parse_depth : parser Nat := do
  let o ← «expr ?» (tk ":" *> small_nat)
  pure <| o 5

/-- The arguments to `rcases`, which in fact dispatch to several other tactics.
* `rcases? expr (: n)?` or `rcases? ⟨expr, ...⟩ (: n)?` calls `rcases_hint`
* `rcases? ⟨expr, ...⟩ (: n)?` calls `rcases_hint_many`
* `rcases (h :)? expr (with patt)?` calls `rcases`
* `rcases ⟨expr, ...⟩ (with patt)?` calls `rcases_many`
-/
unsafe inductive rcases_args
  | hint (tgt : Sum pexpr (List pexpr)) (depth : Nat)
  | rcases (name : Option Name) (tgt : pexpr) (pat : rcases_patt)
  | rcases_many (tgt : listΠ pexpr) (pat : rcases_patt)
  deriving has_reflect

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- Syntax for a `rcases` pattern:
* `rcases? expr (: n)?`
* `rcases (h :)? expr (with patt_list (: expr)?)?`. -/
unsafe def rcases_parse : parser rcases_args :=
  with_desc "('?' expr (: n)?) | ((h :)? expr (with patt)?)" <| do
    let hint ← «expr ?» (tk "?")
    let p ← Sum.inr <$> brackets "⟨" "⟩" (sep_by (tk ",") (parser.pexpr 0)) <|> Sum.inl <$> texpr
    match hint with
      | none => do
        let p ←
          (do
                let Sum.inl (expr.local_const h _ _ _) ← pure p
                tk ":" *> (@Sum.inl _ (Sum pexpr (List pexpr)) ∘ Prod.mk h) <$> texpr) <|>
              pure (Sum.inr p)
        let ids ← «expr ?» (tk "with" *> rcases_patt_parse)
        let ids := ids (rcases_patt.tuple [])
        pure <|
            match p with
            | Sum.inl (Name, tgt) => rcases_args.rcases (some Name) tgt ids
            | Sum.inr (Sum.inl tgt) => rcases_args.rcases none tgt ids
            | Sum.inr (Sum.inr tgts) => rcases_args.rcases_many tgts ids
      | some _ => do
        let depth ← rcases_parse_depth
        pure <| rcases_args.hint p depth

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr *»
mutual
  /-- `rintro_patt_parse_hi` and `rintro_patt_parse` are like `rcases_patt_parse`, but is used for
  parsing top level `rintro` patterns, which allow sequences like `(x y : t)` in addition to simple
  `rcases` patterns.
  
  * `rintro_patt_parse_hi` will parse a high precedence `rcases` pattern, `rintro_patt_hi` below.
    This means only tuples and identifiers are allowed; alternations and type ascriptions
    require `(...)` instead, which switches to `patt`.
  * `rintro_patt_parse` will parse a low precedence `rcases` pattern, `rintro_patt` below.
    This consists of either a sequence of patterns `p1 p2 p3` or an alternation list `p1 | p2 | p3`
    treated as a single pattern, optionally followed by a `: ty` type ascription, which applies to
    every pattern in the list.
  * `rintro_patt_parse_low` parses `rintro_patt_low`, which is the same as `rintro_patt_parse tt` but
    it does not permit an unparenthesized alternation list, it must have the form `p1 p2 p3 (: ty)?`.
  
  ```lean
  rintro_patt ::= (rintro_patt_hi+ | patt_med) (":" expr)?
  rintro_patt_low ::= rintro_patt_hi* (":" expr)?
  rintro_patt_hi ::= patt_hi | "(" rintro_patt ")"
  ```
  -/
  unsafe def rintro_patt_parse_hi' : parser (listΠ rcases_patt)
    | x =>
      (brackets "(" ")" (rintro_patt_parse' true) <|> do
          let p ← rcases_patt_parse_hi
          pure [p])
        x
  /-- `rintro_patt_parse_hi` and `rintro_patt_parse` are like `rcases_patt_parse`, but is used for
  parsing top level `rintro` patterns, which allow sequences like `(x y : t)` in addition to simple
  `rcases` patterns.
  
  * `rintro_patt_parse_hi` will parse a high precedence `rcases` pattern, `rintro_patt_hi` below.
    This means only tuples and identifiers are allowed; alternations and type ascriptions
    require `(...)` instead, which switches to `patt`.
  * `rintro_patt_parse` will parse a low precedence `rcases` pattern, `rintro_patt` below.
    This consists of either a sequence of patterns `p1 p2 p3` or an alternation list `p1 | p2 | p3`
    treated as a single pattern, optionally followed by a `: ty` type ascription, which applies to
    every pattern in the list.
  * `rintro_patt_parse_low` parses `rintro_patt_low`, which is the same as `rintro_patt_parse tt` but
    it does not permit an unparenthesized alternation list, it must have the form `p1 p2 p3 (: ty)?`.
  
  ```lean
  rintro_patt ::= (rintro_patt_hi+ | patt_med) (":" expr)?
  rintro_patt_low ::= rintro_patt_hi* (":" expr)?
  rintro_patt_hi ::= patt_hi | "(" rintro_patt ")"
  ```
  -/
  unsafe def rintro_patt_parse' : Bool → parser (listΠ rcases_patt)
    | med => do
      let ll ← «expr *» rintro_patt_parse_hi'
      let pats ←
        match med, ll.join with
          | tt, [] => failure
          | tt, [pat] => do
            let l ← rcases_patt_parse_list_rest pat
            pure [rcases_patt.alts' l]
          | _, pats => pure pats
      (do
            tk ":"
            let e ← texpr
            pure (pats fun p => rcases_patt.typed p e)) <|>
          pure pats
end

/-- `rintro_patt_parse_hi` will parse a high precedence `rcases` pattern, `rintro_patt_hi` below.
This means only tuples and identifiers are allowed; alternations and type ascriptions
require `(...)` instead, which switches to `patt`.
```lean
rintro_patt_hi ::= patt_hi | "(" rintro_patt ")"
```
-/
unsafe def rintro_patt_parse_hi :=
  with_desc "rintro_patt_hi" rintro_patt_parse_hi'

/-- `rintro_patt_parse` will parse a low precedence `rcases` pattern, `rintro_patt` below.
This consists of either a sequence of patterns `p1 p2 p3` or an alternation list `p1 | p2 | p3`
treated as a single pattern, optionally followed by a `: ty` type ascription, which applies to
every pattern in the list.
```lean
rintro_patt ::= (rintro_patt_hi+ | patt_med) (":" expr)?
```
-/
unsafe def rintro_patt_parse :=
  with_desc "rintro_patt" <| rintro_patt_parse' true

/-- `rintro_patt_parse_low` parses `rintro_patt_low`, which is the same as `rintro_patt_parse tt` but
it does not permit an unparenthesized alternation list, it must have the form `p1 p2 p3 (: ty)?`.
```lean
rintro_patt_low ::= rintro_patt_hi* (":" expr)?
```
-/
unsafe def rintro_patt_parse_low :=
  with_desc "rintro_patt_low" <| rintro_patt_parse' false

/-- Syntax for a `rintro` pattern: `('?' (: n)?) | rintro_patt`. -/
unsafe def rintro_parse : parser (Sum (listΠ rcases_patt) Nat) :=
  with_desc "('?' (: n)?) | patt*" <| tk "?" >> Sum.inr <$> rcases_parse_depth <|> Sum.inl <$> rintro_patt_parse_low

namespace Interactive

open Interactive Interactive.Types Expr

/-- `rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* An alteration pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.

`rcases` also has special support for quotient types: quotient induction into Prop works like
matching on the constructor `quot.mk`.

`rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an
assumption `h : e = PAT` will be added to the context.

`rcases? e` will perform case splits on `e` in the same way as `rcases e`,
but rather than accepting a pattern, it does a maximal cases and prints the
pattern that would produce this case splitting. The default maximum depth is 5,
but this can be modified with `rcases? e : n`.
-/
unsafe def rcases : parse rcases_parse → tactic Unit
  | rcases_args.rcases h p ids => tactic.rcases h p ids
  | rcases_args.rcases_many ps ids => tactic.rcases_many ps ids
  | rcases_args.hint p depth => do
    let (pe, patt) ←
      match p with
        | Sum.inl p => Prod.mk <$> pp p <*> rcases_hint p depth
        | Sum.inr ps => do
          let patts ← rcases_hint_many ps depth
          let pes ← ps.mmap pp
          pure (format.bracket "⟨" "⟩" (format.comma_separated pes), rcases_patt.tuple patts)
    let ppat ← pp patt
    trace <| ↑"Try this: rcases " ++ pe ++ " with " ++ ppat

add_tactic_doc
  { Name := "rcases", category := DocCategory.tactic, declNames := [`tactic.interactive.rcases], tags := ["induction"] }

/-- The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintro (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro`, unlike `rcases`, also supports the form `(x y : ty)` for introducing
and type-ascripting multiple variables at once, similar to binders.

`rintro?` will introduce and case split on variables in the same way as
`rintro`, but will also print the `rintro` invocation that would have the same
result. Like `rcases?`, `rintro? : n` allows for modifying the
depth of splitting; the default is 5.

`rintros` is an alias for `rintro`.
-/
unsafe def rintro : parse rintro_parse → tactic Unit
  | Sum.inl [] => intros []
  | Sum.inl l => tactic.rintro l
  | Sum.inr depth => do
    let ps ← tactic.rintro_hint depth
    let fs ←
      ps.mmap fun p => do
          let f ← pp <| p.format true
          pure <| format.space ++ format.group f
    trace <| ↑"Try this: rintro" ++ format.join fs

/-- Alias for `rintro`. -/
unsafe def rintros :=
  rintro

add_tactic_doc
  { Name := "rintro", category := DocCategory.tactic,
    declNames := [`tactic.interactive.rintro, `tactic.interactive.rintros], tags := ["induction"],
    inheritDescriptionFrom := `tactic.interactive.rintro }

setup_tactic_parser

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- Parses `patt? (: expr)? (:= expr)?`, the arguments for `obtain`.
 (This is almost the same as `rcases_patt_parse`,
but it allows the pattern part to be empty.) -/
unsafe def obtain_parse : parser ((Option rcases_patt × Option pexpr) × Option (Sum pexpr (List pexpr))) :=
  with_desc "patt? (: expr)? (:= expr)?" <| do
    let (pat, tp) ←
      (do
            let pat ← rcases_patt_parse
            pure <|
                match pat with
                | rcases_patt.typed pat tp => (some pat, some tp)
                | _ => (some pat, none)) <|>
          Prod.mk none <$> «expr ?» (tk ":" >> texpr)
    Prod.mk (pat, tp) <$>
        «expr ?» do
          tk ":="
          guardₓ tp >> Sum.inr <$> brackets "⟨" "⟩" (sep_by (tk ",") (parser.pexpr 0)) <|> Sum.inl <$> texpr

/-- The `obtain` tactic is a combination of `have` and `rcases`. See `rcases` for
a description of supported patterns.

```lean
obtain ⟨patt⟩ : type,
{ ... }
```
is equivalent to
```lean
have h : type,
{ ... },
rcases h with ⟨patt⟩
```

The syntax `obtain ⟨patt⟩ : type := proof` is also supported.

If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

If `type` is omitted, `:= proof` is required.
-/
unsafe def obtain : parse obtain_parse → tactic Unit
  | ((pat, _), some (Sum.inr val)) => tactic.rcases_many val (pat.getOrElse default)
  | ((pat, none), some (Sum.inl val)) => tactic.rcases none val (pat.getOrElse default)
  | ((pat, some tp), some (Sum.inl val)) => tactic.rcases none val <| (pat.getOrElse default).typed tp
  | ((pat, some tp), none) => do
    let nm ← mk_fresh_name
    let e ← to_expr tp >>= assert nm
    let g :: gs ← get_goals
    set_goals gs
    tactic.rcases none (pquote.1 (%%ₓe)) (pat (rcases_patt.one `this))
    let gs ← get_goals
    set_goals (g :: gs)
  | ((pat, none), none) =>
    fail <|
      "`obtain` requires either an expected type or a value.\n" ++
        "usage: `obtain ⟨patt⟩? : type (:= val)?` or `obtain ⟨patt⟩? (: type)? := val`"

add_tactic_doc
  { Name := "obtain", category := DocCategory.tactic, declNames := [`tactic.interactive.obtain], tags := ["induction"] }

end Interactive

end Tactic

