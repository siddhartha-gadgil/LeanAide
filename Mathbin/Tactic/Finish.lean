/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Jesse Michael Han
-/
import Mathbin.Tactic.Hint

/-!
# The `finish` family of tactics

These tactics do straightforward things: they call the simplifier, split conjunctive assumptions,
eliminate existential quantifiers on the left, and look for contradictions. They rely on ematching
and congruence closure to try to finish off a goal at the end.

The procedures *do* split on disjunctions and recreate the smt state for each terminal call, so
they are only meant to be used on small, straightforward problems.

## Main definitions

We provide the following tactics:

* `finish`  -- solves the goal or fails
* `clarify` -- makes as much progress as possible while not leaving more than one goal
* `safe`    -- splits freely, finishes off whatever subgoals it can, and leaves the rest

All accept an optional list of simplifier rules, typically definitions that should be expanded.
(The equations and identities should not refer to the local context.)

-/


initialize
  registerTraceClass.1 `auto.done

initialize
  registerTraceClass.1 `auto.finish

namespace Tactic

namespace Interactive

unsafe def revert_all :=
  tactic.revert_all

end Interactive

end Tactic

open Tactic Expr

namespace Auto

/-! ### Utilities -/


unsafe def whnf_reducible (e : expr) : tactic expr :=
  whnf e reducible

-- stolen from interactive.lean
unsafe def add_simps : simp_lemmas → List Name → tactic simp_lemmas
  | s, [] => return s
  | s, n :: ns => do
    let s' ← s.add_simp n
    add_simps s' ns

/-- Configuration information for the auto tactics.
* `(use_simp := tt)`: call the simplifier
* `(max_ematch_rounds := 20)`: for the "done" tactic
-/
structure AutoConfig : Type where
  useSimp := true
  maxEmatchRounds := 20
  deriving DecidableEq, Inhabited

/-!
### Preprocess goal.

We want to move everything to the left of the sequent arrow. For intuitionistic logic,
we replace the goal `p` with `∀ f, (p → f) → f` and introduce.
-/


theorem by_contradiction_trick (p : Prop) (h : ∀ f : Prop, (p → f) → f) : p :=
  h p id

unsafe def preprocess_goal : tactic Unit := do
  repeat (intro1 >> skip)
  let tgt ← target >>= whnf_reducible
  if ¬is_false tgt then ((mk_mapp `` Classical.by_contradiction [some tgt] >>= apply) >> intro1) >> skip else skip

/-!
### Normalize hypotheses

Bring conjunctions to the outside (for splitting),
bring universal quantifiers to the outside (for ematching). The classical normalizer
eliminates `a → b` in favor of `¬ a ∨ b`.

For efficiency, we push negations inwards from the top down. (For example, consider
simplifying `¬ ¬ (p ∨ q)`.)
-/


section

universe u

variable {α : Type u}

variable (p q : Prop)

variable (s : α → Prop)

attribute [local instance] Classical.propDecidable

theorem not_not_eq : (¬¬p) = p :=
  propext not_not

theorem not_and_eq : (¬(p ∧ q)) = (¬p ∨ ¬q) :=
  propext not_and_distrib

theorem not_or_eq : (¬(p ∨ q)) = (¬p ∧ ¬q) :=
  propext not_or_distrib

theorem not_forall_eq : (¬∀ x, s x) = ∃ x, ¬s x :=
  propext not_forall

theorem not_exists_eq : (¬∃ x, s x) = ∀ x, ¬s x :=
  propext not_exists

theorem not_implies_eq : (¬(p → q)) = (p ∧ ¬q) :=
  propext not_imp

theorem Classical.implies_iff_not_or : p → q ↔ ¬p ∨ q :=
  imp_iff_not_or

end

def commonNormalizeLemmaNames : List Name :=
  [`` bex_def, `` forall_and_distrib, `` exists_imp_distrib, `` Or.assoc, `` Or.comm, `` Or.left_comm, `` And.assoc,
    `` And.comm, `` And.left_comm]

def classicalNormalizeLemmaNames : List Name :=
  common_normalize_lemma_names ++ [`` classical.implies_iff_not_or]

/-- optionally returns an equivalent expression and proof of equivalence -/
private unsafe def transform_negation_step (cfg : AutoConfig) (e : expr) : tactic (Option (expr × expr)) := do
  let e ← whnf_reducible e
  match e with
    | quote.1 ¬%%ₓNe => do
      let ne ← whnf_reducible Ne
      match Ne with
        | quote.1 ¬%%ₓa => do
          let pr ← mk_app `` not_not_eq [a]
          return (some (a, pr))
        | quote.1 ((%%ₓa) ∧ %%ₓb) => do
          let pr ← mk_app `` not_and_eq [a, b]
          return (some (quote.1 ((¬%%ₓa) ∨ ¬%%ₓb), pr))
        | quote.1 ((%%ₓa) ∨ %%ₓb) => do
          let pr ← mk_app `` not_or_eq [a, b]
          return (some (quote.1 ((¬%%ₓa) ∧ ¬%%ₓb), pr))
        | quote.1 (Exists (%%ₓp)) => do
          let pr ← mk_app `` not_exists_eq [p]
          let quote.1 ((%%ₓ_) = %%ₓe') ← infer_type pr
          return (some (e', pr))
        | pi n bi d p =>
          if p then do
            let pr ← mk_app `` not_forall_eq [lam n bi d (expr.abstract_local p n)]
            let quote.1 ((%%ₓ_) = %%ₓe') ← infer_type pr
            return (some (e', pr))
          else do
            let pr ← mk_app `` not_implies_eq [d, p]
            let quote.1 ((%%ₓ_) = %%ₓe') ← infer_type pr
            return (some (e', pr))
        | _ => return none
    | _ => return none

/-- given an expr `e`, returns a new expression and a proof of equality -/
private unsafe def transform_negation (cfg : AutoConfig) : expr → tactic (Option (expr × expr)) := fun e => do
  let opr ← transform_negation_step cfg e
  match opr with
    | some (e', pr) => do
      let opr' ← transform_negation e'
      match opr' with
        | none => return (some (e', pr))
        | some (e'', pr') => do
          let pr'' ← mk_eq_trans pr pr'
          return (some (e'', pr''))
    | none => return none

unsafe def normalize_negations (cfg : AutoConfig) (h : expr) : tactic Unit := do
  let t ← infer_type h
  let (_, e, pr) ←
    simplify_top_down ()
        (fun _ => fun e => do
          let oepr ← transform_negation cfg e
          match oepr with
            | some (e', pr) => return ((), e', pr)
            | none => do
              let pr ← mk_eq_refl e
              return ((), e, pr))
        t
  replace_hyp h e pr
  skip

unsafe def normalize_hyp (cfg : AutoConfig) (simps : simp_lemmas) (h : expr) : tactic Unit :=
  (do
      let (h, _) ← simp_hyp simps [] h
      try (normalize_negations cfg h)) <|>
    try (normalize_negations cfg h)

unsafe def normalize_hyps (cfg : AutoConfig) : tactic Unit := do
  let simps ← add_simps simp_lemmas.mk classicalNormalizeLemmaNames
  local_context >>= Monadₓ.mapm' (normalize_hyp cfg simps)

/-!
### Eliminate existential quantifiers
-/


/-- eliminate an existential quantifier if there is one -/
unsafe def eelim : tactic Unit := do
  let ctx ← local_context
  first <|
      ctx fun h => do
        let t ← infer_type h >>= whnf_reducible
        guardₓ (is_app_of t `` Exists)
        let tgt ← target
        to_expr (pquote.1 (@Exists.elim _ _ (%%ₓtgt) (%%ₓh))) >>= apply
        intros
        clear h

/-- eliminate all existential quantifiers, fails if there aren't any -/
unsafe def eelims : tactic Unit :=
  eelim >> repeat eelim

/-!
### Substitute if there is a hypothesis `x = t` or `t = x`
-/


/-- carries out a subst if there is one, fails otherwise -/
unsafe def do_subst : tactic Unit := do
  let ctx ← local_context
  first <|
      ctx fun h => do
        let t ← infer_type h >>= whnf_reducible
        match t with
          | quote.1 ((%%ₓa) = %%ₓb) => subst h
          | _ => failed

unsafe def do_substs : tactic Unit :=
  do_subst >> repeat do_subst

/-!
### Split all conjunctions
-/


/-- Assumes `pr` is a proof of `t`. Adds the consequences of `t` to the context
 and returns `tt` if anything nontrivial has been added. -/
unsafe def add_conjuncts : expr → expr → tactic Bool := fun pr t =>
  let assert_consequences := fun e t => mcond (add_conjuncts e t) skip (note_anon t e >> skip)
  do
  let t' ← whnf_reducible t
  match t' with
    | quote.1 ((%%ₓa) ∧ %%ₓb) => do
      let e₁ ← mk_app `` And.left [pr]
      assert_consequences e₁ a
      let e₂ ← mk_app `` And.right [pr]
      assert_consequences e₂ b
      return tt
    | quote.1 True => do
      return tt
    | _ => return ff

/-- return `tt` if any progress is made -/
unsafe def split_hyp (h : expr) : tactic Bool := do
  let t ← infer_type h
  mcond (add_conjuncts h t) (clear h >> return tt) (return ff)

/-- return `tt` if any progress is made -/
unsafe def split_hyps_aux : List expr → tactic Bool
  | [] => return false
  | h :: hs => do
    let b₁ ← split_hyp h
    let b₂ ← split_hyps_aux hs
    return (b₁ || b₂)

/-- fail if no progress is made -/
unsafe def split_hyps : tactic Unit :=
  local_context >>= split_hyps_aux >>= guardb

/-!
### Eagerly apply all the preprocessing rules
-/


/-- Eagerly apply all the preprocessing rules -/
unsafe def preprocess_hyps (cfg : AutoConfig) : tactic Unit := do
  repeat (intro1 >> skip)
  preprocess_goal
  normalize_hyps cfg
  repeat (do_substs <|> split_hyps <|> eelim)

/-!
### Terminal tactic
-/


/-- The terminal tactic, used to try to finish off goals:
- Call the contradiction tactic.
- Open an SMT state, and use ematching and congruence closure, with all the universal
  statements in the context.

TODO(Jeremy): allow users to specify attribute for ematching lemmas?
-/
--<|> self_simplify_hyps
unsafe def mk_hinst_lemmas : List expr → smt_tactic hinst_lemmas
  | [] =>-- return hinst_lemmas.mk
  do
    get_hinst_lemmas_for_attr `ematch
  | h :: hs => do
    let his ← mk_hinst_lemmas hs
    let t ← infer_type h
    match t with
      | pi _ _ _ _ => do
        let t' ← infer_type t
        if t' = quote.1 Prop then
            (do
                let new_lemma ← hinst_lemma.mk h
                return (hinst_lemmas.add his new_lemma)) <|>
              return his
          else return his
      | _ => return his

private unsafe def report_invalid_em_lemma {α : Type} (n : Name) : smt_tactic α :=
  fail f! "invalid ematch lemma '{n}'"

private unsafe def add_hinst_lemma_from_name (md : Transparency) (lhs_lemma : Bool) (n : Name) (hs : hinst_lemmas)
    (ref : pexpr) : smt_tactic hinst_lemmas := do
  let p ← resolve_name n
  match p with
    | expr.const n _ =>
      (do
          let h ← hinst_lemma.mk_from_decl_core md n lhs_lemma
          tactic.save_const_type_info n ref
          return <| hs h) <|>
        (do
            let hs₁ ← smt_tactic.mk_ematch_eqn_lemmas_for_core md n
            tactic.save_const_type_info n ref
            return <| hs hs₁) <|>
          report_invalid_em_lemma n
    | _ =>
      (do
          let e ← to_expr p
          let h ← hinst_lemma.mk_core md e lhs_lemma
          try (tactic.save_type_info e ref)
          return <| hs h) <|>
        report_invalid_em_lemma n

private unsafe def add_hinst_lemma_from_pexpr (md : Transparency) (lhs_lemma : Bool) (hs : hinst_lemmas) :
    pexpr → smt_tactic hinst_lemmas
  | p@(expr.const c []) => add_hinst_lemma_from_name md lhs_lemma c hs p
  | p@(expr.local_const c _ _ _) => add_hinst_lemma_from_name md lhs_lemma c hs p
  | p => do
    let new_e ← to_expr p
    let h ← hinst_lemma.mk_core md new_e lhs_lemma
    return <| hs h

private unsafe def add_hinst_lemmas_from_pexprs (md : Transparency) (lhs_lemma : Bool) (ps : List pexpr)
    (hs : hinst_lemmas) : smt_tactic hinst_lemmas :=
  List.mfoldl (add_hinst_lemma_from_pexpr md lhs_lemma) hs ps

/-- `done` first attempts to close the goal using `contradiction`. If this fails, it creates an
SMT state and will repeatedly use `ematch` (using `ematch` lemmas in the environment,
universally quantified assumptions, and the supplied lemmas `ps`) and congruence closure.
-/
unsafe def done (ps : List pexpr) (cfg : AutoConfig := {  }) : tactic Unit := do
  trace_state_if_enabled `auto.done "entering done"
  contradiction <|>
      (solve1 <| do
        revert_all
        using_smt do
            smt_tactic.intros
            let ctx ← local_context
            let hs ← mk_hinst_lemmas ctx
            let hs' ← add_hinst_lemmas_from_pexprs reducible ff ps hs
            smt_tactic.iterate_at_most cfg (smt_tactic.ematch_using hs' >> smt_tactic.try smt_tactic.close))

/-!
### Tactics that perform case splits
-/


inductive CaseOption
  | force-- fail unless all goals are solved

  | at_most_one-- leave at most one goal

  | accept
  deriving DecidableEq, Inhabited

-- leave as many goals as necessary
private unsafe def case_cont (s : CaseOption) (cont : CaseOption → tactic Unit) : tactic Unit := do
  match s with
    | case_option.force => cont case_option.force >> cont case_option.force
    |
    case_option.at_most_one =>-- if the first one succeeds, commit to it, and try the second
          mcond
          (cont case_option.force >> return tt) (cont case_option.at_most_one) skip <|>
        (-- otherwise, try the second
            swap >>
            cont case_option.force) >>
          cont case_option.at_most_one
    | case_option.accept => focus' [cont case_option.accept, cont case_option.accept]

-- three possible outcomes:
--   finds something to case, the continuations succeed ==> returns tt
--   finds something to case, the continutations fail ==> fails
--   doesn't find anything to case ==> returns ff
unsafe def case_hyp (h : expr) (s : CaseOption) (cont : CaseOption → tactic Unit) : tactic Bool := do
  let t ← infer_type h
  match t with
    | quote.1 ((%%ₓa) ∨ %%ₓb) => (cases h >> case_cont s cont) >> return tt
    | _ => return ff

unsafe def case_some_hyp_aux (s : CaseOption) (cont : CaseOption → tactic Unit) : List expr → tactic Bool
  | [] => return false
  | h :: hs => mcond (case_hyp h s cont) (return true) (case_some_hyp_aux hs)

unsafe def case_some_hyp (s : CaseOption) (cont : CaseOption → tactic Unit) : tactic Bool :=
  local_context >>= case_some_hyp_aux s cont

/-!
### The main tactics
-/


/-- `safe_core s ps cfg opt` negates the goal, normalizes hypotheses
(by splitting conjunctions, eliminating existentials, pushing negations inwards,
and calling `simp` with the supplied lemmas `s`), and then tries `contradiction`.

If this fails, it will create an SMT state and repeatedly use `ematch`
(using `ematch` lemmas in the environment, universally quantified assumptions,
and the supplied lemmas `ps`) and congruence closure.

`safe_core` is complete for propositional logic. Depending on the form of `opt`
it will:

- (if `opt` is `case_option.force`) fail if it does not close the goal,
- (if `opt` is `case_option.at_most_one`) fail if it produces more than one goal, and
- (if `opt` is `case_option.accept`) ignore the number of goals it produces.
-/
unsafe def safe_core (s : simp_lemmas × List Name) (ps : List pexpr) (cfg : AutoConfig) : CaseOption → tactic Unit :=
  fun co =>
  focus1 <| do
    trace_state_if_enabled `auto.finish "entering safe_core"
    if cfg then do
        trace_if_enabled `auto.finish "simplifying hypotheses"
        simp_all s.1 s.2 { failIfUnchanged := ff }
        trace_state_if_enabled `auto.finish "result:"
      else skip
    tactic.done <|> do
        trace_if_enabled `auto.finish "preprocessing hypotheses"
        preprocess_hyps cfg
        trace_state_if_enabled `auto.finish "result:"
        done ps cfg <|>
            mcond (case_some_hyp co safe_core) skip
              (match co with
              | case_option.force => done ps cfg
              | case_option.at_most_one => try (done ps cfg)
              | case_option.accept => try (done ps cfg))

/-- `clarify` is `safe_core`, but with the `(opt : case_option)`
parameter fixed at `case_option.at_most_one`.
-/
unsafe def clarify (s : simp_lemmas × List Name) (ps : List pexpr) (cfg : AutoConfig := {  }) : tactic Unit :=
  safe_core s ps cfg CaseOption.at_most_one

/-- `safe` is `safe_core`, but with the `(opt : case_option)`
parameter fixed at `case_option.accept`.
-/
unsafe def safe (s : simp_lemmas × List Name) (ps : List pexpr) (cfg : AutoConfig := {  }) : tactic Unit :=
  safe_core s ps cfg CaseOption.accept

/-- `finish` is `safe_core`, but with the `(opt : case_option)`
parameter fixed at `case_option.force`.
-/
unsafe def finish (s : simp_lemmas × List Name) (ps : List pexpr) (cfg : AutoConfig := {  }) : tactic Unit :=
  safe_core s ps cfg CaseOption.force

end Auto

/-! ### interactive versions -/


open Auto

namespace Tactic

namespace Interactive

setup_tactic_parser

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `clarify [h1,...,hn] using [e1,...,en]` negates the goal, normalizes hypotheses
(by splitting conjunctions, eliminating existentials, pushing negations inwards,
and calling `simp` with the supplied lemmas `h1,...,hn`), and then tries `contradiction`.

If this fails, it will create an SMT state and repeatedly use `ematch`
(using `ematch` lemmas in the environment, universally quantified assumptions,
and the supplied lemmas `e1,...,en`) and congruence closure.

`clarify` is complete for propositional logic.

Either of the supplied simp lemmas or the supplied ematch lemmas are optional.

`clarify` will fail if it produces more than one goal.
-/
unsafe def clarify (hs : parse simp_arg_list) (ps : parse («expr ?» (tk "using" *> pexpr_list_or_texpr)))
    (cfg : AutoConfig := {  }) : tactic Unit := do
  let s ← mk_simp_set false [] hs
  auto.clarify s (ps []) cfg

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `safe [h1,...,hn] using [e1,...,en]` negates the goal, normalizes hypotheses
(by splitting conjunctions, eliminating existentials, pushing negations inwards,
and calling `simp` with the supplied lemmas `h1,...,hn`), and then tries `contradiction`.

If this fails, it will create an SMT state and repeatedly use `ematch`
(using `ematch` lemmas in the environment, universally quantified assumptions,
and the supplied lemmas `e1,...,en`) and congruence closure.

`safe` is complete for propositional logic.

Either of the supplied simp lemmas or the supplied ematch lemmas are optional.

`safe` ignores the number of goals it produces, and should never fail.
-/
unsafe def safe (hs : parse simp_arg_list) (ps : parse («expr ?» (tk "using" *> pexpr_list_or_texpr)))
    (cfg : AutoConfig := {  }) : tactic Unit := do
  let s ← mk_simp_set false [] hs
  auto.safe s (ps []) cfg

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `finish [h1,...,hn] using [e1,...,en]` negates the goal, normalizes hypotheses
(by splitting conjunctions, eliminating existentials, pushing negations inwards,
and calling `simp` with the supplied lemmas `h1,...,hn`), and then tries `contradiction`.

If this fails, it will create an SMT state and repeatedly use `ematch`
(using `ematch` lemmas in the environment, universally quantified assumptions,
and the supplied lemmas `e1,...,en`) and congruence closure.

`finish` is complete for propositional logic.

Either of the supplied simp lemmas or the supplied ematch lemmas are optional.

`finish` will fail if it does not close the goal.
-/
unsafe def finish (hs : parse simp_arg_list) (ps : parse («expr ?» (tk "using" *> pexpr_list_or_texpr)))
    (cfg : AutoConfig := {  }) : tactic Unit := do
  let s ← mk_simp_set false [] hs
  auto.finish s (ps []) cfg

add_hint_tactic finish

/-- These tactics do straightforward things: they call the simplifier, split conjunctive assumptions,
eliminate existential quantifiers on the left, and look for contradictions. They rely on ematching
and congruence closure to try to finish off a goal at the end.

The procedures *do* split on disjunctions and recreate the smt state for each terminal call, so
they are only meant to be used on small, straightforward problems.

* `finish`:  solves the goal or fails
* `clarify`: makes as much progress as possible while not leaving more than one goal
* `safe`:    splits freely, finishes off whatever subgoals it can, and leaves the rest

All accept an optional list of simplifier rules, typically definitions that should be expanded.
(The equations and identities should not refer to the local context.) All also accept an optional
list of `ematch` lemmas, which must be preceded by `using`.
-/
add_tactic_doc
  { Name := "finish / clarify / safe", category := DocCategory.tactic,
    declNames := [`tactic.interactive.finish, `tactic.interactive.clarify, `tactic.interactive.safe],
    tags := ["logic", "finishing"] }

end Interactive

end Tactic

