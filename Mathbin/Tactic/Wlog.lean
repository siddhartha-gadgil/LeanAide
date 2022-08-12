/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Without loss of generality tactic.
-/
import Mathbin.Data.List.Perm

open Expr

setup_tactic_parser

namespace Tactic

private unsafe def update_pp_name : expr → Name → expr
  | local_const n _ bi d, pp => local_const n pp bi d
  | e, n => e

private unsafe def elim_or : ℕ → expr → tactic (List expr)
  | 0, h => fail "zero cases"
  | 1, h => return [h]
  | n + 1, h => do
    let [(_, [hl], []), (_, [hr], [])] ← induction h
    let-- there should be no dependent terms
      [gl, gr]
      ← get_goals
    set_goals [gr]
    let hsr ← elim_or n hr
    let gsr ← get_goals
    set_goals (gl :: gsr)
    return (hl :: hsr)

private unsafe def dest_or : expr → tactic (List expr)
  | e => do
    let quote.1 ((%%ₓa) ∨ %%ₓb) ← whnf e | return [e]
    let lb ← dest_or b
    return (a :: lb)

private unsafe def match_perms (pat : pattern) : expr → tactic (List <| List expr)
  | t =>
    (do
        let m ← match_pattern pat t
        guardₓ (m.2.all expr.is_local_constant)
        return [m.2]) <|>
      do
      let quote.1 ((%%ₓl) ∨ %%ₓr) ← whnf t
      let m ← match_pattern pat l
      let rs ← match_perms r
      return (m.2 :: rs)

unsafe def wlog (vars' : List expr) (h_cases fst_case : expr) (perms : List (List expr)) : tactic Unit := do
  guardₓ h_cases
  let nr
    ←-- reorder s.t. context is Γ ⬝ vars ⬝ cases ⊢ ∀deps, …
        revert_lst
        (vars' ++ [h_cases])
  let vars ← intron' vars'.length
  let h_cases ← intro h_cases.local_pp_name
  let cases ← infer_type h_cases
  let h_fst_case ←
    mk_local_def h_cases.local_pp_name
        (fst_case.instantiate_locals <| (vars'.zip vars).map fun ⟨o, n⟩ => (o.local_uniq_name, n))
  let ((), pr) ← solve_aux cases (repeat <| exact h_fst_case <|> left >> skip)
  let t ← target
  let fixed_vars ← vars.mmap update_type
  let t' := (instantiate_local h_cases.local_uniq_name pr t).pis (fixed_vars ++ [h_fst_case])
  let (h, [g]) ←
    local_proof `this t' do
        clear h_cases
        vars clear
        intron nr
  let h₀ :: hs ← elim_or perms.length h_cases
  solve1 do
      exact (h <| vars ++ [h₀])
  focus
      ((hs perms).map fun ⟨h_case, perm⟩ => do
        let p_v := (vars' vars).map fun ⟨p, v⟩ => (p, v)
        let p := perm fun p => p p_v
        note `this none (h <| p ++ [h_case])
        clear h
        return ())
  let gs ← get_goals
  set_goals (g :: gs)

namespace Interactive

open Interactive Interactive.Types Expr

private unsafe def parse_permutations : Option (List (List Name)) → tactic (List (List expr))
  | none => return []
  | some [] => return []
  | some perms@(p₀ :: ps) => do
    guardₓ p₀ <|> fail "No permutation `xs_i` in `using [xs_1, …, xs_n]` should contain the same variable twice."
    guardₓ (perms fun p => p p₀) <|>
        fail ("The permutations `xs_i` in `using [xs_1, …, xs_n]` must be permutations of the same" ++ " variables.")
    perms fun p => p get_local

/-- Without loss of generality: reduces to one goal under variables permutations.

Given a goal of the form `g xs`, a predicate `p` over a set of variables, as well as variable
permutations `xs_i`. Then `wlog` produces goals of the form

* The case goal, i.e. the permutation `xs_i` covers all possible cases:
  `⊢ p xs_0 ∨ ⋯ ∨ p xs_n`
* The main goal, i.e. the goal reduced to `xs_0`:
  `(h : p xs_0) ⊢ g xs_0`
* The invariant goals, i.e. `g` is invariant under `xs_i`:
  `(h : p xs_i) (this : g xs_0) ⊢ gs xs_i`

Either the permutation is provided, or a proof of the disjunction is provided to compute the
permutation. The disjunction need to be in assoc normal form, e.g. `p₀ ∨ (p₁ ∨ p₂)`. In many cases
the invariant goals can be solved by AC rewriting using `cc` etc.

For example, on a state `(n m : ℕ) ⊢ p n m` the tactic `wlog h : n ≤ m using [n m, m n]` produces
the following states:
* `(n m : ℕ) ⊢ n ≤ m ∨ m ≤ n`
* `(n m : ℕ) (h : n ≤ m) ⊢ p n m`
* `(n m : ℕ) (h : m ≤ n) (this : p n m) ⊢ p m n`

`wlog` supports different calling conventions. The name `h` is used to give a name to the introduced
case hypothesis. If the name is avoided, the default will be `case`.

1. `wlog : p xs0 using [xs0, …, xsn]`  
   Results in the case goal `p xs0 ∨ ⋯ ∨ ps xsn`, the main goal `(case : p xs0) ⊢ g xs0` and the
   invariance goals `(case : p xsi) (this : g xs0) ⊢ g xsi`.

2. `wlog : p xs0 := r using xs0`  
   The expression `r` is a proof of the shape `p xs0 ∨ ⋯ ∨ p xsi`, it is also used to compute the
   variable permutations.

3. `wlog := r using xs0`  
   The expression `r` is a proof of the shape `p xs0 ∨ ⋯ ∨ p xsi`, it is also used to compute the
   variable permutations. This is not as stable as (2), for example `p` cannot be a disjunction.

4. `wlog : R x y using x y` and `wlog : R x y`  
   Produces the case `R x y ∨ R y x`. If `R` is ≤, then the disjunction discharged using linearity.
   If `using x y` is avoided then `x` and `y` are the last two variables appearing in the
   expression `R x y`.
-/
unsafe def wlog (h : parse ident ?) (pat : parse (tk ":" *> texpr)?) (cases : parse (tk ":=" *> texpr)?)
    (perms : parse (tk "using" *> (list_of ident* <|> (fun x => [x]) <$> ident*))?)
    (discharger : tactic Unit :=
      tactic.solve_by_elim <|>
        tactic.tautology { classical := true } <|> using_smt (smt_tactic.intros >> smt_tactic.solve_goals)) :
    tactic Unit := do
  let perms ← parse_permutations perms
  let (pat, cases_pr, cases_goal, vars, perms) ←
    match cases with
      | some r => do
        let vars :: _ ← return perms |
          fail "At least one set of variables expected, i.e. `using x y` or `using [x y, y x]`."
        let cases_pr ← to_expr r
        let cases_pr ←
          if cases_pr.is_local_constant then
              return <|
                match h with
                | some n => update_pp_name cases_pr n
                | none => cases_pr
            else do
              note (h `case) none cases_pr
        let cases ← infer_type cases_pr
        let (pat, perms') ←
          match pat with
            | some pat => do
              let pat ← to_expr pat
              let vars' := vars.filter fun v => v.occurs pat
              let case_pat ← mk_pattern [] vars' pat [] vars'
              let perms' ← match_perms case_pat cases
              return (pat, perms')
            | none => do
              let p :: ps ← dest_or cases
              let vars' := vars.filter fun v => v.occurs p
              let case_pat ← mk_pattern [] vars' p [] vars'
              let perms' ←
                (p :: ps).mmap fun p => do
                    let m ← match_pattern case_pat p
                    return m.2
              return (p, perms')
        let vars_name := vars.map local_uniq_name
        guardₓ (perms' fun p => p fun v => v ∧ v ∈ vars_name) <|>
            fail "Cases contains variables not declared in `using x y z`"
        let perms ←
          if perms.length = 1 then do
              return (perms' fun p => p ++ vars fun v => p fun v' => v' ≠ v)
            else do
              guardₓ (perms = perms') <|>
                  fail "The provided permutation list has a different length then the provided cases."
              return perms
        return (pat, cases_pr, @none expr, vars, perms)
      | none => do
        let name_h := h.getOrElse `case
        let some pat ← return pat | fail "Either specify cases or a pattern with permutations"
        let pat ← to_expr pat
        (do
              let [x, y] ←
                match perms with
                  | [] => return pat
                  | [l] => return l
                  | _ => failed
              let cases := mk_or_lst [pat, pat [(x, y), (y, x)]]
              (do
                    let quote.1 ((%%ₓx') ≤ %%ₓy') ← return pat
                    let (cases_pr, []) ← local_proof name_h cases (exact (pquote.1 (le_totalₓ (%%ₓx') (%%ₓy'))))
                    return (pat, cases_pr, none, [x, y], [[x, y], [y, x]])) <|>
                  do
                  let (cases_pr, [g]) ← local_proof name_h cases skip
                  return (pat, cases_pr, some g, [x, y], [[x, y], [y, x]])) <|>
            do
            guardₓ (perms ≥ 2) <|>
                fail
                  ("To generate cases at least two permutations are required, i.e. `using [x y, y x]`" ++
                    " or exactly 0 or 2 variables")
            let vars :: perms' ← return perms
            let names := vars local_uniq_name
            let cases := mk_or_lst (pat :: perms' fun p => pat (names p))
            let (cases_pr, [g]) ← local_proof name_h cases skip
            return (pat, cases_pr, some g, vars, perms)
  let name_fn :=
    if perms.length = 2 then fun _ => `invariant else fun i => mkSimpleName ("invariant_" ++ toString (i + 1))
  with_enable_tags <|
      tactic.focus1 <| do
        let t ← get_main_tag
        tactic.wlog vars cases_pr pat perms
        tactic.focus
            (set_main_tag (mkNumName `_case 0 :: `main :: t) ::
              (List.range (perms - 1)).map fun i => do
                set_main_tag (mkNumName `_case 0 :: name_fn i :: t)
                try discharger)
        match cases_goal with
          | some g => do
            set_tag g (mkNumName `_case 0 :: `cases :: t)
            let gs ← get_goals
            set_goals (g :: gs)
          | none => skip

add_tactic_doc { Name := "wlog", category := DocCategory.tactic, declNames := [`` wlog], tags := ["logic"] }

end Interactive

end Tactic

