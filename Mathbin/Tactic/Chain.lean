/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro
-/
import Mathbin.Tactic.Ext

open Interactive

namespace Tactic

/-
This file defines a `chain` tactic, which takes a list of tactics,
and exhaustively tries to apply them to the goals, until no tactic succeeds on any goal.

Along the way, it generates auxiliary declarations, in order to speed up elaboration time
of the resulting (sometimes long!) proofs.

This tactic is used by the `tidy` tactic.
-/
-- α is the return type of our tactics. When `chain` is called by `tidy`, this is string,
-- describing what that tactic did as an interactive tactic.
variable {α : Type}

inductive TacticScript (α : Type) : Type
  | base : α → tactic_script
  | work (index : ℕ) (first : α) (later : List tactic_script) (closed : Bool) : tactic_script

unsafe def tactic_script.to_string : TacticScript Stringₓ → Stringₓ
  | tactic_script.base a => a
  | tactic_script.work n a l c =>
    "work_on_goal " ++ toString (n + 1) ++ " { " ++ ", ".intercalate (a :: l.map tactic_script.to_string) ++ " }"

unsafe instance : HasToString (TacticScript Stringₓ) where toString := fun s => s.toString

unsafe instance tactic_script_unit_has_to_string :
    HasToString (TacticScript Unit) where toString := fun s => "[chain tactic]"

unsafe def abstract_if_success (tac : expr → tactic α) (g : expr) : tactic α := do
  let type ← infer_type g
  let is_lemma ← is_prop type
  if is_lemma then
      -- there's no point making the abstraction, and indeed it's slower
        tac
        g
    else do
      let m ← mk_meta_var type
      let a ← tac m
      (do
            let val ← instantiate_mvars m
            guardₓ (val = [])
            let c ← new_aux_decl_name
            let gs ← get_goals
            set_goals [g]
            add_aux_decl c type val ff >>= unify g
            set_goals gs) <|>
          unify m g
      return a

mutual
  /-- `chain_many tac` recursively tries `tac` on all goals, working depth-first on generated subgoals,
  until it no longer succeeds on any goal. `chain_many` automatically makes auxiliary definitions.
  -/
  unsafe def chain_single {α} (tac : tactic α) : expr → tactic (α × List (TacticScript α))
    | g => do
      set_goals [g]
      let a ← tac
      let l ← get_goals >>= chain_many
      return (a, l)
  /-- `chain_many tac` recursively tries `tac` on all goals, working depth-first on generated subgoals,
  until it no longer succeeds on any goal. `chain_many` automatically makes auxiliary definitions.
  -/
  unsafe def chain_many {α} (tac : tactic α) : List expr → tactic (List (TacticScript α))
    | [] => return []
    | [g] =>
      (do
          let (a, l) ← chain_single g
          return (tactic_script.base a :: l)) <|>
        return []
    | gs => chain_iter gs []
  /-- `chain_many tac` recursively tries `tac` on all goals, working depth-first on generated subgoals,
  until it no longer succeeds on any goal. `chain_many` automatically makes auxiliary definitions.
  -/
  unsafe def chain_iter {α} (tac : tactic α) : List expr → List expr → tactic (List (TacticScript α))
    | [], _ => return []
    | g :: later_goals, stuck_goals =>
      (-- we keep the goals up to date, so they are correct at the end
        do
          let (a, l) ← abstract_if_success chain_single g
          let new_goals ← get_goals
          let w := TacticScript.work stuck_goals.length a l (new_goals = [])
          let current_goals := stuck_goals.reverse ++ new_goals ++ later_goals
          set_goals current_goals
          let l' ← chain_many current_goals
          return (w :: l')) <|>
        chain_iter later_goals (g :: stuck_goals)
end

unsafe def chain_core {α : Type} [HasToString (TacticScript α)] (tactics : List (tactic α)) : tactic (List Stringₓ) :=
  do
  let results ← get_goals >>= chain_many (first tactics)
  when results (fail "`chain` tactic made no progress")
  return (results toString)

variable [HasToString (TacticScript α)] [has_to_format α]

initialize
  registerTraceClass.1 `chain

unsafe def trace_output (t : tactic α) : tactic α := do
  let tgt ← target
  let r ← t
  let name ← decl_name
  trace f! "`chain` successfully applied a tactic during elaboration of {Name}:"
  let tgt ← pp tgt
  trace f! "previous target: {tgt}"
  trace f! "tactic result: {r}"
  let tgt ← try_core target
  let tgt ←
    match tgt with
      | some tgt => pp tgt
      | none => return "no goals"
  trace f! "new target: {tgt}"
  pure r

unsafe def chain (tactics : List (tactic α)) : tactic (List Stringₓ) :=
  chain_core (if is_trace_enabled_for `chain then tactics.map trace_output else tactics)

end Tactic

