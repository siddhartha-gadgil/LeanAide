/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen, Keeley Hoek, Leonardo de Moura

Converter monad for building simplifiers.
-/
import Mathbin.Tactic.Core
import Mathbin.Tactic.Converter.OldConv

namespace OldConv

unsafe def save_info (p : Pos) : old_conv Unit := fun r lhs => do
  let ts ← tactic.read
  (-- TODO(Leo): include context
        tactic.save_info_thunk
        p fun _ => ts lhs) >>
      return ⟨(), lhs, none⟩

unsafe def step {α : Type} (c : old_conv α) : old_conv Unit :=
  c >> return ()

unsafe def istep {α : Type} (line0 col0 line col : Nat) (c : old_conv α) : old_conv Unit := fun r lhs ts =>
  (@scopeTrace _ line col fun _ => (c >> return ()) r lhs ts).clamp_pos line0 line col

unsafe def execute (c : old_conv Unit) : tactic Unit :=
  conversion c

namespace Interactive

setup_tactic_parser

unsafe def itactic : Type :=
  old_conv Unit

unsafe def whnf : old_conv Unit :=
  old_conv.whnf

unsafe def dsimp : old_conv Unit :=
  old_conv.dsimp

unsafe def trace_state : old_conv Unit :=
  old_conv.trace_lhs

unsafe def change (p : parse texpr) : old_conv Unit :=
  old_conv.change p

unsafe def find (p : parse lean.parser.pexpr) (c : itactic) : old_conv Unit := fun r lhs => do
  let pat ← tactic.pexpr_to_pattern p
  let s ← simp_lemmas.mk_default
  let-- to be able to use congruence lemmas @[congr]
    (found, new_lhs, pr)
    ←
    tactic.ext_simplify_core false { zeta := false, beta := false, singlePass := true, eta := false, proj := false } s
        (fun u => return u)
        (fun found s r p e => do
          guardₓ (Not found)
          let matched ← tactic.match_pattern pat e >> return true <|> return false
          guardₓ matched
          let ⟨u, new_e, pr⟩ ← c r e
          return (tt, new_e, pr, ff))
        (fun a s r p e => tactic.failed) r lhs
  if Not found then tactic.fail "find converter failed, pattern was not found" else return ⟨(), new_lhs, some pr⟩

end Interactive

end OldConv

namespace Conv

open Tactic

unsafe def replace_lhs (tac : expr → tactic (expr × expr)) : conv Unit := do
  let (e, pf) ← lhs >>= tac
  update_lhs e pf

-- Attempts to discharge the equality of the current `lhs` using `tac`,
-- moving to the next goal on success.
unsafe def discharge_eq_lhs (tac : tactic Unit) : conv Unit := do
  let pf ←
    lock_tactic_state do
        let m ← lhs >>= mk_meta_var
        set_goals [m]
        tac >> done
        instantiate_mvars m
  congr
  let the_rhs ← rhs
  update_lhs the_rhs pf
  skip
  skip

namespace Interactive

setup_tactic_parser

open Tactic.Interactive (rw_rules)

/-- The `conv` tactic provides a `conv` within a `conv`. It allows the user to return to a
previous state of the outer conv block to continue editing an expression without having to
start a new conv block. -/
protected unsafe def conv (t : conv.interactive.itactic) : conv Unit := do
  transitivity
  let a :: rest ← get_goals
  set_goals [a]
  t
  all_goals reflexivity
  set_goals rest

unsafe def erw (q : parse rw_rules) (cfg : RewriteCfg := { md := semireducible }) : conv Unit :=
  rw q cfg

open Interactive.Types

/-- `guard_target t` fails if the target of the conv goal is not `t`.
We use this tactic for writing tests.
-/
unsafe def guard_target (p : parse texpr) : conv Unit := do
  let quote.1 ((%%ₓt) = _) ← target
  tactic.interactive.guard_expr_eq t p

end Interactive

end Conv

namespace Tactic

namespace Interactive

setup_tactic_parser

unsafe def old_conv (c : old_conv.interactive.itactic) : tactic Unit := do
  let t ← target
  let (new_t, pr) ← c.to_tactic `eq t
  replace_target new_t pr

unsafe def find (p : parse lean.parser.pexpr) (c : old_conv.interactive.itactic) : tactic Unit :=
  old_conv <| old_conv.interactive.find p c

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
unsafe def conv_lhs (loc : parse («expr ?» (tk "at" *> ident))) (p : parse («expr ?» (tk "in" *> parser.pexpr)))
    (c : conv.interactive.itactic) : tactic Unit :=
  conv loc p (conv.interactive.to_lhs >> c)

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
unsafe def conv_rhs (loc : parse («expr ?» (tk "at" *> ident))) (p : parse («expr ?» (tk "in" *> parser.pexpr)))
    (c : conv.interactive.itactic) : tactic Unit :=
  conv loc p (conv.interactive.to_rhs >> c)

end Interactive

end Tactic

