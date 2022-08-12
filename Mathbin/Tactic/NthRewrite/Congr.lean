/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import Mathbin.Tactic.Core
import Mathbin.Tactic.NthRewrite.Basic

namespace Tactic

namespace NthRewrite.Congr

open NthRewrite

/-- Helper function which just tries to rewrite `e` using the equality `r` without assigning any
metavariables in the tactic state, and without creating any metavariables which cannot be
discharged by `cfg.discharger` in the process. -/
unsafe def rewrite_without_new_mvars (r : expr) (e : expr) (cfg : nth_rewrite.cfg := {  }) : tactic (expr × expr) :=
  lock_tactic_state <|-- This makes sure that we forget everything in between rewrites;
  -- otherwise we don't correctly find everything!
  do
    let (new_t, prf, metas) ← rewrite_core r e { cfg.to_rewrite_cfg with md := semireducible }
    try_apply_opt_auto_param cfg metas
    set_goals metas
    all_goals (try cfg)
    done
    let prf ← instantiate_mvars prf
    -- This is necessary because of the locked tactic state.
        return
        (new_t, prf)

/-- Returns true if the argument is a proof that the entire expression was rewritten.

This is a bit of a hack: we manually inspect the proof that `rewrite_core` produced, and deduce from
that whether or not the entire expression was rewritten.-/
unsafe def rewrite_is_of_entire : expr → Bool
  | quote.1 (@Eq.ndrec _ (%%ₓterm) (%%ₓC) (%%ₓp) _ _) =>
    match C with
    | quote.1 fun p => _ = p => true
    | _ => false
  | _ => false

/-- Function which tries to perform the rewrite associated to the equality `r : expr × bool` (the
bool indicates whether we should flip the equality first), at the position pointed to by
`l : expr_lens`, by rewriting `e : expr`. If this succeeds, `rewrite_at_lens` computes (by unwinding
`l`) a proof that the entire expression represented by `l.fill e` is equal to the entire expression
`l.fill f`, where `f` is the `expr` which has replaced `e` due to the rewrite. It then returns the
singleton list containing this rewrite (and the tracking data needed to reconstruct it directly). If
it fails, it just returns the empty list. -/
unsafe def rewrite_at_lens (cfg : nth_rewrite.cfg) (r : expr × Bool) (l : expr_lens) (e : expr) :
    tactic (List tracked_rewrite) := do
  let (v, pr) ← rewrite_without_new_mvars r.1 e { cfg with symm := r.2 }
  -- Now we determine whether the rewrite transforms the entire expression or not:
      if ¬rewrite_is_of_entire pr then return []
    else do
      let w := l v
      let qr ← l pr
      let s ← try_core (cfg w)
      let (w, qr) ←
        match s with
          | none => pure (w, qr)
          | some (w', qr') => do
            let qr ← mk_eq_trans qr qr'
            return (w', qr)
      return [⟨w, pure qr, l⟩]

/-- List of all rewrites of an expression `e` by `r : expr × bool`.
Here `r.1` is the substituting expression and `r.2` flags the direction of the rewrite. -/
unsafe def all_rewrites (e : expr) (r : expr × Bool) (cfg : nth_rewrite.cfg := {  }) : tactic (List tracked_rewrite) :=
  e.app_map (rewrite_at_lens cfg r)

end NthRewrite.Congr

end Tactic

