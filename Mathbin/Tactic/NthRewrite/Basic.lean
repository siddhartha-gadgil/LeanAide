/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Keeley Hoek, Scott Morrison
-/
import Mathbin.Meta.ExprLens

namespace Tactic

open Expr

namespace NthRewrite

/-- Configuration options for nth_rewrite. -/
unsafe structure cfg extends RewriteCfg where
  try_simp : Bool := false
  discharger : tactic Unit := skip
  -- Warning: rewrite_search can't produce tactic scripts when the simplifier is used.
  simplifier : expr → tactic (expr × expr) := fun e => failed

/-- A data structure to track rewrites of subexpressions.
The field `exp` contains the new expression,
while `proof` contains a proof that `exp` is equivalent to the expression that was rewritten. -/
unsafe structure tracked_rewrite where
  exp : expr
  proof : tactic expr
  -- If `addr` is not provided by the underlying implementation of `nth_rewrite` (i.e. kabstract)
  -- `rewrite_search` will not be able to produce tactic scripts.
  addr : Option (List ExprLens.Dir)

namespace TrackedRewrite

/-- Postprocess a tracked rewrite into a pair
of a rewritten expression and a proof witness of the rewrite. -/
unsafe def eval (rw : tracked_rewrite) : tactic (expr × expr) := do
  let prf ← rw.proof
  return (rw, prf)

end TrackedRewrite

end NthRewrite

end Tactic

