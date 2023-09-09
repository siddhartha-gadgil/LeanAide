import Lean.Meta.ExprLens
import Mathlib.Tactic
import Std

open Lean Expr 

-- TODO Check whether this function already exists
def Lean.Expr.getName! : Expr → Name
  | .lam n _ _ _ => n
  | .letE n _ _ _ _ => n
  | .forallE n _ _ _ => n
  | _               => panic! "Unable to get name for expression."

open Meta in
partial def Lean.Expr.getConvEnters (expr : Expr) (φ : Expr → MetaM α)
    (explicit? : Bool) : MetaM (Array (List String × α)) :=
  match expr with
  | .app _ _ => do
    let fn := expr.getAppFn 
    let args := expr.getAppArgs
    let fnInfo ← getFunInfo fn
    let argsWithBinderInfo := Array.zip args (fnInfo.paramInfo.map (·.isExplicit))
    let args' :=
      argsWithBinderInfo.filterMap <| fun (arg, bi) ↦
        if explicit? || (!explicit? && bi) then
          some arg
        else none
    let enterArgs ← args'.mapIdxM fun idx arg ↦ do
      let argConvEnters ← arg.getConvEnters φ explicit?
      let enterArg := (if explicit? then "@" else "") ++ s!"{idx.val + 1}"
      return argConvEnters.map <| fun (path, a) ↦ (enterArg :: path, a) 
    return (enterArgs.push #[([], ← φ expr)]).concatMap id
  | .forallE _ _ _ _ => do
    let binders := expr.getForallBinderNames |>.map (·.getRoot.toString)
    let body := expr.getForallBody
    body.getConvEnters φ explicit? >>= updatePaths binders
  | .lam _ _ _ _ 
  | .letE _ _ _ _ _ =>
    lambdaLetTelescope expr <| fun args body ↦ do
      let binders := args |>.map (·.getName!.toString) |>.toList
      body.getConvEnters φ explicit? >>= updatePaths binders
  | .mdata _ expr => getConvEnters expr φ explicit?
  | .proj _ _ struct => do
    struct.getConvEnters φ explicit? >>= updatePaths ["1"]
  | _ => return #[]
  where updatePaths (pre : List String) (entries : Array (List String × α)) : 
      MetaM <| Array (List String × α) := do
    return ( entries.map <| fun (path, a) ↦ (pre ++ path, a) ) |>.push ([], ← φ expr)

open Meta Elab Term in
#eval show TermElabM _ from do
  let stx ← `(term| ∀ x, Nat.succ x = 1) 
  let t ← Term.elabTerm stx none
  let enters ← t.getConvEnters pure (explicit? := false)
  for (path, expr) in enters do
    IO.println path
    let stx ← PrettyPrinter.delab expr
    IO.println stx.raw.reprint.get!

def Lean.Meta.DiscrTree.getSubexpressionConvMatches (d : Meta.DiscrTree α s) 
    (e : Expr) (explicit? : Bool) : MetaM (Array (List String × α)) := do
  let convEnters ← e.getConvEnters d.getMatch explicit?
  return convEnters.concatMap <| fun (path, as) ↦ as.map (path, ·) 

macro (priority := high) "enter" "[""]" : conv => `(conv| skip)

open Parser Tactic Conv
syntax (name := targeted_rw) "tgt_rw" (config)? rwRuleSeq (" at " ident)? " entering " "[" enterArg,* "]" : tactic

macro_rules
  | `(tactic| tgt_rw $[$cfg]? $rules $[at $loc]? entering [$args,*]) =>
    `(tactic| conv $[at $loc]? => enter [$args,*]; rw $[$cfg]? $rules)

example (y : ℕ) : ∀ x : ℕ, y + (x + 0) = x + y := by
  tgt_rw [Nat.add_zero] entering [x, 1, 2]
  tgt_rw [Nat.add_comm] entering [x]
  intro; rfl

-- The code below is modified from `Mathlib/Tactic/Rewrites`
-- Copyright of Scott Morrison

open Mathlib.Tactic.Rewrites

/--
Find lemmas which can rewrite the goal.

This core function returns a monadic list, to allow the caller to decide how long to search.
See also `rewrites` for a more convenient interface.
-/
-- We need to supply the current `MetavarContext` (which will be reused for each lemma application)
-- because `MLList.squash` executes lazily,
-- so there is no opportunity for `← getMCtx` to record the context at the call site.
def targetedRewritesCore (hyps : Array (Expr × Bool × Nat))
    (lemmas : Meta.DiscrTree (Name × Bool × Nat) s × Meta.DiscrTree (Name × Bool × Nat) s)
    (ctx : MetavarContext) (goal : MVarId) (target : Expr) :
    MLList MetaM RewriteResult := MLList.squash fun _ => do
  -- Get all lemmas which could match some subexpression
  let candidates := (← lemmas.1.getSubexpressionMatches target)
    ++ (← lemmas.2.getSubexpressionMatches target)

  -- Sort them by our preferring weighting
  -- (length of discriminant key, doubled for the forward implication)
  let candidates := candidates.insertionSort fun r s => r.2.2 > s.2.2

  -- Now deduplicate. We can't use `Array.deduplicateSorted` as we haven't completely sorted,
  -- and in fact want to keep some of the residual ordering from the discrimination tree.
  let mut forward : NameSet := ∅
  let mut backward : NameSet := ∅
  let mut deduped := #[]
  for (l, s, w) in candidates do
    if s then
      if ¬ backward.contains l then
        deduped := deduped.push (l, s, w)
        backward := backward.insert l
    else
      if ¬ forward.contains l then
        deduped := deduped.push (l, s, w)
        forward := forward.insert l

  trace[Tactic.rewrites.lemmas] m!"Candidate rewrite lemmas:\n{deduped}"

  -- Lift to a monadic list, so the caller can decide how much of the computation to run.
  let hyps := MLList.ofArray <| hyps.map fun ⟨hyp, _symm, weight⟩ => (Sum.inl hyp, _symm, weight)
  let lemmas := MLList.ofArray <| deduped.map fun ⟨lem, _symm, weight⟩ => (Sum.inr lem, _symm, weight)

  pure <| (hyps |>.append fun _ => lemmas).filterMapM fun ⟨lem, _symm, weight⟩ => Meta.withMCtx ctx do
    let some expr ← (match lem with
    | .inl hyp => pure (some hyp)
    | .inr lem => try? <| Meta.mkConstWithFreshMVarLevels lem) | return none
    trace[Tactic.rewrites] m!"considering {if _symm then "←" else ""}{expr}"
    let some result ← try? do goal.rewrite target expr _symm
      | return none
    return if result.mvarIds.isEmpty then
      some ⟨expr, _symm, weight, result, none, ← getMCtx⟩
    else
      -- TODO Perhaps allow new goals? Try closing them with solveByElim?
      -- A challenge is knowing what suggestions to print if we do so!
      none

/-- Find lemmas which can rewrite the goal. -/
def targetedRewrites (hyps : Array (Expr × Bool × Nat))
    (lemmas : Meta.DiscrTree (Name × Bool × Nat) s × Meta.DiscrTree (Name × Bool × Nat) s)
    (goal : MVarId) (target : Expr) (stopAtRfl : Bool := false) (max : Nat := 20)
    (leavePercentHeartbeats : Nat := 10) : MetaM (List RewriteResult) := do
  let results ← rewritesCore hyps lemmas (← getMCtx) goal target
    -- Don't report duplicate results.
    -- (TODO: we later pretty print results; save them here?)
    -- (TODO: a config flag to disable this,
    -- if distinct-but-pretty-print-the-same results are desirable?)
    |>.dedupBy (fun r => do pure <| (← Meta.ppExpr r.result.eNew).pretty)
    -- Stop if we find a rewrite after which `with_reducible rfl` would succeed.
    |>.mapM RewriteResult.computeRfl -- TODO could simply not compute this if `stopAtRfl` is False
    |>.takeUpToFirst (fun r => stopAtRfl && r.rfl? = some true)
    -- Don't use too many heartbeats.
    |>.whileAtLeastHeartbeatsPercent leavePercentHeartbeats
    -- Bound the number of results.
    |>.takeAsList max
  return match results.filter (fun r => stopAtRfl && r.rfl? = some true) with
  | [] =>
    -- TODO consider sorting the results,
    -- e.g. if we use solveByElim to fill arguments,
    -- prefer results using local hypotheses.
    results
  | results => results

open Elab Term Syntax Parser Tactic Std.Tactic.TryThis in
def addTargetedRewriteSuggestion (ref : Syntax) (rules : List (Expr × Bool))
  (path : List String) (type? : Option Expr := none) (loc? : Option Ident := none)
  (origSpan? : Option Syntax := none) :
    TermElabM Unit := do
  let rules_stx := TSepArray.ofElems <| ← rules.toArray.mapM fun ⟨e, _symm⟩ => do
    let t ← delabToRefinableSyntax e
    if _symm then `(rwRule| ← $t:term) else `(rwRule| $t:term)
  let env ← getEnv
  let pathArgs : List (TSyntax ``enterArg) ← path.mapM fun arg ↦ do
    let .ok enter_arg := Parser.runParserCategory env ``enterArg arg | failure
    return ⟨enter_arg⟩
  let path_stx := TSepArray.ofElems pathArgs.toArray
  let tac ← `(tactic| tgt_rw [$rules_stx,*] $[at $loc?]? entering [$path_stx,*])

  let mut tacMsg :=
    let rulesMsg := MessageData.sbracket <| MessageData.joinSep
      (rules.map fun ⟨e, _symm⟩ => (if _symm then "← " else "") ++ m!"{e}") ", "
    if let some loc := loc? then
      m!"tgt_rw {rulesMsg} at {loc} entering {path}"
    else
      m!"tgt_rw {rulesMsg} entering {path}"
  let mut extraMsg := ""
  if let some type := type? then
    tacMsg := tacMsg ++ m!"\n-- {type}"
    extraMsg := extraMsg ++ s!"\n-- {← PrettyPrinter.ppExpr type}"
  addSuggestion ref tac (suggestionForMessage? := tacMsg)
    (extraMsg := extraMsg) (origSpan? := origSpan?)

open Lean.Parser.Tactic

/--
`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [←h]`.
`rw?!` is the "I'm feeling lucky" mode, and will run the first rewrite it finds.
-/
syntax (name := tgt_rw?) "tgt_rw?" (" at" ident)? : tactic

-- open Elab.Tactic Elab Tactic in
-- elab_rules : tactic |
--   `(tactic| tgt_rw?%$tk) => do
--   let lems ← rewriteLemmas.get -- This can be replaced with a custom cache
--   reportOutOfHeartbeats `rewritesConv tk
--   let goal ← getMainGoal
--   -- TODO fix doc of core to say that * fails only if all failed
--   withLocation (Location.targets #[] true)
--     fun f => do
--       let some a ← f.findDecl? | return
--       if a.isImplementationDetail then return
--       let target ← instantiateMVars (← f.getType)
--       let results ← rewritesConv lems goal target (stop_at_rfl := false)
--       reportOutOfHeartbeats `rewritesConv tk
--       if results.isEmpty then
--         throwError "Could not find any lemmas which can rewrite the hypothesis {
--           ← f.getUserName}"
--       for (path, r) in results do
--         addTargetedRewriteSuggestion tk [(← Meta.mkConstWithFreshMVarLevels r.name, r.symm)] path
--           r.result.eNew (origSpan? := ← getRef)
--     -- See https://github.com/leanprover/lean4/issues/2150
--     do withMainContext do
--       let target ← instantiateMVars (← goal.getType)
--       let results ← rewritesConv lems goal target (stop_at_rfl := true)
--       reportOutOfHeartbeats `rewritesConv tk
--       if results.isEmpty then
--         throwError "Could not find any lemmas which can rewrite the goal"
--       for (path, r) in results do
--         let newGoal := if r.rfl? = some true then Expr.lit (.strVal "no goals") else r.result.eNew
--         addTargetedRewriteSuggestion tk [(← Meta.mkConstWithFreshMVarLevels r.name, r.symm)] path
--           newGoal (origSpan? := ← getRef)
--     (λ _ => throwError "Failed to find a rewrite for some location")                                                                                                                                   