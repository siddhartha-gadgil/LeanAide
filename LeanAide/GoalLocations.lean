import Lean.Meta.ExprLens
import Mathlib.Tactic
import Init.Conv
import Std

open Lean Expr 

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
    (ctx : MetavarContext) (goal : MVarId) (target : Expr) (explicit? := false) :
    MLList MetaM (List String × RewriteResult) := MLList.squash fun _ => do
  -- Get all lemmas which could match some subexpression
  let candidates := (← lemmas.1.getSubexpressionConvMatches target explicit?)
    ++ (← lemmas.2.getSubexpressionConvMatches target explicit?)

  -- Sort them by our preferring weighting
  -- (length of discriminant key, doubled for the forward implication)
  let candidates := candidates.insertionSort fun r s => r.2.2.2 > s.2.2.2

  -- Now deduplicate. We can't use `Array.deduplicateSorted` as we haven't completely sorted,
  -- and in fact want to keep some of the residual ordering from the discrimination tree.
  let mut forward : NameSet := ∅
  let mut backward : NameSet := ∅
  let mut deduped := #[]
  for (p, l, s, w) in candidates do
    if s then
      if ¬ backward.contains l then
        deduped := deduped.push (p, l, s, w)
        backward := backward.insert l
    else
      if ¬ forward.contains l then
        deduped := deduped.push (p, l, s, w)
        forward := forward.insert l

  trace[Tactic.rewrites.lemmas] m!"Candidate rewrite lemmas:\n{deduped}"

  -- let hyps' : Array (List String × Expr × Bool × ℕ) ← hyps.concatMapM fun ⟨hyp, _symm, weight⟩ ↦ do
  --   let enters ← hyp.getConvEnters pure explicit?
  --   return enters.map fun (path, subhyp) ↦ (path, subhyp, _symm, weight)
  
  -- Lift to a monadic list, so the caller can decide how much of the computation to run.
  -- let hyps := MLList.ofArray <| hyps'.map fun ⟨path, hyp, _symm, weight⟩ => (path, Sum.inl hyp, _symm, weight)
  let lemmas := MLList.ofArray <| deduped.map fun ⟨path, lem, _symm, weight⟩ => (path, Sum.inr lem, _symm, weight)

  pure <| (/-hyps |>.append fun _ =>-/ lemmas).filterMapM fun ⟨path, lem, _symm, weight⟩ => Meta.withMCtx ctx do
    let some expr ← (match lem with
    | .inl hyp => pure (some hyp)
    | .inr lem => try? <| Meta.mkConstWithFreshMVarLevels lem) | return none
    trace[Tactic.rewrites] m!"considering {if _symm then "←" else ""}{expr}"
    let some result ← try? do goal.rewrite target expr _symm
      | return none
    return if result.mvarIds.isEmpty then
      some ⟨path, expr, _symm, weight, result, none, ← getMCtx⟩
    else
      -- TODO Perhaps allow new goals? Try closing them with solveByElim?
      -- A challenge is knowing what suggestions to print if we do so!
      none

/-- Find lemmas which can rewrite the goal. -/
def targetedRewrites (hyps : Array (Expr × Bool × Nat))
    (lemmas : Meta.DiscrTree (Name × Bool × Nat) s × Meta.DiscrTree (Name × Bool × Nat) s)
    (goal : MVarId) (target : Expr) (stopAtRfl : Bool := false) (max : Nat := 20)
    (leavePercentHeartbeats : Nat := 10) : MetaM (List (List String × RewriteResult)) := do
  let results ← targetedRewritesCore hyps lemmas (← getMCtx) goal target
    -- Don't report duplicate results.
    -- (TODO: we later pretty print results; save them here?)
    -- (TODO: a config flag to disable this,
    -- if distinct-but-pretty-print-the-same results are desirable?)
    |>.dedupBy (fun (_, r) => do pure <| (← Meta.ppExpr r.result.eNew).pretty)
    -- Stop if we find a rewrite after which `with_reducible rfl` would succeed.
    |>.mapM (fun (path, r) ↦ do pure (path, ← r.computeRfl)) -- TODO could simply not compute this if `stopAtRfl` is False
    |>.takeUpToFirst (fun (_, r) => stopAtRfl && r.rfl? = some true)
    -- -- Don't use too many heartbeats.
    |>.whileAtLeastHeartbeatsPercent leavePercentHeartbeats
    -- -- Bound the number of results.
    |>.takeAsList max
  return match results.filter (fun (_, r) => stopAtRfl && r.rfl? = some true) with
  | [] =>
    -- TODO consider sorting the results,
    -- e.g. if we use solveByElim to fill arguments,
    -- prefer results using local hypotheses.
    results
  | results => results

def runParserDescr (descr : ParserDescr) (input : String) (fileName : String := "<input>") : MetaM Syntax := do
  let env ← getEnv
  let categories := (parserExtension.getState env).categories
  let p ← compileParserDescr categories descr
  let ictx := mkInputContext input fileName
  let s := p.fn.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    failure
  else if input.atEnd s.pos then
    return s.stxStack.back
  else
    failure

open Elab Term Syntax Parser Tactic Std.Tactic.TryThis in
def addTargetedRewriteSuggestion (ref : Syntax) (rules : List (Expr × Bool))
  (path : List String) (type? : Option Expr := none) (loc? : Option Ident := none)
  (origSpan? : Option Syntax := none) :
    TermElabM Unit := do
  let rules_stx := TSepArray.ofElems <| ← rules.toArray.mapM fun ⟨e, _symm⟩ => do
    let t ← delabToRefinableSyntax e
    if _symm then `(rwRule| ← $t:term) else `(rwRule| $t:term)
  let pathArgs : List (TSyntax ``enterArg) ← path.mapM fun arg ↦ do
    return ⟨← runParserDescr Conv.enterArg arg⟩
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
syntax (name := tgt_rewrites) "tgt_rw?" "!"? (ppSpace location)? : tactic

open Meta Elab.Tactic Elab Tactic in
elab_rules : tactic |
    `(tactic| tgt_rw?%$tk $[!%$lucky]? $[$loc]?) => do
  let lems ← rewriteLemmas.get
  reportOutOfHeartbeats `targetedRewrites tk
  let goal ← getMainGoal
  -- TODO fix doc of core to say that * fails only if all failed
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    fun f => do
      let some a ← f.findDecl? | return
      if a.isImplementationDetail then return
      let target ← instantiateMVars (← f.getType)
      let hyps ← localHypotheses (except := [f])
      let results ← targetedRewrites hyps lems goal target (stopAtRfl := false)
      reportOutOfHeartbeats `targetedRewrites tk
      let nm ← f.getUserName
      if results.isEmpty then
        throwError "Could not find any lemmas which can rewrite the hypothesis {nm}"
      for (path, r) in results do withMCtx r.mctx do
        addTargetedRewriteSuggestion tk [(r.expr, r.symm)] path
          r.result.eNew (loc? := .some (.mk <| .ident .none "".toSubstring nm [])) 
          (origSpan? := ← getRef)
      if lucky.isSome then
        match results[0]? with
        | some (path, r) => do
            setMCtx r.mctx
            let replaceResult ← goal.replaceLocalDecl f r.result.eNew r.result.eqProof
            replaceMainGoal (replaceResult.mvarId :: r.result.mvarIds)
        | _ => failure
    -- See https://github.com/leanprover/lean4/issues/2150
    do withMainContext do
      let target ← instantiateMVars (← goal.getType)
      let hyps ← localHypotheses
      let results ← targetedRewrites hyps lems goal target (stopAtRfl := true)
      reportOutOfHeartbeats `targetedRewrites tk
      if results.isEmpty then
        throwError "Could not find any lemmas which can rewrite the goal"
      for (path, r) in results do withMCtx r.mctx do
        let newGoal := if r.rfl? = some true then Expr.lit (.strVal "no goals") else r.result.eNew
        addTargetedRewriteSuggestion tk [(r.expr, r.symm)] path
          newGoal (origSpan? := ← getRef)
      if lucky.isSome then
        match results[0]? with
        | some (path, r) => do
            setMCtx r.mctx
            replaceMainGoal
              ((← goal.replaceTargetEq r.result.eNew r.result.eqProof) :: r.result.mvarIds)
            evalTactic (← `(tactic| try rfl))
        | _ => failure
    (fun _ => throwError "Failed to find a rewrite for some location")

@[inherit_doc tgt_rewrites] macro "tgt_rw?!" h:(ppSpace location)? : tactic =>
  `(tactic| tgt_rw? ! $[$h]?)
@[inherit_doc tgt_rewrites] macro "tgt_rw!?" h:(ppSpace location)? : tactic =>
  `(tactic| tgt_rw? ! $[$h]?)

example : 1 = 1 := by
  tgt_rw?
  sorry