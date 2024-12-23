import Lean
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.PermuteGoals
import Mathlib.Tactic.Classical

open Lean Elab Parser Term Meta Tactic

syntax (name := seq) "seq" tacticSeq : tactic

section Source
  -- modified from `Lean.Elab.Tactic.Simp`
  def traceSimpCall' (stx : Syntax) (usedSimps : Simp.UsedSimps) : MetaM Syntax := do
    let mut stx := stx
    if stx[3].isNone then
      stx := stx.setArg 3 (mkNullNode #[mkAtom "only"])
    let mut args := #[]
    let mut localsOrStar := some #[]
    let lctx ← getLCtx
    let env ← getEnv
    for (thm, _) in usedSimps.toArray.qsort (·.2 < ·.2) do
      match thm with
      | .decl declName => -- global definitions in the environment
        if env.contains declName && !simpOnlyBuiltins.contains declName then
          args := args.push (← `(Parser.Tactic.simpLemma| $(mkIdent (← unresolveNameGlobal declName)):ident))
      | .fvar fvarId => -- local hypotheses in the context
        if let some ldecl := lctx.get? fvarId then
          localsOrStar := localsOrStar.flatMap fun locals =>
            if !ldecl.userName.isInaccessibleUserName &&
                (lctx.findFromUserName? ldecl.userName).get!.fvarId == ldecl.fvarId then
              some (locals.push ldecl.userName)
            else
              none
        -- Note: the `if let` can fail for `simp (config := {contextual := true})` when
        -- rewriting with a variable that was introduced in a scope. In that case we just ignore.
      | .stx _ thmStx => -- simp theorems provided in the local invocation
        args := args.push ⟨thmStx⟩
      | .other _ => -- Ignore "special" simp lemmas such as constructed by `simp_all`.
        pure ()     -- We can't display them anyway.
    if let some locals := localsOrStar then
      args := args ++ (← locals.mapM fun id => `(Parser.Tactic.simpLemma| $(mkIdent id):ident))
    else
      args := args.push ⟨(← `(Parser.Tactic.simpStar| *))⟩
    let argsStx := if args.isEmpty then #[] else #[mkAtom "[", (mkAtom ",").mkSep args, mkAtom "]"]
    stx := stx.setArg 4 (mkNullNode argsStx)
    return stx

  def dsimpLocation' (ctx : Simp.Context) (loc : Location) : TacticM Syntax := do
    match loc with
    | Location.targets hyps simplifyTarget =>
      withMainContext do
        let fvarIds ← getFVarIds hyps
        go fvarIds simplifyTarget
    | Location.wildcard =>
      withMainContext do
        go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
  where
    go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Syntax := do
      let mvarId ← getMainGoal
      let (result?, usedSimps) ← dsimpGoal mvarId ctx (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIdsToSimp)
      match result? with
      | none => replaceMainGoal []
      | some mvarId => replaceMainGoal [mvarId]
      traceSimpCall' (← getRef) usedSimps

  def getMainGoal' : TacticM (MVarId × List MVarId) := do
  loop (← getGoals)
    where
  loop : List MVarId → TacticM (MVarId × List MVarId)
    | [] => throwNoGoalsToBeSolved
    | mvarId :: mvarIds => do
      if (← mvarId.isAssigned) then
        loop mvarIds
      else
        setGoals (mvarId :: mvarIds)
        return (mvarId, mvarIds)

/--
  Searches for a metavariable `g` s.t. `tag` is its exact name.
  If none then searches for a metavariable `g` s.t. `tag` is a suffix of its name.
  If none, then it searches for a metavariable `g` s.t. `tag` is a prefix of its name. -/
def findTag? (mvarIds : List MVarId) (tag : Name) : TacticM (Option MVarId) := do
  match (← mvarIds.findM? fun mvarId => return tag == (← mvarId.getDecl).userName) with
  | some mvarId => return mvarId
  | none =>
  match (← mvarIds.findM? fun mvarId => return tag.isSuffixOf (← mvarId.getDecl).userName) with
  | some mvarId => return mvarId
  | none => mvarIds.findM? fun mvarId => return tag.isPrefixOf (← mvarId.getDecl).userName

def getCaseGoals (tag : TSyntax `Lean.flatMaperIdent) : TacticM (MVarId × List MVarId) := do
  let gs ← getUnsolvedGoals
  let g ← if let `(Lean.flatMaperIdent| $tag:ident) := tag then
    let tag := tag.getId
    let some g ← findTag? gs tag | throwError "tag not found"
    pure g
  else
    getMainGoal
  return (g, gs.erase g)

def matchAltTac := Term.matchAlt (rhsParser := matchRhs)

end Source

def traceGoalsAt (stx : TSyntax `tactic) : TacticM Unit := do
  let gs ← getUnsolvedGoals
  withRef stx <| addRawTrace (goalsToMessageData gs)

def traceTacticCallAt (stx : TSyntax `tactic) (tac : TSyntax `tactic) : TacticM Unit := do
  withRef stx <| addRawTrace m!"[TACTIC] {tac}"

#check Split.applyMatchSplitter

partial def evalTacticWithTrace : TSyntax `tactic → TacticM Unit
  /- Dealing with bracketing -/
  | `(tactic| { $[$tacs]* }) => do
    for tac in tacs do
      evalTacticWithTrace tac
  | `(tactic| ( $[$tacs]* )) => do
    for tac in tacs do
      evalTacticWithTrace tac
  /- Dealing with focused goals -/
  | `(tactic| · $[$tacs]*) => do
    let (mainGoal, otherGoals) ← getMainGoal'
    setGoals [mainGoal]
    for tac in tacs do
      evalTacticWithTrace tac
    setGoals otherGoals
  | `(tactic| focus $[$tacs]*) => do
    let (mainGoal, otherGoals) ← getMainGoal'
    setGoals [mainGoal]
    for tac in tacs do
      evalTacticWithTrace tac
    setGoals otherGoals
  /- Handle trace for the `classical` tactic -/
  | `(tactic| classical $[$tacs]*) => do
      modifyEnv Meta.instanceExtension.pushScope
      Meta.addInstance ``Classical.propDecidable .local 10
      try for tac in tacs do evalTacticWithTrace tac
      finally modifyEnv Meta.instanceExtension.popScope
   /- Trace `simp` calls with the complete list of theorems used -/
  | stx@`(tactic| simp%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) => do
    traceGoalsAt stx
    let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
    let usedSimps ← dischargeWrapper.with fun discharge? =>
      simpLocation ctx discharge? (expandOptLocation stx.raw[5])
    traceTacticCallAt stx ⟨← traceSimpCall' stx usedSimps⟩
    traceGoalsAt stx
  | stx@`(tactic| simp_all%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?) => do
    traceGoalsAt stx
    let { ctx, .. } ← mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
    let (result?, usedSimps) ← simpAll (← getMainGoal) ctx
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    traceTacticCallAt stx ⟨← traceSimpCall' stx usedSimps⟩
    traceGoalsAt stx
  | stx@`(tactic| dsimp%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?) => do
    traceGoalsAt stx
    let { ctx, .. } ← withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
    traceTacticCallAt stx ⟨← dsimpLocation' ctx (expandOptLocation stx.raw[5])⟩
    traceGoalsAt stx
  /- Treat a rewrite sequence as a sequence of individual rewrites, with a trace provided at each step -/
  | `(tactic| rw $[$cfg]? [$rs,*] $[$loc]?) => do
    for r in (rs : TSyntaxArray `Lean.Parser.Tactic.rwRule) do
      traceGoalsAt ⟨r.raw⟩
      let rtac ← `(tactic| rw $[$cfg]? [$r] $[$loc]?)
      evalTactic rtac
      traceTacticCallAt ⟨r.raw⟩ rtac
      traceGoalsAt ⟨r.raw⟩
  | `(tactic| erw [$rs,*] $[$loc]?) => do
    for r in (rs : TSyntaxArray `Lean.Parser.Tactic.rwRule) do
      traceGoalsAt ⟨r.raw⟩
      let rtac ← `(tactic| erw [$r] $[$loc]?)
      evalTactic rtac
      traceTacticCallAt ⟨r.raw⟩ rtac
      traceGoalsAt ⟨r.raw⟩
  | `(tactic| rwa [$rs,*] $[$loc]?) => do
    for r in (rs : TSyntaxArray `Lean.Parser.Tactic.rwRule) do
      traceGoalsAt ⟨r.raw⟩
      let rtac ← `(tactic| rw [$r] $[$loc]?)
      evalTactic rtac
      traceTacticCallAt ⟨r.raw⟩ rtac
      traceGoalsAt ⟨r.raw⟩
    `(tactic| assumption) >>= evalTactic ∘ TSyntax.raw
  /- Annotate `apply` and `exact` applications with the type information -/
  | stx@`(tactic| apply $v) => do
    traceGoalsAt stx
    evalTactic stx
    let trm ← Tactic.elabTerm v none
    let typ ← inferType trm
    let (mainGoal, otherGoals) ← getMainGoal'
    let newGoals ← mainGoal.apply trm
    setGoals <| newGoals ++ otherGoals
    let typ ← instantiateMVars typ
    let typStx ← PrettyPrinter.delab typ
    `(tactic| apply ($v : $typStx)) >>= traceTacticCallAt stx
    traceGoalsAt stx
  | stx@`(tactic| exact $v) => do
    traceGoalsAt stx
    evalTactic stx
    let trm ← Tactic.elabTerm v none
    let typ ← inferType trm
    let typStx ← PrettyPrinter.delab typ
    `(tactic| exact ($v : $typStx)) >>= traceTacticCallAt stx
    traceGoalsAt stx
  /- Handling `match`, `induction` and `cases` -/
  | stx@`(tactic| case $[$tag $hs*]|* =>%$arr $tac:tacticSeq) => do
    for tag in tag, h in hs do
      traceGoalsAt ⟨arr⟩
      traceTacticCallAt ⟨arr⟩ stx -- TODO (unimportant) remove the `tacticSeq` from `stx`
      let (g, _) ← getCaseGoals tag
      withRef arr <| addRawTrace (goalsToMessageData [g])
    let stx ← `(tactic| case $[$tag $hs*]|* =>%$arr seq $tac:tacticSeq)
    evalTactic stx.raw
  | stx@`(tactic| case' $[$tag $hs*]|* =>%$arr $tac:tacticSeq) => do
    for tag in tag, h in hs do
      traceGoalsAt ⟨arr⟩
      traceTacticCallAt ⟨arr⟩ stx -- TODO (unimportant) remove the `tacticSeq` from `stx`
      let (g, _) ← getCaseGoals tag
      withRef arr <| addRawTrace (goalsToMessageData [g])
    let stx ← `(tactic| case' $[$tag $hs*]|* =>%$arr seq $tac:tacticSeq)
  | `(tactic| induction $[$ts],* $[using $id:ident]?  $[generalizing $gs*]? with $[$tac]? $is*) => do
    let is' : TSyntaxArray ``inductionAlt ←
      is.mapM <|
        fun
          | `(inductionAlt| $il* => $ts:tacticSeq) => `(inductionAlt| $il* => seq $ts)
          | i => return ⟨i⟩
    let stx' ← `(tactic| induction $[$ts],* $[using $id:ident]?  $[generalizing $gs*]? with $[$tac]? $is'*)
    evalTactic stx'
  | `(tactic| cases $[$cs],* $[using $id:ident]? with $[$tac]? $is*) => do
    let is' : TSyntaxArray ``inductionAlt ←
      is.mapM <|
        fun
          | `(inductionAlt| $il* => $ts:tacticSeq) => `(inductionAlt| $il* => seq $ts)
          | i => return ⟨i⟩
    let stx' ← `(tactic| cases $[$cs],* $[using $id:ident]? with $[$tac]? $is'*)
    evalTactic stx'
  | `(tactic| match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*) => do
    let alts' : TSyntaxArray ``matchAlt ←
      alts.mapM <|
        fun
          | `(matchAltTac| | $[$pats,*]|* => $rhs:tacticSeq) => do
              let alt ← `(matchAltTac| | $[$pats,*]|* => seq $rhs)
              return ⟨alt⟩
          | alt =>  return ⟨alt⟩
      let stx' ← `(tactic| match $[$gen]? $[$motive]? $discrs,* with $alts':matchAlt*)
      evalTactic stx'
  /- Display the expected type in `have` and `let` statements -/
  | stx@`(tactic| have $[$x:ident]? := $prf) => do
    traceGoalsAt stx
    evalTactic stx
    let trm ← Tactic.elabTerm prf none
    let typ ← inferType trm
    let typStx ← PrettyPrinter.delab typ
    `(tactic| have $[$x:ident]? : $typStx := $prf) >>= traceTacticCallAt stx
    traceGoalsAt stx
  | stx@`(tactic| let $x:ident := $val) => do
    traceGoalsAt stx
    evalTactic stx
    let trm ← Tactic.elabTerm val none
    let typ ← inferType trm
    let typStx ← PrettyPrinter.delab typ
    `(tactic| let $x:ident : $typStx := $val) >>= traceTacticCallAt stx
    traceGoalsAt stx
  /- Otherwise, evaluate the tactic normally -/
  | stx@`(tactic| $tac) => do
    traceGoalsAt stx
    evalTactic tac
    traceTacticCallAt stx tac
    traceGoalsAt stx

@[tactic seq]
def traceSequence : Tactic := fun s => do
  -- Leonardo de Moura's code for extracting the list of tactics
  match s with
  | `(tactic| seq $[$tacs]*) =>
    for tac in tacs do
      evalTacticWithTrace tac
  | _ => evalTactic <| ← `(tactic.sorry)

-- an example of the `seq` tactic
example (h : x = y) : 0 + x = y ∧ 1 = 1 := by
  seq
    rw [Nat.zero_add, (h : x = y)]
  refine' ⟨_, _⟩
  focus
    rw [←h, h]
  · rfl

-- a deep copy of Lean's `by` tactic, called `by'`
syntax (name := byTactic') "by' " tacticSeq : term

@[term_elab byTactic'] def elabByTactic' : TermElab := fun stx expectedType? => do
  match expectedType? with
  | some expectedType =>
    let mvar ← mkFreshExprMVar expectedType MetavarKind.syntheticOpaque
    let mvarId := mvar.mvarId!
    let ref ← getRef
    registerSyntheticMVar ref mvarId <| SyntheticMVarKind.tactic stx (← saveContext)
    return mvar
  | none =>
    tryPostpone
    throwError ("invalid 'by\'' tactic, expected type has not been provided")

example : 1 + 1 = 2 := by' -- the new `by'` syntax can be used to replace `by`
  focus
  rfl

-- intercepting the `by` tactic to output intermediate trace data
-- the `by'` clone is needed here to avoid infinite recursion
macro_rules
  | `(by $t) => `(by' seq $t)

section Test

set_option linter.unreachableTactic false

-- the `by` tactic now generates trace data by default
example (h : x = y) : x + 0 + x = x + y ∧ 1 = 1 := by
  have := (rfl : 1 = 1)
  let a := 5
  simp at this
  refine' ⟨_, _⟩
  · apply Eq.symm
    apply Eq.symm
    erw [h, ← h, h, ← h]
    simp_all
  · apply Eq.symm
    apply Eq.symm
    subst h
    rfl
  done

example : ∀ n : Nat, n = n := by
  intro n
  let x : ∀ m : ℕ, m = m := by
    intro a
    rfl
  match n with
  | .zero => rfl
  | .succ _ => rfl

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨x, y⟩
    constructor
    · assumption
    · assumption
  · intro ⟨_, _⟩
    constructor
    · assumption
    · assumption

example : ∀ n : Nat, n = n := by
  intro n
  induction n
  case zero => rfl
  case succ _ ih => simp

example : ∀ n : Nat, n + n = n + n := by
  intro n
  induction n with
    | zero => rfl
    | succ _ _ => rfl

example : ∀ n : Nat, n + n = n + n := by
  intro n
  cases n with
    | zero =>
      let h := (rfl : 1 = 1)
      rfl
    | succ _ => rfl

example : ∀ n : Nat, n + n = n + n := by
  intro n
  match n with
    | .zero => rfl
    | .succ _ => rfl

end Test
