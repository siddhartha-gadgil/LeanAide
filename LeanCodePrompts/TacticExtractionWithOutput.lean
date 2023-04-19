import Lean
import LeanCodePrompts.TacticExtractionOutputCache
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.PermuteGoals
import Mathlib.Tactic.Classical

open Lean Elab Parser Term Meta Tactic

section Misc

  section Utils
  
  def evalTacticM (stx : TacticM <| TSyntax `tactic) : TacticM Unit :=
    stx >>= evalTactic ∘ TSyntax.raw

  def Lean.TSyntax.succ : TSyntax `num → TSyntax `num :=
    fun nm ↦ Syntax.mkNumLit <| toString nm.getNat.succ

  def matchAltTac := Term.matchAlt (rhsParser := matchRhs)

  end Utils

  section Source

    section Simp

    -- modified from `Lean.Elab.Tactic.Simp`
      def traceSimpCall' (stx : Syntax) (usedSimps : Simp.UsedSimps) : MetaM <| TSyntax `tactic := do
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
            if let some ldecl := lctx.find? fvarId then
              localsOrStar := localsOrStar.bind fun locals =>
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
        return ⟨stx⟩

      def dsimpLocation' (ctx : Simp.Context) (loc : Location) (stx : Syntax) : TacticM <| TSyntax `tactic := do
        match loc with
        | Location.targets hyps simplifyTarget =>
          withMainContext do
            let fvarIds ← getFVarIds hyps
            go fvarIds simplifyTarget
        | Location.wildcard =>
          withMainContext do
            go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
      where
        go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM <| TSyntax `tactic := do
          let mvarId ← getMainGoal
          let (result?, usedSimps) ← dsimpGoal mvarId ctx (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIdsToSimp)
          match result? with
          | none => replaceMainGoal []
          | some mvarId => replaceMainGoal [mvarId]
          traceSimpCall' stx usedSimps

        end Simp

  end Source

  section Logging

  def logTacticSnapshot (depth : ℕ) (tac : TacticM <| TSyntax `tactic) (ref : Option Syntax) : TacticM Unit := do
    let goalsBefore ← getUnsolvedGoals
    let strGoalsBefore ← MessageData.toString <| ← addMessageContext <| goalsToMessageData goalsBefore
    evalTacticM <| tac
    let goalsAfter ← getUnsolvedGoals
    let strGoalsAfter ← MessageData.toString <| ← addMessageContext <| goalsToMessageData goalsAfter
    let snap : TacticSnapshot := ⟨depth, strGoalsBefore, ← tac, strGoalsAfter, ref⟩
    tacticSnapRef.push snap

  elab "trace_tactic_snapshots" : tactic => do
    let snaps ← tacticSnapRef.get
    for snap in snaps do
      match snap.ref with
      | .some ref =>
       withRef ref <| addRawTrace snap.goalsBefore
       withRef ref <| addRawTrace m!"[TACTIC] {snap.tactic}"
       withRef ref <| addRawTrace snap.goalsAfter
      | none => continue
      
  def TacticSnapshot.toJson : TacticSnapshot → IO Json
    | ⟨depth, goalsBefore, tac, goalsAfter, _⟩ => do
      return .mkObj <| [
        ("depth", depth),
        ("goals_before", goalsBefore),
        ("tactic", ← do
          let .some s ← pure tac.raw.reprint | throw <| IO.userError "Failed to print syntax while exporting snapshot to Json."
          return s),
        ("goals_after", goalsAfter)
      ]

  def outputLocation : System.FilePath := 
    "."/"data"/"tactics"/"test.json"
  
  elab "log_and_clear_ref" : tactic => do
    let snaps ← tacticSnapRef.get
    let jsnaps ← snaps.mapM (TacticSnapshot.toJson ·)
    let h ← IO.FS.Handle.mk outputLocation IO.FS.Mode.append false
    h.putStr <| Json.pretty <| Json.arr jsnaps
    tacticSnapRef.set #[]

  end Logging

end Misc

syntax (name := snap) "snap" num tactic : tactic
syntax (name := seq) "seq" num tacticSeq : tactic

macro_rules
  | `(tactic| seq $n $[$tacs]*) => do
    let tacs' ← tacs.mapM <|
      fun tac ↦ `(tactic| snap $n $tac)
    `(tactic| {$[$tacs']*})

@[tactic seq] def traceSeq : Tactic
  | `(tacticSeq| seq $n $[$tacs]*) => do
    -- withoutModifyingState <| logTacticSnapshot n.getNat <| ← `(tactic| {$[$tacs]*} )
    dbg_trace n
    for tac in tacs do
      evalTacticM `(tactic| snap $n.succ $tac)
  | _ => panic! "Invalid `seq` format."

@[tactic snap] partial def traceTacticSnap : Tactic
| `(tactic| snap $n $t) =>
  match t with
  | `(tactic| focus $[$tacs]*) => do
    withoutModifyingState <| logTacticSnapshot n.getNat `(tactic| focus $[$tacs]*) none
    evalTacticM `(tactic| focus seq $n.succ $[$tacs]*)
  | `(tactic| · $[$tacs]*) => do
    withoutModifyingState <| logTacticSnapshot n.getNat `(tactic| · $[$tacs]*) none
    evalTacticM `(tactic| · seq $n.succ $[$tacs]*)
  | `(tactic| {$[$tacs]*}) => do
    withoutModifyingState <| logTacticSnapshot n.getNat `(tactic| {$[$tacs]*}) none
    evalTacticM `(tactic| {seq $n.succ $[$tacs]*})
  | `(tactic| ($[$tacs]*)) => do
    withoutModifyingState <| logTacticSnapshot n.getNat `(tactic| ($[$tacs]*)) none
    evalTacticM `(tactic| (seq $n.succ $[$tacs]*))
  | `(tactic| classical $[$tacs]*) => do
    withoutModifyingState <| logTacticSnapshot n.getNat `(tactic| classical $[$tacs]*) none
    evalTacticM `(tactic| classical seq $n.succ $[$tacs]*)
  | stx@`(tactic| simp%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) => do
    let usedSimps ← withoutModifyingState <| do
      let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
      dischargeWrapper.with fun discharge? =>
        simpLocation ctx discharge? (expandOptLocation stx.raw[5])
    logTacticSnapshot n.getNat (traceSimpCall' stx usedSimps) stx
  | stx@`(tactic| simp_all%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?) => do
    let usedSimps ← withoutModifyingState <| do
      let { ctx, .. } ← mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
      Prod.snd <$> simpAll (← getMainGoal) ctx
    logTacticSnapshot n.getNat (traceSimpCall' stx usedSimps) stx
  -- TODO Fix `dsimp`
  | stx@`(tactic| dsimp%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?) => do
    let c ← withoutModifyingState <| do
      let { ctx, .. } ← withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
      dsimpLocation' ctx (expandOptLocation stx.raw[5]) stx
    logTacticSnapshot n.getNat (pure c) stx
  | `(tactic| rw $[$cfg]? [$rs,*] $[$loc]?) => do
    for r in (rs : TSyntaxArray `Lean.Parser.Tactic.rwRule) do
      logTacticSnapshot n.getNat `(tactic| rw $[$cfg]? [$r] $[$loc]?) r
  | `(tactic| erw [$rs,*] $[$loc]?) => do
    for r in (rs : TSyntaxArray `Lean.Parser.Tactic.rwRule) do
      logTacticSnapshot n.getNat `(tactic| erw [$r] $[$loc]?) r
  | `(tactic| rwa%$tk [$rs,*] $[$loc]?) => do
    for r in (rs : TSyntaxArray `Lean.Parser.Tactic.rwRule) do
      logTacticSnapshot n.getNat `(tactic| rw [$r] $[$loc]?) r
    logTacticSnapshot n.getNat `(tactic| assumption) tk
  | stx@`(tactic| case $[$tag $hs*]|* =>%$arr $tac:tacticSeq) => do
    logTacticSnapshot n.getNat `(tactic| case $[$tag $hs*]|* =>%$arr seq $n.succ $tac:tacticSeq) stx
  | stx@`(tactic| case' $[$tag $hs*]|* =>%$arr $tac:tacticSeq) => do
    logTacticSnapshot n.getNat `(tactic| case' $[$tag $hs*]|* =>%$arr seq $n.succ $tac:tacticSeq) stx
  | `(tactic| induction $[$ts],* $[using $id:ident]?  $[generalizing $gs*]? with $[$tac]? $is*) => do
    let is' : TSyntaxArray ``inductionAlt ←
      is.mapM <|
        fun
          | `(inductionAlt| $il* => $ts:tacticSeq) => `(inductionAlt| $il* => seq $n.succ $ts)
          | i => return ⟨i⟩
    logTacticSnapshot n.getNat `(tactic| induction $[$ts],* $[using $id:ident]?  $[generalizing $gs*]? with $[$tac]? $is'*) none
  | `(tactic| cases $[$cs],* $[using $id:ident]? with $[$tac]? $is*) => do
    let is' : TSyntaxArray ``inductionAlt ←
      is.mapM <|
        fun
          | `(inductionAlt| $il* => $ts:tacticSeq) => `(inductionAlt| $il* => seq $n.succ $ts)
          | i => return ⟨i⟩
    logTacticSnapshot n.getNat `(tactic| cases $[$cs],* $[using $id:ident]? with $[$tac]? $is'*) none
  | `(tactic| match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*) => do
    let alts' : TSyntaxArray ``matchAlt ←
      alts.mapM <|
        fun
          | `(matchAltTac| | $[$pats,*]|* => $rhs:tacticSeq) => do
              let alt ← `(matchAltTac| | $[$pats,*]|* => seq $n.succ $rhs)
              return ⟨alt⟩
          | alt =>  return ⟨alt⟩
    logTacticSnapshot n.getNat `(tactic| match $[$gen]? $[$motive]? $discrs,* with $alts':matchAlt*) none
  | `(tactic| $t:tactic) => do
    logTacticSnapshot n.getNat (pure t) (some t)
| _ => panic! "Invalid `snap` format."

section ByTactic

-- a clone of the `by` tactic
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

-- intercepting the `by` tactic to output intermediate trace data
-- the `by'` clone is needed here to avoid infinite recursion
macro_rules
  | `(by $t) => do
    let tacs : TSyntaxArray `tactic :=
      #[← `(tactic| seq 0 $t), 
        -- Uncomment to enable tactic trace
        -- ← `(tactic| trace_tactic_snapshots), 
        ← `(tactic| log_and_clear_ref)]
    `(by' $[$tacs]*) 

end ByTactic

section Examples

set_option linter.unreachableTactic false

example : a + 0 = a := by
  dsimp

example : ∀ n : Nat, n = n ∧ n = n := by
  intro n
  constructor
  · rfl
  · rfl

example : a = a + 0 := by
  rw [← Nat.zero_add a, ← Nat.add_zero a, Nat.add_zero, Nat.zero_add, Nat.add_zero]

end Examples