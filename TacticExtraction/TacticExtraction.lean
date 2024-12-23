import Lean
import TacticExtraction.TacticExtractionCache

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

  def logTacticSnapshotAt (idx : Nat) (depth : Nat) (tac : TSyntax `tactic) (ref : Option Syntax) : TacticM Unit := do
    let goalsBefore ← getUnsolvedGoals
    let strGoalsBefore ← MessageData.toString <| ← addMessageContext <| goalsToMessageData goalsBefore
    evalTactic tac
    let goalsAfter ← getUnsolvedGoals
    let strGoalsAfter ← MessageData.toString <| ← addMessageContext <| goalsToMessageData goalsAfter
    let snap : TacticSnapshot := ⟨depth, strGoalsBefore, tac, strGoalsAfter, ref⟩
    tacticSnapRef.insert idx snap

  syntax (name := trace_tactic_snapshots) "trace_tactic_snapshots" num : tactic

  @[tactic trace_tactic_snapshots] def traceTacticSnapshots : Tactic
    | `(tactic| trace_tactic_snapshots $i) => do
      let idx := i.getNat
      let snaps ← tacticSnapRef.getIdx idx
      for snap in snaps do
        match snap.ref with
        | .some ref =>
          withRef ref <| addRawTrace snap.goalsBefore
          withRef ref <| addRawTrace m!"[TACTIC] {snap.tactic}"
          withRef ref <| addRawTrace snap.goalsAfter
        | none => pure ()
    | _ => throwUnsupportedSyntax

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
    "."/"TacticStepData"

  syntax (name := log_and_clear_ref) "log_and_clear_ref" num : tactic

  @[tactic log_and_clear_ref] def logAndClearRef : Tactic
    | `(tactic| log_and_clear_ref $i) => do
      let idx := i.getNat
      let snaps ← tacticSnapRef.getIdx idx
      let jsnaps ← snaps.mapM (TacticSnapshot.toJson ·)
      let mod ← getMainModule
      let fileName := s!"{mod}-{idx}.json"
      IO.FS.writeFile (outputLocation / fileName) <| Json.pretty <| Json.arr jsnaps
      tacticSnapRef.setIdx idx #[]
    | _ => throwUnsupportedSyntax

  end Logging

end Misc

syntax (name := snap) "snap" num num tactic : tactic
syntax (name := seq) "seq" num num tacticSeq : tactic

elab_rules:tactic
  | `(tactic| seq $idx $n $[$tacs]*) => do
    let tacs' ← tacs.mapM <|
      fun tac ↦ `(tactic| snap $idx $n $tac)
    evalTacticM `(tactic| {$[$tacs']*})

@[tactic snap] partial def traceTacticSnap : Tactic
| `(tactic| snap $idx $n $t) => do
  withoutModifyingState <| logTacticSnapshotAt idx.getNat n.getNat t none
  evalTactic t
  -- match t with
  -- | `(tactic| focus $[$tacs]*) =>
  --   evalTacticM `(tactic| focus seq $idx $n.succ $[$tacs]*)
  -- | `(tactic| · $[$tacs]*) =>
  --   evalTacticM `(tactic| · seq $idx $n.succ $[$tacs]*)
  -- | `(tactic| {$[$tacs]*}) =>
  --   evalTacticM `(tactic| {seq $idx $n.succ $[$tacs]*})
  -- | `(tactic| ($[$tacs]*)) =>
  --   evalTacticM `(tactic| (seq $idx $n.succ $[$tacs]*))
  -- | `(tactic| case $[$tag $hs*]|* =>%$arr $tac:tacticSeq) =>
  --   evalTacticM `(tactic| case $[$tag $hs*]|* =>%$arr seq $idx $n.succ $tac:tacticSeq)
  -- | `(tactic| case' $[$tag $hs*]|* =>%$arr $tac:tacticSeq) =>
  --   evalTacticM `(tactic| case' $[$tag $hs*]|* =>%$arr seq $idx $n.succ $tac:tacticSeq)
  -- | `(tactic| induction $[$ts],* $[using $id:ident]?  $[generalizing $gs*]? with $[$tac]? $is*) =>
  --   let is' : TSyntaxArray ``inductionAlt ←
  --     is.mapM <| fun
  --       | `(inductionAlt| $il* => $ts:tacticSeq) => `(inductionAlt| $il* => seq $idx $n.succ $ts)
  --       | i => return ⟨i⟩
  --   evalTacticM `(tactic| induction $[$ts],* $[using $id:ident]?  $[generalizing $gs*]? with $[$tac]? $is'*)
  -- | `(tactic| cases $[$cs],* $[using $id:ident]? with $[$tac]? $is*) =>
  --   let is' : TSyntaxArray ``inductionAlt ←
  --     is.mapM <| fun
  --       | `(inductionAlt| $il* => $ts:tacticSeq) => `(inductionAlt| $il* => seq $idx $n.succ $ts)
  --       | i => return ⟨i⟩
  --   evalTacticM `(tactic| cases $[$cs],* $[using $id:ident]? with $[$tac]? $is'*)
  -- | `(tactic| match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*) =>
  --   let alts' : TSyntaxArray ``matchAlt ←
  --     alts.mapM <| fun
  --       | `(matchAltTac| | $[$pats,*]|* => $rhs:tacticSeq) => do
  --           let alt ← `(matchAltTac| | $[$pats,*]|* => seq $idx $n.succ $rhs)
  --           return ⟨alt⟩
  --       | alt =>  return ⟨alt⟩
  --   evalTacticM `(tactic| match $[$gen]? $[$motive]? $discrs,* with $alts':matchAlt*)
  -- | `(tactic| $t:tactic) =>
  --   evalTactic t
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
@[term_elab byTactic] def elabByTacticLog : TermElab :=
  adaptExpander <| fun
    | `(term| by $tacs:tacticSeq) => do
      let i ← counter.getIdx
      let idx := Syntax.mkNumLit <| toString i
      let ts : TSyntaxArray `tactic :=
        #[← `(tactic| seq $idx 0 $tacs),
          -- Uncomment to enable tactic trace
          -- ← `(tactic| trace_tactic_snapshots $idx),
          ← `(tactic| log_and_clear_ref $idx)]
      `(by' $[$ts]*)
    | _ => throwUnsupportedSyntax

end ByTactic

-- section Examples

-- example : a + 0 = a := by
--   dsimp

-- example : ∀ n : Nat, n = n ∧ n = n := by
--   intro n
--   constructor
--   · rfl
--   · rfl

-- def xyz : a = a + 0 := by
--   rw [← Nat.zero_add a, ← Nat.add_zero a, Nat.add_zero, Nat.zero_add, Nat.add_zero]

-- end Examples
