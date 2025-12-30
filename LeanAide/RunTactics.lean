import Lean
import LeanAide.Aides
import LeanAide.SimpleFrontend
import LeanAide.DefData
import LeanSearchClient
import Hammer

open Lean Meta Elab Term PrettyPrinter Nat

namespace LeanAide

#logIO leanaide.interpreter.info

structure MessageCore where
  severity: MessageSeverity
  text : String
deriving Inhabited, ToJson, FromJson

def MessageCore.ofMessageM (msg: Message) : MetaM MessageCore := do
  return {severity := msg.severity, text := ← msg.data.toString}

def runFrontEndMsgCoreM (inp : String) : MetaM (List MessageCore) := do
  let msgs ← runFrontEndForMessages inp -- cache this
  msgs.toList.mapM fun msg => MessageCore.ofMessageM msg

open LeanSearchClient in
def suggestionsForGoal (goal: MVarId) (maxSuggestions: Nat := 5) (leanVersion := "v4.22.0") : MetaM (Array Name) := do
  try
    let fmt ← ppGoal goal
    let res ← queryStateSearch fmt.pretty maxSuggestions leanVersion
    return res.map fun r => r.name.toName
  catch e =>
    traceAide `leanaide.interpreter.info s!"Error querying StateSearch for goal {← PrettyPrinter.ppExpr <| ← goal.getType}: {← e.toMessageData.toString}"
    return #[]

open Parser.Tactic
def checkGrind (name: Name) : MetaM Bool := do
  let id := mkIdent name
  let p ← `(grindParam| $id:ident)
  let stx ←  `(command| example : 1 = 1 := by grind [$p])
  let l ← checkElabFrontM (← ppCommand stx).pretty
  return l.isEmpty

def suggestionsForGrind (goal: MVarId) (maxSuggestions: Nat := 5) (leanVersion := "v4.22.0") : MetaM (Array Name) := do
  let all ← suggestionsForGoal goal maxSuggestions leanVersion
  all.filterM fun name => checkGrind name

def grindWithSuggestions (goal: MVarId) (localNames : Array Name) (maxSuggestions: Nat := 5) (leanVersion := "v4.22.0") : MetaM (TSyntax ``tacticSeq) := do
  let names ← suggestionsForGrind goal maxSuggestions leanVersion
  let names := names ++ localNames
  let params : Array (TSyntax ``grindParam) ← names.mapM fun
    name => do
      let id := mkIdent name
      `(grindParam| $id:ident)
  `(tacticSeq| grind? [$params,*])

def simpWithSuggestions (goal: MVarId) (localNames : Array Name) (maxSuggestions: Nat := 5) (leanVersion := "v4.22.0") : MetaM (TSyntax ``tacticSeq) := do
  let names ← suggestionsForGoal goal maxSuggestions leanVersion
  let names := names ++ localNames
  let params : Array (TSyntax ``simpLemma) ← names.mapM fun
    name => do
      let id := mkIdent name
      `(simpLemma| $id:ident)
  `(tacticSeq| simp? [$params,*])


open Parser.Tactic
-- TODO: add errors and warnings
def runForSingleGoal (mvarId : MVarId) (tacticCode : TSyntax ``tacticSeq) : TermElabM <| Option MVarId :=
    mvarId.withContext do
  -- let tacticCode ← `(tacticSeq| skip)
  let s₀ ← saveState
  let s₀' : Meta.SavedState ←  Meta.saveState
  try
    let ctx ← read
    let (mvars, s) ←
      withoutErrToSorry do
      Elab.runTactic mvarId tacticCode {ctx with mayPostpone := false, errToSorry := false, declName? := some `_tacticCode}
         (s:= ← get)
    match mvars with
    | [] =>
      traceAide `leanaide.interpreter.info s!"Tactics returned no goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}"
      set s
      return none
    | [mvar] =>
      set s
      return mvar
    | _ =>
      s₀'.restore
      traceAide `leanaide.interpreter.info s!"Tactics returned multiple goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {mvars.length} instead of 1"
      s₀.restore
      return none
  catch e =>
    traceAide `leanaide.interpreter.info s!"Tactics failed on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {← e.toMessageData.toString}"
    traceAide `leanaide.interpreter.info s!"Tactic code: \n{← ppCategory ``tacticSeq tacticCode}"
    traceAide `leanaide.interpreter.info s!"Tactics:"
    let tacs := getTactics tacticCode
    for tac in tacs do
      traceAide `leanaide.interpreter.info s!"{← ppTactic tac}"
      traceAide `leanaide.interpreter.info ""
    traceAide `leanaide.interpreter.info s!"Assignment: {← mvarId.isAssigned}; {← PrettyPrinter.ppExpr <| mkMVar mvarId} "
    s₀.restore
    return mvarId

def runAndGetMVars (mvarId : MVarId) (tacs : Array Syntax.Tactic)
    (n: Nat)(allowClosure: Bool := false):TermElabM <| List MVarId :=
    mvarId.withContext do
  let tacticCode ← `(tacticSeq| $tacs*)
  -- let tacticCode ← `(tacticSeq| skip)
  try
    let ctx ← read
    let msgs' ← Core.getMessageLog
    let (mvars, s) ←
      withoutErrToSorry do
      Elab.runTactic mvarId tacticCode {ctx with mayPostpone := false, errToSorry := false, declName? := some `_tacticCode}
        (s:= ← get)
    let msgs ← Core.getMessageLog
    traceAide `leanaide.interpreter.info s!"Messages from `runAndGetMVars` (skipping {msgs'.toList.length}):"
    for msg in msgs.toList.drop (msgs'.toList.length) do
      traceAide `leanaide.interpreter.info s!"Message from `runAndGetMVars` (Error: {msg.severity == .error}) : {← msg.data.toString}"
      if msg.severity == MessageSeverity.error then
        throwError s!"Error in `runAndGetMVars`: {← msg.data.toString}"
    if allowClosure && mvars.isEmpty then
      set s
      traceAide `leanaide.interpreter.info s!"Tactics returned no goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}"
      traceAide `leanaide.interpreter.info s!"Assignment: {← mvarId.isAssigned}; {← PrettyPrinter.ppExpr <| mkMVar mvarId} "
      for tac in tacs do
        traceAide `leanaide.interpreter.info s!"Tactic: {← ppTactic tac}"
      throwError
        s!"Tactics returned no goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}, but allowClosure is true"
    unless mvars.length == n do
      traceAide `leanaide.interpreter.info s!"Tactics returned wrong number of goals on {← mvarId.getType}: {mvars.length} instead of {n}"
      for tac in tacs do
        traceAide `leanaide.interpreter.info s!"Tactic: {← ppTactic tac}"
      throwError
        s!"Tactics returned wrong number of goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {mvars.length} instead of {n}"
    set s
    -- traceAide `leanaide.interpreter.info s!"Tactics succeeded on {← PrettyPrinter.ppExpr <| ← mvarId.getType}"
    return mvars
  catch e =>
    traceAide `leanaide.interpreter.info s!"Tactics failed on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {← e.toMessageData.toString}"
    traceAide `leanaide.interpreter.info s!"Tactic code: {← ppCategory ``tacticSeq tacticCode}"
    for tac in tacs do
      traceAide `leanaide.interpreter.info s!"Tactic: {← ppTactic tac}"
    throwError
      s!"Tactics failed on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {← e.toMessageData.toString} when expecting {n} goals."

def relDecls : List (Option LocalDecl) → Syntax.Term → MetaM Syntax.Term
  | [], term => pure term
  | none :: rest, term =>
    -- traceAide `leanaide.interpreter.info s!"Skipping internal declaration in relDecls: {term}"
    relDecls rest term
  | (some decl) :: rest, term => do
    let prev ← relDecls rest term
    match decl with
    | .ldecl _ _ n type val _ _ =>
      let n := mkIdent n
      let typeStx ← delabDetailed type
      let valStx ← delabDetailed val
      `(let $n:ident : $typeStx := $valStx; $prev)
    | .cdecl _ _ n type bi .. =>
      let n := mkIdent n
      let typeStx ← delabDetailed type
      match bi with
      | BinderInfo.default => `(($n:ident : $typeStx) →  $prev)
      | BinderInfo.instImplicit => `([$n:ident : $typeStx] →  $prev)
      | BinderInfo.implicit => `({$n:ident : $typeStx} →  $prev)
      | BinderInfo.strictImplicit => `({{$n:ident : $typeStx}} →  $prev)

def frontendCodeForTactics (mvarId : MVarId) (tactics : Array Syntax.Tactic): TermElabM String  :=
    mvarId.withContext do
  traceAide `leanaide.interpreter.info s!"Running tactics on {← PrettyPrinter.ppExpr <| ← mvarId.getType} to get messages in context:"
  let lctx ← getLCtx
  let mut vars : Array Syntax.Term := #[]
  let fvars : Array Expr ← getLocalHyps
  let decls := lctx.decls.toList
  for decl in lctx do
    unless decl.isImplementationDetail  do
      let name := decl.userName
      traceAide `leanaide.interpreter.debug s!"Adding variable: {decl.userName} (internal: {decl.userName.isInternal}, isLet: {decl.isLet} and {decl.isLet true}) : {← PrettyPrinter.ppExpr decl.type}"
      let term ← if !name.isInternal then
        let id := mkIdent name
        `($id)
      else
        `(_)
      vars := vars.push term
    traceAide `leanaide.interpreter.info s!"Declaration: {decl.userName} (internal: {decl.userName.isInternal}) : {← PrettyPrinter.ppExpr decl.type}"
  -- vars := vars[1:]
  -- let targetType := lctx.mkForall  fvars <| ← mvarId.getType
  traceAide `leanaide.interpreter.info s!"LocalHyps: {← (← getLocalHyps).mapM fun h => do PrettyPrinter.ppExpr h}"
  traceAide `leanaide.interpreter.info "FVars:"
  for fvar in fvars do
    traceAide `leanaide.interpreter.info s!"{← PrettyPrinter.ppExpr fvar} : {← PrettyPrinter.ppExpr <| ← inferType fvar}"
  let typeStx ← relDecls decls <| ← delabDetailed <| ← mvarId.getType
  let typeView ← PrettyPrinter.ppTerm typeStx
  traceAide `leanaide.interpreter.info s!"Target type: {typeView}"
  logInfo m!"Target type: {typeView}"
  let introTac ← `(tactic| intro $vars*)
  let tactics := if vars.isEmpty then tactics else  #[introTac] ++ tactics
  let tacticCode ← `(tacticSeq| $tactics*)
  let termView ← PrettyPrinter.ppTerm <| ← `(by $tacticCode)
  logInfo m!"Tactic proof: {termView}"
  let egCode := s!"example : {typeView} := {termView}"
  -- let code := topCode ++ egCode
  return egCode


def runTacticsAndGetMessages (mvarId : MVarId) (tactics : Array Syntax.Tactic): TermElabM <| MessageLog  :=
    mvarId.withContext do
  let egCode ← frontendCodeForTactics mvarId tactics
  -- let code := topCode ++ egCode
  traceAide `leanaide.interpreter.info s!"Running frontend with code:\n{egCode}"
  let msgs' ← runFrontEndForMessages egCode
  traceAide `leanaide.interpreter.info s!"Ran frontend, Messages:"
  for msg in msgs'.toList do
    traceAide `leanaide.interpreter.info s!"{← msg.data.toString}"
  return msgs'

def getTacticsFromMessageData? (s: String) :
    MetaM <| Option (Array Syntax.Tactic) := do
  let s := s.trim
  if s.startsWith "Try this:" || s.startsWith "Try these:" then
    -- let s' := (s.splitOn "[apply] ")[1]!
    let ss := (s.splitOn "[apply] ").drop 1
    let tacticSeq? ← ss.findSomeM? getTacticsFromText?
    tacticSeq?.mapM fun tacticSeq => do
      let tacs := getTactics tacticSeq
      traceAide `leanaide.interpreter.info s!"Extracted tactics from message: {s}"
      return tacs
  else
    -- traceAide `leanaide.interpreter.info s!"Message: {s} does not start with Try this:"
    return none

def runTacticsAndGetTryThis? (goal : MVarId) (tactics : Array Syntax.Tactic) (strict : Bool := false) (previous: String := ""): TermElabM <| Option (Array Syntax.Tactic) :=
    withoutModifyingState do
  -- Add code from earlier theorems in the document
  let egCode ← frontendCodeForTactics goal tactics
  let egCode :=
    if previous == "" then
      egCode
    else
      previous ++ "\n\n" ++ egCode
  traceAide `leanaide.interpreter.info s!"Running frontend with code:\n{egCode}"
  let msgs' ← runFrontEndMsgCoreM egCode
  traceAide `leanaide.interpreter.debug s!"Ran frontend, Messages:"
  if strict then
    for msg in msgs' do
      traceAide `leanaide.interpreter.debug s!"{msg.text}"
      if msg.severity == MessageSeverity.error then
        return none
      -- if msg.severity == MessageSeverity.warning then
      --   if msg.text == "declaration uses 'sorry'" then
      --     return none
  let trys ← msgs'.filterMapM
    fun msg => do getTacticsFromMessageData? msg.text
  if trys.isEmpty then
    return none
  else
    return some <| trys.foldl (fun acc tacs => acc ++ tacs) #[]

def runTacticsAndFindTryThis? (goal : MVarId) (tacticSeqs : List (TSyntax ``tacticSeq)) (strict : Bool := true) (previous: String := ""): TermElabM <| Option (TSyntax ``tacticSeq) := do
  tacticSeqs.findSomeM?
    fun tacticSeq => do
      let tacs := getTactics tacticSeq
      let tacs? ← runTacticsAndGetTryThis? goal tacs strict previous
      tacs?.mapM fun tacs => mkTacticSeq tacs


def getQuickTactics? (goal: MVarId) : TermElabM <| Option (TSyntax ``tacticSeq) := do
  let tactics? ← runTacticsAndFindTryThis? goal [← `(tacticSeq| simp?), ← `(tacticSeq| try simp?; exact?), ← `(tacticSeq| grind?)] (strict := true)
  match tactics? with
  | none => return none
  | some tacs =>
    let tacsArr := getTactics tacs
    if tacsArr.isEmpty then
      return none
    else
      let tacticCode ←  `(tacticSeq| $tacsArr*)
      return some tacticCode

def getExactTactics? (goal: MVarId) : TermElabM <| Option (TSyntax ``tacticSeq) := do
  let tactics? ← runTacticsAndGetTryThis? goal #[(← `(tactic| exact?))]
  match tactics? with
  | none => return none
  | some tacs =>
    if tacs.isEmpty then
      return none
    else
      let tacticCode ←  `(tacticSeq| $tacs*)
      return some tacticCode

def getHammerTactics? (goal: MVarId) : TermElabM <| Option (TSyntax ``tacticSeq) := do
  let tactics? ← runTacticsAndGetTryThis? goal #[(← `(tactic| hammer {aesopPremises := 5, autoPremises := 0}))]
  match tactics? with
  | none => return none
  | some tacs =>
    if tacs.isEmpty then
      return none
    else
      let tacticCode ←  `(tacticSeq| $tacs*)
      return some tacticCode

def getExactTerm? (goal: Expr) : TermElabM <| Option Syntax.Term := do
  let mvarId ← mkFreshExprMVar goal
  let tacticCode? ← getExactTactics? mvarId.mvarId!
  tacticCode?.bindM fun tacticCode => do
    match tacticCode with
    | `(tacticSeq| exact $t:term) =>
      return t
    | _ =>
      return none

def getExactTermParts? (goal: Expr) : TermElabM <| Option <| Array Name := do
  let mvarId ← mkFreshExprMVar goal
  let tacticCode? ← getExactTactics? mvarId.mvarId!
  tacticCode?.mapM fun tacticCode => do
    match tacticCode with
    | `(tacticSeq| exact $t:term) =>
      let term ← elabTerm t none
      defsInExpr term
    | _ =>
      return #[]


elab "#exact? " goal:term : command => Command.liftTermElabM do
  let goal ← elabTerm goal none
  let mvarId ← mkFreshExprMVar goal
  let tacticCode? ← getQuickTactics? mvarId.mvarId!
  match tacticCode? with
  | none => logWarning "exact? tactic failed to find any tactics"
  | some tacticCode =>
    logInfo m!"exact? tactic found tactics: {← ppCategory ``tacticSeq tacticCode}"

-- #exact? ∀ (n m : Nat), n + m = m + n

open PrettyPrinter
def runTacticsAndGetTryThisI (goal : MVarId) (tactics : Array Syntax.Tactic): TermElabM <|  (Array Syntax.Tactic) := do
  let tacs? ← runTacticsAndGetTryThis? goal tactics
  -- traceAide `leanaide.interpreter.info s!"Tactics for goal: {← PrettyPrinter.ppExpr goal}"
  -- if let some tacs := tacs? then
  --   let view ← ppCategory ``tacticSeq <| ← `(tacticSeq|$tacs*)
  --   traceAide `leanaide.interpreter.info s!"Tactics:\n {view}"
  -- else
  --   traceAide `leanaide.interpreter.info "No tactics found"
  let autoTacs ← ppCategory ``tacticSeq <|
    ← `(tacticSeq| $tactics*)
  let headerText := s!"Automation Tactics {autoTacs} for goal: {← PrettyPrinter.ppExpr <| ← goal.getType}"
  let header := Syntax.mkStrLit headerText
  let res :=  tacs?.getD #[(←  `(tactic| repeat (sorry)))]
  let tailText := s!"Finished Automation Tactics {autoTacs} for goal: {← PrettyPrinter.ppExpr <| ← goal.getType}"
  let tail := Syntax.mkStrLit tailText
  return res
  -- return #[← `(tactic| trace $header)] ++ res ++ #[← `(tactic| trace $tail)]

def runTacticsAndFindTryThisI (goal : MVarId) (tacticSeqs : List (TSyntax ``tacticSeq)): TermElabM <|  (Array Syntax.Tactic) := do
  let tacs? ← runTacticsAndFindTryThis? goal tacticSeqs
  let autoTacs ← ppCategory ``tacticSeq <|
    ← flattenTacticSeq tacticSeqs.toArray
  let headerText := s!"Automation Tactics {autoTacs} for goal: {← PrettyPrinter.ppExpr <| ← goal.getType}"
  let header := Syntax.mkStrLit headerText
  let tacs? := tacs?.map getTactics
  let res :=  tacs?.getD #[(←  `(tactic| repeat (sorry)))]
  let tailText := s!"Finished Automation Tactics {autoTacs} for goal: {← PrettyPrinter.ppExpr <| ← goal.getType}"
  let tail := Syntax.mkStrLit tailText
  return res
  -- return #[← `(tactic| trace $header)] ++ res ++ #[← `(tactic| trace $tail)]


partial def extractInstanceIntros (goal: MVarId) (accum: List Name := []) :
    MetaM <| MVarId × List Name := goal.withContext do
  match ← goal.getType with
  | Expr.forallE n type _ BinderInfo.instImplicit => do
    let hash := (← PrettyPrinter.ppExpr type).pretty.hash
    let n := if n.isInternal then s!"{n.components[0]!}_{hash}".toName else n
    let (_, goal') ← goal.intro n
    extractInstanceIntros goal'  (accum ++ [n])
  | _ => do
    return (goal, accum)


partial def extractIntros (goal: MVarId) (maxDepth : Nat) (accum: List Name := []) :
    MetaM <| MVarId × List Name := goal.withContext do
  match maxDepth, ← goal.getType with
  | 0, _ =>
    extractInstanceIntros goal accum
  | k + 1, Expr.forallE n type _ bi => do
    let hash := (← PrettyPrinter.ppExpr type).pretty.hash
    let n := if n.isInternal then s!"{n.components[0]!}_{hash}".toName else n
    let (_, goal') ← goal.intro n
    let k' := if bi.isInstImplicit then k + 1 else k
    extractIntros goal' k' (accum ++ [n])
  | k + 1, Expr.letE n type _ _ _ => do
    let hash := (← PrettyPrinter.ppExpr type).pretty.hash
    let n := if n.isInternal then s!"{n.components[0]!}_{hash}".toName else n
    let (_, goal') ← goal.intro n
    extractIntros goal' k (accum ++ [n])
  | _, _ => do
    return (goal, accum)

-- open Lean Tactic Elab
-- def getPremiseNames (goalType: Expr)
--     (selector: Option Selector := none)
--     (maxSuggestions: Option Nat := none) : MetaM (Array Name) := do
--   let mvar ← mkFreshExprMVar goalType
--   let defaultSelector := Cloud.premiseSelector <|> mepoSelector (useRarity := true) (p := 0.6) (c := 0.9)
--   let selector := selector.getD defaultSelector
--   let mut config : PremiseSelection.Config :=
--     { maxSuggestions := maxSuggestions
--       caller := `premises }
--   let suggestions ← selector mvar.mvarId! config
--   return suggestions.map (fun s => s.name)

-- def getPremiseStatements (goalType: Expr)
--     (selector: Option Selector := none)
--     (maxSuggestions: Option Nat := none) : MetaM (Array String) := do
--   let names ← getPremiseNames goalType selector maxSuggestions
--   let mut statements : Array String := #[]
--   for name in names do
--     try
--       let defData : DefData ← DefData.ofNameM name
--       let view ← defData.statement
--       statements := statements.push view
--     catch _ =>
--       traceAide `leanaide.interpreter.info s!"Failed to get statement for {name}"
--   return statements

-- elab "#premises" goal:term : command =>
--  Command.liftTermElabM do
--  do
--   let goalType ← elabType goal
--   let ss ← getPremiseStatements goalType (maxSuggestions := some 5)
--   for s in ss do
--     logInfo s

-- elab "supergrind" : tactic => do
--   let premiseNames ← getPremiseNames (← getMainTarget)
--   let ids ←  premiseNames.mapM (fun n=>
--       let id := mkIdent n
--       `(grindParam| $id:ident)
--     )
--   evalTactic <| ← `(tactic| grind +ring +splitIndPred +splitImp [$ids,*] )

end LeanAide
