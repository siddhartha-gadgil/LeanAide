import Lean
import LeanAide.Aides
import LeanAide.SimpleFrontend
import LeanAide.DefData
import Hammer

open Lean Meta Elab Term PrettyPrinter Nat

namespace LeanAide

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
      IO.eprintln s!"Tactics returned no goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}"
      set s
      return none
    | [mvar] =>
      set s
      return mvar
    | _ =>
      s₀'.restore
      IO.eprintln s!"Tactics returned multiple goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {mvars.length} instead of 1"
      s₀.restore
      return none
  catch e =>
    IO.eprintln s!"Tactics failed on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {← e.toMessageData.toString}"
    IO.eprintln s!"Tactic code: \n{← ppCategory ``tacticSeq tacticCode}"
    IO.eprintln s!"Tactics:"
    let tacs := getTactics tacticCode
    for tac in tacs do
      IO.eprintln s!"{← ppTactic tac}"
      IO.eprintln ""
    IO.eprintln s!"Assignment: {← mvarId.isAssigned}; {← PrettyPrinter.ppExpr <| mkMVar mvarId} "
    s₀.restore
    return mvarId

def runAndGetMVars (mvarId : MVarId) (tacs : Array Syntax.Tactic)
    (n: Nat)(allowClosure: Bool := false):TermElabM <| List MVarId :=
    mvarId.withContext do
  let tacticCode ← `(tacticSeq| $tacs*)
  -- let tacticCode ← `(tacticSeq| skip)
  try
    let ctx ← read
    let (mvars, s) ←
      withoutErrToSorry do
      Elab.runTactic mvarId tacticCode {ctx with mayPostpone := false, errToSorry := false, declName? := some `_tacticCode}
        (s:= ← get)
    if allowClosure && mvars.isEmpty then
      set s
      IO.eprintln s!"Tactics returned no goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}"
      IO.eprintln s!"Assignment: {← mvarId.isAssigned}; {← PrettyPrinter.ppExpr <| mkMVar mvarId} "
      for tac in tacs do
        IO.eprintln s!"Tactic: {← ppTactic tac}"
      throwError
        s!"Tactics returned no goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}, but allowClosure is true"
    unless mvars.length == n do
      IO.eprintln s!"Tactics returned wrong number of goals on {← mvarId.getType}: {mvars.length} instead of {n}"
      for tac in tacs do
        IO.eprintln s!"Tactic: {← ppTactic tac}"
      throwError
        s!"Tactics returned wrong number of goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {mvars.length} instead of {n}"
    set s
    -- IO.eprintln s!"Tactics succeeded on {← PrettyPrinter.ppExpr <| ← mvarId.getType}"
    return mvars
  catch e =>
    IO.eprintln s!"Tactics failed on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {← e.toMessageData.toString}"
    IO.eprintln s!"Tactic code: {← ppCategory ``tacticSeq tacticCode}"
    for tac in tacs do
      IO.eprintln s!"Tactic: {← ppTactic tac}"
    throwError
      s!"Tactics failed on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {← e.toMessageData.toString} when expecting {n} goals."

def runTacticsAndGetMessages (mvarId : MVarId) (tactics : Array Syntax.Tactic): TermElabM <| MessageLog  :=
    mvarId.withContext do
  IO.eprintln s!"Running tactics on {← PrettyPrinter.ppExpr <| ← mvarId.getType} to get messages in context:"
  let lctx ← getLCtx
  let mut vars : Array Syntax.Term := #[]
  let mut fvars : Array Expr := lctx.getFVarIds.map (mkFVar)
  for decl in lctx do
    unless decl.isImplementationDetail || decl.isLet do
      let name := decl.userName
      let term ← if !name.isInternal then
        let id := mkIdent name
        `($id)
      else
        `(_)
      vars := vars.push term
    IO.eprintln s!"Declaration: {decl.userName} (internal: {decl.userName.isInternal}) : {← PrettyPrinter.ppExpr decl.type}"
  -- vars := vars[1:]
  let targetType := lctx.mkForall  fvars <| ← mvarId.getType
  let typeStx ← delabDetailed targetType
  let typeView ← PrettyPrinter.ppTerm typeStx
  logInfo m!"Target type: {typeView}"
  let introTac ← `(tactic| intro $vars*)
  let tactics := if vars.isEmpty then tactics else  #[introTac] ++ tactics
  let tacticCode ← `(tacticSeq| $tactics*)
  let termView ← PrettyPrinter.ppTerm <| ← `(by $tacticCode)
  logInfo m!"Tactic proof: {termView}"
  let egCode := s!"example : {typeView} := {termView}"
  -- let code := topCode ++ egCode
  IO.eprintln s!"Running frontend with code:\n{egCode}"
  let (_, msgs') ← runFrontendM egCode
  IO.eprintln s!"Ran frontend, Messages:"
  for msg in msgs'.toList do
    IO.eprintln s!"{← msg.data.toString}"
  return msgs'

def runTacticsAndGetMessages' (mvarId : MVarId) (tactics : Array Syntax.Tactic): TermElabM <| MessageLog  :=
    mvarId.withContext do
  -- IO.eprintln s!"Running tactics on {← PrettyPrinter.ppExpr <| ← mvarId.getType} to get messages in context:"
    -- IO.eprintln s!"Declaration: {decl.userName} (internal: {decl.userName.isInternal}) : {← PrettyPrinter.ppExpr decl.type}"
  -- vars := vars[1:]
  let targetType ← mvarId.getType
  let typeStx ← delabDetailed targetType
  let typeView ← PrettyPrinter.ppTerm typeStx
  logInfo m!"Target type: {typeView}"
  let tacticCode ← `(tacticSeq| $tactics*)
  let termView ← PrettyPrinter.ppTerm <| ← `(by $tacticCode)
  logInfo m!"Tactic proof: {termView}"
  let egCode := s!"example : {typeView} := {termView}"
  -- let code := topCode ++ egCode
  let (_, msgs') ← runFrontendM egCode
  IO.eprintln s!"Ran frontend, Messages:"
  for msg in msgs'.toList do
    IO.eprintln s!"{← msg.data.toString}"
  return msgs'


def getTacticsFromMessage? (msg: Message) :
    MetaM <| Option (Array Syntax.Tactic) := do
  let s ← msg.data.toString
  let s := s.trim
  if s.startsWith "Try this:" then
    let s' := s.drop 10 |>.trim
    match Parser.runParserCategory (← getEnv) `term ("by\n  " ++ s') with
    | Except.ok term => do
      match term with
      | `(by $[$t]*) =>
        -- IO.eprintln "Parsed tactics:"
        return t
      | _ =>
        IO.eprintln s!"Message: {s} starts with Try this:, but failed to parse {"by\n  " ++ s'} as a tactic sequence"
        return none
    | Except.error e => do
      IO.eprintln s!"Message: {s} starts with Try this:, but failed to parse {s'} with error {e}"
      return none
  else
    -- IO.eprintln s!"Message: {s} does not start with Try this:"
    return none

def runTacticsAndGetTryThis? (goal : Expr) (tactics : Array Syntax.Tactic) (strict : Bool := false): TermElabM <| Option (Array Syntax.Tactic) :=
    withoutModifyingState do
  let mvar ← mkFreshExprMVar goal
  let msgs ←
    runTacticsAndGetMessages mvar.mvarId! tactics
  -- IO.eprintln "Messages:"
  -- for msg in msgs.toList do
  --   IO.eprintln s!"Message: {← msg.data.toString}"
  if strict then
    for msg in msgs.toList do
      if msg.severity == MessageSeverity.error then
        -- IO.eprintln s!"Error message: {← msg.data.toString}"
        return none
      if msg.severity == MessageSeverity.warning then
        if (← msg.data.toString).trim == "declaration uses 'sorry'" then
          -- IO.eprintln s!"Warning message with Try this: {← msg.data.toString}"
          return none
  msgs.toList.findSomeM?
    fun msg => getTacticsFromMessage? msg

def runTacticsAndGetTryThis'? (goal : Expr) (tactics : Array Syntax.Tactic) (strict : Bool := false): TermElabM <| Option (Array Syntax.Tactic) :=
    withoutModifyingState do
  let mvar ← mkFreshExprMVar goal
  let msgs ←
    runTacticsAndGetMessages' mvar.mvarId! tactics
  IO.eprintln "Messages:"
  for msg in msgs.toList do
    IO.eprintln s!"Message: {← msg.data.toString}"
  if strict then
    for msg in msgs.toList do
      if msg.severity == MessageSeverity.error then
        -- IO.eprintln s!"Error message: {← msg.data.toString}"
        return none
      if msg.severity == MessageSeverity.warning then
        if (← msg.data.toString).trim == "declaration uses 'sorry'" then
          -- IO.eprintln s!"Warning message with Try this: {← msg.data.toString}"
          return none
  msgs.toList.findSomeM?
    fun msg => getTacticsFromMessage? msg

def getExactTactics? (goal: Expr) : TermElabM <| Option (TSyntax ``tacticSeq) := do
  let tactics? ← runTacticsAndGetTryThis? goal #[(← `(tactic| first | simp? | exact?))]
  match tactics? with
  | none => return none
  | some tacs =>
    if tacs.isEmpty then
      return none
    else
      let tacticCode ←  `(tacticSeq| $tacs*)
      return some tacticCode

def getHammerTactics? (goal: Expr) : TermElabM <| Option (TSyntax ``tacticSeq) := do
  let tactics? ← runTacticsAndGetTryThis? goal #[(← `(tactic| first | simp? | hammer {aesopPremises := 5, autoPremises := 0}))]
  match tactics? with
  | none => return none
  | some tacs =>
    if tacs.isEmpty then
      return none
    else
      let tacticCode ←  `(tacticSeq| $tacs*)
      return some tacticCode

def getExactTerm? (goal: Expr) : TermElabM <| Option Syntax.Term := do
  let tacticCode? ← getExactTactics? goal
  tacticCode?.bindM fun tacticCode => do
    match tacticCode with
    | `(tacticSeq| exact $t:term) =>
      return t
    | _ =>
      return none

def getExactTermParts? (goal: Expr) : TermElabM <| Option <| Array Name := do
  let tacticCode? ← getExactTactics? goal
  tacticCode?.mapM fun tacticCode => do
    match tacticCode with
    | `(tacticSeq| exact $t:term) =>
      let term ← elabTerm t none
      defsInExpr term
    | _ =>
      return #[]


elab "#exact? " goal:term : command => Command.liftTermElabM do
  let goal ← elabTerm goal none
  let tacticCode? ← getExactTactics? goal
  match tacticCode? with
  | none => logWarning "exact? tactic failed to find any tactics"
  | some tacticCode =>
    logInfo m!"exact? tactic found tactics: {← ppCategory ``tacticSeq tacticCode}"

-- #exact? ∀ (n m : Nat), n + m = m + n

open PrettyPrinter
def runTacticsAndGetTryThisI (goal : Expr) (tactics : Array Syntax.Tactic): TermElabM <|  (Array Syntax.Tactic) := do
  let tacs? ← runTacticsAndGetTryThis? goal tactics
  -- IO.eprintln s!"Tactics for goal: {← PrettyPrinter.ppExpr goal}"
  -- if let some tacs := tacs? then
  --   let view ← ppCategory ``tacticSeq <| ← `(tacticSeq|$tacs*)
  --   IO.eprintln s!"Tactics:\n {view}"
  -- else
  --   IO.eprintln "No tactics found"
  let autoTacs ← ppCategory ``tacticSeq <|
    ← `(tacticSeq| $tactics*)
  let headerText := s!"Automation Tactics {autoTacs} for goal: {← PrettyPrinter.ppExpr goal}"
  let header := Syntax.mkStrLit headerText
  let res :=  tacs?.getD #[(←  `(tactic| repeat (sorry)))]
  let tailText := s!"Finished Automation Tactics {autoTacs} for goal: {← PrettyPrinter.ppExpr goal}"
  let tail := Syntax.mkStrLit tailText
  return #[← `(tactic| trace $header)] ++ res ++ #[← `(tactic| trace $tail)]

partial def extractInstanceIntros (goal: MVarId) (accum: List Name := []) :
    MetaM <| MVarId × List Name := do
  match ← goal.getType with
  | Expr.forallE n type _ BinderInfo.instImplicit => do
    let hash := (← PrettyPrinter.ppExpr type).pretty.hash
    let n := if n.isInternal then s!"{n.components[0]!}_{hash}".toName else n
    let (_, goal') ← goal.intro n
    extractInstanceIntros goal'  (accum ++ [n])
  | _ => do
    return (goal, accum)


partial def extractIntros (goal: MVarId) (maxDepth : Nat) (accum: List Name := []) :
    MetaM <| MVarId × List Name := do
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

open Lean PremiseSelection Tactic Elab
def getPremiseNames (goalType: Expr)
    (selector: Option Selector := none)
    (maxSuggestions: Option Nat := none) : MetaM (Array Name) := do
  let mvar ← mkFreshExprMVar goalType
  let defaultSelector := Cloud.premiseSelector <|> mepoSelector (useRarity := true) (p := 0.6) (c := 0.9)
  let selector := selector.getD defaultSelector
  let mut config : PremiseSelection.Config :=
    { maxSuggestions := maxSuggestions
      caller := `premises }
  let suggestions ← selector mvar.mvarId! config
  return suggestions.map (fun s => s.name)

def getPremiseStatements (goalType: Expr)
    (selector: Option Selector := none)
    (maxSuggestions: Option Nat := none) : MetaM (Array String) := do
  let names ← getPremiseNames goalType selector maxSuggestions
  let mut statements : Array String := #[]
  for name in names do
    try
      let defData : DefData ← DefData.ofNameM name
      let view ← defData.statement
      statements := statements.push view
    catch _ =>
      IO.eprintln s!"Failed to get statement for {name}"
  return statements

elab "#premises" goal:term : command =>
 Command.liftTermElabM do
 do
  let goalType ← elabType goal
  let ss ← getPremiseStatements goalType (maxSuggestions := some 5)
  for s in ss do
    logInfo s

elab "supergrind" : tactic => do
  let premiseNames ← getPremiseNames (← getMainTarget)
  let ids ←  premiseNames.mapM (fun n=>
      let id := mkIdent n
      `(grindParam| $id:ident)
    )
  evalTactic <| ← `(tactic| grind +ring +splitIndPred +splitImp [$ids,*] )

end LeanAide
