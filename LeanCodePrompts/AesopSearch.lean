import Aesop.Search.Main
import Aesop
import Lean
import LeanCodePrompts.Utils
open Aesop Lean Meta Elab Parser.Tactic

initialize tacticSuggestions : IO.Ref (Array Syntax.Tactic) 
        ← IO.mkRef #[]

initialize rewriteSuggestions : IO.Ref (Array Syntax.Term) 
        ← IO.mkRef #[]

initialize subgoalSuggestions : IO.Ref (Array Syntax.Term) 
        ← IO.mkRef #[]

initialize fibOut : IO.Ref (Array String) 
        ← IO.mkRef #[]

def getFib : IO (Array String) := do
  fibOut.get


def setFib (s: String) : IO Unit := do
  fibOut.set <| (← getFib).push  s


theorem mpFrom (α  : Prop) {β : Prop} : α  → (α  → β) → β  := 
  fun a f => f a   

example : 1 = 1 := by
  apply mpFrom (2 = 2)
  · rfl
  · simp only [Nat.succ]


def getTacticSuggestions: IO (Array Syntax.Tactic) := 
  tacticSuggestions.get 

def rwTacticSuggestions : MetaM (Array Syntax.Tactic) := do
  let rws ← rewriteSuggestions.get
  let rwTacs ← rws.mapM fun rw => do
    let rw ← `(tactic|rw [$rw:term])
    return rw
  let rwTacFlips ← rws.mapM fun rw => do
    let rw ← `(tactic|rw [← $rw:term])
    return rw
  return rwTacs ++ rwTacFlips

def rwAtTacticSuggestions : MetaM (Array Syntax.Tactic) := do
  let rws ← rewriteSuggestions.get
  let mut tacs := #[]
  let lctx ←  getLCtx
  let fvarIdents := lctx.getFVarIds.map (mkIdent ·.name) 
  for r in rws do
    for f in fvarIdents do
      let tac ← `(tactic|rw [$r:term] at $f:ident)
      tacs := tacs.push tac
      let tac ← `(tactic|rw [← $r:term] at $f:ident)
      tacs := tacs.push tac
  return tacs

def subgoalTacticSuggestions : MetaM (Array Syntax.Tactic) := do
  let subgoals ← subgoalSuggestions.get
  let mp := mkIdent ``mpFrom
  subgoals.mapM <| fun α => do
    let fx ← `($mp $α:term) 
    `(tactic|apply $fx:term)


def clearSuggestions : IO Unit := do
  tacticSuggestions.set #[]
  rewriteSuggestions.set #[]
  subgoalSuggestions.set #[]

def addTacticSuggestions (suggestions: Array Syntax.Tactic) : IO Unit := do
  let old ← tacticSuggestions.get
  tacticSuggestions.set (old ++ suggestions)

def addTacticSuggestion (suggestion: Syntax.Tactic) : IO Unit := do
  let old ← tacticSuggestions.get
  tacticSuggestions.set (old.push suggestion)

def addRwSuggestions (suggestions: Array Syntax.Term) : IO Unit := do
  let old ← rewriteSuggestions.get
  rewriteSuggestions.set (old ++ suggestions)

def addRwSuggestion (suggestion: Syntax.Term) : IO Unit := do
  let old ← rewriteSuggestions.get
  rewriteSuggestions.set (old.push suggestion)

def addSubgoalSuggestions (suggestions: Array Syntax.Term) : IO Unit := do
  let old ← subgoalSuggestions.get
  subgoalSuggestions.set (old ++ suggestions)

def addSubgoalSuggestion (suggestion: Syntax.Term) : IO Unit := do
  let old ← subgoalSuggestions.get
  subgoalSuggestions.set (old.push suggestion)

def addConstRewrite (decl: Name)(flip: Bool) : MetaM Unit := do
  let stx : Syntax.Term := mkIdent decl
  if flip  then
    addTacticSuggestion <| ← `(tactic|rw [← $stx])
  else
    addTacticSuggestions #[← `(tactic|rw [$stx:term])]

/-- Rule set member for `apply` for a global constant -/
def applyConstRuleMember (decl: Name)(p: Float) : MetaM RuleSetMember := do
  let type := (← getConstInfo decl).type
  let indexingMode ←  IndexingMode.targetMatchingConclusion type
  let name : RuleName := {
    name := decl
    builder := BuilderName.apply
    phase := PhaseName.«unsafe»
    scope := ScopeName.global
  }
  return RuleSetMember.unsafeRule {
    name:= name
    indexingMode := indexingMode
    usesBranchState := false
    extra:= ⟨⟨p⟩⟩
    tac := .applyConst decl}

/-- Rule set members for `simp` for a global constant proof -/
partial def simpConstRuleMember (decl: Name) : MetaM <| Array RuleSetMember := do
  let cinfo ← getConstInfo decl
  let val := cinfo.value!
  if ¬(← isProof val) then 
    let head := RuleSetMember.unfoldRule {
      decl := decl
      unfoldThm? := ← getUnfoldEqnFor? decl
    }
    if let some eqns ← getEqnsFor? decl then
      let r ← eqns.mapM simpConstRuleMember
      let r := r.foldl (fun c r => c ++ r) #[] 
      return r.push head
    else
      return #[head] 
  else
    let entries ←  mkSimpTheorems (.decl decl) cinfo.levelParams.toArray val
    let name : RuleName := {
      name := decl
      builder := BuilderName.simp
      phase := PhaseName.norm
      scope := ScopeName.global
    }
    return #[RuleSetMember.normSimpRule {
      name:= name
      entries := entries.map .thm 
      }]

def tacticExpr (goal : MVarId) (tac : Syntax.Tactic) :
    MetaM (Array MVarId × RuleTacScriptBuilder) := 
  goal.withContext do
  let goalState ← runTactic goal tac 
      {errToSorry := false, implicitLambda := false} {}
  let goals := goalState.1.toArray
  let scriptBuilder :=
    ScriptBuilder.ofTactic goals.size (pure tac)
  return (goals, scriptBuilder)

def applyTacticsAux (tacs : Array Syntax.Tactic) : RuleTac := fun input => do
  let initialState ← saveState
  let appsTacs ← tacs.filterMapM fun (tac) => do
    try
      let (goals, scriptBuilder) ← tacticExpr input.goal tac
      let postState ← saveState
      return some ({ postState, goals, scriptBuilder }, tac)
    catch _ =>
      return none
    finally
      restoreState initialState
  let (apps, tacs) := appsTacs.unzip
  if apps.isEmpty then 
    throwError "failed to apply any of the tactics"
  trace[leanaide.proof.info] "applied custom tactics {tacs}" 
  return { applications := apps, postBranchState? := none }

def customTactics : RuleTac := fun input => do 
  let tacs ← getTacticSuggestions
  logInfo m!"customTactics: {tacs}"
  applyTacticsAux tacs input

def customRuleMember (p: Float) : MetaM RuleSetMember := do
  let name : RuleName := {
    name := `customTactics
    builder := BuilderName.tactic
    phase := PhaseName.«unsafe»
    scope := ScopeName.global
  }
  return RuleSetMember.unsafeRule {
    name:= name
    indexingMode := IndexingMode.unindexed
    usesBranchState := false
    extra:= ⟨⟨p⟩⟩
    tac := .ruleTac ``customTactics}

def getRuleSet (p: Float) (apps simps rws : Array Name) : MetaM RuleSet := do
  clearSuggestions
  for n in rws do
    addConstRewrite n false
    addConstRewrite n true
  let appRules ← apps.mapM (applyConstRuleMember · p)
  let simpRules ← simps.mapM simpConstRuleMember
  let simpRules := simpRules.foldl (fun c r => c ++ r) #[]
  let defaultRules ←
      Frontend.getDefaultRuleSet (includeGlobalSimpTheorems := true)
  let allRules : RuleSet := 
    ((appRules ++ simpRules).push (← customRuleMember p)).foldl
    (fun c r => c.add r) defaultRules
  return allRules

def Lean.MessageData.format? (msg: MessageData) : Option Format :=
  match msg with
  | .ofFormat f => some f
  | _ => none

def Lean.MessageData.ppformat? (msg: MessageData) : Option PPFormat :=
  match msg with
  | .ofPPFormat f => some f
  | _ => none

-- to extract tactics later
def Lean.MessageData.split (msg: MessageData) : Array MessageData :=
  match msg with
  | .compose l₁ l₂ => l₁.split ++ l₂.split
  | .nest n l => #[m!"nest {n}"] ++ l.split
  | .withContext _ l => #[m!"ctx"] ++ l.split
  | .withNamingContext _ l => #[m!"nmgctx"] ++ l.split
  | .ofFormat _ => #["format", msg]
  | .ofPPFormat _ => #["ppformat", msg]
  | _ => #[msg]

def runAesop (p: Float) (apps simps rws : Array Name) : MVarId → MetaM (List MVarId) := fun goal => goal.withContext do
  let allRules ← getRuleSet p apps simps rws
  let (goals, _) ← Aesop.search goal allRules {traceScript := true} 
  let msgLog ← Core.getMessageLog  
  -- let msgs := msgLog.toList
  -- logInfo m!"Messages: {msgs.map (·.data.split)}"
  return goals.toList

example : α → α := by
  aesop

-- For introducing local definitions
/- Convert the given goal `Ctx |- target` into `Ctx |- let name : type := val; target`. It assumes `val` has type `type` -/
#check MVarId.define -- Lean.MVarId.define (mvarId : MVarId) (name : Name) (type val : Expr) : MetaM MVarId

#check MessageData.instAppendMessageData

def getMsgTactic?  : CoreM <| Option Syntax := do
  let msgLog ← Core.getMessageLog  
  let msgs := msgLog.toList
  let mut tac? : Option Syntax := none
  for msg in msgs do
    let msg := msg.data
    let msg ← msg.toString 
    let msg := msg.replace "Try this:" "" |>.trim
    let parsedMessage := Parser.runParserCategory (←getEnv)  `tactic msg
    match parsedMessage with
    | Except.ok tac => 
      tac? := some tac
    | _ =>
      logInfo m!"failed to parse tactic {msg}"
  return tac?
 
open Tactic

elab "messages" tac:tacticSeq : tactic => do
  let goal ← getMainGoal
  evalTactic tac
  let tac ← getMsgTactic?
  logInfo m!"tactic in message: {tac}"
  admitGoal goal 