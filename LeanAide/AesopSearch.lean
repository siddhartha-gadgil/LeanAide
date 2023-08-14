import Aesop.Search.Main
import Aesop
import Lean
import LeanAide.Aides
open Aesop Lean Meta Elab Parser.Tactic

initialize tacticSuggestions : IO.Ref (Array Syntax.Tactic) 
        ← IO.mkRef #[]

initialize tacticStrings : IO.Ref (Array String) 
        ← IO.mkRef #[]

initialize rewriteSuggestions : IO.Ref (Array Syntax.Term) 
        ← IO.mkRef #[]

initialize subgoalSuggestions : IO.Ref (Array Syntax.Term) 
        ← IO.mkRef #[]


theorem mpFrom (α  : Prop) {β : Prop} : α  → (α  → β) → β  := 
  fun a f => f a   

example : 1 = 1 := by
  apply mpFrom (2 = 2)
  · rfl
  · simp only [Nat.succ]


def getTacticSuggestions: IO (Array Syntax.Tactic) := 
  tacticSuggestions.get 

def getTacticStrings: IO (Array String) := 
  tacticStrings.get 

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
  let fvarNames ←  lctx.getFVarIds.toList.tail.mapM (·.getUserName) 
  for r in rws do
    for n in fvarNames do
      let f := mkIdent n
      let tac ← `(tactic|rw [$r:term] at $f:ident)
      tacs := tacs.push tac
      let tac ← `(tactic|rw [← $r:term] at $f:ident)
      tacs := tacs.push tac
  return tacs

#check FVarId.getUserName

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
  tacticStrings.set #[]

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
  addRwSuggestions #[stx]
  if flip  then
    addTacticSuggestion <| ← `(tactic|rw [← $stx])    
  else
    addTacticSuggestions #[← `(tactic|rw [$stx:term])]

def addTacticString (tac: String) : MetaM Unit := do 
  let old ← tacticStrings.get
  tacticStrings.set (old.push tac)


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
    extra:= ⟨⟨p⟩⟩
    tac := .applyConst decl TransparencyMode.default}

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
  let goalType ← inferType (mkMVarEx input.goal) 
  let lctx ←  getLCtx
  let fvarNames ←  lctx.getFVarIds.toList.tail.mapM (·.getUserName) 
  trace[leanaide.proof.info] "trying dynamic tactics: {tacs} for goal {←ppExpr  goalType}; fvars: {fvarNames}"
  let initialState : SavedState ← saveState
  let appsTacs ← tacs.filterMapM fun (tac) => do
    try
      let (goals, scriptBuilder) ← tacticExpr input.goal tac
      let postState ← saveState
      return some (⟨ goals, postState, scriptBuilder ⟩, tac)      
    catch _ =>
      return none
    finally
      restoreState initialState
  let (apps, tacs) := appsTacs.unzip
  if apps.isEmpty then 
    throwError "failed to apply any of the tactics"
  trace[leanaide.proof.info] "applied dynamic tactics {tacs}" 
  return { applications := apps}

def dynamicTactics : RuleTac := fun input => do 
  let tacs ← getTacticSuggestions
  let rwsAt ← rwAtTacticSuggestions 
  let tacString ← getTacticStrings 
  let mut parsedTacs : Array Syntax.Tactic := #[]
  for tac in tacString do
    match parseAsTacticSeq (←getEnv) tac with
      | Except.ok tacs => 
        parsedTacs := parsedTacs.push <| ← `(tactic|($tacs))
      | Except.error err => throwError err
  logInfo m!"dynamicTactics: {tacs}"
  applyTacticsAux (tacs ++ rwsAt 
    ++ parsedTacs
    ) input

def dynamicRuleMember (p: Float) : RuleSetMember := 
  let name : RuleName := {
    name := `dynamicTactics
    builder := BuilderName.tactic
    phase := PhaseName.«unsafe»
    scope := ScopeName.global
  }
  RuleSetMember.unsafeRule {
    name:= name
    indexingMode := IndexingMode.unindexed
    extra:= ⟨⟨p⟩⟩
    tac := .ruleTac ``dynamicTactics}

def tacticMember (p: Float)(tac : Name) : RuleSetMember := 
  let name : RuleName := {
    name := tac
    builder := BuilderName.tactic
    phase := PhaseName.«unsafe»
    scope := ScopeName.global
  }
  RuleSetMember.unsafeRule {
    name:= name
    indexingMode := IndexingMode.unindexed
    extra:= ⟨⟨p⟩⟩
    tac := .tacticM tac}

def getRuleSet (p: Float) (apps simps rws : Array Name)
  (tacs: Array String) : MetaM RuleSet := do
  clearSuggestions
  for n in rws do
    addConstRewrite n false
    addConstRewrite n true
  for t in tacs do
    addTacticString t
  let appRules ← apps.mapM (applyConstRuleMember · p)
  let simpRules ← simps.mapM simpConstRuleMember
  let simpRules := simpRules.foldl (fun c r => c ++ r) #[]
  let defaultRules ←
      Frontend.getDefaultRuleSet (includeGlobalSimpTheorems := true)
      {}
  let allRules : RuleSet := 
    ((appRules ++ simpRules).push (dynamicRuleMember p)).foldl
    (fun c r => c.add r) defaultRules
  return allRules

def runAesop (p: Float) (apps simps rws : Array Name) 
  (tacs: Array String := #[]): MVarId → MetaM (List MVarId) := fun goal => goal.withContext do
  let allRules ← getRuleSet p apps simps rws tacs
  let (goals, _) ← Aesop.search goal allRules {traceScript := true,  maxRuleApplicationDepth := 120, maxRuleApplications := 800,} 
  return goals.toList


-- For introducing local definitions
/- Convert the given goal `Ctx |- target` into `Ctx |- let name : type := val; target`. It assumes `val` has type `type` -/
#check MVarId.define -- Lean.MVarId.define (mvarId : MVarId) (name : Name) (type val : Expr) : MetaM MVarId

