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
  let mut dynTactics := #[]
  let lctx ←  getLCtx
  let fvarNames ←  lctx.getFVarIds.toList.tail.mapM (·.getUserName) 
  for r in rws do
    for n in fvarNames do
      let f := mkIdent n
      let tac ← `(tactic|rw [$r:term] at $f:ident)
      dynTactics := dynTactics.push tac
      let tac ← `(tactic|rw [← $r:term] at $f:ident)
      dynTactics := dynTactics.push tac
  return dynTactics

def clearSuggestions : IO Unit := do
  tacticSuggestions.set #[]
  rewriteSuggestions.set #[]
  tacticStrings.set #[]

def addTacticSuggestion (suggestion: Syntax.Tactic) : IO Unit := do
  let old ← tacticSuggestions.get
  tacticSuggestions.set (old.push suggestion)

def addRwSuggestions (suggestions: Array Syntax.Term) : IO Unit := do
  let old ← rewriteSuggestions.get
  rewriteSuggestions.set (old ++ suggestions)


def addConstRewrite (decl: Name)(flip: Bool) : MetaM Unit := do
  let stx : Syntax.Term := mkIdent decl
  addRwSuggestions #[stx]
  if flip  then
    addTacticSuggestion <| ← `(tactic|rw [← $stx])    
  else
    addTacticSuggestion <| ← `(tactic|rw [$stx:term])

def addTacticString (tac: String) : MetaM Unit := do 
  let old ← tacticStrings.get
  tacticStrings.set (old.push tac)


/-- Rule set member for `apply` for a global constant -/
def applyConstRuleMembers (decl: Name)(p: Float) : MetaM <| Array RuleSetMember := do
  let prob :=  Syntax.mkNumLit s!"{p * 100}"
  let stx ← `(attr|aesop unsafe $prob:num % apply) 
  let config ← runTermElabMAsCoreM $ Aesop.Frontend.AttrConfig.elab stx
  let rules ← runMetaMAsCoreM $
      config.rules.concatMapM (·.buildAdditionalGlobalRules decl)
  return rules.map (·.1)

def safeApplyConstRuleMembers (decl: Name) : MetaM <| Array RuleSetMember := do
  let stx ← `(attr|aesop safe apply) 
  let config ← runTermElabMAsCoreM $ Aesop.Frontend.AttrConfig.elab stx
  let rules ← runMetaMAsCoreM $
      config.rules.concatMapM (·.buildAdditionalGlobalRules decl)
  return rules.map (·.1)

#check Parser.numLit

/-- Rule set members for `simp` for a global constant proof -/
partial def simpConstRuleMember (decl: Name) : MetaM <| Array RuleSetMember := do
  let stx ← `(attr|aesop norm simp) 
  let config ← runTermElabMAsCoreM $ Aesop.Frontend.AttrConfig.elab stx
  let rules ← runMetaMAsCoreM $
      config.rules.concatMapM (·.buildAdditionalGlobalRules decl)
  return rules.map (·.1)

/-- Rule set member for `forward` for a global constant -/
def forwardConstRuleMembers (decl: Name)(p: Float) : MetaM <| Array RuleSetMember := do
  let prob :=  Syntax.mkNumLit s!"{p * 100}"
  let stx ← `(attr|aesop unsafe $prob:num % forward) 
  let config ← runTermElabMAsCoreM $ Aesop.Frontend.AttrConfig.elab stx
  let rules ← runMetaMAsCoreM $
      config.rules.concatMapM (·.buildAdditionalGlobalRules decl)
  return rules.map (·.1)

/-- Rule set member for `destruct` for a global constant -/
def destructConstRuleMembers (decl: Name)(p: Float) : MetaM <| Array RuleSetMember := do
  let prob :=  Syntax.mkNumLit s!"{p * 100}"
  let stx ← `(attr|aesop unsafe $prob:num % destruct) 
  let config ← runTermElabMAsCoreM $ Aesop.Frontend.AttrConfig.elab stx
  let rules ← runMetaMAsCoreM $
      config.rules.concatMapM (·.buildAdditionalGlobalRules decl)
  return rules.map (·.1)

/-- Rule set member for `cases` for a global constant -/
def casesConstRuleMembers (decl: Name)(p: Float) : MetaM <| Array RuleSetMember := do
  let prob :=  Syntax.mkNumLit s!"{p * 100}"
  let stx ← `(attr|aesop unsafe $prob:num % cases) 
  let config ← runTermElabMAsCoreM $ Aesop.Frontend.AttrConfig.elab stx
  let rules ← runMetaMAsCoreM $
      config.rules.concatMapM (·.buildAdditionalGlobalRules decl)
  return rules.map (·.1)

/-- Rule set member for `constructors` for a global constant -/
def constructorConstRuleMembers (decl: Name)(p: Float) : MetaM <| Array RuleSetMember := do
  let prob :=  Syntax.mkNumLit s!"{p * 100}"
  let stx ← `(attr|aesop unsafe $prob:num % constructors) 
  let config ← runTermElabMAsCoreM $ Aesop.Frontend.AttrConfig.elab stx
  let rules ← runMetaMAsCoreM $
      config.rules.concatMapM (·.buildAdditionalGlobalRules decl)
  return rules.map (·.1)

/-- Rule set member for `unfold` for a global constant -/
def unfoldConstRuleMembers (decl: Name) : MetaM <| Array RuleSetMember := do
  let stx ← `(attr|aesop norm unfold) 
  let config ← runTermElabMAsCoreM $ Aesop.Frontend.AttrConfig.elab stx
  let rules ← runMetaMAsCoreM $
      config.rules.concatMapM (·.buildAdditionalGlobalRules decl)
  return rules.map (·.1)

/-- Rule set member for `tactic` for a global constant -/
def tacticConstRuleMembers (decl: Name)(p: Float) : MetaM <| Array RuleSetMember := do
  let prob :=  Syntax.mkNumLit s!"{p * 100}"
  let stx ← `(attr|aesop unsafe $prob:num % tactic) 
  let config ← runTermElabMAsCoreM $ Aesop.Frontend.AttrConfig.elab stx
  let rules ← runMetaMAsCoreM $
      config.rules.concatMapM (·.buildAdditionalGlobalRules decl)
  return rules.map (·.1)



def tacticExpr (goal : MVarId) (tac : Syntax.Tactic) :
    MetaM (Array MVarId × RuleTacScriptBuilder) := 
  goal.withContext do
  let goalState ← runTactic goal tac 
      {errToSorry := false, implicitLambda := false} {}
  let goals := goalState.1.toArray
  let scriptBuilder :=
    ScriptBuilder.ofTactic goals.size (pure tac)
  return (goals, scriptBuilder)

def dynamicRuleTac (dynTactics : Array Syntax.Tactic) : RuleTac := fun input => do
  let goalType ← inferType (mkMVarEx input.goal) 
  let lctx ←  getLCtx
  let fvarNames ←  lctx.getFVarIds.toList.tail.mapM (·.getUserName) 
  trace[leanaide.proof.info] "trying dynamic tactics: {dynTactics} for goal {←ppExpr  goalType}; fvars: {fvarNames}"
  let initialState : SavedState ← saveState
  let appsTacs ← dynTactics.filterMapM fun (tac) => do
    try
      let (goals, scriptBuilder) ← tacticExpr input.goal tac
      let postState ← saveState
      return some (⟨ goals, postState, scriptBuilder ⟩, tac)      
    catch _ =>
      return none
    finally
      restoreState initialState
  let (apps, dynTactics) := appsTacs.unzip
  if apps.isEmpty then 
    throwError "failed to apply any of the tactics"
  trace[leanaide.proof.info] "applied dynamic tactics {dynTactics}" 
  return { applications := apps}

def dynamicTactics : RuleTac := fun input => do 
  let dynTactics ← getTacticSuggestions
  let rwsAt ← rwAtTacticSuggestions 
  let tacString ← getTacticStrings 
  let mut parsedTacs : Array Syntax.Tactic := #[]
  for tac in tacString do
    match parseAsTacticSeq (←getEnv) tac with
      | Except.ok dynTactics => 
        parsedTacs := parsedTacs.push <| ← `(tactic|($dynTactics))
      | Except.error err => throwError err
  logInfo m!"dynamicTactics: {dynTactics}"
  dynamicRuleTac (dynTactics ++ rwsAt 
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


-- Copied from Aesop source code
open Aesop.BuiltinRules in
def introsWithTransparency (transparency: TransparencyMode) : RuleTac := RuleTac.ofSingleRuleTac λ input => do
    let md? := some transparency
    let (newFVars, goal) ← unhygienic $
      if let some md := md? then
        withTransparency md $ introsUnfolding input.goal
      else
        input.goal.intros
    if newFVars.size == 0 then
      throwError "nothing to introduce"
    let scriptBuilder? ←
      if input.options.generateScript then
        goal.withContext do
          let newFVarUserNames ← newFVars.mapM (mkIdent <$> ·.getUserName)
          let tac ← `(tactic| intro $newFVarUserNames:ident*)
          let tac :=
            if let some md := md? then
              withAllTransparencySyntax md tac
            else
              pure tac
          pure $ some $ .ofTactic 1 tac

      else
        pure none
    return (#[goal], scriptBuilder?)

-- @[aesop unsafe 90% tactic]
def introsWithDefault : RuleTac := introsWithTransparency TransparencyMode.default
def introsWithAll : RuleTac := introsWithTransparency TransparencyMode.all
def introsWithReducible : RuleTac := introsWithTransparency TransparencyMode.reducible
def introsWithInstances : RuleTac := introsWithTransparency TransparencyMode.instances

partial def syntaxNames (stx: Syntax) : List Name := 
  match stx with
  | Syntax.node _ _ args => 
    args.toList.bind syntaxNames
  | Syntax.ident _ _ name _ =>    
    [name]
  | _ => []

def syntaxConsts (stx: Syntax) : CoreM <| List Name := do
  let env ← getEnv
  let names := syntaxNames stx
  let consts := names.filter (fun n => env.contains n)
  return consts

-- To possibly use for cases, constructors
def syntaxInductives (stx : Syntax) : CoreM <| List Name := do
  let env ← getEnv
  let consts ← syntaxConsts stx
  let inductives := consts.filter (fun n => 
    match env.find? n with
    | some (ConstantInfo.inductInfo _) => true
    | _ => false)
  return inductives

-- To be included based on identifiers in goal
def structProjs (name: Name) : CoreM <| List Name := do
  let env ← getEnv
  let structNames := getStructureFields env name
  return structNames.toList.map (fun n => name.append n)

def syntaxStructProjs (stx: Syntax) : CoreM <| List Name := do
  let inductives ← syntaxInductives stx
  let structProjs ← inductives.mapM structProjs
  return structProjs.join

#eval structProjs ``And
#check And.left

structure AesopSearchConfig extends Aesop.Options where
  traceScript := true
  maxRuleApplicationDepth := 120
  maxRuleApplications := 800
  apps : Array <| Name × Float := #[] 
  safeApps : Array Name := #[]
  simps : Array Name := #[]
  rws : Array Name := #[]
  forwards : Array <| Name × Float := #[] 
  destructs : Array <| Name × Float := #[] 
  cases : Array <| Name × Float := #[]
  constructors : Array <| Name × Float := #[]
  tactics : Array <| Name × Float := #[] -- usually tactics are not named
  dynTactics : Array String := #[]
  dynProb : Float := 0.5

def AesopSearchConfig.addSimp (config: AesopSearchConfig) (decl: Name) : AesopSearchConfig := {
  config with
  simps := config.simps.push decl
}

def withAndWithoutSimpsList (configs : List AesopSearchConfig)
  (decls: List Name): List AesopSearchConfig :=
  match decls with
  | [] => configs
  | head :: tail => 
    let newConfigs := configs.map (·.addSimp head)
    withAndWithoutSimpsList (newConfigs ++ configs) tail

def withAndWithoutSimps (config: AesopSearchConfig) 
  (decls: List Name) : List AesopSearchConfig :=
  withAndWithoutSimpsList [config] decls

def AesopSearchConfig.ruleSet (config: AesopSearchConfig) : 
    MetaM RuleSet := do
  clearSuggestions
  for n in config.rws do
    addConstRewrite n false
    addConstRewrite n true
  for t in config.dynTactics do
    addTacticString t
  let appRules : Array RuleSetMember := (← config.apps.mapM 
    (fun (n, p) => applyConstRuleMembers n p) 
    ).foldl (fun c r => c ++ r) #[]
  let safeAppRules : Array RuleSetMember := (← config.safeApps.mapM 
    (fun n => safeApplyConstRuleMembers n) 
    ).foldl (fun c r => c ++ r) #[]
  let forwardRules : Array RuleSetMember := (← config.forwards.mapM 
    (fun (n, p) => forwardConstRuleMembers n p) 
    ).foldl (fun c r => c ++ r) #[]
  let destructRules : Array RuleSetMember := (← config.destructs.mapM
    (fun (n, p) => destructConstRuleMembers n p) 
    ).foldl (fun c r => c ++ r) #[]
  let casesRules : Array RuleSetMember := (← config.cases.mapM
    (fun (n, p) => casesConstRuleMembers n p) 
    ).foldl (fun c r => c ++ r) #[]
  let constructorRules : Array RuleSetMember := (← config.constructors.mapM
    (fun (n, p) => constructorConstRuleMembers n p) 
    ).foldl (fun c r => c ++ r) #[]
  let tacticRules :=  (← 
    config.tactics.push (``introsWithDefault, 0.9) |>.mapM 
    (fun (n, p) => tacticConstRuleMembers n p)
    ).foldl (fun c r => c ++ r) #[]
  let simpRules ← config.simps.mapM simpConstRuleMember
  let simpRules := simpRules.foldl (fun c r => c ++ r) #[]
  let defaultRules ←
      Frontend.getDefaultRuleSet (includeGlobalSimpTheorems := true)
      {}
  let allRules : RuleSet := 
    ((appRules ++ simpRules ++ tacticRules ++ safeAppRules 
     ++ forwardRules ++ destructRules ++ casesRules ++ constructorRules
     ).push (dynamicRuleMember config.dynProb)).foldl
    (fun c r => c.add r) defaultRules
  return allRules



def runAesop (config: AesopSearchConfig): MVarId → MetaM (List MVarId) := fun goal => 
  goal.withContext do
  let allRules ← config.ruleSet
  let (goals, _) ← Aesop.search goal allRules config.toOptions 
  return goals.toList

def polyAesopRun (configs: List AesopSearchConfig) : 
    MVarId → MetaM Bool := 
  fun goal => goal.withContext do
  match configs with
  | [] => return false
  | head :: tail =>
    let s ← saveState 
    let allRules ← head.ruleSet
    let (goals, _) ← Aesop.search goal allRules head.toOptions 
    if goals.isEmpty then
      return true
    else
      s.restore
      polyAesopRun tail goal