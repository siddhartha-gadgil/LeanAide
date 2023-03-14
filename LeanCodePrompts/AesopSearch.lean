import Aesop.Search.Main
import Aesop
import Lean
open Aesop Lean Meta Elab Parser.Tactic

initialize tacticSuggestions : IO.Ref (Array Syntax.Tactic) 
        ← IO.mkRef #[]

def getTacticSuggestions: IO (Array Syntax.Tactic) := tacticSuggestions.get

def clearTacticSuggestions : IO Unit := tacticSuggestions.set #[]

def addTacticSuggestions (suggestions: Array Syntax.Tactic) : IO Unit := do
  let old ← tacticSuggestions.get
  tacticSuggestions.set (old ++ suggestions)

def addTacticSuggestion (suggestion: Syntax.Tactic) : IO Unit := do
  let old ← tacticSuggestions.get
  tacticSuggestions.set (old.push suggestion)

def addConstRewrite (decl: Name)(flip: Bool) : MetaM Unit := do
  let stx : Syntax.Term := mkIdent decl
  if flip  then
    addTacticSuggestion <| ← `(tactic|rw [← $stx])
  else
    let rule : TSyntax `Lean.Parser.Tactic.rwRule := ⟨stx.raw⟩
    addTacticSuggestions #[← `(tactic|rw [$rule])]


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
def simpConstRuleMember (decl: Name) : MetaM RuleSetMember := do
  let cinfo ← getConstInfo decl
  let val := cinfo.value!
  if ¬(← isProof val) then throwError "simpConstRuleMember: expected proof, got {val}" 
  let entries ←  mkSimpTheorems (.decl decl) cinfo.levelParams.toArray val
  let name : RuleName := {
    name := decl
    builder := BuilderName.simp
    phase := PhaseName.norm
    scope := ScopeName.global
  }
  return RuleSetMember.normSimpRule {
    name:= name
    entries := entries.map .thm 
    }

def tacticExpr (goal : MVarId) (tac : Syntax.Tactic) :
    MetaM (Array MVarId × RuleTacScriptBuilder) := do
  let goalState ← runTactic goal tac 
      {errToSorry := false, implicitLambda := false} {}
  let goals := goalState.1.toArray
  let scriptBuilder :=
    ScriptBuilder.ofTactic goals.size (pure tac)
  return (goals, scriptBuilder)

def applyTacticsAux (tacs : Array Syntax.Tactic) : RuleTac := fun input => do
  let initialState ← saveState
  let apps ← tacs.filterMapM fun (tac) => do
    try
      let (goals, scriptBuilder) ← tacticExpr input.goal tac
      let postState ← saveState
      return some { postState, goals, scriptBuilder }
    catch _ =>
      return none
    finally
      restoreState initialState
  if apps.isEmpty then throwError
    "failed to apply any of the tactics"
  return { applications := apps, postBranchState? := none }

def customTactics : RuleTac := fun input => do 
  let tacs ← getTacticSuggestions
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
  clearTacticSuggestions
  for n in rws do
    addConstRewrite n false
    addConstRewrite n true
  let appRules ← apps.mapM (applyConstRuleMember · p)
  let simpRules ← simps.mapM simpConstRuleMember
  let defaultRules ←
      Frontend.getDefaultRuleSet (includeGlobalSimpTheorems := true)
  let allRules : RuleSet := 
    ((appRules ++ simpRules).push (← customRuleMember p)).foldl
    (fun c r => c.add r) defaultRules
  return allRules

def runAesop (p: Float) (apps simps rws : Array Name) : MVarId → MetaM (List MVarId) := fun goal => do
  let allRules ← getRuleSet p apps simps rws
  let (goals, _) ← Aesop.search goal allRules
  return goals.toList

example : α → α := by
  aesop