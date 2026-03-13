import Lean
import Qq
import LeanAide.Aides
import LeanAideCore.Translate
import LeanAide.RunTactics
import LeanAide.AutoTactic
import LeanAideCore.Syntax
import LeanAideCore.CodegenCore
import Hammer
/-!
## Code generation from JSON data

This module provides a way to generate Lean code from JSON data in an extensible way. The main function is `getCode`, which takes a `CodeGenerator`, an optional goal, a syntax category, and a JSON object, and returns the corresponding syntax or throws an error.
-/


open Lean Meta Qq Elab LeanAide

namespace LeanAide
namespace Codegen

def exType : Q(Type) :=
    q(CodeGenerator → Option MVarId  → (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)))

-- #eval exType


#logIO leanaide.codegen.info
#logFile leanaide.codegen.info


open Lean.Parser.Tactic
/--
Empty tactic sequence, used as an initial value for accumulating tactics.
-/
def emptyTacs : CoreM (TSyntax ``tacticSeq) := do
  let xs: Array (TSyntax `tactic) := #[]
  `(tacticSeq| $xs*)

/--
Helper function to append tactics obtained from JSON sources to an existing sequence of tactics.
-/
def getCodeTacticsAux (translator: CodeGenerator) (goal :  MVarId)
  (sources: List Json) (accum: TSyntax ``tacticSeq) :
    TranslateM ((TSyntax ``tacticSeq) × Option MVarId) :=
  goal.withContext do
  traceAide `leanaide.codegen.info "Trying assumptions"
  try
    goal.assumption
    return (← appendTacticSeqSeq accum (← `(tacticSeq| assumption)), none)
  catch _ =>
  traceAide `leanaide.codegen.info "Trying exact tactics or automation"
  match ← getQuickTactics? goal with
  | some code => do
    traceAide `leanaide.codegen.info s!"exact tactics found for goal: {← ppExpr <| ← goal.getType}"
    -- traceAide `leanaide.codegen.info s!"tactics: {← PrettyPrinter.ppCategory ``tacticSeq code}"
    return (← appendTacticSeqSeq accum code, none)
  | none => do
  traceAide `leanaide.codegen.info "No exact or automation tactics found, trying sources"
  match sources with
  | [] => do
    return (accum, goal)
  | source::sources => do
    let code? ← try
        getCode translator (some goal) ``tacticSeq source
      catch e =>
        let err ←   e.toMessageData.toString
        traceAide `leanaide.codegen.info err
        --let sourceId := mkIdent (s!"error_source_{hash source}").toName
        let strLit := Syntax.mkStrLit s!"Error in processing:{source.pretty}"
        let sourceTacs ← `(tacticSeq| trace $strLit)
          -- try
          --  let stx ← getJsonSyntax source
          --  `(tacticSeq| let $sourceId : Json := json% $stx; sorry)
          -- catch _ =>
          --  let strLit := Syntax.mkStrLit (source.pretty)
          --  `(tacticSeq| let $sourceId : String := $strLit; sorry)
        -- let errs := "Error: " ++  err |>.splitOn "\n"
        -- let errStxs : List Syntax.Tactic ←
        --   errs.mapM fun err =>
        --   let errStx := Syntax.mkStrLit <| err
        --   `(tactic| trace $errStx)
        -- let errStxs := errStxs.toArray
        -- pure <| some <| ← `(tacticSeq| $errStxs*)
        pure <| some <| sourceTacs
    match code? with
    | none => do -- pure side effect, no code generated
      getCodeTacticsAux translator goal sources accum
    | some code => do
      if (getTactics code).isEmpty then
        -- no tactics generated, but side effect
        getCodeTacticsAux translator goal sources accum
      else
        if ← endsWithDone code then
          -- the tactics are "done", so we can return the accumulated tactics
          traceAide `leanaide.codegen.info s!"goal still open after tactics, but tactics end with 'done' so no further tactics generated."
          traceAide `leanaide.codegen.info s!"goal: {← ppExpr <| ← goal.getType}"
          traceAide `leanaide.codegen.info s!"tactics: {← PrettyPrinter.ppCategory ``tacticSeq code}"
          return (← appendTacticSeqSeq accum code, none)
        else
            -- continue with the next source
        let goal? ← runForSingleGoal goal code
        match goal? with
        | none => do -- tactics closed the goal
          traceAide `leanaide.codegen.info s!"goal closed by tactics"
          traceAide `leanaide.codegen.info s!"goal: {← ppExpr <| ← goal.getType}"
          traceAide `leanaide.codegen.info s!"tactics: {← PrettyPrinter.ppCategory ``tacticSeq code}"
          return (← appendTacticSeqSeq accum code, none)
        | some newGoal => do
          let newAccum ← appendTacticSeqSeq accum code
          getCodeTacticsAux translator newGoal sources newAccum


def findTactics? (goal :  MVarId):
    TranslateM (Option (TSyntax ``tacticSeq)) := goal.withContext do
  traceAide `leanaide.codegen.info "Trying automation tactics"
  let localNames  ← Translate.defsNames
  traceAide `leanaide.codegen.info s!"previous definitions/theorems names: {localNames}"
  let grindWs ← grindWithSuggestions goal (← localNames.filterM fun n => checkGrind n)
  let simpWs ← simpWithSuggestions goal localNames
  runTacticsAndFindTryThis? goal ([← `(tacticSeq|  simp?), ← `(tacticSeq | grind?), ← `(tacticSeq| try?), grindWs, simpWs, ← `(tacticSeq| try simp; exact?)] ++ (← getAutoTactics).toList) (strict := true)

def findTacticsI (goal :  MVarId):
    TranslateM (Array (Syntax.Tactic)) := goal.withContext do
  let tacs? ← findTactics? goal
  let defaultTacs ← `(tacticSeq| repeat (sorry))
  return getTactics <| tacs?.getD defaultTacs

/--
Obtain a sequence of tactics to apply to a goal, given a list of JSON sources. The function first tries to find exact tactics for the goal type, then checks for automation tactics, and finally processes the sources to generate a sequence of tactics.
-/
def getCodeTactics (translator: CodeGenerator) (goal :  MVarId)
  (sources: List Json) :
    TranslateM (TSyntax ``tacticSeq) := goal.withContext do
  match ← findTactics? goal with
  | some autoTacs => do
    -- let traceText := Syntax.mkStrLit <| s!"Automation tactics found for {← ppExpr <| ← goal.getType}, closing goal"
    let autoTacs :=
      (getTactics autoTacs)
    let autoTac ← `(tacticSeq| $autoTacs*)
    traceAide `leanaide.codegen.info s!"automation closes the goal"
    return autoTac
  | none => do
  let accum ← emptyTacs
  let (tacs, goal?) ←
     getCodeTacticsAux translator goal sources accum
  match goal? with
  | none => do
    return tacs
  | some goal => goal.withContext do
    if ← goal.isAssigned then
      return tacs
    else
    traceAide `leanaide.codegen.info s!"goal still open after tactics: {← ppExpr <| ← goal.getType}"
    traceAide `leanaide.codegen.info "Local context:"
    let lctx ← getLCtx
    for decl in lctx do
      traceAide `leanaide.codegen.info s!"{decl.userName} : {← ppExpr <| decl.type}"
    let autoTacs ←
      findTacticsI goal
    traceAide `leanaide.codegen.info s!"auto tactics:"
    for tac in autoTacs do
      traceAide `leanaide.codegen.info s!"{← PrettyPrinter.ppTactic tac}"
    appendTacticSeqSeq tacs (← `(tacticSeq| $autoTacs*))


/--
Given a `CodeGenerator`, an optional goal, and a list of JSON sources, this function generates a sequence of commands. It processes each source, attempting to generate code for each one. If no code is generated, it continues to the next source. The final result is a sequence of commands that can be executed in Lean.
-/
def getCodeCommands (translator: CodeGenerator) (goal? : Option MVarId)
  (sources: List Json) :
    TranslateM (TSyntax ``commandSeq) := withoutModifyingState do
  let mut accum : Array <| TSyntax ``commandSeq := #[]
  for source in sources do
    let code? ←
      try
        -- Translate.withDeferredTheorems do
          getCode translator goal? ``commandSeq source
      catch e =>
        let err ←   e.toMessageData.toString
        let errs := "Error: " ++  err |>.splitOn "\n"
        let errStxs : List Syntax.Command ←
          errs.mapM fun err =>
          let errStx := Syntax.mkStrLit <| err
          `(command| #check $errStx)
        let errStxs := errStxs.toArray
        pure <| some <| ← `(commandSeq| $errStxs*)

    match code? with
    | none => do -- error with obtaining commands
      continue
    | some code => do
      accum := accum.push code
  if accum.isEmpty then
    let empty : Array <| TSyntax `command := #[]
    `(commandSeq| $empty*)
  else
    let res ← flattenCommandSeq accum
    Translate.addCommands res
    return res


/--
No code generation function, used when no code is expected to be generated from the JSON object. It returns `none` for the given syntax category.
-/
def noCode : CodeGenerator → Option MVarId  →
  (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)) := fun _ _ _ _  => do
  return none

/--
Placeholder function for code generation that is not implemented yet. It logs a warning and returns `none` for the given syntax category. This is used to indicate that the code generation for a specific key or category is not yet implemented.
-/
def notImplementedCode (name: String) : CodeGenerator → Option MVarId  →
  (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)) := fun _ _ _ _  => do
  traceAide `leanaide.codegen.info s!"{name} not implemented"
  logWarning m!"codegen: {name} not implemented"
  return none

macro "#notImplementedCode" name:str : command => do
  let thmName := mkIdent <| (name.getString ++ "Impl").toName
  `(command | @[codegen $name]
  def $thmName := notImplementedCode $name)

/--
Generate code for a context run, which is expected to be a pure side effect without returning any code. It processes an array of JSON objects and logs a warning if any code is generated.
-/
def contextRun (translator: CodeGenerator) (goal? : Option MVarId)
  (kind: SyntaxNodeKinds) (source: Json) :
    TranslateM Unit := do
  match source.getArr?  with
  | .ok sources => do
    for source in sources do
      let _code ← getCode translator goal? kind source
      -- unless code.isNone do
      --   traceAide `leanaide.codegen.info s!"contextCode expected pure side effect, but got {code}"
      --   logWarning m!"codegen: contextCode expected pure side effect, but got {code}"
    return
  | .error _ => do
    throwError
      s!"codegen: contextCode expected an array of JSON objects, but got {source}"

end Codegen

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
#add_auto_tactics [hammer {aesopPremises := 5, autoPremises := 0}, try_this (constructor) then (grind?)]

-- #eval getAutoTactics


open Command Elab Term Tactic Codegen
-- @[command_elab codegenCmd]
def elabCodegenCmdImpl' : CommandElab
| stx@`(command| #codegen $s:term) =>
  Command.liftTermElabM do
  withoutModifyingEnv do
    let source : Q(Json) ← elabTerm s q(Json)
    let e := q(getCode CodeGenerator.default none ``commandSeq $source)
    let codeM? ←
      unsafe evalExpr (TranslateM (Option (TSyntax ``commandSeq))) q((TranslateM (Option (TSyntax ``commandSeq)))) e
    let code? ←  codeM?.run' {}
    let code := code?.getD (← `(commandSeq|#check "No code generated"))
    TryThis.addSuggestion stx code
| _ => throwUnsupportedSyntax


/-!
Resolving existential theorems:
* We have a series of let statements, each of which introduces a variable and a proof that it exists.
* The proof is passed recursively to the next let statement.
* We start with a type and a witness for it.
* If the type is existential, we resolve the witness.
* The resolved proof and term used will depend on variables, so we will have to export these.
* **Alternative:** We only resolve other existential theorems if they are used, and we fill in the arguments with the local context.
* Seems like a good approach to include used theorems in the local context, filling in the arguments with the local context.
-/
example : True := by
  have egExists : ∃ n: Nat, n = 3 := by
    use 3
  let ⟨n, h⟩ := egExists
  simp




end LeanAide
