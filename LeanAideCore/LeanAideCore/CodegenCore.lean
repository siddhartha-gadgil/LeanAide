import Lean
import LeanAideCore.Aides
import LeanAideCore.Syntax
import LeanAideCore.RunTactics
import LeanAideCore.LLMTactic

/-!
## Code generation from JSON data

This module provides a way to generate Lean code from JSON data in an extensible way. The main function is `getCode`, which takes a `CodeGenerator`, an optional goal, a syntax category, and a JSON object, and returns the corresponding syntax or throws an error.
-/


open Lean Meta Elab LeanAide

initialize registerTraceClass `LeanAide.Codegen
namespace LeanAide

instance : Repr SyntaxNodeKinds where
  reprPrec kinds n :=
    let names : List Name := kinds
    Repr.reprPrec names n

instance : ToString SyntaxNodeKinds where
  toString kinds :=
    let names : List Name := kinds
    ToString.toString names

namespace Codegen

#add_auto_tactics [llm?]

#logIO leanaide.codegen.info
#logFile leanaide.codegen.info

/--
Attribute for generating Lean code, more precisely Syntax of a given category, from JSON data. More precisely, we generate `TranslateM <| Option <| TSyntax Q` from a JSON object, with the matching key as part of the attribute. In some cases, no syntax is generated as the goal is purely to have a side-effect to modify the context.

As the same statement can generate different syntax categories (e.g. `def` and `let`) this is not specified in the attribute. Instead the target category is part of the signature of the function.
-/
syntax (name := codegen) "codegen" (str,*)? : attr

/-- Environment extension storing code generation lemmas -/
initialize codegenExt :
    SimpleScopedEnvExtension (Name × (Option String)) (Std.HashMap (Option String) (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, key?) =>
        m.insert key? <| (m.getD key? #[] ).push n
    initial := {}
  }

/--
Extract the keys from the `codegen` attribute syntax. If no keys are provided, return `none`. If keys are provided, return an array of strings.
-/
def codegenKeyM (stx : Syntax) : CoreM <| Option (Array String) := do
  match stx with
  | `(attr|codegen) => do
    return none
  | `(attr|codegen $x) => do
    return #[x.getString]
  | `(attr|codegen $xs,*) => do
    let keys := xs.getElems
    return keys.map (·.getString)
  | _ => throwUnsupportedSyntax

/--
An environment extension for code generation functions. It stores the functions that can be used to generate code from JSON data. The key is a string that identifies the function, and the value is an array of names of the functions that can be used to generate code for that key.
-/
initialize registerBuiltinAttribute {
  name := `codegen
  descr := "Lean code generator"
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    -- Obtained from Qq.
    let expectedType := Expr.forallE Name.anonymous (Expr.const `LeanAide.CodeGenerator [])
      (Expr.forallE Name.anonymous ((Expr.const `Option [Level.zero]).app (Expr.const `Lean.MVarId []))
        (Expr.forallE `kind (Expr.const `Lean.SyntaxNodeKinds [])
          (Expr.forallE Name.anonymous (Expr.const `Lean.Json [])
            ((Expr.const `LeanAide.TranslateM []).app
              ((Expr.const `Option [Level.zero]).app ((Expr.const `Lean.TSyntax []).app (Expr.bvar 1))))
            BinderInfo.default)
          BinderInfo.default)
        BinderInfo.default)
      BinderInfo.default
    unless ← isDefEq declTy expectedType do
      throwError -- replace with error
        s!"codegen: {decl} has type {declTy}, but expected {expectedType}"
    let keys ← codegenKeyM stx
    -- logInfo m!"codegen: {decl}; keys: {keys}"
    match keys with
    | none => do
      -- no keys, just add the name
      codegenExt.add (decl, none) kind
    | some keys =>
    for key in keys do
      codegenExt.add (decl, key) kind
}

/--
Get the code generation functions for a given key. The key is a string that identifies the function. If no function is found for the key, an error is thrown.
-/
def codegenMatches (key: String) : CoreM <| Array Name := do
  let allKeys := (codegenExt.getState (← getEnv)).toArray.map (fun (k, _) => k)
  let some fs :=
    (codegenExt.getState (← getEnv)).get? key | throwError
      s!"codegen: no function found for key '{key}' available keys are {allKeys.toList}"
  traceAide `leanaide.codegen.info s!"found {fs.size} functions for key {key}"
  if fs.isEmpty then
    traceAide `leanaide.codegen.info s!"no function found for key {key} in {allKeys.toList}"
  return fs

/--
Get the code generation functions that do not have a key associated with them. These functions are used when no key is found in the JSON object.
-/
def codegenKeyless : CoreM <| Array Name := do
  return (codegenExt.getState (← getEnv)).get? none |>.getD #[]

/--
Given a function *name*, a `CodeGenerator`, an optional goal, a syntax category, and a JSON object, this function evaluates the function in the environment and returns the corresponding syntax or throws an error if the function does not match the expected type.
-/
def codeFromFunc (goal? : Option MVarId) (translator: CodeGenerator) (f: Name) (kind : SyntaxNodeKinds) (source: Json) :
    TranslateM (Option (TSyntax kind)) := do
  -- let expectedType := Expr.forallE Name.anonymous (Expr.const `LeanAide.CodeGenerator [])
  --     (Expr.forallE Name.anonymous ((Expr.const `Option [Level.zero]).app (Expr.const `Lean.MVarId []))
  --       (Expr.forallE `kind (Expr.const `Lean.SyntaxNodeKinds [])
  --         (Expr.forallE Name.anonymous (Expr.const `Lean.Json [])
  --           ((Expr.const `LeanAide.TranslateM []).app
  --             ((Expr.const `Option [Level.zero]).app ((Expr.const `Lean.TSyntax []).app (Expr.bvar 1))))
  --           BinderInfo.default)
  --         BinderInfo.default)
  --       BinderInfo.default)
  --     BinderInfo.default
  let code ← unsafe evalConst (CodeGenerator → Option MVarId  → (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))) f
  -- let f := mkConst f
  -- let code ←
  --   unsafe evalExpr
  --     (CodeGenerator → Option MVarId  → (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))) expectedType f
  code translator goal? kind source

/--
Given a JSON object, return the corresponding syntax by matching with `.getKVorType?` and then calling the function in the environment using `codeFromFunc`. The function is expected to return a `TranslateM (Option (TSyntax kind))`, where `kind` is the syntax category of the object.

The return value is an `Option (TSyntax kind)`, which is `none` if the action is purely side-effecting (e.g. modifying the context) and `some` if the action generates code.
-/
partial def getCode  (translator: CodeGenerator) (goal? : Option MVarId) (kind: SyntaxNodeKinds)
  (source: Json) :
    TranslateM (Option (TSyntax kind)) := do
  match source.getKVorType? with
  | some (key, source) => do
    let key := key.toLower
    let fs ←  codegenMatches key
    let mut accumErrors : Array String := #[]
    for f in fs do
      traceAide `leanaide.codegen.info s!"trying {f} for key {key}"
      let translateState ← get
      let termState ← Term.saveState
      try
        -- logInfo m!"codegen: trying {f} for key {key}"
        let code? ← codeFromFunc goal? translator f kind source
        traceAide `leanaide.codegen.info s!"{f} for key {key} worked; returned : {code?.isSome}"
        termState.restore
        return code?
      catch e =>
        logWarning m!"codegen: error in {f} for key {key}: {← e.toMessageData.toString}"
        accumErrors := accumErrors.push s!"{f}: {← e.toMessageData.toString}"
        termState.restore
        set translateState
        continue -- try next function
    let allErrors := accumErrors.toList.foldl (init := "") (fun acc e => acc ++ "\n" ++ e)
    throwError
      s!"codegen: no valid function found for key {key}\nTried functions: {fs}\nErrors in functions:\n{allErrors}\nsource:\n{source.pretty}"
  | none =>
    match source with
    | Json.arr sources =>
      let obj := Json.mkObj [("document", Json.arr sources)]
      getCode translator goal? kind obj
    | _ => do
    let fs ← codegenKeyless
    if fs.isEmpty then
      throwError
        s!"codegen: no key or type found in JSON object {source}, and no codegen functions registered"
    for f in fs.reverse do
      let translateState ← get
      let termState ← Term.saveState
      try
        let code? ← codeFromFunc goal? translator f kind source
        termState.restore
        return code?
      catch _ =>
        termState.restore
        set translateState
        continue -- try next function
    throwError
      s!"codegen: no key or type found in JSON object {source} and no codegen functions returned a result"

open Parser.Tactic Translate
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
  match ← getQuickTactics? goal (← cmdPreludeBlob).hash with
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
    -- TODO(assigned-goal-invariant): Run tactic-mode `getCode` transactionally.
    -- Save Translate and Term/Meta state before invoking it. On failure, restore
    -- both before propagating or trying another candidate. On success, preserve
    -- intentional Translate effects needed by later JSON sources, but always
    -- restore Term/Meta state because the returned tactic syntax is replayed
    -- below. Any Translate value retained across this boundary must be closed
    -- and independent of restored metavariables. Recursive `proofCode` has
    -- violated this boundary by assigning `goal` to a term containing child
    -- metavariables.
    let code? ←
      withoutModifyingTranslateAndTermState do
      try
        getCode translator (some goal) ``tacticSeq source
      catch e =>
        let err ←   e.toMessageData.toString
        traceAide `leanaide.codegen.info s!"Error in getCode `tacticSeq for source {source.pretty}\nError: {err}"
        -- TODO(handler-backtracking): Reach this catch only after the failed
        -- handler's Translate and Term/Meta snapshot has been restored. Preserve
        -- and rethrow fatal or non-rollbackable errors. A recoverable translation
        -- failure may be handled after rollback, but it should terminate this
        -- affected subgoal or produce one explicitly named outermost hole with
        -- the JSON id/claim; converting it to `skip` falsely reports a successful
        -- no-op and consumes later JSON without a proof of the failed step.
        `(tacticSeq | skip)
    -- TODO(assigned-goal-invariant): Before inspecting `code?`, assert that
    -- `goal` is still unassigned. This check must also cover `none` and empty
    -- syntax results, since a nominally side-effect-only handler can leak a
    -- partial assignment. If assigned, log the assignment and recursively
    -- unresolved child metavariables for diagnostics, restore the pre-handler
    -- state, and throw; do not recover by treating those children as JSON goals.
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
        -- TODO(assigned-goal-invariant): Require `goal` to be unassigned and
        -- known to be the current active goal before replay. Prefer an API where
        -- a handler returns `(syntax, remainingGoals)` so generated code is
        -- either executed once here or already executed, never both. Discovery
        -- of child metavariables by traversing an assigned proof term is not a
        -- substitute: it loses the tactic engine's active-goal contract.
        let goal? ← runForSingleGoal goal code
        match goal? with
        | none => do -- tactics closed the goal
          traceAide `leanaide.codegen.info s!"goal closed by tactics"
          traceAide `leanaide.codegen.info s!"goal: {← ppExpr <| ← goal.getType}"
          traceAide `leanaide.codegen.info s!"tactics: {← PrettyPrinter.ppCategory ``tacticSeq code}"
          return (← appendTacticSeqSeq accum code, none)
        | some newGoal => do
          -- TODO(assigned-goal-invariant): Assert that `newGoal` is unassigned
          -- before recursing. `some` must mean exactly one live active goal;
          -- assigned metavariables, tactic failures, and multiple active goals
          -- need distinct structured results and must not enter this branch.
          let newAccum ← appendTacticSeqSeq accum code
          getCodeTacticsAux translator newGoal sources newAccum

def findTactics? (goal :  MVarId):
    TranslateM (Option (TSyntax ``tacticSeq)) := goal.withContext do
  traceAide `leanaide.codegen.info "Trying automation tactics"
  let localNames  ← Translate.defsNames
  traceAide `leanaide.codegen.info s!"previous definitions/theorems names: {localNames}"
  let grindWs ← grindWithSuggestions
  let simpWs ← simpWithSuggestions goal localNames
  runTacticsAndFindTryThis? goal ([← `(tacticSeq|  simp?), ← `(tacticSeq | grind?),
  -- ← `(tacticSeq| try?),
  grindWs, simpWs, ← `(tacticSeq| try simp; exact?)] ++ (← getAutoTactics).toList)
    (← cmdPreludeBlob).hash (strict := true)

def findTacticsI (goal :  MVarId):
    TranslateM (Array (Syntax.Tactic)) := goal.withContext do
  let tacs? ← findTactics? goal
  -- TODO(generation-check-homogeneous): Return an explicit failure (`none` or
  -- an error) when automation finds no proof. Do not treat `repeat sorry` as a
  -- successful tactic sequence; best-effort output may add one terminal hole
  -- only after all generation for this goal has stopped.
  let defaultTacs ← `(tacticSeq| repeat (sorry))
  return getTactics <| tacs?.getD defaultTacs

/--
Empty tactic sequence, used as an initial value for accumulating tactics.
-/
def emptyTacs : CoreM (TSyntax ``tacticSeq) := do
  let xs: Array (TSyntax `tactic) := #[]
  `(tacticSeq| $xs*)


/--
Obtain a sequence of tactics to apply to a goal, given a list of JSON sources. The function first tries to find exact tactics for the goal type, then checks for automation tactics, and finally processes the sources to generate a sequence of tactics.
-/
def getCodeTactics (translator: CodeGenerator) (goal :  MVarId)
  (sources: List Json) :
    TranslateM (TSyntax ``tacticSeq) := goal.withContext do
  -- TODO(assigned-goal-invariant): Define this function's public contract as
  -- transactional syntax generation: it may execute tactics internally, but it
  -- must always restore the entry Term/Meta state before returning or throwing,
  -- since its result is syntax that callers replay. Successful Translate-state
  -- effects may remain when they are part of the generation contract; callers
  -- such as recursive `proofCode` that want no state effects should add the
  -- stronger always-restore wrapper themselves. This central guarantee would
  -- protect every recursive document/section/proof handler; the checks in
  -- `getCodeTacticsAux` should remain as assertions that identify the first
  -- handler that violated the boundary.
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
    -- TODO(assigned-goal-invariant): Treat an assigned `some goal` as a fatal
    -- internal error, regardless of whether its instantiated assignment still
    -- contains metavariables. `getCodeTacticsAux` promises that `some` is one
    -- live, unassigned active goal; a fully assigned value should have returned
    -- `none`, while an assigned value with child metavariables indicates leaked
    -- tactic state. Keep the `instantiateMVars`/`getMVars` traversal only to log
    -- useful diagnostics, then throw after restoring the transactional state.
    -- Do not run automation on rediscovered children: they may not preserve the
    -- tactic engine's goal order, focus, or distinction between user goals and
    -- implementation metavariables.
    let remaining ←
      if ← goal.isAssigned then
        let proof ← instantiateMVars (mkMVar goal)
        let deps ← getMVars proof
        deps.toList.filterM fun m => return !(← m.isAssigned)
      else
        pure [goal]
    if remaining.isEmpty then
      return tacs
    let remainingTacs ← remaining.foldlM (init := #[]) fun accum goal =>
      goal.withContext do
        traceAide `leanaide.codegen.info s!"goal still open after tactics: {← ppExpr <| ← goal.getType}"
        traceAide `leanaide.codegen.info "Local context:"
        let lctx ← getLCtx
        for decl in lctx do
          traceAide `leanaide.codegen.info s!"{decl.userName} : {← ppExpr <| decl.type}"
        let autoTacs ← findTacticsI goal
        traceAide `leanaide.codegen.info s!"auto tactics:"
        for tac in autoTacs do
          traceAide `leanaide.codegen.info s!"{← PrettyPrinter.ppTactic tac}"
        return accum ++ autoTacs
    -- TODO(generation-check-homogeneous): Return an explicit unresolved/terminal
    -- status with these fallback tactics. Syntax containing `repeat sorry` must
    -- not be embedded in a nested proof and followed by more parent proof steps.
    appendTacticSeqSeq tacs (← `(tacticSeq| $remainingTacs*))


/--
Given a `CodeGenerator`, an optional goal, and a list of JSON sources, this function generates a sequence of commands. It processes each source, attempting to generate code for each one. If no code is generated, it continues to the next source. The final result is a sequence of commands that can be executed in Lean.
-/
def getCodeCommands (translator: CodeGenerator) (goal? : Option MVarId)
  (sources: List Json) :
    TranslateM (TSyntax ``commandSeq) := withoutModifyingTranslateAndTermState do
  let mut accum : Array <| TSyntax ``commandSeq := #[]
  for source in sources do
    let code? ←
      try
        -- Translate.withDeferredTheorems do
          getCode translator goal? ``commandSeq source
      catch e =>
        let err ←   e.toMessageData.toString
        traceAide `leanaide.codegen.info s!"Error in processing source for command {source.pretty};\nError: {err}"
        traceAide `leanaide.codegen.info err
        continue

    match code? with
    | none => do -- error with obtaining commands
      continue
    | some code => do
      accum := accum.push code
      runAndCommitCommands code
  if accum.isEmpty then
    let empty : Array <| TSyntax `command := #[]
    `(commandSeq| $empty*)
  else
    let res ← flattenCommandSeq accum
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


partial def getVars (type: Expr) : MetaM <| List Name := do
  match type with
  | .forallE n type body bi => do
    withLocalDecl n  bi type fun x => do
      let type' := body.instantiate1 x
      let names ← getVars type'
      return n::names
  | _ => return []


def findLocalDecl? (name: Name) (type : Expr) : MetaM <| Option FVarId := do
  let lctx ← getLCtx
  match lctx.findFromUserName? name with
  | some (.cdecl _ fVarId _ dtype ..) =>
    let check ← isDefEq dtype type
    logInfo m!"Checking {dtype} and {type} gives {check}"
    if check
      then return fVarId
      else return none
  | _ =>
    if ← isProp type then
      lctx.decls.findSomeM? fun decl =>
        match decl with
        | some <| .cdecl _ fVarId _ dtype .. => do
          let check ← isDefEq dtype type
          traceAide `leanaide.lctx.debug s!"Checking {dtype} and {type} gives {check}"
          if check then pure <| some fVarId
          else pure none
        | _ => pure none
    else
      return none


partial def dropLocalContext (type: Expr) : MetaM Expr := do
  match type with
  | .forallE name binderType body _ => do
    let lctx ← getLCtx
    match lctx.findFromUserName? name with
    | some (.cdecl _ fVarId _ dtype ..) =>
      let check ← match dtype, binderType with
      | .sort _, .sort _ => pure true
      | _, _ =>   isDefEq dtype binderType
        traceAide `leanaide.lctx.debug s!"Checking {dtype} and {type} gives {check}"
      if check then
        let body' := body.instantiate1 (mkFVar fVarId)
        dropLocalContext body'
      else
        traceAide `leanaide.lctx.info s!"Matched username but not {← PrettyPrinter.ppExpr dtype} and {← PrettyPrinter.ppExpr binderType}"
        return type
    | some (.ldecl _ _ _ dtype value ..) =>
      let check ← isDefEq dtype binderType
      traceAide `leanaide.lctx.debug s!"Checking {dtype} and {type} gives {check}"
      if check then
        let body' := body.instantiate1 value
        dropLocalContext body'
      else
        traceAide `leanaide.lctx.info s!"Matched username but not {← PrettyPrinter.ppExpr dtype} and {← PrettyPrinter.ppExpr binderType}"
        return type
    | none =>
      match ← findLocalDecl? name binderType with
      | some fVarId =>
        let body' := body.instantiate1 (mkFVar fVarId)
        dropLocalContext body'
      | none =>
        return type
  | .letE name ltype value body _ =>
    let lctx ← getLCtx
    match lctx.findFromUserName? name with
    | some (.ldecl _ _ _ dtype dvalue ..) =>
      let check ← isDefEq dtype ltype <&&> isDefEq dvalue value
      -- logInfo m!"Checking {dtype} and {type} gives {check}"
      if check then
        let body' := body.instantiate1 value
        dropLocalContext body'
      else
        logToStdErr `leanaide.translate.info s!"Matched username but not {← PrettyPrinter.ppExpr dtype} and {← PrettyPrinter.ppExpr type} or {← PrettyPrinter.ppExpr dvalue} and {← PrettyPrinter.ppExpr value}"
        return type
    | _ =>
      withLetDecl name ltype value fun x => do
          let body' := body.instantiate1 x
          let inner ← dropLocalContext body'
          mkLetFVars #[x] inner
  | _ => return type

partial def fillLocalContext (expr: Expr) : MetaM Expr := do
  match expr with
  | .lam name binderType body _ => do
    let lctx ← getLCtx
    match lctx.findFromUserName? name with
    | some (.cdecl _ fVarId _ dtype ..) =>
      let check ← isDefEq dtype binderType
      -- logInfo m!"Checking {dtype} and {type} gives {check}"
      if check then
        let body' := body.instantiate1 (mkFVar fVarId)
        fillLocalContext body'
      else
        logToStdErr `leanaide.translate.info s!"Matched username but not {← PrettyPrinter.ppExpr dtype} and {← PrettyPrinter.ppExpr binderType}"
        return expr
    | some (.ldecl _ _ _ dtype value ..) =>
      let check ← isDefEq dtype binderType
      -- logInfo m!"Checking {dtype} and {type} gives {check}"
      if check then
        let body' := body.instantiate1 value
        fillLocalContext body'
      else
        logToStdErr `leanaide.translate.info s!"Matched username but not {← PrettyPrinter.ppExpr dtype} and {← PrettyPrinter.ppExpr binderType}"
        return expr
    | _ => return expr
  | .letE name type value body _ =>
    let lctx ← getLCtx
    match lctx.findFromUserName? name with
    | some (.ldecl _ _ _ dtype dvalue ..) =>
      let check ← isDefEq dtype type <&&> isDefEq dvalue value
      -- logInfo m!"Checking {dtype} and {type} gives {check}"
      if check then
          let body' := body.instantiate1 dvalue
          fillLocalContext body'
      else
        logToStdErr `leanaide.translate.info s!"Matched username but not {← PrettyPrinter.ppExpr dtype} and {← PrettyPrinter.ppExpr type} or {← PrettyPrinter.ppExpr dvalue} and {← PrettyPrinter.ppExpr value}"
        return expr
    | _ =>
      withLetDecl name type value fun x => do
          let body' := body.instantiate1 x
          let inner ← fillLocalContext body'
          mkLetFVars #[x] inner
  | _ => return expr



open Lean Meta Tactic Elab Term

partial def existsVarTypesStx (type: Syntax.Term) : MetaM <| Option (Array <| Syntax.Ident × Syntax.Term) := do
  match type with
  | `(∃ $n:ident, $t) => do
    return some <| #[(n, t)] ++ ((← existsVarTypesStx t).getD #[])
  | `(∃ ($n:ident: $_), $t) => do
    return some <| #[(n, t)] ++ ((← existsVarTypesStx t).getD #[])
  | `(∃ $n:ident: $_, $t) => do
    return some <| #[(n, t)] ++ ((← existsVarTypesStx t).getD #[])
  | `(∃ $n:ident $ms*, $t) => do
    let ms' := ms.toList.toArray
    let t' ← `(∃ $ms':binderIdent*, $t)
    return some <| #[(n, t')] ++ ((← existsVarTypesStx t').getD #[])
  | `(∃ ($n:ident :  $_) $ms*, $t) => do
    let t' ← `(∃ $ms*, $t)
    return some <| #[(n, t')] ++ ((← existsVarTypesStx t').getD #[])
  | `(∃ ($n:ident $ms* : $type), $t) => do
    let ms' := ms.toList.toArray
    let t' ← `(∃ $ms':binderIdent* : $type, $t)
    return some <| #[(n, t')] ++ ((← existsVarTypesStx t').getD #[])
  | `(∃ $n:ident $ms* : $type, $t) => do
    let ms' := ms.toList.toArray
    let t' ← `(∃ $ms':binderIdent* : $type, $t)
    return some <| #[(n, t')] ++ ((← existsVarTypesStx t').getD #[])
  | _ =>
    -- logInfo s!"No vars in {type}, i.e., {← ppTerm {env := ← getEnv} type}"
    return none


def resolveExistsHave (type : Syntax.Term) (typeTerm? : Option Syntax.Term :=none) : TermElabM <| Array Syntax.Tactic := do
  let existsVarTypes? ← existsVarTypesStx type
  let existsVarTypes := existsVarTypes?.getD #[]
  let existsVarTypeIdents ←  existsVarTypes.mapM fun (n, t) => do
    let fmt ← ppTerm {env := ← getEnv} t
    let hash₀ := hash fmt.pretty
    let tId : Syntax.Term := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
    pure (n, tId)
  let fmt ← ppTerm {env := ← getEnv} type
  let hash₀ := hash fmt.pretty
  let typeIdent : Syntax.Term := typeTerm?.getD <| mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  let rhsIdents :=
    #[typeIdent] ++ existsVarTypeIdents.map fun (_, tId) => tId
  (existsVarTypeIdents.zip rhsIdents).mapM
    fun ((name, tId), rhs) =>
      `(tactic| let ⟨$name, $tId⟩  := $rhs:term)

def cmdResolveExistsHave (type : Syntax.Term) : TermElabM <| Array Syntax.Command := do
  let existsVarTypes? ← existsVarTypesStx type
  let existsVarTypes := existsVarTypes?.getD #[]
  let mut cmds : Array Syntax.Command := #[]
  let existsVarTypeIdents : Array (Ident ×  Ident × Term) ← existsVarTypes.mapM fun (n, t) => do
    let fmt ← ppTerm {env := ← getEnv} t
    let hash₀ := hash fmt.pretty
    let tId  := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
    pure (n, tId, type)
  let fmt ← ppTerm {env := ← getEnv} type
  let hash₀ := hash fmt.pretty
  let typeIdent : Syntax.Term := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  let mut prevTypeIdent := typeIdent
  let hIdent := mkIdent `h
  for (name, tId, type) in existsVarTypeIdents do
    let defCmd ←
      `(command| def $name  := match $prevTypeIdent:term with
        | ⟨$hIdent, _⟩ => $hIdent)
    cmds := cmds.push defCmd
    let thmCmd ← `(command| theorem $tId : $type  := match $prevTypeIdent:term with
        | ⟨_, $hIdent⟩ => $hIdent)
    cmds := cmds.push thmCmd
    prevTypeIdent := tId
  return cmds


def purgeLocalContext: Syntax.Command →  TranslateM Syntax.Command
| `(command|def $name  : $type := $value) => do
  let typeElab ← elabType type
  let type ← dropLocalContext typeElab
  let type ← delabDetailed type
  `(command|def $name : $type := $value)
| `(command|theorem $name  : $type := $value) => do
  let typeElab ← elabType type
  let type ← dropLocalContext typeElab
  let type ← delabDetailed type
  `(command|theorem $name : $type := $value)
| stx => return stx

example (p: ∃ n m : Nat, n + m = 3): True := by
  let ⟨n, m, h⟩ := p
  exact trivial

open Lean.Parser.Term
/--
Convert theorem or definition to `have` or `let`
-/
def commandToTactic (cmd: Syntax.Command) : TermElabM Syntax.Tactic := do
  match cmd with
  | `(command| theorem $name:ident $args:bracketedBinder* : $type := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| have $name $letArgs* : $type := $value)
  | `(command| def $name:ident $args:bracketedBinder* : $type := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| let $name $letArgs* : $type := $value)
  | `(command| def $name:ident $args:bracketedBinder* := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| let $name $letArgs*  := $value)
  | `(command| noncomputable def $name:ident $args:bracketedBinder* : $type := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| let $name $letArgs* : $type := $value)
  | `(command| noncomputable def $name:ident $args:bracketedBinder* := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| let $name $letArgs*  := $value)
  | _ => `(tactic| sorry)

def commandToTerm (cmd: Syntax.Command) : TermElabM Syntax.Term := do
  match cmd with
  | `(command| $[noncomputable]? def $_name:ident $_args:bracketedBinder* $[: $_type]? := $value) =>
      `(term| $value)
  | _ => throwError s!"commandToTerm: unsupported command {cmd}"

  open Lean.Parser.Tactic

def commandSeqToTacticSeq (cmdSeq: TSyntax ``commandSeq) : TermElabM <| TSyntax ``tacticSeq := do
  let cmds := getCommands cmdSeq
  let tactics ← cmds.mapM commandToTactic
  `(tacticSeq| $tactics:tactic*)

def namesFromCommands (cmds: Array Syntax.Command) : Array Name :=
  cmds.foldl (fun acc cmd =>
    match cmd with
    | `(command| theorem $name:ident $_:bracketedBinder* : $_ := $_) => acc.push name.getId
    | `(command| def $name:ident $_:bracketedBinder* : $_ := $_) => acc.push name.getId
    | _ => acc) #[]

end Codegen
open Codegen

def orAllSimple (terms: List Syntax.Term) : Syntax.Term :=
  match terms with
  | [] => mkIdent `False
  | [h] => h
  | h :: t =>
      -- let t' : List Syntax.Term := t.map fun term => ⟨term⟩
    t.foldl (fun acc cond => Syntax.mkApp (mkIdent `or) #[acc, cond]) h

def orAllSimpleExpr (terms: List Expr) : MetaM Expr := do
  match terms with
  | [] => return mkConst ``False
  | [h] => return h
  | h :: t =>
    let mut result := h
    for term in t do
      result ← mkAppM ``Or #[result, term]
    return result


partial def orAllWithGoal (terms: List Expr) (goal: Expr) : MetaM Expr := do
  match goal with
  | .forallE name type _ bi =>
    withLocalDecl name bi type fun x => do
      let inner ← orAllWithGoal terms type
      mkForallFVars #[x] inner
  | _ =>
    let terms ← terms.mapM dropLocalContext
    orAllSimpleExpr terms


def matchAltTac := Lean.Parser.Term.matchAlt (rhsParser := Lean.Parser.Tactic.matchRhs)

end LeanAide
