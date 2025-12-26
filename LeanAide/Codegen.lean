import Lean
import Qq
import LeanAide.Aides
import LeanAide.TranslateM
import LeanCodePrompts.Translate
import LeanAide.RunTactics
import LeanAide.AutoTactic
import LeanAideCore.Syntax
import Hammer
/-!
## Code generation from JSON data

This module provides a way to generate Lean code from JSON data in an extensible way. The main function is `getCode`, which takes a `CodeGenerator`, an optional goal, a syntax category, and a JSON object, and returns the corresponding syntax or throws an error.
-/


open Lean Meta Qq Elab LeanAide

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
    let expectedType : Q(Type) :=
    q(CodeGenerator → Option MVarId  → (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)))
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
  let expectedType : Q(Type) :=
    q(CodeGenerator → Option MVarId  →  (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)))
  let f := mkConst f
  let code ←
    unsafe evalExpr
      (CodeGenerator → Option MVarId  → (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))) expectedType f
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
      try
        -- logInfo m!"codegen: trying {f} for key {key}"
        let code? ← codeFromFunc goal? translator f kind source
        traceAide `leanaide.codegen.info s!"{f} for key {key} worked; returned : {code?.isSome}"
        return code?
      catch e =>
        logWarning m!"codegen: error in {f} for key {key}: {← e.toMessageData.toString}"
        accumErrors := accumErrors.push s!"{f}: {← e.toMessageData.toString}"
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
      try
        let code? ← codeFromFunc goal? translator f kind source
        return code?
      catch _ =>
        continue -- try next function
    throwError
      s!"codegen: no key or type found in JSON object {source} and no codegen functions returned a result"

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
  match ← getSimpOrExactTactics? goal with
  | some code => do
    traceAide `leanaide.codegen.info s!"exact tactics found for goal: {← ppExpr <| ← goal.getType}"
    -- traceAide `leanaide.codegen.info s!"tactics: {← PrettyPrinter.ppCategory ``tacticSeq code}"
    return (← appendTacticSeqSeq accum code, none)
  | none => do
  -- IO.eprintln "Trying automation tactics"
  -- match ← runTacticsAndGetTryThis? (← goal.getType) #[← `(tactic| hammer {aesopPremises := 5, autoPremises := 0})] (strict := true) with
  -- | some autoTacs => do
  --   let autoTac ← `(tacticSeq| $autoTacs*)
  --   traceAide `leanaide.codegen.info s!"automation closes the goal"
  --   return (← appendTactics accum autoTac, none)
  -- | none => do
  traceAide `leanaide.codegen.info "No exact or automation tactics found, trying sources"
  match sources with
  | [] => do
    return (accum, goal)
  | source::sources => do
    let code? ← try
        getCode translator (some goal) ``tacticSeq source
      catch e =>
        let err ←   e.toMessageData.toString
        let errs := "Error: " ++  err |>.splitOn "\n"
        let errStxs : List Syntax.Tactic ←
          errs.mapM fun err =>
          let errStx := Syntax.mkStrLit <| err
          `(tactic| trace $errStx)
        let errStxs := errStxs.toArray
        pure <| some <| ← `(tacticSeq| $errStxs*)
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

/--
Obtain a sequence of tactics to apply to a goal, given a list of JSON sources. The function first tries to find exact tactics for the goal type, then checks for automation tactics, and finally processes the sources to generate a sequence of tactics.
-/
def getCodeTactics (translator: CodeGenerator) (goal :  MVarId)
  (sources: List Json) :
    TranslateM (TSyntax ``tacticSeq) := goal.withContext do
  traceAide `leanaide.codegen.info "Trying automation tactics"
  match ← runTacticsAndFindTryThis? goal [← `(tacticSeq|  simp?), ← `(tacticSeq | grind?), ← `(tacticSeq| try (try simp?); exact?), ← `(tacticSeq| hammer {aesopPremises := 5, autoPremises := 0})] (strict := true) with
  | some autoTacs => do
    let traceText := Syntax.mkStrLit <| s!"Automation tactics found for {← ppExpr <| ← goal.getType}, closing goal"
    let autoTacs :=
      #[← `(tactic| trace $traceText)] ++ (getTactics autoTacs)
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
      runTacticsAndFindTryThisI goal [← `(tacticSeq|  simp?), ← `(tacticSeq | grind?), ← `(tacticSeq| try (try simp?); exact?), ← `(tacticSeq| hammer {aesopPremises := 5, autoPremises := 0})]
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
